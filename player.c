/*
 * Slave-clocked ALAC stream player. This file is part of Shairport.
 * Copyright (c) James Laird 2011, 2013
 * All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/types.h>
#include <pthread.h>
#include <openssl/aes.h>
#include <math.h>
#include <sys/stat.h>
#include <sys/signal.h>
#include <assert.h>
#include <fcntl.h>
#include <stdlib.h>
#include <soxr.h>
//#include <soxr-lsr.h>

#include "common.h"
#include "player.h"
#include "rtp.h"

#ifdef FANCY_RESAMPLING
#include <samplerate.h>
#endif

#include "alac.h"

// parameters from the source
static unsigned char *aesiv;
static AES_KEY aes;
static int sampling_rate, frame_size;
static int ntp_sync_rate;

#define FRAME_BYTES(frame_size) (4*frame_size)
// maximal resampling shift - conservative
#define OUTFRAME_BYTES(frame_size) (4*(frame_size+3))

static pthread_t player_thread;
static int please_stop;

static alac_file *decoder_info;

#ifdef FANCY_RESAMPLING
static int fancy_resampling = 1;
static SRC_STATE *src;
#endif
static soxr_quality_spec_t qspec;


// interthread variables
static double volume = 1.0;
static int fix_volume = 0x10000;
static pthread_mutex_t vol_mutex = PTHREAD_MUTEX_INITIALIZER;

// default buffer size
// needs to be a power of 2 because of the way BUFIDX(seqno) works
#define BUFFER_FRAMES  512
#define MAX_PACKET      2048
#define RESEND_FOCUS   (BUFFER_FRAMES/4)
static int sane_buffer_size;

//player states
#define BUFFERING 0
#define SYNCING   1
#define PLAYING   2
int state;

//buffer states
#define SIGNALLOSS 0
#define UNSYNC 1
#define INSYNC 2

typedef struct audio_buffer_entry {   // decoded audio packets
    int ready;
    sync_cfg sync;
    signed short *data;
} abuf_t;
static abuf_t audio_buffer[BUFFER_FRAMES];
#define BUFIDX(seqno) ((seq_t)(seqno) % BUFFER_FRAMES)

// mutex-protected variables
static seq_t ab_read, ab_write;
static int ab_buffering = 1, ab_synced = SIGNALLOSS;
static pthread_mutex_t ab_mutex = PTHREAD_MUTEX_INITIALIZER;

static void ab_resync(void) {
    int i;
    for (i=0; i<BUFFER_FRAMES; i++)
        audio_buffer[i].ready = 0;
    ab_synced = SIGNALLOSS;
    ab_buffering = 1;
    state = BUFFERING;
}

// reset the audio frames in the range to NOT ready
static void ab_reset(seq_t from, seq_t to) {
    abuf_t *abuf = 0;

    while (seq_diff(from, to)) {
        if (seq_diff(from, to) >= BUFFER_FRAMES) {
           from =  from + BUFFER_FRAMES;
        } else {
           abuf = audio_buffer + BUFIDX(from);
           abuf->ready = 0;
           from++;
        }
    }
}

// the sequence numbers will wrap pretty often.
// this returns true if the second arg is after the first
static inline int seq_order(seq_t a, seq_t b) {
    signed short d = b - a;
    return d > 0;
}

static void alac_decode(short *dest, uint8_t *buf, int len) {
    unsigned char packet[MAX_PACKET];
    assert(len<=MAX_PACKET);

    unsigned char iv[16];
    int aeslen = len & ~0xf;
    memcpy(iv, aesiv, sizeof(iv));
    AES_cbc_encrypt(buf, packet, aeslen, &aes, iv, AES_DECRYPT);
    memcpy(packet+aeslen, buf+aeslen, len-aeslen);

    int outsize;

    alac_decode_frame(decoder_info, packet, dest, &outsize);

    assert(outsize == FRAME_BYTES(frame_size));
}


static int init_decoder(int32_t fmtp[12]) {
    alac_file *alac;

    frame_size = fmtp[1]; // stereo samples
    sampling_rate = fmtp[11];

    int sample_size = fmtp[3];
    if (sample_size != 16)
        die("only 16-bit samples supported!");

    alac = alac_create(sample_size, 2);
    if (!alac)
        return 1;
    decoder_info = alac;

    alac->setinfo_max_samples_per_frame = frame_size;
    alac->setinfo_7a =      fmtp[2];
    alac->setinfo_sample_size = sample_size;
    alac->setinfo_rice_historymult = fmtp[4];
    alac->setinfo_rice_initialhistory = fmtp[5];
    alac->setinfo_rice_kmodifier = fmtp[6];
    alac->setinfo_7f =      fmtp[7];
    alac->setinfo_80 =      fmtp[8];
    alac->setinfo_82 =      fmtp[9];
    alac->setinfo_86 =      fmtp[10];
    alac->setinfo_8a_rate = fmtp[11];
    alac_allocate_buffers(alac);
    return 0;
}

static void free_decoder(void) {
    alac_free(decoder_info);
}

#ifdef FANCY_RESAMPLING
static int init_src(void) {
    int err;
    if (fancy_resampling)
        src = src_new(SRC_SINC_MEDIUM_QUALITY, 2, &err);
    else
        src = NULL;

    return err;
}
static void free_src(void) {
    src_delete(src);
    src = NULL;
}
#endif

static void init_buffer(void) {
    int i;
    for (i=0; i<BUFFER_FRAMES; i++)
        audio_buffer[i].data = malloc(OUTFRAME_BYTES(frame_size));
    ab_resync();
}

static void free_buffer(void) {
    int i;
    for (i=0; i<BUFFER_FRAMES; i++)
        free(audio_buffer[i].data);
}

static long us_to_frames(long long us) {
    return us * sampling_rate / 1000000;
}

static inline long long get_sync_time(long long ntp_tsp) {
    long long sync_time_est;
    sync_time_est = (ntp_tsp + config.delay) - (tstp_us() + get_ntp_offset() + config.output->get_delay());
    return sync_time_est;
}

void player_put_packet(seq_t seqno, sync_cfg sync_tag, uint8_t *data, int len) {
    abuf_t *abuf = 0;
    int16_t buf_fill;

    pthread_mutex_lock(&ab_mutex);
    if (ab_synced == SIGNALLOSS) {
        debug(2, "picking up first seqno %04X\n", seqno);
        ab_write = seqno;
        ab_read = seqno;
        ab_synced = UNSYNC;
    }
    debug(3, "packet: ab_write %04X, ab_read %04X, seqno %04X\n", ab_write, ab_read, seqno);
    if (seq_diff(ab_write, seqno) == 0) {                  // expected packet
        abuf = audio_buffer + BUFIDX(seqno);
        ab_write++;
    } else if (seq_order(ab_write, seqno)) {    // newer than expected
	// Be careful with new packets that are in advance
	// Too far in advance will lead to multiple resends and probable overrun
	// Better just to force a resync on the new packet
	if (seq_diff(ab_write, seqno) >= (BUFFER_FRAMES/4)) {	// packet too far in advance - better to resync
	   warn("out of range re-sync %04X (%04X:%04X)", seqno, ab_read, ab_write);
	   ab_resync();
	   ab_synced = UNSYNC;
	   ab_read = seqno;
	} else if (seq_diff(ab_read,seqno) >= BUFFER_FRAMES) {	// this packet will cause overrun
								// must handle here to tidy buffer frames skipped
           warn("advance overrun %04X (%04X:%04X)", seqno, ab_read, ab_write);
           ab_read = seqno - (BUFFER_FRAMES/2);			// restart at a sane distance
           ab_reset((ab_write - BUFFER_FRAMES), ab_read);	// reset any ready frames in those we've skipped (avoiding wrap around)
	} else {
           debug(1, "advance packet %04X (%04X:%04X)\n", seqno, ab_read, ab_write);
           if (!ab_buffering) {rtp_request_resend(ab_write, seqno-1);}
	}
        abuf = audio_buffer + BUFIDX(seqno);
        ab_write = seqno+1;
    } else if (seq_order(ab_read - 1, seqno)) {     // late but not yet played
        abuf = audio_buffer + BUFIDX(seqno);
	if (abuf->ready) {			// discard this frame if frame previously received
	   abuf =0;
           debug(1, "duplicate packet %04X (%04X:%04X)\n", seqno, ab_read, ab_write);
	}
    } else {    // too late.
        if (seq_diff(ab_read, ab_write)) { debug(1, "late packet %04X (%04X:%04X)\n", seqno, ab_read, ab_write); } // Assume flush if buffer empty - don't debug
    }
    buf_fill = seq_diff(ab_read, ab_write);
    pthread_mutex_unlock(&ab_mutex);

    if (abuf) {
        alac_decode(abuf->data, data, len);
        abuf->sync.rtp_tsp = sync_tag.rtp_tsp;
        // sync packets with extension bit seem to be one audio packet off:
        // if the extension bit was set, pull back the ntp time by one packet's time
        if (sync_tag.sync_mode == E_NTPSYNC) {
            abuf->sync.ntp_tsp = sync_tag.ntp_tsp - (long long)frame_size * 1000000LL / (long long)sampling_rate;
            abuf->sync.sync_mode = NTPSYNC;
        } else {
            abuf->sync.ntp_tsp = sync_tag.ntp_tsp;
            abuf->sync.sync_mode = sync_tag.sync_mode;
        }
        abuf->ready = 1;
    }

    pthread_mutex_lock(&ab_mutex);
    if ((abuf) && (ab_synced == UNSYNC) && ((sync_tag.sync_mode == NTPSYNC) || (sync_tag.sync_mode == E_NTPSYNC))) {
       // only stop buffering when the new frame is a timestamp with good sync
       long long sync_time = get_sync_time(abuf->sync.ntp_tsp);
       if (sync_time > (config.delay/8)) {
          debug(1, "found good sync (%04X:%04X) sync: %lld\n", ab_read, ab_write, sync_time);
          ab_synced = INSYNC;
       } else {
          debug(1, "sync not yet found (%04X:%04X) sync: %lld\n", ab_read, ab_write, sync_time);
       }
       ab_reset(ab_read, seqno);
       ab_read = seqno;
    }
    if ((abuf) && (ab_synced == INSYNC) && (ab_buffering) && (buf_fill >= sane_buffer_size)) {
        debug(1, "buffering over. starting play\n");
        ab_buffering = 0;
    }
    pthread_mutex_unlock(&ab_mutex);
}


static short lcg_rand(void) {
	static unsigned long lcg_prev = 12345;
	lcg_prev = lcg_prev * 69069 + 3;
	return lcg_prev & 0xffff;
}

static inline short dithered_vol(short sample) {
    static short rand_a, rand_b;
    long out;

    out = (long)sample * fix_volume;
    if (fix_volume < 0x10000) {
        rand_b = rand_a;
        rand_a = lcg_rand();
        out += rand_a;
        out -= rand_b;
    }
    return out>>16;
}

// get the next frame, when available. return 0 if underrun/stream reset.
static short *buffer_get_frame(sync_cfg *sync_tag) {
    int16_t buf_fill;
    seq_t next;
    abuf_t *abuf = 0;
    int i;

    sync_tag->sync_mode = NOSYNC;

    pthread_mutex_lock(&ab_mutex);
    if (ab_buffering) {
        pthread_mutex_unlock(&ab_mutex);
        return 0;
    }

    buf_fill = seq_diff(ab_read, ab_write);
    if (buf_fill < 1) {
        warn("underrun %i (%04X:%04X)", buf_fill, ab_read, ab_write);
	ab_resync();
        pthread_mutex_unlock(&ab_mutex);
        return 0;
    }
    if (buf_fill >= BUFFER_FRAMES) {   // overrunning! uh-oh. restart at a sane distance
        warn("overrun %i (%04X:%04X)", buf_fill, ab_read, ab_write);
        ab_read = ab_write - (BUFFER_FRAMES/2);
	ab_reset((ab_write - BUFFER_FRAMES), ab_read);	// reset any ready frames in those we've skipped (avoiding wrap around)
    }

    // check if t+16, t+32, t+64, t+128, ... resend focus boundary
    // packets have arrived... last-chance resend
    if (!ab_buffering) {
        for (i = 16; i <= RESEND_FOCUS; i = (i * 2)) {
            next = ab_read + i;
            abuf = audio_buffer + BUFIDX(next);
            if ((!abuf->ready) && (seq_order(next,(ab_write-1)))){
                rtp_request_resend(next, next);
                debug(1, "last chance resend T+%i, %04X (%04X:%04X)\n", i, next, ab_read, ab_write);
            }
        }
    }

    abuf_t *curframe = audio_buffer + BUFIDX(ab_read);
    if (!curframe->ready) {
        debug(1, "missing frame %04X\n", ab_read);
        memset(curframe->data, 0, FRAME_BYTES(frame_size));
    }
    ab_read++;
    curframe->ready = 0;
    sync_tag->rtp_tsp = curframe->sync.rtp_tsp;
    sync_tag->ntp_tsp = curframe->sync.ntp_tsp;
    sync_tag->sync_mode = curframe->sync.sync_mode;
    pthread_mutex_unlock(&ab_mutex);

    return curframe->data;
}

#define TUNE_RATIO 10.0
#define TUNE_THRESHOLD 5.0

static long tuning_samples = 0L;
static long tuning_stuffs = 0L;
static long max_sync_delay = 0L;
static long min_sync_delay = 0L;

static int stuff_buffer(short *inptr, short *outptr, long *sync_info, double *sync_diff, int *stuff_count) {
    int i, samp;
    int stuff = 0;
    int frames;
    double p_stuff;
    signed short *out = outptr;

    // use the sync info which contains the total number of samples adrift
    // to adjust the behaviour of stuff buffer

    frames =  *sync_info / frame_size;
    if (frames < -2) {                                       	// if we are more than a couple of full frame behind drop that frame
        *sync_info = *sync_info + frame_size;
        debug(3, "stuff buffer, dropped frame\n");
        return 0;
    }

    // maintain tuning statistics for the rate matching algorithm
    if (tuning_samples >= 1000000L) {
       debug(1, "playback: corrections (stuffs) %3ld ppm, sync err (samples) max/min %3ld:%4ld\n", tuning_stuffs, max_sync_delay, min_sync_delay);

       tuning_samples = 0L;
       tuning_stuffs = 0L;
       max_sync_delay = 0L;
       min_sync_delay = 0L;
    }
    tuning_samples = tuning_samples + frame_size;
    max_sync_delay = (*sync_info > max_sync_delay ? *sync_info : max_sync_delay);
    min_sync_delay = (*sync_info < min_sync_delay ? *sync_info : min_sync_delay);

    p_stuff = (labs(*sync_diff) / TUNE_RATIO);	  		 // Set to add or delete the desired samples one per frame
    if ((rand() < (p_stuff * RAND_MAX/(double)ntp_sync_rate)) && // Apply over the next ntp sync period to frames chosen pseudo randomly
        (p_stuff > TUNE_THRESHOLD)) {	                         // Do not stuff on minor delta
        stuff = *sync_diff/labs(*sync_diff);                     // this should mean we are adjusting fewer samples - better for bit perfect playback (!)
    }

    pthread_mutex_lock(&vol_mutex);
    memset(outptr, 0, OUTFRAME_BYTES(frame_size));
    for (i=0; i<frame_size; i++) {   // the whole frame, if no stuffing
        *outptr++ = dithered_vol(*inptr++);
        *outptr++ = dithered_vol(*inptr++);
    };
    outptr = out;						// Reset the pointers to the start of each buffer
    if (stuff) {
    	soxr_io_spec_t io_spec;
  	signed short *src_s_out, *src_s_out_bu;

  	src_s_out_bu = src_s_out = malloc(sizeof(*src_s_out) * 2 * (frame_size + 2)); /* Allocate output buffer. */

    	io_spec.itype = SOXR_INT16_I;
    	io_spec.otype = SOXR_INT16_I;
    	io_spec.flags = 0;
    	io_spec.scale = 1.0;
    	io_spec.e = 0;

    	size_t odone;
    	soxr_error_t error = soxr_oneshot(frame_size, frame_size + stuff, 2, /* Rates and # of chans. */
    	outptr, frame_size, NULL, /* Input. */
    	src_s_out, frame_size + stuff, &odone, /* Output. */
    	&io_spec, /* I/O format */
    	&qspec, NULL); /* Default configuration.*/
    	if (error)
    		die("soxr error: %s\n", "error: %s\n", soxr_strerror(error));

    	// assert we have the whole frame
    	if (odone > frame_size + 1)
    		die("odone = %d!\n", odone);

        (*stuff_count)++;
        tuning_stuffs++;

    	// keep last 7 samples
        if (stuff==1) {
            debug(3, "+++++++++\n");
            // shift samples right
            for (i=0; i < 7 * 2; i++){
            	samp = (frame_size * 2) - 1 - i;
                outptr[samp + 2] = outptr[samp];
            }
        } else if (stuff==-1) {
            debug(3, "---------\n");
            // shift samples left
            for (i=0; i < 7 * 2; i++){
            	samp = (frame_size * 2) - 7 * 2 + i;
                outptr[samp - 2] = outptr[samp];
            }
        }
    	// keep first 7 samples
    	outptr = outptr + 7 * 2;
    	src_s_out = src_s_out + 7 * 2;

    	// copy SOXR buffer keep first & last 7 samples from original
        for (i=0; i<frame_size + stuff - 7 * 2; i++) {   //
            *outptr++ = *src_s_out++;
            *outptr++ = *src_s_out++;
        }
        free(src_s_out_bu);
    }
    pthread_mutex_unlock(&vol_mutex);

    return frame_size + stuff;
}

//constant first-order filter
#define ALPHA 0.50

static void *player_thread_func(void *arg) {
    int play_samples = frame_size;
    int ntp_sync_count = 0;
    sync_cfg sync_tag;
    long long sync_time;
    long sync_frames = 0;
    double sync_frames_diff;
    int stuff_count = 0;
    state = BUFFERING;

    signed short *inbuf, *outbuf, *resbuf, *silence;
    outbuf = resbuf = malloc(OUTFRAME_BYTES(frame_size));
    inbuf = silence = malloc(OUTFRAME_BYTES(frame_size));
    memset(silence, 0, OUTFRAME_BYTES(frame_size));


#ifdef FANCY_RESAMPLING
    float *frame, *outframe;
    SRC_DATA srcdat;
    if (fancy_resampling) {
        frame = malloc(frame_size*2*sizeof(float));
        outframe = malloc(2*frame_size*2*sizeof(float));

        srcdat.data_in = frame;
        srcdat.data_out = outframe;
        srcdat.input_frames = FRAME_BYTES(frame_size);
        srcdat.output_frames = 2*FRAME_BYTES(frame_size);
        srcdat.src_ratio = 1.0;
        srcdat.end_of_input = 0;
    }
#endif
    debug(1,"Player STATE: %d\n", state);
    while (!please_stop) {
        switch (state) {
        case BUFFERING: {
            inbuf = buffer_get_frame(&sync_tag);
            // as long as the buffer keeps returning NULL, we assume it is still filling up
            if (inbuf) {
                if (sync_tag.sync_mode != NOSYNC) {
                    // figure out how much silence to insert before playback starts
                    sync_frames = us_to_frames(get_sync_time(sync_tag.ntp_tsp));
                } else {
                    // what if first packet(s) is lost?
                    warn("Ouch! first packet has no sync...\n");
                    sync_frames = us_to_frames(config.delay) - config.output->get_delay();
                }
                if (sync_frames < 0)
                    sync_frames = 0;
                debug(1, "Fill with %ld frames and %ld samples\n", sync_frames / frame_size , sync_frames % frame_size);
                state = SYNCING;
                debug(1,"Changing player STATE: %d\n", state);
            }
            outbuf = silence;
            play_samples = frame_size;
            break;
        }
        case SYNCING: {
            if (sync_frames > 0) {
                if (((sync_frames < frame_size * 50) && (sync_frames >= frame_size * 49)) && \
                        (sync_tag.sync_mode != NOSYNC)) {
                    debug(3,"sync_frames adjusting: %d->", sync_frames);
                    // figure out how much silence to insert before playback starts
                    sync_frames = us_to_frames(get_sync_time(sync_tag.ntp_tsp));
                    if (sync_frames < 0)
                        sync_frames = 0;
                    debug(3,"%d\n", sync_frames);
                }
                play_samples = (sync_frames >= frame_size ? frame_size : sync_frames);
                outbuf = silence;
                sync_frames -= play_samples;

                debug(3,"Samples to go before playback start: %d\n", sync_frames);
            } else {
                outbuf = resbuf;
                sync_frames_diff = 0.0;
                play_samples = stuff_buffer(inbuf, outbuf, &sync_frames, &sync_frames_diff, &stuff_count);
                stuff_count = 0;
                state = PLAYING;
                debug(1,"Changing player STATE: %d\n", state);
            }
            break;
        }
        case PLAYING: {
            inbuf = buffer_get_frame(&sync_tag);
            if (!inbuf)
                inbuf = silence;
#ifdef FANCY_RESAMPLING
            if (fancy_resampling) {
                int i;
                pthread_mutex_lock(&vol_mutex);
                for (i=0; i<2*FRAME_BYTES(frame_size); i++) {
                    frame[i] = (float)inbuf[i] / 32768.0;
                    frame[i] *= volume;
                }
                pthread_mutex_unlock(&vol_mutex);
                srcdat.src_ratio = bf_playback_rate;
                src_process(src, &srcdat);
                assert(srcdat.input_frames_used == FRAME_BYTES(frame_size));
                src_float_to_short_array(outframe, outbuf, FRAME_BYTES(frame_size)*2);
                play_samples = srcdat.output_frames_gen;
            } else
#endif
            ntp_sync_count++;
            if (sync_tag.sync_mode == NTPSYNC) {
                ntp_sync_rate = ntp_sync_count;				// Establish the number of frames between NTP Syncs
                ntp_sync_count = 0;
                //check if we're still in sync.
                sync_time = get_sync_time(sync_tag.ntp_tsp);
                sync_frames = us_to_frames(sync_time);
                sync_frames_diff = (ALPHA * sync_frames_diff) + ((1.0 - ALPHA) * (double) sync_frames);
                debug(2, "Sync timers: fill %i, NTP fame rate %d. sync (time) %5lld (samples) %5d:%6.1f, previous stuffs %d\n", seq_diff(ab_read, ab_write), ntp_sync_rate, sync_time, sync_frames, sync_frames_diff, stuff_count);
                stuff_count = 0;
            }
            play_samples = stuff_buffer(inbuf, outbuf, &sync_frames, &sync_frames_diff, &stuff_count);
            break;
        }
        default:
            break;
        }
        config.output->play(outbuf, play_samples);
    }

    free(resbuf);
    free(silence);
    return 0;
}

// takes the volume as specified by the airplay protocol
void player_volume(double f) {
    double linear_volume = pow(10.0, 0.05*f);

    if (config.output->volume) {
        config.output->volume(linear_volume);
    } else {
        pthread_mutex_lock(&vol_mutex);
        volume = linear_volume;
        fix_volume = 65536.0 * volume;
        pthread_mutex_unlock(&vol_mutex);
    }
}

unsigned long player_flush(int seqno, unsigned long rtp_tsp) {
    unsigned long result = 0;
    pthread_mutex_lock(&ab_mutex);
    abuf_t *curframe = audio_buffer + BUFIDX(ab_read);
    if (curframe->ready) {
        result = curframe->sync.rtp_tsp;
    }

    ab_resync();
    ab_write = seqno;
    ab_read = seqno;
    // a negative seqno mean the client did not supply one, so we will
    // treat the first audio packet that comes along, as the first in the audio stream
    ab_synced = (seqno < 0 ? SIGNALLOSS : UNSYNC);
    pthread_mutex_unlock(&ab_mutex);
    return result;
}

int player_play(stream_cfg *stream) {
    AES_set_decrypt_key(stream->aeskey, 128, &aes);
    aesiv = stream->aesiv;
    init_decoder(stream->fmtp);
    // must be after decoder init
    init_buffer();
#ifdef FANCY_RESAMPLING
    init_src();
#endif
    qspec = soxr_quality_spec(config.soxr, 0);

    sane_buffer_size = (us_to_frames(config.delay)/frame_size) * 3 / 10;
    sane_buffer_size = (sane_buffer_size >= 10 ? sane_buffer_size : 10);
    if (sane_buffer_size > BUFFER_FRAMES)
        die("buffer starting fill %d > buffer size %d", sane_buffer_size, BUFFER_FRAMES);
    debug(1, "soxr quality %d, buffer start size set to %d\n", config.soxr, sane_buffer_size);

    please_stop = 0;
    command_start();
    config.output->start(sampling_rate);
    // generic outputs cannot report the delay, so we estimate the buffer depth
    // at startup and hope for the best
    if (!config.output->get_delay) {
        config.output->get_delay = audio_get_delay;
        audio_estimate_delay(config.output);
    }
    pthread_create(&player_thread, NULL, player_thread_func, NULL);

    return 0;
}

void player_stop(void) {
    please_stop = 1;
    pthread_join(player_thread, NULL);
    config.output->stop();
    command_stop();
    free_buffer();
    free_decoder();
#ifdef FANCY_RESAMPLING
    free_src();
#endif
}
