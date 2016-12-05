#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
//#include <wmmintrin.h>

#include <oqs/rand.h>

//#include "crypto_encrypt.h"
#include <nacl/crypto_stream_salsa20.h>
#include <nacl/crypto_onetimeauth_poly1305.h>
#include <nacl/crypto_uint16.h>

#define unit uint64_t
#define half uint32_t
#define UBYTES sizeof(unit)
#define UBITS (sizeof(unit) * 8)
#define UBITSBITS 6
/*
#define unit uint32_t
#define half uint16_t
#define UBYTES sizeof(unit)
#define UBITS (sizeof(unit) * 8)
#define UBITSBITS 5
*/
#define LEN 4801
#define LENEXP2 6
#define LENBIT 13
//#define LEN 9856
//#define LENEXP2 7
//#define LENBIT 14
//#define LEN 32768
//#define LENEXP2 15
//#define LENBIT 15

#define TAIL (LEN % UBITS)
#define TAILMASK ((1 << TAIL)-1)

#define LENBYTES ((LEN + 7)/8)
#define LEN2 (LEN << 1)
#define LEN2BYTES ((LEN2 + 7)/8)
#define ULEN ((LEN + UBITS -1) / UBITS)
#define ULEN2 (ULEN << 1)

#define WT 90
#define ERR 84
//#define WT 142
//#define ERR 134
//#define WT 274
//#define ERR 264

/////////////////////////////////////////////////

#define max(x,y) ((x >= y) ? x:y)
#define vec_ixor(a, b) (a = _mm_xor_si128(a,b))

/////////////////////////////////////////////////

static void vec_set1s(unit * vec, int nu, crypto_uint16 *idx, int w)
{
	int i, j;

	uint16_t idx_int[ max(ERR, WT/2) ];

	unit mask;
	unit v[ max(ERR, WT/2) ];

	for (i = 0; i < w; i++)
	{
		idx_int[i] = idx[i] >> UBITSBITS;

		v[i] = 1;
		v[i] <<= idx[i] & (UBITS-1);
	}

	for (i = 0; i < nu; i++)
	{
		vec[i] = 0;

		for (j = 0; j < w; j++)
		{
			mask = idx_int[j] ^ i;
			mask -= 1;
			mask >>= UBITS-1;
			mask = -mask;

			vec[i] |= v[j] & mask;
		}
	}
}

/////////////////////////////////////////////////

static void pseudo_randombytes(unsigned char * out, unsigned long long len, OQS_RAND * r)
{
	unsigned char key[32];
	unsigned char nonce[8] = {0};

    OQS_RAND_n(r, (uint8_t *)key, sizeof(key));

	crypto_stream_salsa20(out, len, nonce, key);
}

static void indices_gen(crypto_uint16 * sk, int w, int bound, OQS_RAND * r)
{
	int i, j;
	int count = 0, err;

	crypto_uint16 mask;
	crypto_uint16 cand[ w*3 ]; // ???

	/* generating mask */

	mask = -1;
	while (mask/2 >= bound-1)
		mask = mask/2;

	/* generating secret key */

	do
	{
		pseudo_randombytes((unsigned char *) cand, sizeof(cand), r);

		for (i = 0; i < w*3; i++)
			cand[i] &= mask;

		for (count = i = 0; i < w*3; i++)
		{
			err = 0;

			if (cand[i] >= bound) continue;

			for (j = 0; j < count; j++)
				if (cand[i] == sk[j])
					{ err = 1; break; }

			if (err) continue;

			sk[ count++ ] = cand[i];

			if (count == w) break;
		}
	}

	while (count != w);
}


static crypto_uint16 load_2(const unsigned char *in)
{
  crypto_uint16 result;

  result = (crypto_uint16) in[0];
  result |= ((crypto_uint16) in[1]) << 8;

  return result;
}

static void store_2(unsigned char *out, const crypto_uint16 *in)
{
  out[0] = in[0] & 0xFF;
  out[1] = in[0] >> 8;
}

static void load_bytes(unit * dest, const unsigned char * src, int len)
{
	int i;

//	printf("print 'UBYTES', %d\n", UBYTES);

	for (i = 0; i < len; i++)
	{
		if (i % UBYTES == 0)
			dest[i / UBYTES]  = src[i];
		else
			dest[i / UBYTES] |= ((unit) src[i]) << ((i % UBYTES) * 8);
	}
}

static void store_bytes(unsigned char * src, const unit * dest, int len)
{
	int i;

	for (i = 0; i < len; i++)
		src[i] = (dest[i / UBYTES] >> ((i % UBYTES) * 8)) & 0xFF;
}

static void ha(unit *s, unit *c, unit a, unit b)
{
	*s = (a ^ b);
	*c = (a & b);
}

static void fa(unit *s, unit *c_out, unit a, unit b, unit c_in)
{
	*s = (a ^ b) ^ c_in;
	*c_out = (a & b) | (c_in & (a ^ b));
}

static void byte_half_adder(unit * bits, unit v)
{
	int i;

	unit c_out = 0;

	for (i = 0; i < 6; i++)
	{
		ha(&bits[i], &c_out, bits[i], v);

		v = c_out;
	}
}

static void byte_full_adder(unit * bits, unit * v)
{
	int i;

	unit c_in = 0;
	unit c_out = 0;

	for (i = 0; i < 7; i++)
	{
		fa(&bits[i], &c_out, bits[i], v[i], c_in);

		c_in = c_out;
	}
}

static void set_negative(unit *v, uint8_t t)
{
	uint8_t t_neg = -t;
	int i;

	for (i = 0; i < 8; i++)
		v[i] = (((t_neg >> i) & 1) == 1) ? -1 : 0;
}


static void qc_mv_prod(unit * u, const uint16_t *  sk, unit * v, int type, unsigned char th)
{
	/* data */

	uint32_t sk_len;

	uint32_t i;
	uint32_t j;
	uint32_t t;

	uint32_t us; // unit shift


	unit th_slice[8];

	unit b;
//	unit w[ ULEN ];
	unit v0[ ULEN ];
	unit v1[ ULEN ];
	unit *x = v0;
 	unit *w = v1;
 	unit *ptr;
	unit tmp;
	unit mask, mask_block;

	uint16_t s_low, s_high, mask_neg, s;
	unit sum[ULEN * 2][8];

	//////////////////////////////////////////////////////


	if (type == 0) sk_len = WT;
	if (type == 1) sk_len = WT;
	if (type == 2) sk_len = ERR;

	for (t = 0; t < sk_len; t++)
	{
		/* get shift value for the block */

		mask_block = 0;
		mask_block -= (((unit) sk[t]) - LEN) >> (UBITS-1);

		s = (sk[t] & mask_block) | ((sk[t] - LEN) & ~mask_block);

//		printf("s = %d\n", s);

		/* conditionally negating shift value */

		if (type > 0)
		{
			mask_neg = 0;
			mask_neg -= ((uint16_t) -s) >> 15;
			s = ((LEN - s) & mask_neg) | (s & ~mask_neg);
		}

//		printf("s = %d\n", s);
		/* first power-of-2 shift */

		b = (s >> (LENBIT-1)) & 1;
		mask = -b;

		us = (1 << (LENBIT-1-UBITSBITS));


		if (type == 0)
		{
			if (mask_block) for (j = 0; j < ULEN; j++) w[ j ] = v[j];
			else            for (j = 0; j < ULEN; j++) w[ j ] = v[ j+ULEN ];
		}

		if (type == 1)
		{
			for (j = 0; j < ULEN; j++) w[ j ] = v[ j ];
		}

		if (type == 2)
		{
			for (j = 0; j < ULEN; j++) w[ j ] = (v[j] & mask_block) ^ (v[j + ULEN] & ~mask_block);
		}

		/* remaining power-of-2 shifts */

		for (i = 0; i < LENBIT - UBITSBITS; i++)
		{
			mask = 0 - ((s >> (LENBIT-1-i)) & 1);
			us = (1 << (LENBIT-1-UBITSBITS-i));

			ptr = x; x = w; w = ptr;

			for (j = 0; j < ULEN-1-us; j++)
				w[ j ] = (x[ (j + us) ] & mask) ^ (x[ j ] & ~mask);

			w[ ULEN-1-us ] = ((x[ ULEN-1 ] | (x[0] << TAIL)) & mask) ^ (x[ ULEN-1-us ] & ~mask);

			for (j = 1; j < us; j++)
				w[ j + ULEN-1-us ] = (((x[ j ] << TAIL) | (x[ j-1 ] >> (UBITS-TAIL))) & mask) ^ (x[ j + ULEN-1-us ] & ~mask);

			w[ ULEN-1 ] = ((x[ us-1 ] >> (UBITS - TAIL)) & mask) ^ (x[ ULEN-1 ] & ~mask);
		}

		/* shifts inside units */

		s_low = s & ((1 << UBITSBITS)-1);
		mask = ((unit)(s_low - 1) >> (UBITS-1))-1;
		s_high = UBITS - s_low;

		tmp = w[0];

		for (j = 0; j < ULEN-2; j++)
		{
			w[ j ] >>= s_low;
			w[ j ] |= (w[ j+1 ] << s_high) & mask;
		}

		w[ ULEN-2 ] >>= s_low;
		w[ ULEN-1 ] |= tmp << TAIL;
		w[ ULEN-2 ] |= (w[ ULEN-1 ] << s_high) & mask;
		w[ ULEN-1 ] >>= s_low;
		w[ ULEN-1 ] |= (tmp << s_high) & mask;
		w[ ULEN-1 ] &= (1 << TAIL)-1;

		/* post-process */

		if (type == 0 || type == 2)
		{
			if (t == 0) for (i = 0; i < ULEN; i++) u[i]  = w[i];
			else        for (i = 0; i < ULEN; i++) u[i] ^= w[i];
		}

		if (type == 1)
		{
			if (t == 0)
			{
				memset(sum, 0, sizeof(sum));
			}

			/* conditional accumulation */

			if (mask_block) for (i = 0; i < ULEN; i++) byte_half_adder(sum[i       ], w[i]);
			else            for (i = 0; i < ULEN; i++) byte_half_adder(sum[i + ULEN], w[i]);

			/* XOR with the signed bit */

			if (t == WT-1)
			{
				set_negative(th_slice, th);

				for (i = 0; i < ULEN*2; i++)
				{
					byte_full_adder(sum[i], th_slice);
					u[i] ^= ~sum[i][6];
				}
			}

		}

	}
}

static unit expand(unit x)
{
	static unit B[] = {0x5555555555555555, 0x3333333333333333, 0x0F0F0F0F0F0F0F0F, 0x00FF00FF00FF00FF, 0x0000FFFF0000FFFF};
	static const unsigned int S[] = {1, 2, 4, 8, 16};

	x = (x | (x << S[4])) & B[4];
	x = (x | (x << S[3])) & B[3];
	x = (x | (x << S[2])) & B[2];
	x = (x | (x << S[1])) & B[1];
	x = (x | (x << S[0])) & B[0];

	return x;
}

static void sq(unit * poly_sq, unit * poly)
{
	int i;
	unit x;
	unit buf[ ULEN ];

	for (i = 0; i < ULEN-1; i++)
	{
		x = ((half *) poly)[i];
		x = expand(x);

		buf[i] = x;
	}

	for (i = ULEN-1; i <= (ULEN-1)*2; i++)
	{
		x = ((half *) poly)[i];
		x = expand(x);

		buf[ i+1-ULEN ] ^= (x >> TAIL);

		if (i > ULEN-1) buf[ i-ULEN ] ^= x << (UBITS - TAIL);
		else            buf[ ULEN-1 ]  = x & TAILMASK;
	}

	for (i = 0; i < ULEN; i++)
		poly_sq[i] = buf[i];
}
/*
inline void clmul(unit * low, unit * high, unit x, unit y)
{
        int i;

        unit v;
        unit v0,v1;

        //

        *low = x * ((y >> 0) & 1);
        v = x * ((y >> 1) & 1);
        *low  ^= v << 1;
        *high = v >> (UBITS-1);

        for (i = 2; i < UBITS; i+=2)
        {
                v0 = x * ((y >> i) & 1);
                v1 = x * ((y >> (i+1)) & 1);

                *low  ^= v0 << i;
                *low  ^= v1 << (i+1);

                *high ^= v0 >> (UBITS-i);
                *high ^= v1 >> (UBITS-(i+1));
        }
}
*/

static void clmul(unit * low, unit * high, unit x, unit y)
{
        int i;
        const unit mask = (((unit) 1) << (UBITS/2)) + 1;

        unit v0;
        unit v1;

        //

        unit x0 = x & ((half) -1);
        unit x1 = x >> (UBITS/2);

        *low = x0 * (y & mask);
        v1 = x1 * (y & mask);
        *low ^= v1 << (UBITS/2);
        *high = v1 >> (UBITS/2);

        for (i = 1; i < (UBITS/2); i++)
        {
                v0 = x0 * ((y >> i) & mask);
                v1 = x1 * ((y >> i) & mask);

                *low  ^= (v0 << i);
                *high ^= (v0 >> (UBITS-i));

                *low  ^= (v1 << (i + UBITS/2));
                *high ^= (v1 >> (UBITS/2 - i));
        }
}

static void poly_mul(unit * poly_r, unit * poly_p, unit * poly_q)
{
	int i, j;

	unit buf[ ULEN2 ];
	unit low;
	unit high;
	unit x;


	memset(buf, 0, sizeof(buf));

	for (i = 0; i < ULEN; i++)
	{
		for (j = 0; j < ULEN; j++)
		{
			clmul(&low, &high, poly_p[i], poly_q[j]);

			buf[i+j] ^= low;
			buf[i+j+1] ^= high;
		}
	}

	//

	for (i = 0; i < ULEN; i++)
		poly_r[i] = buf[i];

	for (i = ULEN; i < ULEN*2 - 1; i++)
	{
		x = buf[i];

		poly_r[i - ULEN    ] ^= x << (UBITS - TAIL) ;
		poly_r[i - ULEN + 1] ^= x >> TAIL;
	}

	x = buf[ ULEN*2-1 ];

	poly_r[ ULEN-1 ] ^= x << (UBITS - TAIL);

	x >>= TAIL;

	poly_r[ 0 ] ^= x << (UBITS - TAIL);
	poly_r[ 1 ] ^= x >> TAIL;
	poly_r[ 0 ] ^= poly_r[ ULEN-1 ] >> TAIL;
	poly_r[ ULEN-1 ] &= (1 << TAIL)-1;
}

static int pk_gen_power(unsigned char * pk, const unsigned char * sk)
{
	//printf("power\n");

	int i, j, t;

	crypto_uint16 sk_int[ WT ];

	unit sk_dense[ ULEN ];
	unit tmp[ 5 ][ ULEN ];
	unit buf[ ULEN ];

	const unsigned exp[2] = {109, 11};
	const unsigned exp_len[2] = {7, 4};

	unsigned sq_count[4];
	unsigned dest_i = 0;
	unsigned d;

	/* raise to big power */

	for (i = 0;    i < WT; i++) sk_int[i] = load_2( &sk[i*2] );
	for (i = WT/2; i < WT; i++) sk_int[i] = load_2( &sk[i*2] ) - LEN;

	vec_set1s(sk_dense, ULEN, sk_int, WT/2);

	memcpy(tmp[0], sk_dense, sizeof(sk_dense));

	for (t = 0; t < 2; t++)
	{
		/* precomputing powers */

		sq_count[0] = 1; if (t > 0) sq_count[0] *= exp[0];

		for (i = 1; i < exp_len[t]; i++)
		{
			dest_i += d = (exp[t] >> (i-1)) & 1;

			sq_count[ dest_i ] = (1 << i); if (t > 0) sq_count[ dest_i ] *= exp[0];

			sq(buf, tmp[ dest_i - d ]);
			for (j = 0; j < sq_count[ dest_i ]/2-1; j++)
				sq(buf, buf);

			poly_mul(tmp[ dest_i ], buf, tmp[ dest_i - d ]);
		}

		/* combine precomputed powers */

		for (; dest_i >= 1; dest_i--)
		{
			for (j = 0; j < sq_count[ dest_i-1 ]; j++)
				sq(tmp[ dest_i ], tmp[ dest_i ]);

			poly_mul(tmp[ dest_i-1 ], tmp[ dest_i-1 ], tmp[ dest_i ]);
		}
	}

	sq(tmp[0], tmp[0]);

	/* muliply row_0 by the inverse */

	poly_mul(buf, sk_dense, tmp[0]);

	/* check */

	if (buf[0] != 1)
		return 1;

	for (i = 1; i < ULEN; i++)
		if (buf[i] != 0)
			return 1;

	/* multiply row_1 by the inverse */

	vec_set1s(sk_dense, ULEN, sk_int + WT/2, WT/2);
	poly_mul(buf, sk_dense, tmp[0]);

	store_bytes(pk, buf, LENBYTES);

	return 0;
}

static void syndrome(unit * synd, uint16_t * e, unit * pk)
{
	int i;

	unit v[ ULEN*2 ];

	/* compute syndrome */

	v[0] = 1;
	for (i = 1; i < ULEN; i++) v[i] = 0;
	for (i = 0; i < ULEN; i++) v[i + ULEN] = pk[i];

	qc_mv_prod(synd, e, v, 2, 0);
}


int OQS_KEX_code_qcbits_crypto_encrypt(
       unsigned char *c,unsigned long long *clen,
       const unsigned char *m,unsigned long long mlen,
       const unsigned char *pk,
       OQS_RAND *r
)
{
	int i;

	unsigned char key[64];
	unsigned char nonce[8] = {0};
	unsigned char * ct = c + LENBYTES;
	unsigned char * tag = ct + mlen;

	crypto_uint16 e[ ERR ];

	unit ev[ ULEN2 ];
	unit * pk_int = ev;
	unit * synd = ev + ULEN;

	unsigned char ev_stream[ LEN2BYTES ];
	unsigned char * pk_tmp = ev_stream;

	/* computing encryption and authentication key*/

	indices_gen(e, ERR, LEN2, r);

	vec_set1s(ev, ULEN2, e, ERR);

	store_bytes(ev_stream, ev, sizeof(ev_stream));
	OQS_SHA3_sha3512(key, ev_stream, sizeof(ev_stream));


	for (i = ULEN2-1; i >= ULEN; i--)
	{
		ev[ i ] <<= (UBITS - TAIL);
		ev[ i ] |= ev[ i-1 ] >> TAIL;
	}

	ev[ ULEN-1 ] &= (1 << TAIL)-1;

	/* reversing bits; can also consider changing the definition of pk */

#include "byte_reverse_table.data"

	int tail = LEN % 8;

	for (i = 0; i < LENBYTES-1; i++)
	{
		pk_tmp[i] = (pk[ LENBYTES-1-i ] << (8-tail)) | (pk[ LENBYTES-2-i ] >> tail);
		pk_tmp[i] = byte_reverse_table[ pk_tmp[i] ];
	}

	pk_tmp[ LENBYTES-1 ] = byte_reverse_table[ pk[i] & ((1 << (tail-1))-1) ] >> (8 - (tail-1));

	for (i = LENBYTES-1; i >= 1; i--)
	{
		pk_tmp[i] <<= 1;
		pk_tmp[i] |= (pk_tmp[i-1] >> 7);
	}

	pk_tmp[0] = (pk_tmp[0] << 1) | (pk[0] & 1);

	load_bytes(pk_int, pk_tmp, LENBYTES);

	/* compute syndrome, encrypt, authenticate */

	syndrome(synd, e, pk_int);
	store_bytes(c, synd, LENBYTES);

	crypto_stream_salsa20_xor(ct, m, mlen, nonce, key);
	crypto_onetimeauth_poly1305(tag, ct, mlen, key + 32);

	*clen = LENBYTES + mlen + 16;

	return 0; // return value???
}

static const uint8_t thresholds[20] = {29, 27, 25, 24, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23};

static int decode(unit * e, const unit * s, const uint16_t * sk)
{
	int i;

	unit synd[ ULEN ];

	/* find preimage and */

	for (i = 0; i < ULEN; i++) e[i] = s[i];
	for (i = 0; i < ULEN; i++) e[i + ULEN] = 0;

	/* bit-flipping */

	for(i = 0; i < 6; i++)
	{
		qc_mv_prod(synd, sk, e, 0, 0);
		qc_mv_prod(e, sk, synd, 1, thresholds[i]);
	}

	for (i = 0; i < ULEN; i++) e[i] ^= s[i];

	return 0;
}


int OQS_KEX_code_qcbits_crypto_encrypt_open(
       unsigned char *m,unsigned long long *mlen,
       const unsigned char *c,unsigned long long clen,
       const unsigned char *sk
)
{
	int i;
	int ret_verify;

	unsigned char key[64];
	unsigned char nonce[8] = {0};
	unsigned char ev_stream[ LEN2BYTES ];

	crypto_uint16 sk_int[ WT ];

	unit synd[ ULEN ];
	unit ev[ ULEN2 ];

	//

	if (clen < LENBYTES + 16) return -1;
	else *mlen = clen - LENBYTES - 16;

	for (i = 0; i < WT; i++)
		sk_int[i] = load_2( &sk[i*2] );

	load_bytes(synd, c, LENBYTES);

	decode(ev, synd, sk_int);

#define ct (c + LENBYTES)
#define tag (ct + *mlen)

	for (i = ULEN; i < ULEN2; i++)
	{
		ev[i-1] |= ev[ i ] << TAIL;
		ev[i] >>= (UBITS - TAIL);
	}

	store_bytes(ev_stream, ev, sizeof(ev_stream));
	OQS_SHA3_sha3512(key,ev_stream, sizeof(ev_stream));

	ret_verify = crypto_onetimeauth_poly1305_verify(tag, ct, *mlen, key + 32); // mlen???
	crypto_stream_salsa20_xor(m, ct, *mlen, nonce, key);

#undef ct
#undef tag

	return ret_verify;

}

int OQS_KEX_code_qcbits_crypto_encrypt_keypair
(
       unsigned char *pk,
       unsigned char *sk,
       OQS_RAND *r
)
{
	int i;
	crypto_uint16 sk_int[WT];

	while(1)
	{
		indices_gen(sk_int,        WT/2, LEN, r);
		indices_gen(sk_int + WT/2, WT/2, LEN, r);

		for (i = 0; i < WT/2; i++) sk_int[ i + WT/2 ] += LEN;
		for (i = 0; i < WT;   i++) store_2(&sk[i*2], &sk_int[i]);

		if (pk_gen_power(pk, sk) == 0) break;
	}

	return 0;
}

/////////////////////////////////////////////////

