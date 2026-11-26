---
title: Certifying and measuring the AFV signed-noise kernel at full example dimensions
refs: [definition:WE_CircuitSAT, note:pq-we-afv-cyclic-sampler]
tags: [witness-encryption, predicate-encryption, lwe, cost]
---

The cyclic sampler uses one conditional mass table per independent AFV base error. Building that table by repeated high-precision integer convolution can be expensive. Here a histogram-dependent Fourier sieve and a single interval DFT give a checkable alternative. We ran the whole signed-noise kernel for m=524288, p=117, D=61341696, L=1048576 and denominator Q=2^245. The parent note gives the public norm and lift bounds, the fair-bit reservoir and the table-wide TV accounting. No new computational hardness premise is needed.

### A one-sided certificate for the whole table

For Z=sum_j a_j B_j with independent fair bits and nonnegative magnitudes a_j, write c_a for their histogram and S=sum_j a_j. Its positive-exponent characteristic function on the cyclic group has coefficients

    phi(f) = exp(pi i f S/L) product_a cos(pi f a/L)^c_a.

Write r_a for the distance of fa to the nearest multiple of L. On 0<=t<1/2, differentiating log cos(pi t) gives -pi tan(pi t)<=-pi²t. Integration and the endpoint at 1/2 therefore give |cos(pi t)|<=exp(-2t²). Drop a mode when 2 sum_a c_a r_a² >= k L² with k=245. Its modulus is at most exp(-k)<=1/Q. Partial sums of the nonnegative sieve can stop at the threshold. By Fourier inversion with its factor 1/L, omitting any set of such modes changes each bin by at most 1/Q. This works for periodic or sparse supports: any large secondary peaks survive the same test.

Compute the retained positive half by 320-bit real and complex ball arithmetic, fill its Hermitian conjugate half, and use the forward negative-exponent DFT. Let b_i be a rigorous lower endpoint for the real output multiplied by Q/L. Take w_i=max(0,floor(b_i)-1). For the exact conditional cyclic probabilities p_i we have 0<=w_i<=Q p_i. Put Delta=Q-sum_i w_i; transfer these remaining units to bin zero. The original and completed distributions both dominate the common subprobability w/Q, so their TV distance is at most Delta/Q. Accept this construction only if 0<=Delta and 2^tau D Delta<=Q. For any accepted profile the D-draw error contribution is at most 2^-tau. This single check replaces the parent note's convolution-rounding budget, giving the same total bound of 2^-132 across the WE table. If finite computation does not certify a profile, compute its table by the parent's integer convolution. Aborting on that condition alone would need a separate probability bound. The benchmark returns a distinct exit code on this branch; it measures the spectral path.

The integer certificate is sufficient given valid enclosures for all DFT outputs. Its smallness alone cannot validate unchecked floating-point roots or a platform FFT. The prototype uses [FLINT complex-ball transforms](https://flintlib.org/doc/acb_dft.html). The small-profile mode independently constructs all cyclic masses as exact integers and checks each one-sided bound. This numerical validation is distinct from a Lean proof or a verified implementation of the library.

### Native measurements

The benchmark took one fixed synthetic rounded Gaussian profile per seed (sd=64) and generated every scalar signed sum, prior to its last reduction modulo the AFV ciphertext modulus. Each run includes a new spectrum, DFT, mass certificate, alias table and 61,341,696 draws. Inputs and the pseudo-random stream are reproducible diagnostics. Real encryption needs cryptographic fair coins and also pays for building its base error and the remaining AFV operations. Internal timings start after reading the magnitudes; the spectrum time excludes histogram input. Peak RSS covers the process. All runs used the same single-process C program and FLINT 3.3.1 on an AMD Ryzen 9 7950X3D.

| Seed | Positive-half modes incl. DC | Delta (units of 2^-245) | Spectrum / DFT and masses / alias / draws (s) | Logical fair bits | Peak KiB |
|---:|---:|---:|---:|---:|---:|
| 2718 | 251 | 1241796 | 0.100 / 1.494 / 0.064 / 3.383 | 1349501679 | 304476 |
| 2719 | 251 | 1240352 | 0.104 / 1.621 / 0.065 / 3.443 | 1349509678 | 304768 |
| 2720 | 251 | 1240084 | 0.105 / 1.644 / 0.065 / 3.108 | 1349530979 | 304220 |

Seed 2718 had 278 distinct nonzero magnitudes. Its certified bound D Delta/Q is less than 2^-198.88. All three runs fit the public reservoir of 1,410,859,548 bits. For scale, the previous note's native benchmark on the *same* seed-2718 magnitudes, with its W=256 tables and 4,096 outputs, measured medians of 56.81 ms for grouped popcount, 23.73 ms for the CDF-prefix sampler, and 165.94 ms for the bit-plane contraction (five repetitions). Those controls ran on a smaller output batch and a different benchmark PRNG. No full-batch speedup factor has been measured against those controls.

With F magnitudes the half-spectrum sieve has at most O(LF) integer steps; expensive root/power products are needed only on retained frequencies. A radix-2 transform uses O(L log L) complex-ball operations. Frequency retention, certified precision and the fallback matter in a worst-case bound. The reported 4.97–5.28 seconds per process cover one AFV entry's sign-noise kernel. Multiplying this cost by the WE entry cap would still make the split-witness example impractical. The measurements do not supply concrete secure LWE parameters, a cost in the registered tape model, or a clock for complete WE.

### Reproduction

Save the C listing as spectrum.c. With the FLINT prefix in FLINT_PREFIX, build and run as follows on a little-endian or big-endian system with 64-bit FLINT limbs. The extraction uses limb positions, not a byte serialization.

~~~sh
gcc -O3 -std=gnu11 -I"$FLINT_PREFIX/include" spectrum.c -L"$FLINT_PREFIX/lib" -Wl,-rpath,"$FLINT_PREFIX/lib" -lflint -o spectrum
echo '0 1 2 2 4 9 3 3 5' | ./spectrum 1
python -c 'import random; g=random.Random(2718); print("\n".join(str(abs(round(g.gauss(0,64)))) for _ in range(1<<19)))' > magnitudes
/usr/bin/time -f 'peak_KiB=%M elapsed_s=%e' ./spectrum 0 < magnitudes
~~~

The smaller timing control uses the C++ listing and table generator in pq-we-afv-sign-noise. Replace its outer four-profile loop and synthetic histogram generation with a single m=524288, sd=64 block that reads magnitudes from stdin and counts positive values. Keep its D=4096, W=256, measured kernels and repetitions.

~~~c
#include <flint/acb_dft.h>
#include <flint/fmpz_vec.h>
#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

enum { precision=320, k=245 };
static const uint64_t D=117ULL*(1<<19), tau=180;
static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
    return t.tv_sec+1e-9*t.tv_nsec;
}
// Deterministic benchmark source; count the logical prefix actually used.
static uint64_t state=8137612, word=0, bits=0, cap;
static unsigned available=0;
static uint64_t take(unsigned n) {
    if(bits+n>cap){fprintf(stderr,"reservoir exhausted\n");exit(2);}
    if(available<n){
        state^=state<<13; state^=state>>7; state^=state<<17;
        // This benchmark only requests at most 20 bits at once.
        word |= (state & ((UINT64_C(1)<<44)-1)) << available;
        available+=44;
    }
    uint64_t v=word&((UINT64_C(1)<<n)-1);
    word>>=n; available-=n; bits+=n; return v;
}

int main(int argc,char **argv) {
    if(argc!=2)return 1;
    int small=atoi(argv[1])==1;
    int ell=small?4:20, L=1<<ell, m=0;
    unsigned count[55000]={0}, magn[55000], F=0;
    int a; uint64_t S=0, norm2=0;
    while(scanf("%d",&a)==1){
        if(a<0 || a>=55000 || ++m>(1<<19))return 1;
        if(a && count[a]++==0)magn[F++]=a;
        S+=a;norm2+=(uint64_t)a*a;
    }
    if(!m || norm2>54944ULL*54944 || (small && m>20))return 1;
    double start=now();
    acb_ptr spec=_acb_vec_init(L);
    arb_t angle,cosine,prod; arb_init(angle);arb_init(cosine);arb_init(prod);
    arf_t lower;arf_init(lower);
    fmpz_t Q,sum,deficit,test; fmpz_init(Q);fmpz_init(sum);fmpz_init(deficit);fmpz_init(test);
    fmpz_one_2exp(Q,k);
    int kept=0;
    for(int f=0;f<=L/2;++f){
        uint64_t energy=0;
        for(unsigned i=0;i<F;++i){
            unsigned a=magn[i]; uint64_t r=(uint64_t)f*a%L;
            if(r>L/2)r=L-r;
            energy+=count[a]*r*r;
            if(2*energy>=(uint64_t)k*L*L)break;
        }
        if(2*energy>=(uint64_t)k*L*L)continue;
        ++kept;arb_one(prod);
        for(unsigned i=0;i<F;++i){
            unsigned a=magn[i];
            arb_set_ui(angle,((uint64_t)f*a)%(2*L));arb_mul_2exp_si(angle,angle,-ell);
            arb_cos_pi(cosine,angle,precision);
            arb_pow_ui(cosine,cosine,count[a],precision);
            arb_mul(prod,prod,cosine,precision);
        }
        // Positive-exponent characteristic function; the forward DFT
        // has negative exponent and recovers the unnormalized histogram.
        arb_set_ui(angle,((uint64_t)f*S)%(2*L));arb_mul_2exp_si(angle,angle,-ell);
        arb_sin_cos_pi(acb_imagref(spec+f),acb_realref(spec+f),angle,precision);
        acb_mul_arb(spec+f,spec+f,prod,precision);
        if(f && f<L/2)acb_conj(spec+L-f,spec+f);
    }
    double spectrum=now();
    acb_dft_rad2_inplace(spec,ell,precision);
    fmpz *weights=_fmpz_vec_init(L);
    for(int i=0;i<L;++i){
        arb_mul_2exp_si(angle,acb_realref(spec+i),k-ell);
        if(!arb_is_finite(angle))return 3;
        arb_get_lbound_arf(lower,angle,precision);
        arf_get_fmpz(weights+i,lower,ARF_RND_FLOOR);
        fmpz_sub_ui(weights+i,weights+i,1); // At most one unit lost to omitted modes.
        if(fmpz_sgn(weights+i)<0)fmpz_zero(weights+i);
        fmpz_add(sum,sum,weights+i);
    }
    _acb_vec_clear(spec,L);
    fmpz_sub(deficit,Q,sum);fmpz_mul_ui(test,deficit,D);fmpz_mul_2exp(test,test,tau);
    if(fmpz_sgn(deficit)<0 || fmpz_cmp(test,Q)>0){fprintf(stderr,"use convolution fallback\n");return 3;}
    if(small){
        uint64_t exact[16]={1},tmp[16]; int nz=0;
        for(unsigned j=0;j<F;++j)for(unsigned h=0;h<count[magn[j]];++h){
            for(int i=0;i<L;++i)tmp[i]=exact[i]+exact[(i+L-(magn[j]%L))%L];
            for(int i=0;i<L;++i)exact[i]=tmp[i];
            ++nz;
        }
        for(int i=0;i<L;++i){
            fmpz_set_ui(test,exact[i]);fmpz_mul_2exp(test,test,k-nz);
            assert(fmpz_cmp(weights+i,test)<=0);
        }
    }
    fmpz_add(weights,weights,deficit);
    double masses=now();
    typedef struct {ulong limb[4]; int other;} Slot;
    Slot *slot=calloc(L,sizeof(*slot));int *lo=malloc(L*sizeof(int)),*hi=malloc(L*sizeof(int));
    assert(slot && lo && hi && sizeof(ulong)==8);
    int nl=0,nh=0;
    for(int i=0;i<L;++i){
        fmpz_mul_2exp(weights+i,weights+i,ell);slot[i].other=i;
        if(fmpz_cmp(weights+i,Q)<0)lo[nl++]=i;else hi[nh++]=i;
    }
    while(nl && nh){
        int i=lo[--nl],j=hi[--nh];slot[i].other=j;
        fmpz_get_ui_array(slot[i].limb,4,weights+i);
        fmpz_sub(weights+j,weights+j,Q);fmpz_add(weights+j,weights+j,weights+i);
        if(fmpz_cmp(weights+j,Q)<0)lo[nl++]=j;else hi[nh++]=j;
    }
    for(int i=0;i<nh;++i)assert(fmpz_equal(weights+hi[i],Q));
    assert(!nl);free(lo);free(hi);_fmpz_vec_clear(weights,L);
    double built=now();uint64_t draws=small?4096:D, checksum=0;
    cap=(ell+3)*draws+3*tau;
    for(uint64_t n=0;n<draws;++n){
        int i=take(ell);Slot *s=slot+i;
        if(i!=s->other){
            int use_primary=0;
            for(int b=k-1;b>=0;--b){
                int threshold=(s->limb[b/64]>>(b%64))&1, coin=take(1);
                if(coin!=threshold){use_primary=coin<threshold;break;}
            }
            if(!use_primary)i=s->other;
        }
        int64_t low=(int64_t)S-L;low=low>=0?(low+1)/2:low/2;
        int64_t z=low+(int64_t)(((uint64_t)(i-low))&(L-1));
        checksum+=(uint64_t)((int64_t)S-2*z); // signed result prior to mod q
    }
    printf("m=%d F=%u S=%" PRIu64 " norm2=%" PRIu64 " modes_half=%d deficit=",m,F,S,norm2,kept);
    fmpz_print(deficit);
    printf(" spectrum=%.3f masses=%.3f alias=%.3f draws=%.3f bits=%" PRIu64 " checksum=%" PRIu64 "\n",
           spectrum-start,masses-spectrum,built-masses,now()-built,bits,checksum);
    free(slot);arb_clear(angle);arb_clear(cosine);arb_clear(prod);arf_clear(lower);
    fmpz_clear(Q);fmpz_clear(sum);fmpz_clear(deficit);fmpz_clear(test);flint_cleanup();
}
~~~
