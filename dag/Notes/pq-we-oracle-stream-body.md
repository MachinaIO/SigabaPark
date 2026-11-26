---
title: Seed sizing for a matrix-free WE body in the quantum random oracle model
refs: [definition:WE_CircuitSAT, note:pq-we-rounded-stream-body, note:pq-we-erasure-groups]
tags: [witness-encryption, complexity, quantum-security]
---

For a long classical message, retain the preceding hybrid WE architecture and use a dedicated public quantum random oracle for the body. Encrypt a fresh uniform s-bit K with the WE header. At public chunk index i emit the message chunk XOR a pad H(tag,K,i), truncated on the last chunk. Use a fixed-width oracle output and an injective encoding of the tag, key and index. Each ciphertext has its own fresh secret. The wire format is the header followed by a body of exactly the input length, with any framing priced separately. No public matrix, shifts, or transmitted per-message nonce are needed. A valid witness decrypts the header once. Conditional on correct key recovery the entire body recovers exactly. This is a single-challenge confidentiality construction.

**Oracle cost in the proof.** Use acceptance-probability gaps. Assume the header has false-statement gap at most epsilon_header against the reduction, with an independent public quantum random oracle available. In each of the two message games, switch the encryption of the actual K to an encryption of a dummy seed. The reduction knows K and produces all real body pads using its oracle. Charge these honest calls and the adversary's calls to the header reduction. The remaining comparison has a header independent of K.

Choose an independent random oracle H, uniform K and an independent table of pads indexed by counters. Define G to agree with H except on the tagged K slice, where it returns this table. G is itself a random oracle, and using G together with the table for the message mask reproduces the correlated dummy-header game. Using H with the same table makes the mask independent of the adversary's oracle. The table is conceptual and can be sampled as needed in the distribution argument. For an adversary making Q quantum queries, telescope the pure-state computations with H and G, evaluating each difference on the prefix run with H. On each query the norm change is at most twice the square root of the query probability on the K slice. In the H run the entire algorithm, including any exposed masked body and its oracle-dependent prechallenge state, is independent of K. Each tagged basis input names at most one seed, so averaging over K gives slice mass at most 2^-s, even in a superposition over counters. Jensen's inequality, the triangle inequality and the pure-state trace-distance bound give a one-sided acceptance gap at most 2 Q / sqrt(2^s). Measurements can be purified. This proof compares adversary queries before and after the challenge. Honest masking in the comparison uses the table directly. There is no multiplier for the number of pad chunks in this slice-mass argument. The two ideal message games agree for equal-length chosen messages.

The combined bound is 2 epsilon_header + 4 Q / sqrt(2^s). This elementary hybrid bound is conservative. It covers a single freshly keyed ciphertext, with no body decryption oracle. For a two-message oracle contribution at most 2^-b, select s at least ceil(log2((4Q)^2))+2b. With Q=2^60 and b=128, 380 bits suffice by this calculation. A 384-bit key fits three 128-bit WE encryptions and yields an oracle term at most 2^-130. At Q=2^64 the same target needs 388 bits by this bound. The header's own advantage and failure must cover its multiple blocks; an ordinary quantum proof without an oracle must justify simulation of any independent oracle supplied to its reduction. The unresolved header assumptions remain. A concrete hash implementation does not inherit ideal-oracle security by this calculation.

**Accounting and control.** A 1 MiB body at 4 KiB per chunk needs 256 pad evaluations plus bytewise XOR on each side, in addition to three WE blocks for the 384-bit seed. The preceding illustrative rounded-LWE expansion uses 32 WE blocks and transmits 263 KiB of matrix and shifts. These comparisons use different body assumptions. For fixed seed length and chunk size the body has linear time and can be streamed with one chunk of scratch. The listing uses SHAKE256 to check the byte format, with a fixed test seed and 64-bit counters. The local seven-run median for the Python body transform on 1 MiB was 28.4 ms; it excludes header generation, header decryption, and I/O. Nine round trips include empty input and both sides of chunk boundaries. The ciphertext checksum for the largest test is ef6b18f82bd2c853be05a8eae9d522fc83fdf738c905f83e0c93e92bfb05a43b. SHAKE256 is specified by [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final). For broader quantum oracle-hiding techniques see [Quantum security proofs using semi-classical oracles](https://eprint.iacr.org/2018/904).

~~~python
from hashlib import shake_256, sha256
from statistics import median
from time import perf_counter

TAG = b"WE-body-v1\x00"
CHUNK = 4096

def mask_chunk(seed, index):
    # Fixed domain, seed length and counter give an injective query encoding.
    if len(seed) != 48:
        raise ValueError("expected 384-bit seed")
    return shake_256(TAG + seed + index.to_bytes(8,"big")).digest(CHUNK)

def transform(seed, body):
    result = bytearray()
    for offset in range(0,len(body),CHUNK):
        pad = mask_chunk(seed,offset//CHUNK)
        part = body[offset:offset+CHUNK]
        result.extend(bytes(x^y for x,y in zip(part,pad)))
    return bytes(result)

def seed_bits(query_cap, loss_bits):
    # Smallest integer s satisfying 4 Q / sqrt(2^s) <= 2^-loss_bits.
    if query_cap <= 0 or loss_bits < 0:
        raise ValueError("invalid budget")
    return (((4*query_cap)**2-1).bit_length()+2*loss_bits)

seed = bytes(range(48))
for size in (0,1,4095,4096,4097,8191,8192,8193,1<<20):
    message = bytes((i%251 for i in range(size)))
    ciphertext = transform(seed,message)
    assert len(ciphertext)==size and transform(seed,ciphertext)==message
    if size>CHUNK:
        assert ciphertext[CHUNK] == message[CHUNK]^mask_chunk(seed,1)[0]
assert seed_bits(1<<60,128)==380
assert seed_bits(1<<64,128)==388
assert mask_chunk(seed,0)!=mask_chunk(seed,1)
print("1 MiB body SHA-256",sha256(ciphertext).hexdigest())
times=[]
for _ in range(7):
    start=perf_counter()
    transform(seed,message)
    times.append(perf_counter()-start)
print("median body seconds",median(times))
~~~
