"""Trusted randomness: algorithm `sigaba-learning-sample-v1`.

* Bytes come from the OS CSPRNG (`os.urandom`). Tests may inject another byte source; the CLI
  never does, and every contract records `{"source": "os.urandom"}`.
* A seed of `k` bits is `ceil(k/8)` fresh bytes; bit `i` (the `i`-th character of the 0/1 string,
  which is `Fin k` index `i`) is bit `i % 8` (least significant first) of byte `i // 8`. The
  surplus high bits of the last byte are masked off, so every `k`-bit string is equally likely.
* A uniform integer in `[0, n)` uses the fewest whole bytes covering `n`, masks the surplus bits
  of the top byte, and rejects values `>= n` (never a modulo reduction).
* A categorical draw over integer weights draws a uniform integer below their sum.
* Commitments: `sha256(domain || salt || seed)` where `domain` is
  `b"sigaba-learning-seed-v1\\x00" + context + b"\\x00"` (the context is the contract id, or
  the certification's identity for smoke seeds), `salt` is 32 fresh bytes, and `seed` is the
  ASCII 0/1 string. Seeds are revealed only after the relevant contract ends.
"""

from __future__ import annotations

import hashlib
import os
from typing import Callable

ALGORITHM = "sigaba-learning-sample-v1"
SCHEME = "sha256(domain || salt || seed)"
SALT_BYTES = 32


class RandomSource:
    def __init__(self, randbytes: Callable[[int], bytes] = os.urandom):
        self._rb = randbytes
        self.bytes_used = 0

    def bytes(self, n: int) -> bytes:
        b = self._rb(n)
        if len(b) != n:
            raise RuntimeError("the random source returned the wrong number of bytes")
        self.bytes_used += n
        return b

    def seed_bits(self, k: int) -> str:
        if k < 1:
            raise ValueError("a seed has at least one bit")
        raw = self.bytes((k + 7) // 8)
        return "".join("1" if raw[i // 8] >> (i % 8) & 1 else "0" for i in range(k))

    def uniform(self, n: int) -> int:
        """A uniform integer in [0, n), by rejection."""
        if n < 1:
            raise ValueError("empty range")
        if n == 1:
            return 0
        bits = (n - 1).bit_length()
        nbytes = (bits + 7) // 8
        mask = (1 << bits) - 1
        while True:
            v = int.from_bytes(self.bytes(nbytes), "little") & mask
            if v < n:
                return v

    def categorical(self, weights: list[int]) -> int:
        """An index drawn with probability weight / sum(weights) (positive integer weights)."""
        if not weights or any(not isinstance(w, int) or w < 1 for w in weights):
            raise ValueError("weights must be positive integers")
        r = self.uniform(sum(weights))
        for i, w in enumerate(weights):
            if r < w:
                return i
            r -= w
        raise AssertionError("unreachable")

    def salt(self) -> str:
        return self.bytes(SALT_BYTES).hex()


def domain(context: str) -> bytes:
    return b"sigaba-learning-seed-v1\x00" + context.encode("utf-8") + b"\x00"


def commit(context: str, salt_hex: str, seed: str) -> str:
    salt = bytes.fromhex(salt_hex)
    if len(salt) != SALT_BYTES or set(seed) - {"0", "1"} or not seed:
        raise ValueError("a commitment needs a 32-byte salt and a 0/1 seed")
    return "sha256:" + hashlib.sha256(domain(context) + salt + seed.encode("ascii")).hexdigest()


def verify_reveal(context: str, item: dict) -> bool:
    try:
        return commit(context, item["salt"], item["seed_bits"]) == item["seed_commitment"]
    except (KeyError, ValueError):
        return False


def draw_seed(rng: RandomSource, k: int, context: str) -> dict:
    """A fresh seed of `k` bits with its salt and commitment (private until revealed)."""
    seed = rng.seed_bits(k)
    salt = rng.salt()
    return {"seed_bits": seed, "salt": salt, "seed_commitment": commit(context, salt, seed)}


def run_order(seed_commitment: str) -> tuple[str, str]:
    """The order in which a pair's two arms run: a deterministic bit of the pair's (random,
    already committed) seed commitment, so it is randomized by the evaluation RNG and can be
    reproduced from the records."""
    bit = hashlib.sha256(b"sigaba-learning-order-v1\x00" + seed_commitment.encode()).digest()[0] & 1
    return ("incumbent", "candidate") if bit == 0 else ("candidate", "incumbent")
