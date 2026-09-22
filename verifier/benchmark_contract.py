"""Fixed declared metrics and total-query-work bound; no Lean input interpolation."""

from fractions import Fraction
import json
from pathlib import Path
import re

MAX_TERMS = 128
MAX_COMPONENT = 2**63 - 1


def scalar(path: Path) -> int:
    data = path.read_bytes()
    if len(data) > 32 or not re.fullmatch(rb"[1-9][0-9]*\n?", data):
        raise ValueError(f"{path.name}: expected one positive canonical ASCII integer")
    value = int(data)
    if value > MAX_COMPONENT:
        raise ValueError(f"{path.name}: value exceeds {MAX_COMPONENT}")
    return value


def parse_bound(path: Path) -> list[list[int]]:
    """Each term is [numerator, denominator, workExponent, signExponent, k].

    It denotes (numerator/denominator) * Q^a * qS^b / 2^k, Q = qH + qS.
    No floats, signs, duplicate monomials, unreduced fractions or zero terms.
    """
    data = path.read_bytes()
    if len(data) > 65536:
        raise ValueError("bound.txt exceeds 64 KiB")
    try:
        terms = json.loads(data)
    except RecursionError as error:
        raise ValueError("bound.txt nesting exceeds the parser limit") from error
    if type(terms) is not list or not 1 <= len(terms) <= MAX_TERMS:
        raise ValueError("bound.txt must contain 1..128 terms")
    previous = None
    for term in terms:
        if type(term) is not list or len(term) != 5:
            raise ValueError("each bound term must have five integer components")
        if any(type(x) is not int or not 0 <= x <= MAX_COMPONENT for x in term):
            raise ValueError("bound components must be bounded non-negative integers")
        num, den, a, b, d = term
        if not num or not den or Fraction(num, den).denominator != den:
            raise ValueError("coefficients must be positive reduced fractions")
        # Cap work/sign exponents so kernel evaluation of the floor certificate
        # (which reduces qW^a with qW up to 2^124, and qS^b with qS up to 2^32)
        # cannot be driven to pathological bignum sizes. Usable exponents are far
        # smaller: the floor B(2^b,S) <= 1 with k <= 1024 forces workExponent <= 8
        # and signExponent <= 32, so 32/64 are generous. This bounds only the
        # declared bound; a general expensive proof is bounded by the sandbox caps.
        if a > 32 or b > 64 or d > 1024:
            raise ValueError("bound exponents exceed limits: work<=32, sign<=64, k<=1024")
        key = (a, b, d)
        if previous is not None and key <= previous:
            raise ValueError("monomials must be unique and sorted by (a,b,d)")
        previous = key
    return terms


def metrics(root: Path) -> tuple[int, int, list[list[int]]]:
    return scalar(root / "sigma.txt"), scalar(root / "hverify.txt"), parse_bound(root / "bound.txt")


def lean_bound(terms: list[list[int]]) -> str:
    # Denominators use predecessor encoding in Lean, excluding division by zero.
    return "[" + ", ".join(
        f"⟨{num}, {den - 1}, {a}, {b}, {d}⟩" for num, den, a, b, d in terms
    ) + "]"


def render(sigma: int, hverify: int, terms: list[list[int]]) -> str:
    return f"""/- Generated trusted comparator template; the single definition hole is the scheme. -/
import LeanSphincs.Benchmark.Target

noncomputable def LeanSphincs.Submission.scheme : LeanSphincs.Benchmark.SigScheme :=
  {{ SecretKey := Unit, keygen := pure ([], ()),
    sign := fun _ _ => pure (some []), verify := fun _ _ _ => pure false }}

theorem LeanSphincs.Benchmark.candidate :
    LeanSphincs.Benchmark.SchemeClaim LeanSphincs.Submission.scheme
      {sigma} {hverify} {lean_bound(terms)} := by
  sorry
"""
