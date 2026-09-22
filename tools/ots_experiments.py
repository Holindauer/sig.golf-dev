#!/usr/bin/env python3
"""Exact, uncertified OTS cost/count experiments. Never produces ranked receipts."""

import argparse
from collections import defaultdict
from fractions import Fraction
import json
from math import comb
from oracle_meter import hash_weight, meter_metadata
from scoring_policy import additive_score


def rank_key(size, keygen, signing, verification, beta):
    """Historical four-factor arithmetic; not the current competition score."""
    values = [Fraction(v) for v in (size, keygen, signing, verification)]
    beta = Fraction(beta)
    if any(v <= 0 for v in values) or not 0 < beta < 1:
        raise ValueError("positive metrics and 0 < beta < 1 required")
    s, k, g, v = values
    return (s * g * v) ** beta.denominator * k ** beta.numerator


def multiply(left, right, max_cost, max_values):
    result = defaultdict(int)
    for (c, f), count in left.items():
        for (d, g), other in right.items():
            if c + d <= max_cost and f + g <= max_values:
                result[c + d, f + g] += count * other
    return dict(result)


def power(poly, exponent, max_cost, max_values):
    result = {(0, 0): 1}
    for _ in range(exponent):
        result = multiply(result, poly, max_cost, max_values)
    return result


def hash_cost(blocks, profile):
    """Blocks are 16 bytes; both ROM profiles add a 16-byte gate address.
    rom32 is historical (32-byte input units); rom32-input64 uses the v0.15 meter.
    """
    if blocks < 1:
        raise ValueError("these graph families require nonempty inputs")
    if profile == "paper":
        return (blocks + 3) // 4
    if profile == "rom32":
        return (16 + 16 * blocks + 31) // 32
    if profile == "rom32-input64":
        return hash_weight(16 + 16 * blocks)
    raise ValueError("unknown oracle profile")


def shared_rows(rows, profile):
    expansion = 1 if profile == "paper" else (rows + 1) // 2
    merge = hash_cost(4, profile)
    result = defaultdict(int, {(0, rows): 1, (rows * merge + 4 * expansion, 4): 1})
    for chosen in range(1, rows + 1):
        for seeds in range(4):
            cost = chosen * merge + seeds * expansion
            values = rows - chosen + seeds + chosen * (4 - seeds)
            result[cost, values] += comb(rows, chosen) * comb(4, seeds)
    return dict(result)


def families(profile):
    """The four fixed graph shapes from the note; not an exhaustive graph search."""
    merge = hash_cost(4, profile)
    forest = {(0, 1): 1, **{(merge + j, 4): comb(4, j) for j in range(5)}}
    pairs = shared_rows(2, profile)
    pairs = multiply(pairs, pairs, 1000, 128)
    four = shared_rows(4, profile)

    def component(poly):
        return {(0, 1): 1, **{(c + merge, f): n for (c, f), n in poly.items()}}

    expansion4 = 1 if profile == "paper" else 2
    return [
        ("chains", None, 116, 139, 116),
        ("forest", forest, 32, 4 + merge, 32),
        ("pairs", component(pairs), 12, 8 + 5 * merge, 12),
        ("four", component(four), 18, 4 * expansion4 + 5 * merge, 18),
    ]


def pareto(candidates):
    """Size/verification frontier within one graph (fixed keygen/signing)."""
    result = []
    best_verification = None
    for candidate in sorted(candidates, key=lambda c: (c["padded_signature_bytes"], c["verification"])):
        if best_verification is None or candidate["verification"] < best_verification:
            result.append(candidate)
            best_verification = candidate["verification"]
    return result


def experiments(profile, bits=112, max_values=128, selection="frontier", include_frontier=False,
                bandwidth_price=None):
    if not 1 <= bits <= 127 or not 1 <= max_values <= 128:
        raise ValueError("bounded experiment requires bits in 1..127, values in 1..128")
    if selection not in {"product", "verification", "additive", "frontier"}:
        raise ValueError("unknown selection objective")
    if selection == "additive":
        if bandwidth_price is None:
            raise ValueError("additive selection requires an explicit bandwidth price")
        additive_score(1, 1, bandwidth_price)
    target = 2 ** bits
    output = []
    for name, poly, count, component_cost, roots in families(profile):
        root_cost = hash_cost(roots, profile)
        if name == "chains":
            local_cost = component_cost
            chain1 = {(0, 1): 1, (1, 1): 1}
            chain2 = {**chain1, (2, 1): 1}
            choices = multiply(power(chain2, 23, local_cost, max_values),
                               power(chain1, 93, local_cost, max_values), local_cost, max_values)
        else:
            local_cost = count * component_cost
            choices = power(poly, count, local_cost, max_values)
        row = {"family": name, "keygen": local_cost + root_cost}
        candidates = []
        for cost in range(local_cost + 1):
            available = 0
            for values in range(1, max_values + 1):
                available += choices.get((cost, values), 0)
                if available >= target:
                    candidates.append(dict(reconstruction=cost + root_cost,
                               verification=cost + root_cost + hash_cost(4, profile),
                               disclosure_values_cap=values, padded_signature_bytes=(2 + values) * 16,
                               eligible_count=str(available)))
                    break
        if candidates and selection != "frontier":
            # Product is retained for reproducing historical experiments only.
            def key(candidate):
                v, s = candidate["verification"], candidate["padded_signature_bytes"]
                if selection == "additive":
                    return (additive_score(s, v, bandwidth_price), s, v)
                return (v if selection == "verification" else s * v, s, v)
            row.update(min(candidates, key=key))
        row["codebook_found"] = bool(candidates)
        if include_frontier or selection == "frontier":
            row["frontier"] = pareto(candidates)
        output.append(row)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=["paper", "rom32", "rom32-input64"], required=True,
                        help="rom32-input64 is current; rom32 and paper are historical comparisons")
    parser.add_argument("--bandwidth-price", type=Fraction,
                        help="explicit research price in verification units per byte; absent means Pareto only")
    parser.add_argument("--signing-work", type=Fraction, required=True,
                        help="explicit hypothetical metric, not a derived signing theorem")
    parser.add_argument("--signing-kind", choices=["expected-upper-bound", "worst-case-bound"], required=True)
    parser.add_argument("--include-frontier", action="store_true")
    args = parser.parse_args()
    try:
        if args.signing_work <= 0:
            raise ValueError("positive hypothetical signing work required")
        if args.bandwidth_price is not None:
            additive_score(1, 1, args.bandwidth_price)
    except ValueError as error:
        parser.error(str(error))
    selection = "frontier" if args.bandwidth_price is None else "additive"
    rows = experiments(args.profile, selection=selection, include_frontier=args.include_frontier,
                       bandwidth_price=args.bandwidth_price)
    for row in rows:
        if "verification" in row and args.bandwidth_price is not None:
            row["rank_key"] = str(additive_score(row["padded_signature_bytes"], row["verification"],
                                                args.bandwidth_price))
    meter = (meter_metadata() if args.profile == "rom32-input64" else
             {"id": "rom256-input32-min1-v1" if args.profile == "rom32" else "paper-note-v1",
              "historical": True})
    print(json.dumps({"schema": "leansphincs-ots-experiment-v3", "ranked": False,
        "security_proved": False, "costs_certified": False, "profile": args.profile,
        "hash_meter": meter,
        "bandwidth_price": None if args.bandwidth_price is None else str(args.bandwidth_price),
        "price_is_research_input": args.bandwidth_price is not None,
        "budget_certified": False, "signing_work": str(args.signing_work),
        "signing_kind": args.signing_kind,
        "selection": selection, "objective": "c * signatureBytes + verification",
        "notice": "Fixed graph shapes; assumed layout and canonical padding; hypothetical signing metric.",
        "results": rows}, indent=2))


if __name__ == "__main__":
    main()
