#!/usr/bin/env python3
"""Arithmetic checks for the supplied polynomial-coding annex, not a benchmark.

Only the displayed keygen structure and naive Horner work are covered. The
complete signing/verification algorithms and security theorem were not supplied.
"""

import json
from oracle_meter import hash_weight, meter_metadata


def keygen_estimates():
    columns, rows, coefficients = 64, 256, 64
    parents = 64 + 16 + 4 + 1
    seed_bytes, row_bytes, parent_bytes = 17, 64, 64
    address_bytes = 16  # Assumed layout for comparison, not a registered profile.

    def weight(size):
        return hash_weight(size + address_bytes)

    # A 512-bit coefficient string needs two differently addressed 256-bit calls.
    expansions = columns * 2 * weight(seed_bytes)
    row_hashes = rows * weight(row_bytes)
    parent_hashes = parents * weight(parent_bytes)
    return {
        "ranked": False, "costs_certified": False, "security_proved": False,
        "hash_meter": meter_metadata(),
        "scope": "keygen only; naive Horner counts are not measured RISC-V cycles",
        "paper_keygen_units": columns + rows + parents,
        "assumed_address_bytes": address_bytes,
        "rom32_keygen": {"seed_expansion_units": expansions, "row_units": row_hashes,
                         "parent_units": parent_hashes, "total_units": expansions + row_hashes + parent_hashes},
        "naive_horner": {"field_multiplications": columns * rows * (coefficients - 1),
                         "field_additions": columns * rows * (coefficients - 1)},
        "table_bytes": columns * rows,
        "notice": "No optimized evaluation, concrete hash, signing cost or full-scheme score is claimed.",
    }


if __name__ == "__main__":
    print(json.dumps(keygen_estimates(), indent=2))
