"""Host-side description of the v0.15 Lean meter, not a cost certificate."""

METER_ID = "rom256-input64-ceil-v1"
INPUT_UNIT_BYTES = 64
OUTPUT_BYTES = 32


def hash_weight(input_bytes):
    if type(input_bytes) is not int or input_bytes < 0:
        raise ValueError("input length must be a nonnegative integer number of bytes")
    return (input_bytes + INPUT_UNIT_BYTES - 1) // INPUT_UNIT_BYTES


def meter_metadata():
    return {"id": METER_ID, "input_unit_bytes": INPUT_UNIT_BYTES,
            "output_bytes": OUTPUT_BYTES, "rounding": "ceil", "empty_input_cost": 0,
            "domain_separation_bytes_charged": True}
