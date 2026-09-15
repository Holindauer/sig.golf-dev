"""Exact organizer-owned product scoring; diagnostic scores never confer eligibility."""

from fractions import Fraction
import json

from oracle_meter import METER_ID

CLAIM_ID = "suf-cma-total-work-pk32-adaptive-availability-v2"


def additive_score(size, verification, bandwidth_price):
    """Historical research utility, not the competition scoring authority."""
    size, verification, price = map(Fraction, (size, verification, bandwidth_price))
    if size <= 0 or verification <= 0 or price <= 0:
        raise ValueError("positive size, verification work and bandwidth price required")
    return price * size + verification


def product_score(size, verification):
    if any(type(value) is not int or value <= 0 for value in (size, verification)):
        raise ValueError("positive integer size and verification work required")
    return size * verification


def load_scoring_profile(path):
    profile = json.loads(path.read_text(encoding="utf-8"))
    if type(profile) is not dict or set(profile) != {"schema", "id", "verification_meter"}:
        raise ValueError("invalid organizer scoring profile fields")
    if profile["schema"] != "leansphincs-product-profile-v1" or profile["verification_meter"] != METER_ID:
        raise ValueError("unsupported scoring schema or verification meter")
    if not isinstance(profile["id"], str) or not profile["id"]:
        raise ValueError("scoring profile requires an identifier")
    return profile


def score_entry(profile, sigma, verification):
    value = product_score(sigma, verification)
    return {"value": str(value), "eligible": False, "diagnostic": True,
            "objective": "signatureBytes * verification",
            "units": "signature bytes * verification work units",
            "profile_id": profile["id"], "direction": "minimize", "tie_break": sigma}
