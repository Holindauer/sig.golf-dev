"""Exact organizer-owned additive pricing. A missing coefficient issues no score."""

from fractions import Fraction
import json

from oracle_meter import METER_ID

CLAIM_ID = "suf-cma-total-work-pk32-adaptive-availability-v2"


def additive_score(size, verification, bandwidth_price):
    size, verification, price = map(Fraction, (size, verification, bandwidth_price))
    if size <= 0 or verification <= 0 or price <= 0:
        raise ValueError("positive size, verification work and bandwidth price required")
    return price * size + verification


def load_scoring_profile(path):
    profile = json.loads(path.read_text(encoding="utf-8"))
    required = {"schema", "id", "verification_meter", "bandwidth_price"}
    if type(profile) is not dict or set(profile) != required:
        raise ValueError("invalid organizer scoring profile fields")
    if profile["schema"] != "leansphincs-additive-profile-v1" or profile["verification_meter"] != METER_ID:
        raise ValueError("unsupported scoring schema or verification meter")
    if not isinstance(profile["id"], str) or not profile["id"]:
        raise ValueError("scoring profile requires an identifier")
    price = profile["bandwidth_price"]
    if price is not None:
        if type(price) is not dict or set(price) != {"numerator", "denominator"}:
            raise ValueError("bandwidth price requires an exact fraction")
        if any(type(v) is not int or not 0 < v <= 2**63 - 1 for v in price.values()):
            raise ValueError("bandwidth price requires bounded positive integers")
        fraction = Fraction(price["numerator"], price["denominator"])
        if fraction.denominator != price["denominator"]:
            raise ValueError("bandwidth price must be reduced")
    return profile


def score_entry(profile, sigma, verification):
    price = profile["bandwidth_price"]
    if price is None:
        return None
    value = additive_score(sigma, verification, Fraction(price["numerator"], price["denominator"]))
    return {"value": str(value), "eligible": False, "diagnostic": True, "objective": "c * signatureBytes + verification",
            "profile_id": profile["id"], "direction": "minimize", "tie_break": sigma}
