"""Organizer-owned, fail-closed deployment gates. No executable validator yet.

Execution certificates must bind algorithms, executable and profile, and cover
parsing, malformed-input rejection, arithmetic, randomness, retries and setup.
Raw-query certificates must bound every structural response path, including
ROM-inconsistent responses; runtime measurements alone are insufficient.
Storage certificates count serialized secret and precomputation bytes and state
how keys are restored. RAM accounting does not establish persistent storage.
Side-channel evidence is an independent implementation review under a stated
timing/memory-access leakage model, not a formal noninterference theorem.
"""
import hashlib
import json
from scoring_policy import CLAIM_ID

CAPS = ('reference_execution', 'verification_limit', 'raw_keygen_queries',
        'raw_sign_queries', 'raw_verify_queries', 'persistent_secret_bytes',
        'precomputation_bytes', 'executable_bytes', 'leakage_model',
        'executable_validator', 'side_channel_validator')
FIXED = dict(ram_bytes=65536, keygen_target_ms=60000, sign_target_ms=1500,
             overrun_bits=40, keygen_deadline_ms=360000, sign_deadline_ms=120000)


def load_resource_profile(path):
    profile = json.loads(path.read_text())
    if (set(profile) != {'schema', 'id', *CAPS, *FIXED} or
            profile['schema'] != 'leansphincs-resources-v1' or
            not isinstance(profile['id'], str) or not profile['id'] or
            any(type(profile[k]) is not int or profile[k] != v for k, v in FIXED.items())):
        raise ValueError('invalid organizer resource profile')
    for key in CAPS:
        value = profile[key]
        if value is not None:
            if key in {'reference_execution', 'leakage_model', 'executable_validator', 'side_channel_validator'}:
                if type(value) is not str or not value.strip():
                    raise ValueError('invalid resource profile field: ' + key)
            elif type(value) is not int or value <= 0:
                raise ValueError('invalid resource cap: ' + key)
    return profile


def profile_digest(profile):
    return hashlib.sha256(json.dumps(profile, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def deployment_gates(profile, receipt=None, evidence=None):
    receipt, evidence = receipt or {}, evidence or {}
    missing = [key for key in CAPS if profile.get(key) is None]
    reasons = ['unset ' + key for key in missing]
    if receipt.get('claim_version') != CLAIM_ID or receipt.get('mathematical_verification') is not True:
        reasons.append('current mathematical certificate missing')
    binding = {'claim_version': CLAIM_ID, 'profile_sha256': profile_digest(profile),
               'submission_sha256': receipt.get('submission', {}).get('sha256'),
               'executable_sha256': receipt.get('executable_sha256')}
    for kind in ('execution', 'storage', 'side_channel'):
        item = evidence.get(kind)
        if not item:
            reasons.append(kind + ' evidence missing')
        elif (not all(binding.values()) or any(item.get(k) != v for k, v in binding.items())):
            reasons.append(kind + ' evidence binding mismatch')
    # Deliberately unconditional: identifiers and matching hashes are not validators.
    reasons.append('executable resource validation unimplemented')
    reasons.append('independent side-channel evidence validator unimplemented')
    return {'resource_certification': False, 'side_channel_review': False,
            'deployment_eligible': False, 'reasons': reasons,
            'profile_sha256': profile_digest(profile)}
