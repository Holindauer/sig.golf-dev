import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from eligibility import CAPS, deployment_gates, load_resource_profile, profile_digest
from scoring_policy import CLAIM_ID
VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent

class EligibilityTests(unittest.TestCase):
    def setUp(self):
        self.profile = load_resource_profile(VERIFIER / 'resources.json')

    def test_unset_caps_and_missing_evidence_fail_closed(self):
        gates = deployment_gates(self.profile)
        self.assertFalse(gates['deployment_eligible'])
        for key in CAPS: self.assertIn('unset ' + key, gates['reasons'])
        for kind in ('execution', 'storage', 'side_channel'):
            self.assertIn(kind + ' evidence missing', gates['reasons'])

    def test_even_matching_evidence_cannot_bypass_unimplemented_validators(self):
        profile = copy.deepcopy(self.profile)
        for key in CAPS:
            profile[key] = 1 if key not in {'reference_execution', 'leakage_model',
                                          'executable_validator', 'side_channel_validator'} else 'declared'
        receipt = dict(claim_version=CLAIM_ID, mathematical_verification=True,
                       submission={'sha256': 'source'}, executable_sha256='binary')
        binding = dict(claim_version=CLAIM_ID, profile_sha256=profile_digest(profile),
                       submission_sha256='source', executable_sha256='binary')
        evidence = {kind: binding.copy() for kind in ('execution', 'storage', 'side_channel')}
        for change in (None, 'executable_sha256', 'profile_sha256', 'submission_sha256', 'claim_version'):
            altered = copy.deepcopy(evidence)
            if change: altered['execution'][change] = 'wrong'
            gates = deployment_gates(profile, receipt, altered)
            for key in ('deployment_eligible', 'resource_certification', 'side_channel_review'):
                self.assertFalse(gates[key])
            if change: self.assertIn('execution evidence binding mismatch', gates['reasons'])

    def test_historical_receipt_cannot_be_promoted(self):
        receipt = dict(claim_version='suf-cma-total-work-pk32-decay-v1',
                       mathematical_verification=True, status='accepted', deployment_eligible=True)
        gates = deployment_gates(self.profile, receipt)
        self.assertFalse(gates['deployment_eligible'])
        self.assertIn('current mathematical certificate missing', gates['reasons'])

    def test_invalid_profile_cannot_change_fixed_limits(self):
        for key, value in (('ram_bytes', 65537), ('raw_sign_queries', True), ('extra', 1)):
            altered = self.profile | {key: value}
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'profile.json'
                path.write_text(json.dumps(altered))
                with self.assertRaises(ValueError): load_resource_profile(path)
