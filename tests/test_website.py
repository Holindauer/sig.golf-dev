"""Local structure and decision-consistency checks for the competition draft.

Not a deployment check, full HTML validator, or verification of external links.
"""

from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
import unittest
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


class Page(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.ids = []
        self.links = []
        self.sections = {}
        self.active_section = None
        self.feed(source)
        self.close()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.append(attrs["id"])
        if tag == "a" and "href" in attrs:
            self.links.append(attrs["href"])
        if tag == "section":
            if self.active_section is not None:
                raise ValueError("Unexpected nested section")
            self.active_section = attrs["id"]
            self.sections[self.active_section] = []

    def handle_endtag(self, tag):
        if tag == "section":
            if self.active_section is None:
                raise ValueError("Unmatched section close")
            self.active_section = None

    def handle_data(self, data):
        if self.active_section is not None:
            self.sections[self.active_section].append(data)

    def section_text(self, section):
        return " ".join("".join(self.sections[section]).split())


class WebsiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (ROOT / "index.html").read_text(encoding="utf-8")
        cls.page = Page(cls.source)

    def test_sections_and_anchors(self):
        self.assertIsNone(self.page.active_section)
        self.assertTrue(self.page.sections)
        self.assertEqual([key for key, count in Counter(self.page.ids).items() if count > 1], [])
        for href in self.page.links:
            if href.startswith("#"):
                self.assertIn(unquote(href[1:]), self.page.ids)

    def test_linked_repo_documents_exist(self):
        prefix = "/leanEthereum/leanSphincs/blob/main/"
        checked = 0
        for href in self.page.links:
            url = urlsplit(href)
            if url.netloc == "github.com" and url.path.startswith(prefix):
                path = ROOT / unquote(url.path[len(prefix):])
                self.assertTrue(path.is_file(), href)
                checked += 1
        self.assertGreater(checked, 0)

    def test_version_and_product_objective(self):
        self.assertIn("DRAFT v0.22", self.source)
        self.assertIn("draft rules v0.22", self.source)
        self.assertIn("2026-09-15", self.source)
        self.assertIn('<span class="formula-big">minimize&nbsp;&nbsp;|σ| × V</span>', self.source)
        self.assertIn("Stage 1 is academic research; Stage 2 is the Ethereum selection.", self.source)
        objective = self.page.section_text("objective")
        self.assertIn("both stages", objective)
        self.assertIn("byte × verification-work units", objective)
        self.assertIn("No bandwidth price or conversion coefficient", objective)
        self.assertIn("full Pareto frontier", objective)
        self.assertIn("not directly comparable", objective)
        self.assertIn("1.5 s signing, 1 minute keygen", objective)
        self.assertIn("worst-case cap", objective)
        self.assertIn("2 minutes signing and 6 minutes keygen", objective)
        self.assertIn("Those absolute limits admit no overrun allowance", objective)
        for stale in ("v0.12", "v0.13", "v0.14", "v0.15", "v0.16", "v0.17", "v0.18", "v0.19", "Spacetime", "2^-60", "2<sup>−60</sup>"):
            self.assertNotIn(stale, self.source)

    def test_publication_mechanics_stay_out_of_the_rules(self):
        self.assertIn('<link rel="canonical" href="https://leanethereum.github.io/leanSphincs/">', self.source)
        self.assertNotIn("GitHub is canonical", self.source)
        self.assertNotIn("Claude artifact", self.source)
        self.assertIn('href="https://github.com/leanEthereum/leanSphincs"', self.source)
        agents = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
        self.assertIn("GitHub is canonical", agents)
        self.assertIn("frozen legacy copy", agents)
        self.assertIn("Never republish it", agents)

    def test_current_oracle_meter(self):
        cost = self.page.section_text("costmodels")
        for text in ("32-byte output", "ceil(inputBytes / 64)", "including domain separation",
                     "rom256-input64-ceil-v1", "Sum the per-call ceilings",
                     "empty-input case follows the literal ceiling",
                     "not a concrete compression block or an instruction"):
            self.assertIn(text, cost)
        self.assertNotIn("ceil(inputBytes / 32)", self.source)

    def test_no_false_launch_or_budget_certificate_claim(self):
        self.assertIn("submissions not open", self.source)
        mvp = self.page.section_text("mvp")
        for text in ("explicitly unranked", "does not yet bind the signing and keygen budget certificates",
                     "sigma.txt", "hverify.txt", "bound.txt", "No cryptographic baseline yet",
                     "not in a fourth entrant file", "diagnostic product score"):
            self.assertIn(text, mvp)
        cost = self.page.section_text("costmodels")
        self.assertIn("would not alone prove a worst-case bound", cost)
        self.assertIn("No aggregate hash-throughput estimate certifies", cost)
        rules = self.page.section_text("rules")
        for text in ("Mandatory latency guarantees and absolute resource caps",
                     "Pr[T_keygen > 60 s] ≤ 2^-40", "Pr[T_sign > 1.5 s] ≤ 2^-40",
                     "T_keygen ≤ 360 s", "T_sign ≤ 120 s", "with no probabilistic exception",
                     "(1/256)", "not a lifetime",
                     "Absolute runtime and raw-query caps still apply on every path",
                     "Late completion, signing failure and forgery are separate events",
                     "cannot be substituted for that bound", "permitted adaptive message selection",
                     "every generated secret key and every message",
                     "including failed attempts", "repeated and empty-input calls",
                     "without the required resource certificates is ineligible",
                     "query padding does not establish useful security"):
            self.assertIn(text, rules)

    def test_pure_rom_and_exact_constants(self):
        rules = self.page.section_text("rules")
        for text in ("pure ROM", "No additional cryptographic assumptions",
                     "end-to-end Lean proof", "All constants remain in the bound",
                     "no constants-dropping eligibility rule",
                     "must not depend on Q or s", "1–128 monomials"):
            self.assertIn(text, rules)
        self.assertNotIn("Two proof styles are admissible", self.source)
        self.assertNotIn("excludes MPCiTH and VOLEiTH", self.source)

    def test_query_accounting_and_same_scheme_decay(self):
        rules = self.page.section_text("rules")
        for text in ("Q = qH + qS", "raw hash calls across the whole experiment",
                     "key generation, adversarial hashing, honest signing and final forgery verification",
                     "same scheme, parameters and bound B", "theorem itself must cover",
                     "B(Q, 2^20) ≤ Q / 2^124", "B(Q, 2^32) ≤ Q / 2^100",
                     "conservative sufficient gate"):
            self.assertIn(text, rules)
        baseline = self.page.section_text("baseline")
        self.assertIn("same-scheme extended-lifetime proof is additional work", baseline)

    def test_simple_interface_key_size_and_failure(self):
        rules = self.page.section_text("rules")
        for text in ("Public key at most 32 bytes", "Keygen() → (pk, sk)",
                     "Sign(sk, m) → σ or ⊥", "Verify(pk, m, σ) → 0 or 1",
                     "There is no required separate cache or presign channel",
                     "Immutable precomputation may be part of sk",
                     "exactly the declared length",
                     "adaptive availability", "An absent position is not a failure",
                     "final forgery verification is excluded",
                     "Worst-case failure analysis is separate",
                     "not enforced by the current statement/harness"):
            self.assertIn(text, rules)
        self.assertIn("Q² / 2256", rules)
        self.assertNotIn("Public key at most 64", rules)

    def test_deployment_gates(self):
        for text in ("Deployment eligibility is blocked in this release", "Unset values",
                     "impossible ROM responses", "key restoration", "timing/memory-access",
                     "not a formal noninterference theorem", "2<sup>−96</sup>",
                     "suf-cma-total-work-pk32-adaptive-availability-v2"):
            self.assertIn(text, self.source)

    def test_broad_academic_track_and_composition(self):
        mvp = self.page.section_text("mvp")
        for text in ("academic research track", "few-time primitives", "complete constructions",
                     "Standard hybrid arguments", "generally with a loss",
                     "fully black-box standalone scheme", "Ethereum selection track"):
            self.assertIn(text, mvp)
        rules = self.page.section_text("rules")
        self.assertIn("Reed–Solomon coding are permitted", rules)

    def test_human_credit_is_not_numeric_rank(self):
        fmt = self.page.section_text("format")
        self.assertIn("Numerical ranking is automatic; research credit is human-curated", fmt)
        self.assertIn("do not change a submission's numerical score", fmt)
        self.assertNotIn("post-launch harness bug", self.source)
        self.assertIn("https://blog.zksecurity.xyz/posts/zkgolf/", self.page.links)
        self.assertNotIn("vacation", self.source)
        self.assertNotIn("not yet reviewed by the leanSig authors", self.source)

    def test_no_quantum_promise(self):
        rules = self.page.section_text("rules")
        self.assertIn("A QROM theorem is not an entry requirement", rules)
        self.assertIn("not a promised post-competition formalization", rules)
        self.assertIn("does not establish a generic", rules)


if __name__ == "__main__":
    unittest.main()
