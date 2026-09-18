# Instructions for agents working on this repository

Humans read the published rules; this file is for the AI agents and scripts that
edit them. Keep it short and factual.

## Publication

- **GitHub is canonical** (organizer decision, 2026-09-10). `index.html` on `main`
  is the single source of the competition rules, published unchanged to GitHub
  Pages at https://leanethereum.github.io/leanSphincs/.
- The repository moved from `nconsigny/leansphincs` to `leanEthereum/leanSphincs`
  on 2026-09-15 and was renamed `leanSphincs` the same day to match the
  organization's naming. GitHub redirects both old repository URLs; the old Pages
  address `nconsigny.github.io/leansphincs` is not redirected and must not be cited.
- The earlier Claude artifact
  (https://claude.ai/code/artifact/44cc19cb-44bb-475b-a1c0-e4aad483010a) is a
  frozen legacy copy at draft v0.13. Never republish it, never treat it as the
  current rules, and never wait for it before pushing to `main`.
- Do not tell readers any of the above inside `index.html`. Publication
  mechanics belong here, not in the rules.

## Editing the rules

1. Read the verbatim HTML before replacing text. Plain-text extraction hides
   inline markup such as `<strong>`, `<sub>` and `<span class="tbd">`, and an
   edit that matches the wrong string silently changes nothing.
2. Bump the version marker in the status line and the footer together, and set
   the status-line date.
3. Update `tests/test_website.py` in the same change: it asserts the version and
   the load-bearing sentences of the current rules, and CI runs it.
4. Keep the companion documents consistent: `README.md`, `SCHEMECLAIM_PLAN.md`,
   `IMPLEMENTATION.md`, `SUBMISSION.md`, `OTS_STAGE1.md`,
   `POLYNOMIAL_CODING_REVIEW.md`. Record superseded decisions as history rather
   than deleting them.
5. Style: no em dashes in prose; no vendor or platform names for the
   infrastructure behind sibling competitions (naming the competitions
   themselves is fine); friendly framing toward leanSig, which is a parallel
   track on the consensus layer, not a rival.
6. Amber `<span class="tbd">` marks a value or decision still open. Remove the
   span when the decision closes.

## Submitting a scheme

There is one way in: a pull request against the contract repository that changes only the track's
submission root (`submissions/full/`, see `challenges.json`) and nothing else. Check locally first
with `python3 scripts/verify_pr.py full --source . --json`. The hosted service (`service/`) verifies
the pull request's head in isolation and answers as a commit status and a comment; a verified head
becomes a record only when that exact head is merged. Admission is closed until `challenges.json`
says `open`; do not flip it without the organizers. Website source for the service lives under
`service/`; the rules page it serves is `index.html`.

## Checking a change

```sh
python3 -m unittest discover -s tests
lake build LeanSphincs LeanSphincsTest
lake env lean scripts/check-axioms.lean
```

`lake build` output piped through `tail` hides the exit code; read `PIPESTATUS`.
