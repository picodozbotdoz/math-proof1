# Outreach kit — making this work discoverable

This directory holds ready-to-use material for publishing the project to the
Lean / mathematics community. Work through it top to bottom; nothing here
requires more than a few minutes each. Steps 1–2 are done on github.com,
steps 3–4 are files in this repo, step 5 is a post you publish.

- [x] 1. GitHub repository settings (description, topics, license) — done
- [x] 2. GitHub Pages (site lives in `docs/`) — done
- [x] 3. Release `v0.1.0` + Zenodo DOI — done; concept DOI
      `10.5281/zenodo.23636675` (always-latest) is badged in the README and
      linked from the site footer; the v0.1.0 version DOI is
      `10.5281/zenodo.23636676`. For future releases: bump `version:` in
      `CITATION.cff`, tag, publish — the metadata is already Zenodo-valid.
- [ ] 4. Reservoir listing (automatic once license + 2 stars) — 5 min
- [ ] 5. Lean Zulip post — 5 min

---

## 1. GitHub repository settings

Open https://github.com/picodozbotdoz/math-proof1/settings
(General → "About") and set:

**Description** (paste verbatim):

> Formally verified modular-forms mathematics in Lean 4 + Mathlib: Ramanujan's
> τ function, his congruence τ(n) ≡ σ₁₁(n) (mod 691), and kernel-decided
> nonvanishing τ(n) ≠ 0 for all n ≤ 65536, toward Lehmer's conjecture.

**Topics** (paste into the Topics field one at a time; GitHub lowercases):

```
lean4
mathlib4
formal-verification
theorem-proving
modular-forms
ramanujan-tau
lehmer-conjecture
number-theory
```

**Website** (once Pages is on, see step 2): `https://picodozbotdoz.github.io/math-proof1/`

The **license** ships with this kit (`LICENSE` at the repo root, Apache-2.0,
matching Mathlib's own license so downstream reuse is friction-free). Commit
it together with `CITATION.cff` — GitHub will then show a "Cite this
repository" button and a license badge automatically.

---

## 2. Optional: GitHub Pages for the project site

The site lives in `docs/`: `docs/index.html` is the project landing page and
`docs/langlands.html` the interactive educational page (the directory was
renamed from `langlands-site/` to `docs/` precisely because branch-based
Pages only offers `/ (root)` or `/docs` as the source folder). Enabling
Pages serves it at the site root `https://picodozbotdoz.github.io/math-proof1/`:

Settings → Pages → Build and deployment → Source: **Deploy from a branch** →
Branch `master`, folder `/docs` → Save.

A `.nojekyll` file sits in `docs/` so Pages serves the HTML verbatim
instead of running Jekyll. No GitHub Actions are involved.

---

## 3. Tag a release + Zenodo DOI

Zenodo (zenodo.org) is free and gives the repository a permanent, versioned,
citable DOI — the "contributes to humanity" artifact.

1. Commit and push `LICENSE` and `CITATION.cff` (from this kit) first —
   Zenodo requires a license and reads citation metadata from `CITATION.cff`.
2. Tag and push: `git tag -a v0.1.0 -m "First public release" && git push origin v0.1.0`
3. Log in at zenodo.org with GitHub, click **Get started / + New upload →
   Import from GitHub**, authorize the `math-proof1` repo, and flip it on.
   Every future release tag then gets its own DOI automatically.
4. Edit the Zenodo entry to point the related identifier at
   `https://github.com/picodozbotdoz/math-proof1` and pick resource type
   *Software*; the title/abstract/author come straight from `CITATION.cff`.

Put the DOI badge line Zenodo generates into the README right under the title
(leave a `<!-- DOI badge here -->` comment if you want CI docgen untouched).

---

## 4. Reservoir listing

Reservoir (reservoir.lean-lang.org) is the Lean FRO's official registry of
Lean packages — it indexes, builds, and hosts every qualifying repository,
and mathlib maintainers browse it. **There is no application PR**: Reservoir
re-indexes GitHub roughly daily and picks up any repository meeting its four
inclusion criteria (public repo · root `lake-manifest.json` · OSI-approved
license GitHub recognizes · at least 2 stars). Two of those four need action
from you — the license from this kit, and two stars from other users — and
then the listing happens on its own. Full checklist and status:
[`reservoir-submission.md`](reservoir-submission.md).

---

## 5. Lean Zulip post

A ready-to-paste announcement is in [`zulip-post.md`](zulip-post.md).
Post it in the **#maths** stream (topic suggestion: *Ramanujan τ:
kernel-decided nonvanishing to 65536*). The draft deliberately leads with
the kernel-engineering result — the thing this community finds genuinely
new — and keeps claims calibrated (the congruences are classical; the
headline is the verified-computation bound and the scaling study).
