# Reservoir submission — status and steps

[Reservoir](https://reservoir.lean-lang.org) is the Lean FRO's official
registry of Lean packages: it automatically indexes qualifying GitHub
repositories, builds them on current toolchains, and hosts the results.
Mathlib maintainers and formalization researchers browse it, and being
listed is the single cheapest way for this project to become *findable* by
the right people.

**There is no application PR.** Reservoir re-indexes GitHub approximately
daily; a repository that meets the four inclusion criteria below simply
appears. (Upstream repo: [leanprover/reservoir](https://github.com/leanprover/reservoir).)

## The four inclusion criteria, and where we stand

| Criterion (from reservoir.lean-lang.org/inclusion-criteria) | Status |
|---|---|
| Public GitHub source repository (not a fork or template) | ✅ met — `picodozbotdoz/math-proof1` is public, not a fork |
| Root `lake-manifest.json` | ✅ met — present at the repository root |
| GitHub-recognized OSI-approved license | ⬜ one step away — commit the `LICENSE` (Apache-2.0) from this kit; GitHub then detects and displays "Apache-2.0" on the code page |
| At least 2 GitHub stars | ⬜ needs two stars from *other* users — you cannot star your own repository |

So the whole submission is: **merge the license, get two stars, wait a few
days.** The stars tend to follow naturally from the Zulip announcement
([zulip-post.md](zulip-post.md)) — people who find the work useful star it.
If the repo still does not appear on Reservoir about a week after both
boxes are ticked, open an issue on
[leanprover/reservoir](https://github.com/leanprover/reservoir) reporting
the missed index.

## Notes for the listing

- **Expected build.** Reservoir's builder runs the default `lake` target.
  This repo is set up so that the default build *excludes* the heavy
  kernel-decide modules (`LehmerMod`, `LehmerPacked` — their 65536 check
  needs ~63 GiB of kernel heap; see `AGENTS.md` and
  `research/lehmer-mod-scaling-study.md`). The automatic build is therefore
  expected to succeed; if a maintainer ever asks, point them at those two
  documents rather than treating it as a failure.
- **Metadata.** The repository description and topics from step 1 of the
  kit (`README.md` in this folder) are what make the Reservoir listing page
  readable — do that step first.
- **Releases.** Once a `v0.1.0` tag exists (step 3 of the kit), Reservoir
  can host release artifacts; tags also drive the Zenodo DOI, so tag before
  expecting anything release-shaped to appear.
