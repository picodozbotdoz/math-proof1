# Memory right-sizing on Modal (2026-10-31)

Operator observation: we requested **32 GiB** for runs whose *actual* peak was
often < 1–3 GiB (and the alert/investigation threshold was 64 GiB, so almost
nothing was ever investigated).  Modal's `memory=` is a soft request, but an
inflated request still misrepresents real usage and degrades scheduling.

## Measured: request vs actual (all runs this session, before the change)

| run | request | actual peak (tree) | waste factor |
|---|---|---|---|
| `AxCheckDecide` (iter-20 audit) | 32 GiB | ~1 GiB | ~32× |
| `CongruenceSmall` sanity runs | 32 GiB | ~1.2 GiB | ~27× |
| `HeckeCommute` / `HeckeGeneratedByT2*` | 32 GiB | 5.9–6.3 GiB | ~5× |
| `FrobeniusCycleType` / `JordanPrimitive` | 32 GiB | 3.1 / 3.2 GiB | ~10× |
| `MaedaDim6..10Weights` (T₂) | 32 GiB | 6.4 / 7.1 / 8.1 / 9.3 / 11.6 GiB | 3–5× |
| `MaedaT3Dim{6..10}` + stretch | 32 GiB | 6.8–12.4 GiB | 3–5× |
| documented heavy: `LehmerPacked` 65536 | 98304 (explicit) | ~63 GiB | appropriate |

Every module in the light/CI tree peaks **≤ 12.4 GiB**; the only legitimate
>32 GiB consumers are the documented Tier-C heavy decides.

## New scheme (commits on `dev/iteration20-maeda-dim6-10`)

* **Request ladder, auto-escalated**: `tools/modal_run.sh` requests
  **8192 MiB** by default and re-runs automatically on OOM
  (`lean_check.py` detects peak tree RSS ≥ 97 % of the request on a failed
  build, prints `[memory] OOM likely`, exits 42): 8192 → 16384 → 32768.
  Beyond 32 GiB it stops and tells the caller to pass an explicit
  `LEAN_CHECK_MEMORY_MIB` — known-heavy targets (LehmerPacked-class) were
  always documented as explicit-override anyway.
* **`lean_build.py`**: `memory=` now reads `LEAN_BUILD_MEMORY_MIB`
  (default 8192, was hardcoded 32768).
* **Investigation threshold lowered 64 → 16 GiB** (`LEAN_CHECK_MEM_ALERT_GIB`
  default in `lean_check.py`; AGENTS.md "Memory alerts" policy updated).
  With the ladder in place, any build genuinely reaching 16 GiB is either a
  heavy decide that belongs in Tier C or a leak worth a `[profile]` run.
* Every run now prints `[memory] request … MiB` so logs are self-documenting;
  per-attempt logs carry an `-m<mib>` suffix under the persistent runs dir.

## Validation

* V1 (request path): `--target MathProof.Tau.CongruenceSmall` at the default
  → `[memory] request 8192 MiB`, peak 1.20 GiB, green (was 32 GiB request).
* V2 (escalation path): `LEAN_CHECK_NO_CACHE=1 --file MaedaDim8Weights.lean`
  → **no OOM — green in one attempt at the 8192 MiB request against a 20.1 GiB
  actual peak**: Modal's soft `memory=` over-granted, so the escalation ladder
  never fired.  Conclusion: the ladder is a *fallback* for when Modal actually
  enforces the request (contended hosts), not the primary control.  The
  primary controls are (a) the honest telemetry (per-module peaks, every run),
  and (b) the 16 GiB alert — which fired for the first time in this run and
  was investigated + CLOSED in `research/memory-alerts.md`.
* V2 side-finding (new gotcha, recorded in the alert entry): a NO_CACHE cold
  build rebuilds the whole import closure with ~7 concurrent lean processes,
  so the *tree* peak (20.1 GiB) is the parallel SUM, while the biggest single
  process (what request sizing keys on) peaked at 8.0 GiB.  Tree peaks from
  no-cache runs must not be compared to cached-run tree peaks.
* V2 also caught a real bug: `LEAN_CHECK_NO_CACHE=1` never worked — the env
  var was read *inside* the remote function, and `modal run` does not forward
  the caller's environment.  Fixed by reading it client-side in `main()` and
  passing `use_cache=` explicitly (first V2 attempt silently cache-hit in
  75 s; the redo took 452 s and really rebuilt).
* The escalation re-runs `modal run` from scratch (a fresh app definition per
  invocation), so an OOMed attempt pays its wall time again — the price of
  honest defaults; with the shared build cache the second attempt usually
  restarts warm.

## Cost note

Modal bills by allocation while running; right-sized requests mostly buy
honest scheduling and truthful telemetry rather than dramatic savings — but
the 32× over-request on audit-style runs is exactly the kind of noise this
removes.  The 16 GiB alert restores the memory-alert policy's teeth: between
2026-10-29 and this change, zero alerts fired despite repeated 3–5× waste.
