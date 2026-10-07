# Causal Foundations probability supplement v0.7.0

This subproject formalizes published **Theorem 3**, including an actual attained
first entry, its measurable extension, the invariant null exception set and an
invariant complete path probability measure. See
[source alignment](../THEOREM3_ALIGNMENT.md).

Lean is fixed at 4.24.0 and Mathlib at
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (v4.24.0). The manifest and
`verification/DEPENDENCY_LOCK.json` pin Mathlib and all eight external supporting
repositories. The original core library is the path dependency `..`.
Downloaded runtimes, dependencies and compiled caches are excluded from git.

From this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake resolve-deps
lake exe cache get Mathlib.MeasureTheory.Measure.Typeclasses.Probability Mathlib.MeasureTheory.Measure.Dirac
lake build CausalFoundationsProbability
lake env lean AxiomAudit.lean
lake env lean FirstHittingTests.lean -o .lake/build/lib/lean/FirstHittingTests.olean
python3 verification/run_checks.py \
  --toolchain /absolute/path/to/lean-4.24.0-linux \
  --checker /absolute/path/to/lean4checker \
  --require-standard-runtime
```

There are **21 main theorem declarations and 12 boundary-test theorems**. The
exact dependency registry audits every one; all endpoint dependencies are the
standard `propext`, `Classical.choice`, and `Quot.sound`. Custom proof assumptions,
omitted proofs and native-evaluation dependencies are rejected.

The 16 command checks bind the official runtime, three published PDFs, current
proof sources and exact external dependency commits; compile and audit all new
theorems; reject a false statement; and replay every imported constant into a
fresh environment using the pinned `lean4checker` and the unique
`ProbabilityReplayAll` target, avoiding the core project's `ReplayAll` name. This includes the transitive
Mathlib and core imports. A second build starts from copies of the project's Lean
sources and configuration, with no copied project compilation artifacts, followed
by an equal dependency audit and another full fresh replay. **The pinned external
dependency cache is reused in that cold project build**; its imported constants
are checked by both fresh replays. No cold source compilation of all of Mathlib
is claimed.

The original core's independent 24 command checks remain required. GitHub CI
runs both runners, yielding 40 checks and 201 audited project theorem declarations
in total. Status requires both results for the exact source commit. A compatibility
library is allowed only for explicitly labelled local runs and forbidden in CI.
Replay uses the same official Lean kernel; it is not a separately implemented
verifier or independent certification of the paper-to-statement alignment.
