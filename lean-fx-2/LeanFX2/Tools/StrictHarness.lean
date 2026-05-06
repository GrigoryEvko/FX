import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census
import LeanFX2.Tools.StrictHarness.DeclShape
import LeanFX2.Tools.StrictHarness.AxiomAdjacent
import LeanFX2.Tools.StrictHarness.TrustEscape
import LeanFX2.Tools.StrictHarness.MetaLevel
import LeanFX2.Tools.StrictHarness.Reporting
import LeanFX2.Tools.StrictHarness.Dashboard

/-! # Tools/StrictHarness — umbrella aggregator

This module is now an umbrella that re-exports the strict-harness
gates from sibling submodules under `Tools/StrictHarness/`.  The
split lets Lake compile each submodule in parallel, reducing
wall-clock time on multi-core builds.

The original monolithic `StrictHarness.lean` is split into:

* `Common.lean` — strict-violation taxonomy, classifyStrictViolations,
  detection helpers, aggregate strict-namespace gates, FX1/Core
  host-minimal gate, all import-surface gates, public-umbrella
  reachability, host-heavy import allowlist, import-surface summary.
* `Census.lean` — raw/typed parity gate, schematic-payload census,
  mode-discipline budget, semantic-signature debt gates, bridge
  constructor coverage, rich schema and linkage debt gates.
* `DeclShape.lean` — Step.par cong-rule coverage, Conv cong-rule
  coverage, cast-operator usage, forbidden-shape decl count,
  all-raw-payload Term ctor count, single-step Conv claim detector,
  Reduction.Compat per-cong coverage.
* `AxiomAdjacent.lean` — axiom-adjacent dependency gates (Inhabited,
  HEq, decide, subsingleton, match-compiler, rfl-on-non-trivial),
  universe-polymorphism leak, Quot family deps, Acc/WellFounded
  deps, Lean elaboration deps, toRaw projection coverage, IsClosedTy
  parity.
* `TrustEscape.lean` — inductive ctor-count regression, Coe family,
  OfNat / Subtype / Function-property deps, Reducibility-status
  shape, inductive ctor exact-count, bridge round-trip parity,
  Eq-rewriting deps, True/False empty-result, Term/RawTerm ctor
  delta, dependent-pair deps, Classical reasoning, API typeclass,
  IO effect, anonymous-projection.
* `MetaLevel.lean` — Lean meta-Expr, monadic-stack, heavyweight-
  tactic, Term ctor → Smoke namespace usage parity, absurd/False,
  Setoid/Quotient extended deps.
* `Reporting.lean` — end-of-build summary reporter, naming
  discipline, hypothesis-as-postulate, headline refl-fragment,
  broad manufactured-Step dependent, staged FX1 axiom leak,
  per-namespace decl-count snapshot.
* `Dashboard.lean` — aggregate semantic-debt dashboard.

`import LeanFX2.Tools.StrictHarness` keeps working transparently.
-/
