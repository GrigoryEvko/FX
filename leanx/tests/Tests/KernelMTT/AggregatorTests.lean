import FX.KernelMTT

/-!
# KernelMTT aggregator tests (V1.5-sub)

Pin the scaffold version tag and the closed-R-task ledger so a
drift between the task-list pacing in `closedRTasks` and the
version tag fails `lake build Tests` (not just the library
build).

Coverage:

  * `scaffoldVersion` pins the current R-task-phase string.
  * `closedRTasks` length matches the cumulative close count.
  * Every submodule re-exported through the aggregator is
    reachable from a single `import FX.KernelMTT`.
-/

namespace Tests.KernelMTT.AggregatorTests

open FX.KernelMTT

/-! ## Scaffold-version pinning -/

example : FX.KernelMTT.scaffoldVersion = "V1.5-sub" := rfl

example : FX.KernelMTT.closedRTasks.length = 16 := by decide

/-- The R0.1–R0.8 + R1.1 + R1.4/V1.3 + V1.4 + W2 + W3 + V1.15 +
    V1.5-conv + V1.5-sub task ledger is pinned in exact order
    so an insertion or reordering fails build. -/
example :
    FX.KernelMTT.closedRTasks =
      [ "R0.1 — fx_modecat.md skeleton"
      , "R0.2 — Mode datatype + per-mode configs"
      , "R0.3 — Modality enumeration + admissibility"
      , "R0.4 — four cross-mode adjunction records"
      , "R0.5 — 27 subsumption 2-cells"
      , "R0.6 — §6.8 collision catalog as missing 2-cells"
      , "R0.7 — 2-category coherence laws"
      , "R0.8 — unit/counit 2-cell structure"
      , "R1.1 — tree aggregator + lakefile wiring"
      , "R1.4 / V1.3 — mode-indexed Term inductive"
      , "V1.4 — modality intro/elim primitives"
      , "W2 — well-scoped (Term : Nat → Type) + mutual TermArgs"
      , "W3 — typed shift + substitution"
      , "V1.15 — Reduction.lean (β/ι/ν/modElim-ι/idJ-ι/coerce + whnf)"
      , "V1.5 (first installment) — Conversion.lean (convEq + η)"
      , "V1.5 (second installment) — Subtyping.lean (T-sub)"
      ] := by decide

/-! ## Reachability via the aggregator

Every submodule exposed by `FX.KernelMTT` must be reachable
without an explicit submodule import.  These examples name
symbols from each submodule via the shared `open FX.KernelMTT`
above; if one goes missing from the aggregator, the
corresponding example fails to resolve. -/

-- From `Mode.lean` (R0.2):
example : Mode.all.length = 4 := by decide

-- From `Modality.lean` (R0.3):
example : Modality.all.length = 20 := by decide

-- From `Adjunction.lean` (R0.4 + R0.8):
example : Adjunction.all.length = 4 := by decide
example : Adjunction.twoCellNames.length = 4 := by decide

-- From `TwoCells.lean` (R0.5):
example : SubsumptionCell.all.length = 27 := by decide

-- From `Collisions.lean` (R0.6):
example : CollisionRule.all.length = 9 := by decide
example : Reduction.all.length = 3 := by decide

-- From `Coherence.lean` (R0.7 + R0.8) — prove a concrete
-- coherence theorem to show the module is reachable through
-- the aggregator.  Picking a discrete `Bool`-valued check so
-- the reference compiles without Prop-term machinery.
example :
    Adjunction.all.all (fun adj => adj.leftMode ≠ adj.rightMode) = true :=
  Coherence.adjunctions_cross_modes

end Tests.KernelMTT.AggregatorTests
