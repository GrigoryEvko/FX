import LeanFX2.Term.PreservesTerm.HeterogeneousElim
import LeanFX2.Term.PreservesTerm.UniversalChain.Core
import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullTerm
import LeanFX2.Foundation.TermTranspPathVacuity

/-! # Smoke/AuditTranspCloseLeaf — unblock-E.transp.Close (#2065).

Reviewer-facing audit log for the closure of #2015 unblock-A.leaf.transp:
homogeneous-endpoint `RawStep.par.lift_full_transp` plus the
`DispatchAtom.transp` ctor + driver arm wired into the universal
dispatcher.

## Architectural shape

The raw inversion `RawStep.par.transp_inv` enumerates SEVEN disjuncts
under a `RawTerm.transp pathRaw sourceRaw` head:

1. **cong (transpCong)** — both children par-step independently
2. **transpReflBeta** — shallow β at literal `RawTerm.pathLam typeRaw.weaken`
3. **transpReflBetaDeep** — deep β: `pathRaw → pathLam typeRawTarget.weaken`
4. **uaBeta** — shallow β at `RawTerm.uaToEquiv`
5. **uaBetaDeep** — deep ua β: `pathRaw → uaToEquiv ...`
6. **transpCompose** — shallow β at `RawTerm.pathCompose`
7. **transpComposeDeep** — deep compose β: `pathRaw → pathCompose ...`

Strategy (mirrors `lift_full_hcomp` #2066 and `lift_full_equivApply` #2059):

* Arm 1 → `RawStep.par.lift_transp_cong` (cong-only wrapper, already
  shipped in `EliminatorShallowBeta.lean`).
* Arms 2-3 → both `Step.par.transpReflBetaDeep` (typed ctor from #2063).
  Arm 2 uses `RawStep.par.refl` as path-step; arm 3 forwards the
  inversion's pathStep directly.
* Arms 4-5 → vacuous via `Term.uaToEquiv_excludes_pathTy` (#2101).
* Arms 6-7 → vacuous via `Term.pathCompose_uninhabited` (#2101).

## Scope limitation

The dispatch is restricted to the **homogeneous endpoint case**:
`sourceType = targetType`, `sourceTypeRaw = targetTypeRaw = typeRaw`.
This matches the documented scope of `Step.par.transpReflBetaDeep`
(see ParInductive/Inductive.lean:601 docstring).
Heterogeneous-endpoint transp dispatch remains ROADMAP debt
under unblock-E leaf-coverage.

## Verification

* `lake build LeanFX2` — kernel green (~624 jobs).
* `#assert_no_axioms LeanFX2.RawStep.par.lift_full_transp` shipped
  in `Tools/AuditAll/AuditReduction.lean` (strict gate).
* `DispatchAtom.transp` + driver arm `| transp ... =>` in
  `UniversalChain/Core.lean` and `UniversalChain/LiftFullTerm.lean`.

Closes #2015 unblock-A.leaf.transp. -/

namespace LeanFX2

-- ============================
-- Section A: lift_full_transp leaf — homogeneous endpoint, vacuity discharge
-- ============================

#print axioms RawStep.par.lift_full_transp

-- ============================
-- Section B: Consumed vacuity foundations (#2101)
-- ============================

#print axioms Term.uaToEquiv_excludes_pathTy
#print axioms Term.pathCompose_uninhabited

-- ============================
-- Section C: Consumed typed Step.par β ctors (#2063 + arm-2 refl path)
-- ============================

#print axioms Step.par.transpReflBetaDeep

-- ============================
-- Section D: Surrounding cascade theorems remain zero-axiom
-- ============================

#print axioms RawStep.par.transp_inv
#print axioms RawStep.par.lift_transp_cong
#print axioms Step.par.transpCong

end LeanFX2
