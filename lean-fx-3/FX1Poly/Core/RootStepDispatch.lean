import FX1Poly.Core.StepTable
import FX1Poly.Core.RawTermNF

/-! # FX1Poly/Core/RootStepDispatch
    — the root-redex dispatch: `hasRootStepSource source = true → ∃ target, Step source target`

The detector IS the generic canonical-table walk, so the dispatch is its
soundness: a `some` firing is a table redex, and a table redex is a
kernel `Step` (the adequacy).  ONE generic argument — the historical
eleven-deep per-generator `dite` peel is gone with the bespoke detector.

## Zero-axiom verification

Option-match on the walk result plus the separately-gated generic
soundness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`. -/

namespace FX1Poly.Core

open Foundation

/-- **Root-redex dispatch.**  If `RawTerm.hasRootStepSource` recognizes
`source` as a root redex, `source` takes a `Step` — the walk's firing
is sound for the canonical table, and the canonical table IS the kernel
relation. -/
theorem hasRootStepSource_exists_step {scope : Nat} {source : RawTerm scope}
    (rootSource : RawTerm.hasRootStepSource source = true) :
    ∃ target : RawTerm scope, Step source target := by
  match source with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.hasRootStepSource] at rootSource
      match fireEq :
          fireTableRedexOver iotaRuleTable generator payload children with
      | some reduct =>
          exact ⟨reduct, StepOverTable.toStep
            (fireTableRedexOver_sound iotaRuleTable (fun _ isRow => isRow)
              fireEq)⟩
      | none =>
          rw [fireEq] at rootSource
          nomatch rootSource

end FX1Poly.Core
