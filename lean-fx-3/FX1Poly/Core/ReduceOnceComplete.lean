import FX1Poly.Core.ReduceOnce
import FX1Poly.Core.FireRootRedexComplete

/-! # FX1Poly/Core/ReduceOnceComplete
    — completeness of `reduceOnce`: it halts (returns `none`) exactly at structural normal forms.

`ReduceOnce.lean` shipped the one-step reducer plus SOUNDNESS (a firing is a real `Step`).  This file ships
COMPLETENESS: a term `reduceOnce` cannot reduce is structurally normal.  Combined with soundness this pins
`reduceOnce`'s halting set to exactly `isStepNormalForm` — the precise spec the weak-normalization normalizer
FUNCTION needs to terminate at a *genuine* normal form.

* `reduceOnce_complete` / `reduceOnceSpine_complete` (mutual) — `reduceOnce term = none → isStepNormalForm
  term`.  The term case decomposes a `none` result into "no root redex fired" (→ `hasRootStepSource = false`
  via the contrapositive `fireRootRedex_eq_none_imp_hasRootStepSource_false`) and "no child reduced" (→
  `areStepNormalFormsBool children = true` via the spine IH), which recombine into the two conjuncts of
  `isStepNormalFormBool`.
* `reduceOnce_eq_none_iff_isStepNormalForm` — the biconditional; the backward leg is soundness against
  `isStepNormalForm_blocks_step` (a normal term blocks every `Step`, so it cannot reduce).
* `not_isStepNormalForm_imp_reduceOnce_isSome` — the descent guarantee: a non-normal term *does* reduce, so
  the `Acc StepSuccessor` normalizer always has a successor to step to until it reaches a normal form.

## Zero-axiom verification

The mutual completeness mirrors the soundness mutual in the `none` direction: `dsimp only [reduceOnce]` /
`rfl`-unfold for the two-scrutinee spine, `cases` on the sub-results, `nomatch` on impossible `some = none`,
and a `dsimp`/`show` + `rw` + `decide` recombination of the boolean normality conjuncts.  The corollaries are
`cases` + `absurd` against soundness and `isStepNormalForm_blocks_step`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

mutual

/-- **Completeness of `reduceOnce`.**  A term the reducer cannot step is structurally normal. -/
theorem RawTerm.reduceOnce_complete {scope : Nat} {term : RawTerm scope}
    (irreducible : RawTerm.reduceOnce term = none) :
    RawTerm.isStepNormalForm term := by
  match term with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.reduceOnce] at irreducible
      cases hFire : RawTerm.fireRootRedex generator payload children with
      | some rootReduct =>
          rw [hFire] at irreducible
          nomatch irreducible
      | none =>
          rw [hFire] at irreducible
          cases hSpine : RawTermChildren.reduceOnceSpine children with
          | some reducedChildren =>
              rw [hSpine] at irreducible
              dsimp only [Option.map] at irreducible
              nomatch irreducible
          | none =>
              have hRootFalse : RawTerm.hasRootStepSource (.mkGen generator payload children) = false :=
                RawTerm.fireRootRedex_eq_none_imp_hasRootStepSource_false hFire
              have hChildrenBool : RawTermChildren.areStepNormalFormsBool children = true :=
                RawTermChildren.reduceOnceSpine_complete hSpine
              show RawTerm.isStepNormalFormBool (.mkGen generator payload children) = true
              dsimp only [RawTerm.isStepNormalFormBool]
              rw [hRootFalse, hChildrenBool]
              decide

/-- **Completeness of `reduceOnceSpine`.**  A spine the reducer cannot step is structurally normal. -/
theorem RawTermChildren.reduceOnceSpine_complete {binderShifts : List Nat} {scope : Nat}
    {children : RawTermChildren binderShifts scope}
    (irreducible : RawTermChildren.reduceOnceSpine children = none) :
    RawTermChildren.areStepNormalForms children := by
  match binderShifts, children with
  | [], .childNil =>
      rfl
  | _headShift :: _restShifts, .childCons childHead childTail =>
      have unfoldSpine : RawTermChildren.reduceOnceSpine (.childCons childHead childTail) =
          (match RawTerm.reduceOnce childHead with
            | some reducedHead => some (.childCons reducedHead childTail)
            | none =>
                (RawTermChildren.reduceOnceSpine childTail).map
                  (fun reducedTail => .childCons childHead reducedTail)) := rfl
      rw [unfoldSpine] at irreducible
      cases hHead : RawTerm.reduceOnce childHead with
      | some reducedHead =>
          rw [hHead] at irreducible
          nomatch irreducible
      | none =>
          rw [hHead] at irreducible
          cases hTail : RawTermChildren.reduceOnceSpine childTail with
          | some reducedTail =>
              rw [hTail] at irreducible
              dsimp only [Option.map] at irreducible
              nomatch irreducible
          | none =>
              have hHeadBool : RawTerm.isStepNormalFormBool childHead = true :=
                RawTerm.reduceOnce_complete hHead
              have hTailBool : RawTermChildren.areStepNormalFormsBool childTail = true :=
                RawTermChildren.reduceOnceSpine_complete hTail
              show (RawTerm.isStepNormalFormBool childHead &&
                RawTermChildren.areStepNormalFormsBool childTail) = true
              rw [hHeadBool, hTailBool]
              decide

end

/-- **`reduceOnce` halts exactly at normal forms.**  Forward is completeness; backward is soundness against
`isStepNormalForm_blocks_step` (a normal term admits no `Step`, hence no reduct). -/
theorem RawTerm.reduceOnce_eq_none_iff_isStepNormalForm {scope : Nat} {term : RawTerm scope} :
    RawTerm.reduceOnce term = none ↔ RawTerm.isStepNormalForm term := by
  constructor
  · exact RawTerm.reduceOnce_complete
  · intro normalForm
    cases hReduce : RawTerm.reduceOnce term with
    | none => rfl
    | some reduct =>
        exact absurd (RawTerm.reduceOnce_sound hReduce)
          (RawTerm.isStepNormalForm_blocks_step normalForm reduct)

/-- **Descent guarantee.**  A non-normal term genuinely reduces — the successor the `Acc StepSuccessor`
normalizer steps to.  The computable, function-valued counterpart of `exists_step_of_not_isStepNormalForm`. -/
theorem RawTerm.not_isStepNormalForm_imp_reduceOnce_isSome {scope : Nat} {term : RawTerm scope}
    (notNormal : ¬ RawTerm.isStepNormalForm term) :
    (RawTerm.reduceOnce term).isSome = true := by
  cases hReduce : RawTerm.reduceOnce term with
  | some reduct => rfl
  | none =>
      exact absurd (RawTerm.reduceOnce_eq_none_iff_isStepNormalForm.mp hReduce) notNormal

end FX1Poly.Core
