import FX1Poly.Core.RootStepDispatch

/-! # FX1Poly/Core/ExistsStepOfNotNormal
    — the productive mirror of `isStepNormalForm_blocks_step`: a non-normal term genuinely reduces.

`RawTermNF.lean` proves the SOUNDNESS direction of structural normality — a structurally normal term
(`RawTerm.isStepNormalForm`, the boolean root-redex detector AND on a normal child spine) blocks every
`Step` (`isStepNormalForm_blocks_step`).  This file proves the PRODUCTIVE converse: a term that is *not*
structurally normal genuinely takes a `Step`, and the proof EXHIBITS the reduct.

This is the second ingredient (after the root-redex dispatch `hasRootStepSource_exists_step`) of weak
normalization: descending a strongly-normalizing term along `Acc StepSuccessor`, at each non-normal node
this lemma extracts an actual reduct, so the descent terminates at a genuine normal form.  It feeds raw
decidable conversion and the WHNF migration.

## Proof shape (mutual, structural, mirrors `blocks_step`)

`isStepNormalFormBool (mkGen g p children) = (!hasRootStepSource (mkGen g p children)) && areStepNormalFormsBool children`.
A non-normal term therefore fails ONE of the two conjuncts:

* `hasRootStepSource = true` — a root redex fires; dispatch to `hasRootStepSource_exists_step`.
* `areStepNormalFormsBool children = false` — some child is non-normal; recurse into the child spine
  companion and lift the child step through `Step.cong`.

The child-spine companion mirrors `areStepNormalForms_blocks_stepChildren`: `childNil` is vacuously normal
(contradiction), and for `childCons head tail` either the head fails (term IH → `StepChildren.here`) or the
tail fails (spine IH → `StepChildren.there`).  Recursion is structural on the term / child-spine subterms,
so no termination annotation or fuel is needed — exactly as in the `blocks_step` mutual block.

## Zero-axiom verification

`cases` on booleans (`Bool.rec`), `Eq`-rewrites on boolean detector values (never `Iff`-rewrites), `decide`
on closed boolean residues, and dispatch to the per-redex bricks.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

mutual

/-- **Productive normality, term half.**  A term that is not structurally normal takes a `Step`, and the
proof produces the reduct.  The exact converse of `RawTerm.isStepNormalForm_blocks_step`: where soundness
shows a normal term blocks every step, this shows a non-normal term admits one. -/
theorem exists_step_of_not_isStepNormalForm {scope : Nat} {sourceTerm : RawTerm scope}
    (notNormal : ¬ RawTerm.isStepNormalForm sourceTerm) :
    ∃ target : RawTerm scope, Step sourceTerm target := by
  match sourceTerm with
  | .mkGen generator payload children =>
      cases rootValue : RawTerm.hasRootStepSource (.mkGen generator payload children) with
      | true => exact hasRootStepSource_exists_step rootValue
      | false =>
          cases childrenValue : RawTermChildren.areStepNormalFormsBool children with
          | true =>
              apply absurd _ notNormal
              show RawTerm.isStepNormalFormBool (.mkGen generator payload children) = true
              dsimp only [RawTerm.isStepNormalFormBool]
              rw [rootValue, childrenValue]
              decide
          | false =>
              have childrenNotNormal : ¬ RawTermChildren.areStepNormalForms children := by
                show ¬ (RawTermChildren.areStepNormalFormsBool children = true)
                rw [childrenValue]; exact (by decide)
              obtain ⟨targetChildren, childStep⟩ :=
                exists_stepChildren_of_not_areStepNormalForms childrenNotNormal
              exact ⟨_, Step.cong generator payload childStep⟩

/-- **Productive normality, child-spine half.**  A child spine that is not structurally normal takes a
`StepChildren`, with the reduct produced.  The converse of
`RawTermChildren.areStepNormalForms_blocks_stepChildren`. -/
theorem exists_stepChildren_of_not_areStepNormalForms {binderShifts : List Nat} {scope : Nat}
    {sourceChildren : RawTermChildren binderShifts scope}
    (notNormal : ¬ RawTermChildren.areStepNormalForms sourceChildren) :
    ∃ targetChildren : RawTermChildren binderShifts scope,
      StepChildren sourceChildren targetChildren := by
  match binderShifts, sourceChildren with
  | [], .childNil =>
      exact absurd rfl notNormal
  | _headShift :: _restShifts, .childCons childHead childTail =>
      cases headValue : RawTerm.isStepNormalFormBool childHead with
      | false =>
          have headNotNormal : ¬ RawTerm.isStepNormalForm childHead := by
            show ¬ (RawTerm.isStepNormalFormBool childHead = true)
            rw [headValue]; exact (by decide)
          obtain ⟨headTarget, headStep⟩ := exists_step_of_not_isStepNormalForm headNotNormal
          exact ⟨_, StepChildren.here _ headStep⟩
      | true =>
          have tailNotNormal : ¬ RawTermChildren.areStepNormalForms childTail := by
            show ¬ (RawTermChildren.areStepNormalFormsBool childTail = true)
            intro tailNormal
            apply notNormal
            show (RawTerm.isStepNormalFormBool childHead &&
                RawTermChildren.areStepNormalFormsBool childTail) = true
            rw [headValue, tailNormal]
            decide
          obtain ⟨tailTarget, tailStep⟩ :=
            exists_stepChildren_of_not_areStepNormalForms tailNotNormal
          exact ⟨_, StepChildren.there _ tailStep⟩

end

end FX1Poly.Core
