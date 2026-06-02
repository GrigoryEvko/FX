import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Core/NormalFormUnique
    — uniqueness of the normal form: the strongly-normalizing fragment has a *unique* normal form.

`WeakNormalization.lean` gives the EXISTENCE half (`exists_normalForm_of_isStronglyNormalizing`: an SN
term reaches *some* structural normal form).  This file gives the UNIQUENESS half and packages the two.

Uniqueness is immediate from confluence: two normal reducts of one SN term `Join` (by
`confluence_of_localJoin_and_accessible`, keyed on the same `IsStronglyNormalizing` hypothesis), and a
structurally-normal term has no outgoing `Step` (`RawTerm.isStepNormalForm_blocks_step`), so the join's
shared reduct must equal each normal endpoint — exactly the rigidity argument `Conv.eq_of_noStep` already
packages.  Because `Conv` is definitionally `StepStar.Join`, the confluence output feeds `Conv.eq_of_noStep`
with no glue.

Existence + uniqueness together say: every strongly-normalizing raw term has a *unique* structural normal
form.  That is the mathematical content a normalizer FUNCTION (the eval/quote line, #261/#480) realizes
computationally and that decidable conversion on the SN fragment (#267) rests on — convertible SN terms
share one normal form, distinct normal forms witness non-conversion.

## Zero-axiom verification

Confluence (`Acc`-recursion, already zero-axiom), the soundness lemma `isStepNormalForm_blocks_step`
curried to the no-step shape, and `Conv.eq_of_noStep` (a `Join` destructure plus two rigidity legs).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Uniqueness of the normal form.**  Two structurally-normal reducts of one strongly-normalizing term
coincide.  Confluence joins the two reducts; normality makes each rigid (`isStepNormalForm_blocks_step`),
so the shared reduct equals both — i.e. they are equal. -/
theorem normalForm_unique {scope : Nat} {sourceTerm normalForm1 normalForm2 : RawTerm scope}
    (sourceTerminates : StepStar.IsStronglyNormalizing sourceTerm)
    (chain1 : StepStar sourceTerm normalForm1)
    (firstIsNormal : RawTerm.isStepNormalForm normalForm1)
    (chain2 : StepStar sourceTerm normalForm2)
    (secondIsNormal : RawTerm.isStepNormalForm normalForm2) :
    normalForm1 = normalForm2 := by
  have joined : StepStar.Join normalForm1 normalForm2 :=
    StepStar.confluence_of_localJoin_and_accessible sourceTerminates chain1 chain2
  exact Conv.eq_of_noStep
    (fun reduct firstStep => RawTerm.isStepNormalForm_blocks_step firstIsNormal reduct firstStep)
    (fun reduct secondStep => RawTerm.isStepNormalForm_blocks_step secondIsNormal reduct secondStep)
    joined

/-- **Unique normal form on the SN fragment.**  A strongly-normalizing term reaches a structural normal
form (existence, from weak normalization), and that normal form is the only one it reaches (uniqueness).
This is the packaged "the normal form" handle a normalizer function realizes and decidable conversion on
the SN fragment relies on. -/
theorem exists_unique_normalForm_of_isStronglyNormalizing {scope : Nat} {sourceTerm : RawTerm scope}
    (sourceTerminates : StepStar.IsStronglyNormalizing sourceTerm) :
    ∃ normalForm : RawTerm scope,
      (StepStar sourceTerm normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
      ∀ otherForm : RawTerm scope,
        StepStar sourceTerm otherForm → RawTerm.isStepNormalForm otherForm →
        otherForm = normalForm := by
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing sourceTerminates
  refine ⟨normalForm, ⟨reachesNormalForm, normalFormIsNormal⟩, ?_⟩
  intro otherForm reachesOtherForm otherFormIsNormal
  exact normalForm_unique sourceTerminates reachesOtherForm otherFormIsNormal
    reachesNormalForm normalFormIsNormal

end FX1Poly.Core
