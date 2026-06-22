import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/DataTaitEliminatorDispatch
    — the shared reduce-to-normal-form dispatch for EVERY eliminator member in the closed `dataTaitCandidate`

The closed-canonicity layer needs, for every data eliminator (`fst`, `snd`, `optionMatch`, `eitherMatch`,
`idJ`, `idStrictRec`, and the recursors `boolElim`, `natElim`, `natRec`, `listElim`), that an eliminator cell
whose scrutinee is a member of its data candidate lands in the result `dataTaitCandidate isValue`.  Each arm
followed the SAME template by hand: reduce the scrutinee to its strongly-normalizing normal form, split that
normal form value-or-neutral (the candidate's second projection), fire the matching ι in the value case /
keep the cell neutral in the neutral case, and lift both back through the scrutinee congruence by
`dataTaitCandidate_memberStepStarExpansion`.  This factors that template out once.

This is the sibling of `dependentDataEliminatorMemberFromValueDispatch`: that dispatch lands the cell in an
ARBITRARY result candidate (the motive at the scrutinee) and so peels WEAK-HEAD steps under a supplied
`headExpand`; this one's result candidate is FIXED to `dataTaitCandidate isValue`, which is backward-closed
under FULL `StepStar` for free (`dataTaitCandidate_memberStepStarExpansion`) and supplies its own neutral
closure (`memberOfStronglyNormalizingNeutral`), so it reduces the scrutinee straight to a normal form rather
than peeling.  Each eliminator supplies only its genuinely-per-eliminator data — the cell spine, that spine's
SN-from-scrutinee-SN and scrutinee-congruence lemmas, the value handler (fires the ι, transports the
conditioned branch / recursive result), and the neutral-formation constructor.

## Zero-axiom verification

A normal-form existence (`exists_normalForm_of_isStronglyNormalizing`), one value-or-neutral `rcases` on the
candidate's second projection, and two `dataTaitCandidate_memberStepStarExpansion` lifts routed through the
supplied per-eliminator data.  No `induction` on data, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The shared dataTaitCandidate eliminator member via normal-form dispatch.**  Given a scrutinee that is a
member of its data candidate (`scrutineeMember : dataTaitCandidate scrutineeValue scrutinee`) and an eliminator
whose cell is `cellSpine focus` for the focus in scrutinee position, the cell is a member of
`dataTaitCandidate isValue` provided:

* `cellSpineStronglyNormalizing` — the cell is SN whenever the focus is (the motive / branch SNs are closed
  over by the per-eliminator instance);
* `cellSpineScrutineeCongruence` — a focus reduction lifts to a cell reduction (scrutinee congruence);
* `valueHandler` — when the scrutinee's normal form is a value (with its SN and the reaches-witness), the cell
  at that value is a member: fire the ι and transport the conditioned branch / recursive result (the only
  genuinely per-constructor step);
* `neutralHandler` — a neutral normal form makes the cell neutral.

Every `…DataTaitMember` arm instantiates this once. -/
theorem dataTaitEliminatorMemberViaNormalForm {scope : Nat}
    {isValue : RawTerm scope → Prop} {scrutineeValue : RawTerm scope → Prop}
    {cellSpine : RawTerm scope → RawTerm scope} {scrutinee : RawTerm scope}
    (scrutineeMember : dataTaitCandidate scrutineeValue scrutinee)
    (cellSpineStronglyNormalizing : ∀ {focus : RawTerm scope},
        IsStronglyNormalizing focus → IsStronglyNormalizing (cellSpine focus))
    (cellSpineScrutineeCongruence : ∀ {focusBefore focusAfter : RawTerm scope},
        StepStar focusBefore focusAfter → StepStar (cellSpine focusBefore) (cellSpine focusAfter))
    (valueHandler : ∀ {valueNormalForm : RawTerm scope}, scrutineeValue valueNormalForm →
        IsStronglyNormalizing valueNormalForm → StepStar scrutinee valueNormalForm →
        dataTaitCandidate isValue (cellSpine valueNormalForm))
    (neutralHandler : ∀ {neutralNormalForm : RawTerm scope}, IsNeutral neutralNormalForm →
        IsNeutral (cellSpine neutralNormalForm)) :
    dataTaitCandidate isValue (cellSpine scrutinee) := by
  have cellStronglyNormalizing : IsStronglyNormalizing (cellSpine scrutinee) :=
    cellSpineStronglyNormalizing scrutineeMember.stronglyNormalizing
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing scrutineeMember.stronglyNormalizing
  have cellToNormalFormCell : StepStar (cellSpine scrutinee) (cellSpine scrutineeNormalForm) :=
    cellSpineScrutineeCongruence scrutineeToNormalForm
  rcases scrutineeMember.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    scrutineeNormalFormIsValue | scrutineeNormalFormIsNeutral
  · exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      (valueHandler scrutineeNormalFormIsValue
        (isStronglyNormalizing_of_stepStar scrutineeToNormalForm scrutineeMember.stronglyNormalizing)
        scrutineeToNormalForm)
  · exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      (dataTaitCandidate.memberOfStronglyNormalizingNeutral
        (isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing)
        (neutralHandler scrutineeNormalFormIsNeutral))

end FX1Poly.Core
