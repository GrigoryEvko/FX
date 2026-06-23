import FX1Poly.Core.Metatheory.Canonicity.BasedReflCandidate
import FX1Poly.Core.Rewriting.Normalize.Normalize
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward

/-! # FX1Poly/Core/BasedReflEndpointExtraction
    — the DEstructor companion of the two-endpoint based identity candidate (JMAX-3, the genuine-idJ Conv supplier)

`BasedReflCandidate.lean` builds members of the two-endpoint based candidate
`dataTaitCandidate (isReflValueBetween left right)` (`reflDataTaitMemberBetween`); this file destructs them.

Genuine Paulin-Mohring `idJ` subject reduction fires the iota when its witness reaches a `refl` cell: the
generic Core member's value handler hands the bridge a bare `StepStar witness (reflCell reflPoint)` (no
conversions — see `idJDependentReducibleMember.baseCaseMemberIfReachesRefl`).  The dependent output
reclassification needs the endpoint conversions `Conv left reflPoint` and `Conv right reflPoint` (whence
`Conv left right`, the `idJReflMotiveConv` legs).  Those conversions ARE the based candidate's content — but the
content is certified only at REACHABLE NORMAL FORMS, so they have to be extracted by normalizing.

`isReflValueBetween_endpointConvOfReaches` does that extraction: the witness is strongly normalizing (CR1), so
`reflCell reflPoint` (its reduct) normalizes (`RawTerm.normalize`); the normal form is `reflCell reflPointNormal`
for a reduct `reflPointNormal` of `reflPoint` (`stepStar_under_unaryCell` on `Step.from_refl`); the candidate's
value clause classifies that normal form, where the `refl` head excludes the neutral disjunct and supplies the
based point's two endpoint conversions; chaining the (reversed) `reflPoint ↠ reflPointNormal` reduction retargets
them onto `reflPoint`.  This is the reducibility-level analogue of the typing-level `invertAtReflHead` (JMAX-1) —
both supply the genuine-idJ endpoint conversions, one from the based reducibility member, the other from the union
typing derivation.

## Zero-axiom
`RawTerm.normalize` (`Acc.rec`, axiom-free) + its `reducesTo` / `isStepNormalForm` correctness, `descendStepStar`
(SN reduct closure), `stepStar_under_unaryCell`, the `reflCell` structural injection, the unconditional `Conv`
equivalence (`fromStepStar` / `sym` / `trans`), and a `nomatch` on the `refl`-headed neutral.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the
`FX1Poly.Core` namespace sweep in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **`reflCell` is injective in its witness.**  Two reflexivity cells are equal only when their reflected
points are — the structural injection through the `gen_refl` cell's single `childCons` child (the indices
coincide, so the child equality is plain `Eq`). -/
theorem reflCell_witnessInjective {scope : Nat} {witnessLeft witnessRight : RawTerm scope}
    (cellEq : reflCell witnessLeft = reflCell witnessRight) : witnessLeft = witnessRight := by
  rw [reflCell, reflCell] at cellEq
  injection cellEq with _equationOne _equationTwo _equationThree childrenEq
  -- the `childCons` injection substitutes the (free-variable) reflected point and closes the goal
  injection childrenEq with _childScopeEq _childShiftEq _childRestEq _childHeadEq

/-- **★ JMAX-3: the genuine-idJ endpoint-conversion extractor.**  When a two-endpoint based identity member's
witness reaches a `refl reflPoint`, the reflected point is convertible to BOTH endpoints.  The reducibility-side
supplier of the conversions the genuine Paulin-Mohring `idJ` iota consumes (`idJReflMotiveConv` at JMAX-2): from
`Conv left reflPoint` and `Conv right reflPoint` the base case retypes at the dependent output.  The proof
normalizes the (strongly-normalizing) `reflCell reflPoint`, reads the normal form back as a `refl` of a reduct of
`reflPoint`, applies the candidate's value clause (the `refl` head excludes the neutral disjunct), and retargets
the based point's endpoint conversions onto `reflPoint` along the reduction. -/
theorem isReflValueBetween_endpointConvOfReaches {scope : Nat}
    {left right witness reflPoint : RawTerm scope}
    (member : dataTaitCandidate (isReflValueBetween left right) witness)
    (reaches : StepStar witness (reflCell reflPoint)) :
    Conv left reflPoint ∧ Conv right reflPoint := by
  have reflCellStronglyNormalizing : IsStronglyNormalizing (reflCell reflPoint) :=
    IsStronglyNormalizing.descendStepStar member.stronglyNormalizing reaches
  have normalChain : StepStar (reflCell reflPoint)
      (RawTerm.normalize (reflCell reflPoint) reflCellStronglyNormalizing) :=
    RawTerm.normalize_reducesTo (reflCell reflPoint) reflCellStronglyNormalizing
  have normalFormIsNormal : RawTerm.isStepNormalForm
      (RawTerm.normalize (reflCell reflPoint) reflCellStronglyNormalizing) :=
    RawTerm.normalize_isStepNormalForm (reflCell reflPoint) reflCellStronglyNormalizing
  obtain ⟨reflPointNormal, normalFormEq, reflPointChain⟩ :=
    stepStar_under_unaryCell reflCell Step.from_refl normalChain reflPoint rfl
  rw [normalFormEq] at normalChain normalFormIsNormal
  have witnessReachesRefl : StepStar witness (reflCell reflPointNormal) :=
    StepStar.trans_compose reaches normalChain
  rcases member.2 (reflCell reflPointNormal) witnessReachesRefl normalFormIsNormal with
    valueBetween | neutral
  · obtain ⟨reflectedPoint, cellEq, _reflectedNormal, convReflectedLeft, convReflectedRight⟩ := valueBetween
    have pointEq : reflPointNormal = reflectedPoint := reflCell_witnessInjective cellEq
    subst pointEq
    have convReflPointToNormal : Conv reflPoint reflPointNormal := Conv.fromStepStar reflPointChain
    exact ⟨convReflectedLeft.sym.trans convReflPointToNormal.sym,
           convReflectedRight.sym.trans convReflPointToNormal.sym⟩
  · rw [reflCell] at neutral
    nomatch neutral

end FX1Poly.Core
