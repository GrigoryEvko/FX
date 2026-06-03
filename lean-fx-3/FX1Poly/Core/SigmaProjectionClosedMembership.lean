import FX1Poly.Core.SigmaProjectionCanonicalComputation
import FX1Poly.Core.StrongNormalizationIotaRedexes
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

/-! # FX1Poly/Core/SigmaProjectionClosedMembership
    — a closed `fst` / `snd` on a member pair with a member projected component is a data-candidate member
      (the elimination half of SN-058)

`BoolElimClosedMembership`, `IdEliminatorClosedMembership`, and `MatchClosedMembership` closed the elimination
MEMBERSHIP for the BRANCH eliminators (`boolElim` / `idJ` / `idStrictRec` / `optionMatch` / `eitherMatch`).  This
file is the PROJECTION twin: the elimination membership for the Σ projections `fst` / `snd`, whose ι rules
PROJECT a component out of the scrutinee's pair value (`fst (pair a b) ↝ a`, `snd (pair a b) ↝ b`) — completing
the closed-membership track for ALL non-recursive eliminators.

The projection shape is the cleanest of the eliminators: the ι contractum is the projected COMPONENT (a subterm
of the scrutinee), not an applied branch.  So (a) the cell-SN ingredient is the SHIPPED
`fst/snd_isStronglyNormalizing_of_argument` — needing only the scrutinee's SN, NO respect-hypothesis (the
contractum-SN comes from the component-subterm-SN `firstComponent_isStronglyNormalizing_of_pair`), and (b) the
only obligation is that the projected component reaches a result-candidate value.  Because the closed-layer pair
candidate `isPairValue` records component STRUCTURAL NORMALITY (not result-candidate membership), the membership
of the projected component is supplied as a hypothesis — conditional on the scrutinee actually producing that
pair (`∀ first second, scrutinee ↝* pairCell first second → member (the relevant component)`).  This is exactly
the shape the eventual Tait Σ-elimination supplies (the pair is reducible at Σ, so each projection is reducible
at the corresponding component type); it is `#672`-free at the closed layer.

## Why this assembles

The scrutinee is a canonical Σ member, so it reduces to `pairCell first second` (Σ data canonicity), and
`fst`/`snd` ι-fire to project the component:

1. The cell is SN — `fst/snd_isStronglyNormalizing_of_argument` on the scrutinee's CR1 SN.
2. The cell reduces to the component — `pairCanonicalScrutineeProjectsToComponents` (#690): the scrutinee
   reaches `pairCell first second`, the projection congruence carries that under `fst`/`snd`, and the ι rule
   (`Step.iotaFstPair` / `Step.iotaSndPair`) projects out `first` / `second`.
3. The projected component reaches a value — the `firstComponentMember` / `secondComponentMember` hypothesis
   (applied at the witnessed `scrutinee ↝* pairCell first second`) is a member, so `closedReducesToValue`.

Steps 2 + 3 give `cell ↝* component ↝* value`; with step 1 that is value-reaching weak-head expansion
`CanonicalFormsPredicate.ofStepStarReachingValue` (#735).

## Zero-axiom verification

`obtain` on the projection computation, then `ofStepStarReachingValue` fed the cell-SN and the component
member's `closedReducesToValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **A closed `fst` on a member pair whose first component is a member is a member of the result candidate.**
The Σ-projection analogue of `boolElimClosedIsMember`: the cell is SN (`fst_isStronglyNormalizing_of_argument`
on the scrutinee's CR1 SN), reduces to the first component (`pairCanonicalScrutineeProjectsToComponents`), and
that component — a member of the result candidate by `firstComponentMember` — reaches a value
(`closedReducesToValue`); `ofStepStarReachingValue` lifts membership to the cell.  The first-projection half of
SN-058, closed-layer, `#672`-independent. -/
theorem fstClosedIsMember {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isPairValue scrutinee)
    (firstComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → CanonicalFormsPredicate isValue first) :
    CanonicalFormsPredicate isValue (.mkGen .gen_fst () (.childCons scrutinee .childNil)) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
    fst_isStronglyNormalizing_of_argument scrutineeMember.stronglyNormalizing
  obtain ⟨first, second, scrutineeToPair, fstReducesToFirst, _sndReducesToSecond⟩ :=
    pairCanonicalScrutineeProjectsToComponents scrutineeMember
  exact CanonicalFormsPredicate.ofStepStarReachingValue fstReducesToFirst
    cellStronglyNormalizing (firstComponentMember first second scrutineeToPair).closedReducesToValue

/-- **A closed `snd` on a member pair whose second component is a member is a member of the result candidate.**
Symmetric to `fstClosedIsMember`, projecting the second component via `snd_isStronglyNormalizing_of_argument`
and `Step.iotaSndPair`.  The second-projection half of SN-058, closed-layer, `#672`-independent. -/
theorem sndClosedIsMember {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isPairValue scrutinee)
    (secondComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → CanonicalFormsPredicate isValue second) :
    CanonicalFormsPredicate isValue (.mkGen .gen_snd () (.childCons scrutinee .childNil)) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
    snd_isStronglyNormalizing_of_argument scrutineeMember.stronglyNormalizing
  obtain ⟨first, second, scrutineeToPair, _fstReducesToFirst, sndReducesToSecond⟩ :=
    pairCanonicalScrutineeProjectsToComponents scrutineeMember
  exact CanonicalFormsPredicate.ofStepStarReachingValue sndReducesToSecond
    cellStronglyNormalizing (secondComponentMember first second scrutineeToPair).closedReducesToValue

end FX1Poly.Core
