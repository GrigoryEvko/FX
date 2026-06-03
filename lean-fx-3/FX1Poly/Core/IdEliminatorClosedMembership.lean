import FX1Poly.Core.IdentityEliminatorCanonicalComputation
import FX1Poly.Core.IdentityEliminatorStrongNormalization
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

/-! # FX1Poly/Core/IdEliminatorClosedMembership
    — a closed `idJ` / `idStrictRec` with a member base case is a data-candidate member (the elimination half of
      SN-068 / SN-069)

`BoolElimClosedMembership.lean` closed the elimination MEMBERSHIP for `bool`: a closed `boolElim` on a canonical
scrutinee with member branches is itself a member of the result candidate.  This file is the identity-eliminator
twin — the elimination membership for the path-induction recursor `idJ` and the strict identity recursor
`idStrictRec`, the last NON-GROWING (passive-base) eliminators.

The identity track has, mirroring `bool`:
* INTRODUCTION membership — `refl` is a member (`ReflCanonicalFormsCandidate`);
* WITNESS canonicity — a closed identity member reduces to a `refl` constructor (`reflClosedReducesToValue`);
* ELIMINATION computation — a closed `idJ` / `idStrictRec` on a canonical `refl` witness reduces to its base
  case (`idJCanonicalWitnessReducesToBase` / `idStrictRecCanonicalWitnessReducesToBase`, #691).

This file closes the ELIMINATION MEMBERSHIP: a closed `idJ` / `idStrictRec` whose witness is a canonical identity
member and whose base case is a member of a result candidate is ITSELF a member of that result candidate — the
recursor lands in the candidate, not merely normalizes.

## Why this assembles exactly like `boolElim` (and is `#672`-independent)

`idJ` / `idStrictRec` are the path-induction analogues of the simplest eliminator shape: their single ι rule
`idJ base (refl w) ↝ base` (resp. `idStrictRec base (refl w) ↝ base`) selects the base case DIRECTLY from the
witness position — no payload application, no recursive sub-term reappearing (unlike `optionMatch` / `eitherMatch`,
whose ι applies a branch to a wrapped payload, and unlike the growing recursors `natElim` / `listElim`).  So the
base case IS the contractum, and the three shipped pieces compose verbatim with the `bool` proof:

1. The cell is strongly normalizing — `idJ_isStronglyNormalizing_of_strongly_normalizing_base` (the SN-base
   strengthening, base×witness two-dimensional accessibility induction) fed the members' CR1 SN witnesses
   (`.stronglyNormalizing`).  The SN-base — not SN-NORMAL-base — strengthening is what lets the base be a mere
   member (SN, possibly reducible) rather than a normal form.
2. The cell reduces to its base case — `idJCanonicalWitnessReducesToBase` on the canonical `refl` witness (the
   witness reaches `refl`, the ι rule fires).
3. The base case, being a CLOSED member, reduces to a value (`closedReducesToValue` — a closed member is
   non-neutral by `IsNeutral.noClosed`, so its disjunct collapses to reaches-a-value).

Steps 2 + 3 give `idJ ↝* base ↝* value`; with step 1 that is exactly the value-reaching weak-head expansion
`CanonicalFormsPredicate.ofStepStarReachingValue` (#735).  No fundamental theorem, no member extension, no
`#672` — pure closed-canonicity assembly, the regime where data weak-head expansion holds unconditionally.

## Zero-axiom verification

Each is the SN-base cell-SN lemma plus `ofStepStarReachingValue` fed the canonical-witness computation chain and
`closedReducesToValue` on the base case.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **A closed `idJ` with a member base case is a member of the result candidate.**  Given a canonical identity
witness (a member of the identity candidate) and a base case that is a member of a result candidate `isValue`,
the closed `idJ` cell is itself a member.  The cell is SN
(`idJ_isStronglyNormalizing_of_strongly_normalizing_base` on the members' SN), it reduces to the base case
(`idJCanonicalWitnessReducesToBase`), and that base case — closed and a member — reaches a value
(`closedReducesToValue`); value-reaching weak-head expansion (`ofStepStarReachingValue`) lifts the membership back
to the cell.  The elimination half of SN-068, closed-layer, `#672`-independent. -/
theorem idJClosedIsMember {isValue : RawTerm 0 → Prop}
    {baseCase witness : RawTerm 0}
    (witnessMember : CanonicalFormsPredicate isReflValue witness)
    (baseCaseMember : CanonicalFormsPredicate isValue baseCase) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))) := by
  have idJStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))) :=
    idJ_isStronglyNormalizing_of_strongly_normalizing_base
      baseCaseMember.stronglyNormalizing witnessMember.stronglyNormalizing
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (idJCanonicalWitnessReducesToBase witnessMember)
    idJStronglyNormalizing baseCaseMember.closedReducesToValue

/-- **A closed `idStrictRec` with a member base case is a member of the result candidate.**  Symmetric to
`idJClosedIsMember`: the strict identity eliminator has the same `(base, witness)` spine and the same single ι
rule (`idStrictRec base (refl w) ↝ base`), so the cell-SN (`idStrictRec_isStronglyNormalizing_of_strongly_
normalizing_base`), the witness computation (`idStrictRecCanonicalWitnessReducesToBase`), and the base case's
reaches-a-value (`closedReducesToValue`) compose by `ofStepStarReachingValue` into membership.  The elimination
half of SN-069, closed-layer, `#672`-independent. -/
theorem idStrictRecClosedIsMember {isValue : RawTerm 0 → Prop}
    {baseCase witness : RawTerm 0}
    (witnessMember : CanonicalFormsPredicate isReflValue witness)
    (baseCaseMember : CanonicalFormsPredicate isValue baseCase) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))) := by
  have idStrictRecStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))) :=
    idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base
      baseCaseMember.stronglyNormalizing witnessMember.stronglyNormalizing
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (idStrictRecCanonicalWitnessReducesToBase witnessMember)
    idStrictRecStronglyNormalizing baseCaseMember.closedReducesToValue

end FX1Poly.Core
