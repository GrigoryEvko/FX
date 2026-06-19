import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateDenotation
import FX1Poly.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/DataElimArm
    — the data-elimination FT arm (FTGEN-11, first eliminator) + the elim-native data candidate

The eliminator-reducibility for OPEN reducible scrutinees — the genuinely hard Tait keystone — is already
proven in Core, per eliminator, by Acc-induction on the scrutinee's strong normalization
(`boolElimReducibleScrutineeMember` for the two-branch match; `RecursorReducibleScrutineeMember` for
natElim/natRec/listElim; the projection / path-induction variants likewise).  This file integrates it at the
arc.

## The elim-native data candidate

Those eliminator-reducibility theorems are stated over `CanonicalFormsPredicate isValue` (SN ∧ neutral-or-
reaches-a-value) — NOT the `dataTaitCandidate` (SN ∧ every-NF-value-or-neutral) used for the formation-side
validity (FTGEN-2).  The two are genuinely DIFFERENT candidate presentations (neither bridges trivially: a
term reducing to a neutral NF is a `dataTaitCandidate` member but need not be a `CanonicalFormsPredicate`
member).  Both are valid Girard candidates; `CanonicalFormsPredicate` is the one the elim regime consumes.
`canonicalDataCandidate_valid` records its CR validity (given only that the type's values are normal forms —
the neutral half is discharged unconditionally in Core).

## The elim arm

`twoBranchMatchElim` is the FTGEN-11 arm for the two-branch match: a `boolElim` whose scrutinee is a member of
the bool candidate (and whose motive/branches are members) is a member of the result candidate — NEUTRAL
scrutinee via CR3, VALUE scrutinee via the ι rule + head-expansion lifted through the scrutinee congruence.
The `headExpand` hypothesis is the honest Tait head-expansion INTERFACE (it genuinely fails in the neutral
case — `weakHeadExpansionOfMemberNotNeutral` — so it is a contextual parameter, not a global fact), exactly as
in Core.  The recursor / projection / path-induction arms follow identically from their Core reducibility
theorems.

## FTGEN-11 reconciliation — RESOLVED

(a) and (c) are now done in Core: rather than bridging the incomparable `dataTaitCandidate` (formation) and
`CanonicalFormsPredicate` (this file's elim regime), every eliminator is RE-PROVEN over the head-expansion-closed
`dataTaitCandidate` directly — head-expansion through the scrutinee congruence is supplied free by confluence
(`dataTaitCandidate_memberStepStarExpansion`), so the per-type `headExpand` interface DISAPPEARS.  (b) all ten
reducibility-bearing eliminators are wired (`FX1Poly/Core/Eliminators/Core/` `*DataTaitMember` +
`ClosedEliminatorDataTaitMembers`).  The arc-level consequence — data INTRODUCTION and ELIMINATION composing on
the SINGLE formation candidate — lands in `DataElimReconciledArms`.  This file's `canonicalDataCandidate` arms
remain valid (the elim-native regime) but are superseded for generic-FT composition by the `dataTaitCandidate`
arms.

## Zero-axiom verification

`canonicalDataCandidate_valid` is `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`;
`twoBranchMatchElim` is `boolElimReducibleScrutineeMember` — both shipped, audited Core lemmas.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The elim-native data candidate: `CanonicalFormsPredicate isValue` (SN ∧ neutral-or-reaches-a-value) — the
candidate the Core eliminator-reducibility theorems consume. -/
@[reducible] def canonicalDataCandidate {scope : Nat} (isValue : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  CanonicalFormsPredicate isValue

/-- **★ The elim-native data candidate is a valid Girard candidate** — given only that the type's values are
normal forms (the neutral half of the obligation is discharged unconditionally in Core via
`IsNeutral.closedUnderStep`). -/
theorem canonicalDataCandidate_valid {scope : Nat} {isValue : RawTerm scope → Prop}
    (isValueImpliesNormal :
      ∀ {value : RawTerm scope}, isValue value → RawTerm.isStepNormalForm value) :
    CandidateValidity (canonicalDataCandidate isValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isValueImpliesNormal

/-- **★ FTGEN-11 — the two-branch-match elimination arm.**  A `boolElim` over a reducible (bool-candidate)
scrutinee, with strongly-normalizing motive and reducible branches, is a member of the result candidate.  The
genuine eliminator reducibility (Acc-induction: NEUTRAL → CR3, VALUE → ι + head-expansion through the
scrutinee congruence), via the Core `boolElimReducibleScrutineeMember`.  `headExpand` is the honest Tait
head-expansion interface (a contextual parameter — it fails for the neutral case). -/
theorem twoBranchMatchElim {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : canonicalDataCandidate boolIsValue scrutinee)
    (thenBranchMember : canonicalDataCandidate isValue thenBranch)
    (elseBranchMember : canonicalDataCandidate isValue elseBranch) :
    canonicalDataCandidate isValue (boolElimSpine motive scrutinee thenBranch elseBranch) :=
  boolElimReducibleScrutineeMember headExpand motiveStronglyNormalizing
    scrutineeMember thenBranchMember elseBranchMember

end FX1Poly.Typed
