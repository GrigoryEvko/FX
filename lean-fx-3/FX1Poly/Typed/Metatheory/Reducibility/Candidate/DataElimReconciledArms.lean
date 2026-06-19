import FX1Poly.Core.Eliminators.Core.BoolElimDataTaitMember
import FX1Poly.Core.Eliminators.Core.ClosedEliminatorDataTaitMembers

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/DataElimReconciledArms
    — the data-eliminator FT arms over the FORMATION candidate (FTGEN-11 reconciliation, landed at the arc)

`DataElimArm` / `RecursorElimArms` / `MatchElimArms` / `ProjectionAndPathElimArms` integrate the Core
eliminator-reducibility theorems over `canonicalDataCandidate` (= `CanonicalFormsPredicate`), the candidate the
elim regime was natively stated over — and their docstrings flagged the dataTaitCandidate-vs-
CanonicalFormsPredicate reconciliation as remaining FTGEN-11 work.  That reconciliation is now RESOLVED in Core:
all ten reducibility-bearing eliminators (bool / nat / natRec / list recursors + fst / snd / optionMatch /
eitherMatch / idJ / idStrictRec) have companion theorems over `dataTaitCandidate` — the head-expansion-closed
candidate the fundamental theorem's FORMATION arm assigns (FTGEN-2) and the data INTRODUCTION arm produces
members of (FTGEN-9, `dataTaitCandidate.memberOfValue`).  See `FX1Poly/Core/Eliminators/Core/`:
`BoolElimDataTaitMember`, `NatElimDataTaitMember`, `NatRecDataTaitMember`, `ListElimDataTaitMember`,
`ClosedEliminatorDataTaitMembers`.

## What this file proves: intro and elim compose on ONE candidate

The point of the reconciliation is that the generic fundamental theorem can now compose data INTRODUCTION and
data ELIMINATION on a SINGLE candidate, with no candidate-bridge in between.  This file makes that concrete:
each composition theorem feeds a data-INTRO member (a constructor value, via the formation candidate's
`dataTaitCandidate.memberOfValue`) straight into the corresponding data-ELIM theorem
(`…DataTaitMember`), and both speak `dataElimReducibilityCandidate` (= `dataTaitCandidate`).  Two
representatives across the data-former families — the `bool` match and the `idJ` path-induction — witness that
the composition holds uniformly (the recursors and the other closed eliminators compose identically from their
`…DataTaitMember` companions).

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas (`dataTaitCandidate.memberOfValue`,
`boolElimDataTaitMember`, `idJDataTaitMember`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The data-eliminator FT candidate: `dataTaitCandidate isValue` — the head-expansion-closed candidate the
FORMATION arm assigns and the INTRODUCTION arm produces members of.  The elim arms now agree with it (the
FTGEN-11 reconciliation), so intro and elim compose on this single candidate. -/
@[reducible] def dataElimReducibilityCandidate {scope : Nat} (isValue : RawTerm scope → Prop) :
    RawTerm scope → Prop :=
  dataTaitCandidate isValue

/-- **★ FTGEN-11 — intro+elim compose on one candidate (bool / two-branch match).**  A `boolElim` whose
scrutinee is a bool CONSTRUCTOR VALUE (the data-introduction side: a normal bool value is a member of the
formation candidate by `dataTaitCandidate.memberOfValue`) and whose branches are members is itself a member of
the result candidate — both sides speaking `dataElimReducibilityCandidate`.  The reconciliation payoff: no
candidate-bridge between the formation/introduction candidate and the elimination candidate, because they are
now the SAME candidate. -/
theorem boolReducibilityComposesIntroElim {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (scrutineeIsNormal : RawTerm.isStepNormalForm scrutinee)
    (scrutineeIsBool : boolIsValue scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (thenBranchMember : dataElimReducibilityCandidate isValue thenBranch)
    (elseBranchMember : dataElimReducibilityCandidate isValue elseBranch) :
    dataElimReducibilityCandidate isValue (boolElimSpine motive scrutinee thenBranch elseBranch) :=
  boolElimDataTaitMember motiveStronglyNormalizing
    (dataTaitCandidate.memberOfValue scrutineeIsNormal scrutineeIsBool)
    thenBranchMember elseBranchMember

/-- **★ FTGEN-11 — intro+elim compose on one candidate (idJ / path-induction).**  A closed `idJ` whose witness
is a `refl` CONSTRUCTOR VALUE (the identity-introduction side: a normal refl value is a member of the formation
candidate by `dataTaitCandidate.memberOfValue`) and whose base case is a member is itself a member — both sides
speaking `dataElimReducibilityCandidate`.  The path-induction witness that the reconciliation composition holds
across the data-former families, not just for the two-branch match. -/
theorem idJReducibilityComposesIntroElim {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 2} {baseCase witness : RawTerm 0}
    (witnessIsNormal : RawTerm.isStepNormalForm witness)
    (witnessIsRefl : isReflValue witness)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (baseCaseMember : dataElimReducibilityCandidate isValue baseCase) :
    dataElimReducibilityCandidate isValue
      (.mkGen .gen_idJ ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
  idJDataTaitMember motiveStronglyNormalizing
    (dataTaitCandidate.memberOfValue witnessIsNormal witnessIsRefl)
    baseCaseMember

end FX1Poly.Typed
