import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Core.Eliminators.Core.EitherMatchGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Typed.Ledger.Cell.CellConstructors

/-! # FX1Poly/Typed/BoundedEitherMatchFundamental
    — the bounded DEPENDENT `eitherMatch` member engine (DEP-EITHER bridge, table-independent, engine half)

The `eitherMatch` analogue of `boolElimMemberAtBounded` (`BoundedBoolElimFundamental`): given the dependent
result type `subst0 motive scrutinee` is bound-reducible (candidate `resultCandidate`), the scrutinee is a
head-expansion-closed `dataTaitCandidate isEitherValue` member, the motive and both branches are strongly
normalizing, and each branch APPLIED to the matching reachable payload is a result member, the `eitherMatch`
cell is a bound-reducible member of the result type.  Instantiates the Core `eitherMatchDependentReducibleMember`
at `resultCandidate`: the head-expansion and SN-neutral closures are the result candidate's
`memberWeakHeadExpansion` / `isReducibilityCandidate.memberOfStronglyNormalizingNeutral`, and each reach-
conditioned branch member is transported into `resultCandidate` by `ReducibleTypeAtBounded.deterministic`.

## The two-applied-branch shape (vs `boolElim`)

`boolElim`'s branches land DIRECTLY in the result candidate (`thenBranch ∈ subst0 motive true`); `eitherMatch`'s
branches are Π over the carrier type and the ι APPLIES them to the injected payload
(`eitherMatch … inl(v) ↝ app leftBranch v`).  So this engine, like the Core member it wraps, carries:

  * a left- AND right-branch APPLICATION strong-normalization residue
    (`leftBranchApplicationStronglyNormalizing : ∀ value, SN value → SN (app leftBranch value)`).  This is the
    sum twin of the recursive eliminator's `succContractumTerminates` (`BoundedNatElimFundamentalBridge`): it is
    NOT dischargeable at the open/bounded level — `app branch value` SN for ARBITRARY SN `value` would need the
    branch's domain candidate to be the whole SN candidate, which the carrier-typed branch is not — so it is a
    standing residue THREADED to the closed-term consistency leg (where the scrutinee reduces to a value and the
    payload is a genuine carrier member), exactly as `succContractumTerminates` is threaded;
  * a left- AND right-conditioned branch-application member premise
    (`leftBranchMemberIfReachesInl : ∀ payload, scrutinee ↠ inl payload → member (app leftBranch payload)`),
    DISCHARGEABLE at the bounded level by the bridge from the scrutinee type's carrier inversion + the branch's
    Π membership (the `app` row's `applicationMemberAtBounded` at the carrier candidate).

## Scope note (the `+1` index)

Stated at the successor closing scope `closingScope + 1` because the result type's member weak-head expansion
(`ReducibleTypeAtBounded.memberWeakHeadExpansion`) and CR1 are stated at `scope + 1` — exactly as
`boolElimMemberAtBounded`.  The `+1`-closing fundamental-theorem motive always closes into `targetScope + 1`,
so the FT arm supplies this scope.

## Zero-axiom verification

`eitherMatchMemberAtBounded` composes the Core `eitherMatchDependentReducibleMember` with the shipped bounded
`memberWeakHeadExpansion` / `isReducibilityCandidate` / `deterministic`.  No induction, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The bounded dependent `eitherMatch` member arm.**  Given the result type `subst0 motive scrutinee` is
bound-reducible (candidate `resultCandidate`), the scrutinee is a head-expansion-closed
`dataTaitCandidate isEitherValue` member, the motive / branches are strongly normalizing, each branch
application is strongly normalizing (the threaded residue), and each branch APPLIED to the matching reachable
payload is a result member, the `eitherMatch` cell is a bound-reducible member of the result type.  Instantiates
the Core `eitherMatchDependentReducibleMember` at `resultCandidate`: the head-expansion / SN-neutral closures are
the result candidate's `memberWeakHeadExpansion` / `isReducibilityCandidate.memberOfStronglyNormalizingNeutral`,
and each conditioned branch member is transported into `resultCandidate` by `ReducibleTypeAtBounded.deterministic`
(the sum twin of `boolElimMemberAtBounded`'s branch transport, doubled for the two applied branches). -/
theorem eitherMatchMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)}
    {scrutinee leftBranch rightBranch : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (resultReducible : ReducibleTypeAtBounded env bound (RawTerm.subst0 motive scrutinee) resultCandidate)
    (scrutineeMember : dataTaitCandidate isEitherValue scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (leftBranchStronglyNormalizing : IsStronglyNormalizing leftBranch)
    (rightBranchStronglyNormalizing : IsStronglyNormalizing rightBranch)
    (leftBranchApplicationStronglyNormalizing : ∀ value : RawTerm (closingScope + 1),
        IsStronglyNormalizing value → IsStronglyNormalizing (applicationCell leftBranch value))
    (rightBranchApplicationStronglyNormalizing : ∀ value : RawTerm (closingScope + 1),
        IsStronglyNormalizing value → IsStronglyNormalizing (applicationCell rightBranch value))
    (leftBranchMemberIfReachesInl : ∀ payload : RawTerm (closingScope + 1),
        StepStar scrutinee (eitherInlCell payload) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
          (applicationCell leftBranch payload))
    (rightBranchMemberIfReachesInr : ∀ payload : RawTerm (closingScope + 1),
        StepStar scrutinee (eitherInrCell payload) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
          (applicationCell rightBranch payload)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (eitherMatchCell motive leftBranch rightBranch scrutinee) := by
  refine ⟨resultCandidate, resultReducible, ?_⟩
  refine eitherMatchDependentReducibleMember resultCandidate
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    motiveStronglyNormalizing leftBranchStronglyNormalizing rightBranchStronglyNormalizing
    leftBranchApplicationStronglyNormalizing rightBranchApplicationStronglyNormalizing
    scrutineeMember
    (fun payload reachesInl => ?_) (fun payload reachesInr => ?_)
  · obtain ⟨candidateLeft, candidateLeftReducible, applicationInCandidateLeft⟩ :=
      leftBranchMemberIfReachesInl payload reachesInl
    exact (ReducibleTypeAtBounded.deterministic candidateLeftReducible resultReducible
      (applicationCell leftBranch payload)).mp applicationInCandidateLeft
  · obtain ⟨candidateRight, candidateRightReducible, applicationInCandidateRight⟩ :=
      rightBranchMemberIfReachesInr payload reachesInr
    exact (ReducibleTypeAtBounded.deterministic candidateRightReducible resultReducible
      (applicationCell rightBranch payload)).mp applicationInCandidateRight

end FX1Poly.Typed
