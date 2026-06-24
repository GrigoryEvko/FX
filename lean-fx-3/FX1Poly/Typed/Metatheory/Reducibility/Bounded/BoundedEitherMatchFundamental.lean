import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GenericDependentDataElimBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.Eliminators.Core.EitherMatchGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.UnionCellSubstitution

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

  * NO branch-application strong-normalization residue.  The earlier conditional form carried a UNIVERSALLY-FALSE
    `leftBranchApplicationStronglyNormalizing : ∀ value, SN value → SN (app leftBranch value)` (false by the Ω
    counterexample — a reducible Π-member applied to a merely-SN, non-member argument can diverge, which is why
    Tait reducibility, not SN, is the right argument predicate).  FTGEN-13.5 ELIMINATED it: cell SN is now derived
    self-contained from the member-valued reach residue below (member implies SN via CR1), since the only `value`
    the ι ever applies the branch to is the genuine carrier MEMBER the scrutinee reaches — the engine wraps the
    Core `eitherMatchDependentReducibleMemberSelfContained`, which feeds the scrutinee-reducing SN engine;
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

`eitherMatchMemberAtBounded` composes the Core `eitherMatchDependentReducibleMemberSelfContained` with the shipped
bounded `memberWeakHeadExpansion` / `isReducibilityCandidate` / `deterministic`.  No induction, no `funext`.  No `axiom`,
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
  refine eitherMatchDependentReducibleMemberSelfContained resultCandidate
    (fun member =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).stronglyNormalizing member)
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    motiveStronglyNormalizing leftBranchStronglyNormalizing rightBranchStronglyNormalizing
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

/-- **The `+1`-closing dependent `eitherMatch` fundamental-theorem arm (table-independent engine).**  From the
motive's universe membership in `context.cons (eitherTypeCell A B)`, the scrutinee's `eitherTypeCell A B`
membership, the two branches' memberships at the one-binder dependent inl/inr branch types, and the motive's
under-binder strong normalization, `eitherMatch motive leftBranch rightBranch scrutinee` satisfies the `+1`-closing
fundamental conclusion at the dependent result type `subst0 motive scrutinee`.  The `eitherMatch` analogue of
`fundamentalBoolElimAtBoundedSucc`.

Where `boolElim`'s branches land DIRECTLY in the result candidate, `eitherMatch`'s branches are Π over the carrier
and the ι APPLIES them to the injected payload.  The former universally-false branch-application SN residues are
GONE (FTGEN-13.5, the `eitherMatch` twin of the FTGEN-13.1 recursor elimination): the engine derives cell SN
self-contained.  This arm now carries only the two reach-conditioned branch-application MEMBER residues
(`leftBranchMemberIfReachesInl` / `right…`), the genuine closed-leg residues: extracting `payload ∈ ⟦A⟧` for a
non-normal reachable payload needs the substitution-SN content available at the consistency leg where the closed
scrutinee reduces to a canonical value.
This arm does the dependent plumbing the residues do NOT need: result-type reducibility
from the motive's universe membership at the scrutinee-extended environment, the scrutinee's `dataTaitCandidate`
extraction (`eitherMemberAtBounded_dataTaitCandidate`, via the carrier-aware inversion), and the branch strong
normalizations off the branch obligations.  The elim-FT row wires it from `eitherMatchElimRule`'s obligation IHs. -/
theorem fundamentalEitherMatchAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {typeParamA typeParamB : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee leftBranch rightBranch : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons (eitherTypeCell typeParamA typeParamB)) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee
      (eitherTypeCell typeParamA typeParamB))
    (leftBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context leftBranch
      (eitherMatchDependentInlBranchType motive typeParamA))
    (rightBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context rightBranch
      (eitherMatchDependentInrBranchType motive typeParamB))
    (motiveStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive))
    (leftBranchMemberIfReachesInl : ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution scrutinee) (eitherInlCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive)
              (RawTerm.subst substitution scrutinee))
            (applicationCell (RawTerm.subst substitution leftBranch) payload))
    (rightBranchMemberIfReachesInr : ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution scrutinee) (eitherInrCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive)
              (RawTerm.subst substitution scrutinee))
            (applicationCell (RawTerm.subst substitution rightBranch) payload)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (eitherMatchCell motive leftBranch rightBranch scrutinee) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  have scrutineeEitherMember := scrutineeConclusion substitution envReducible
  obtain ⟨resultCandidate, resultReducible⟩ :=
    dependentMotiveResultTypeReducibleAtBounded env bound context motiveConclusion substitution
      envReducible scrutineeEitherMember
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution, subst_eitherMatchCell]
  exact eitherMatchMemberAtBounded env bound resultReducible
    (eitherMemberAtBounded_dataTaitCandidate scrutineeEitherMember)
    (motiveStronglyNormalizing substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc (leftBranchConclusion substitution envReducible))
    (stronglyNormalizing_of_memberAtBoundedSucc (rightBranchConclusion substitution envReducible))
    (leftBranchMemberIfReachesInl substitution envReducible)
    (rightBranchMemberIfReachesInr substitution envReducible)

end FX1Poly.Typed
