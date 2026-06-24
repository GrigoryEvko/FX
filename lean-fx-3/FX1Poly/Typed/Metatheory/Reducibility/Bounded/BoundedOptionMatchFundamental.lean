import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GenericDependentDataElimBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.Eliminators.Core.OptionMatchGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedOptionMatchFundamental
    — the bounded DEPENDENT `optionMatch` member engine (DEP-OPTION bridge, table-independent, engine half)

The `optionMatch` analogue of `boolElimMemberAtBounded` / `eitherMatchMemberAtBounded`.  Option is the
`bool` / `either` HYBRID: the `none` branch is NULLARY (lands DIRECTLY in the result candidate at
`subst0 motive optionNoneCell`, `bool`-style), and only the `some` branch is Π over the carrier and the ι
APPLIES it to the injected payload (`optionMatch … some(v) ↝ app someBranch v`, `either`-style).  So this engine,
wrapping the Core `optionMatchDependentReducibleMember`, carries exactly the `some`-side residues — and discharges
the `none` side outright.

## The hybrid (vs `boolElim` and `eitherMatch`)

  * the `some` branch carries NO branch-application SN residue.  The earlier conditional form had a
    UNIVERSALLY-FALSE `someBranchApplicationStronglyNormalizing : ∀ value, SN value → SN (app someBranch value)`
    (false by the Ω counterexample — `app f value` is not SN for arbitrary SN `value` and a reducible Π-member `f`).
    FTGEN-13.5 ELIMINATED it: cell SN is now derived self-contained from the member residue below (member implies SN
    via CR1), the engine wrapping the Core `optionMatchDependentReducibleMemberSelfContained`.  The genuine residue is
    the `some`-conditioned branch-application MEMBER premise (`someBranchMemberIfReachesSome`), threaded to the closed
    leg where the closed scrutinee reaches a canonical value;
  * the `none` branch lands DIRECTLY in the result candidate — like `boolElim`'s `then`/`else`, its reach-conditioned
    member is DISCHARGED in the FT arm by `branchMemberTransferAlongScrutineeReduction` (the dependent codomain
    reduces in lockstep with the scrutinee), carrying NO residue.

## Scope note (the `+1` index)

Stated at the successor closing scope `closingScope + 1` because the result type's member weak-head expansion
(`ReducibleTypeAtBounded.memberWeakHeadExpansion`) and CR1 are stated at `scope + 1` — exactly as
`boolElimMemberAtBounded` / `eitherMatchMemberAtBounded`.  The `+1`-closing fundamental-theorem motive always
closes into `targetScope + 1`, so the FT arm supplies this scope.

## Zero-axiom verification

`optionMatchMemberAtBounded` composes the Core `optionMatchDependentReducibleMemberSelfContained` with the shipped
bounded `memberWeakHeadExpansion` / `isReducibilityCandidate` / `deterministic`.  `fundamentalOptionMatchAtBoundedSucc`
reshapes via `subst0_subst_commute` / `subst_optionMatchCell`, recovers result reducibility from the generic
`dependentMotiveResultTypeReducibleAtBounded`, extracts the scrutinee `dataTaitCandidate` via
`optionMemberAtBounded_dataTaitCandidate`, and discharges the `none` branch via
`branchMemberTransferAlongScrutineeReduction`.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The bounded dependent `optionMatch` member arm.**  Given the result type `subst0 motive scrutinee` is
bound-reducible (candidate `resultCandidate`), the scrutinee is a head-expansion-closed
`dataTaitCandidate isOptionValue` member, the motive / branches are strongly normalizing, the some-branch
application is strongly normalizing (the threaded residue), the none branch is a result member WHEN the scrutinee
reaches `none`, and the some branch APPLIED to the matching reachable payload is a result member, the `optionMatch`
cell is a bound-reducible member of the result type.  Instantiates the Core `optionMatchDependentReducibleMember`
at `resultCandidate`: the head-expansion / SN-neutral closures are the result candidate's `memberWeakHeadExpansion`
/ `isReducibilityCandidate.memberOfStronglyNormalizingNeutral`, and each conditioned branch member is transported
into `resultCandidate` by `ReducibleTypeAtBounded.deterministic` (the `none` transport is `boolElim`-style direct,
the `some` transport is `eitherMatch`-style applied). -/
theorem optionMatchMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)}
    {scrutinee noneBranch someBranch : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (resultReducible : ReducibleTypeAtBounded env bound (RawTerm.subst0 motive scrutinee) resultCandidate)
    (scrutineeMember : dataTaitCandidate isOptionValue scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (noneBranchStronglyNormalizing : IsStronglyNormalizing noneBranch)
    (someBranchStronglyNormalizing : IsStronglyNormalizing someBranch)
    (noneBranchMemberIfReachesNone : StepStar scrutinee optionNoneCell →
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee) noneBranch)
    (someBranchMemberIfReachesSome : ∀ payload : RawTerm (closingScope + 1),
        StepStar scrutinee (optionSomeCell payload) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
          (applicationCell someBranch payload)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (optionMatchCell motive noneBranch someBranch scrutinee) := by
  refine ⟨resultCandidate, resultReducible, ?_⟩
  refine optionMatchDependentReducibleMemberSelfContained resultCandidate
    (fun member =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).stronglyNormalizing member)
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    motiveStronglyNormalizing noneBranchStronglyNormalizing someBranchStronglyNormalizing
    scrutineeMember
    (fun reachesNone => ?_) (fun payload reachesSome => ?_)
  · obtain ⟨candidateNone, candidateNoneReducible, noneInCandidate⟩ :=
      noneBranchMemberIfReachesNone reachesNone
    exact (ReducibleTypeAtBounded.deterministic candidateNoneReducible resultReducible noneBranch).mp
      noneInCandidate
  · obtain ⟨candidateSome, candidateSomeReducible, applicationInCandidateSome⟩ :=
      someBranchMemberIfReachesSome payload reachesSome
    exact (ReducibleTypeAtBounded.deterministic candidateSomeReducible resultReducible
      (applicationCell someBranch payload)).mp applicationInCandidateSome

/-- **The `+1`-closing dependent `optionMatch` fundamental-theorem arm (table-independent engine).**  From the
motive's universe membership in `context.cons (optionTypeCell A)`, the scrutinee's `optionTypeCell A` membership,
the none branch's membership at the nullary dependent classifier `subst0 motive optionNoneCell`, the some branch's
membership at the one-binder dependent some branch type `optionMatchDependentSomeBranchType motive A`, and the
motive's under-binder strong normalization, `optionMatch motive noneBranch someBranch scrutinee` satisfies the
`+1`-closing fundamental conclusion at the dependent result type `subst0 motive scrutinee`.  The `optionMatch`
analogue of `fundamentalBoolElimAtBoundedSucc` (none side) crossed with `fundamentalEitherMatchAtBoundedSucc`
(some side).

The `none` branch lands DIRECTLY in the result candidate — its reach-conditioned member is DISCHARGED here by
`branchMemberTransferAlongScrutineeReduction` (the dependent codomain reduces in lockstep with the scrutinee), as
in the `boolElim` arm.  The `some` branch is Π over the carrier and the ι APPLIES it to the injected payload; the
former universally-false some-branch-application SN residue is GONE (FTGEN-13.5 — the engine derives cell SN
self-contained), so this arm now carries only the some reach-conditioned branch-application MEMBER residue
(`someBranchMemberIfReachesSome`), the genuine closed-leg residue.  The elim-FT row wires it from
`optionMatchElimRule`'s obligation IHs. -/
theorem fundamentalOptionMatchAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {typeParamA : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee noneBranch someBranch : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons (optionTypeCell typeParamA)) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee
      (optionTypeCell typeParamA))
    (noneBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context noneBranch
      (RawTerm.subst0 motive optionNoneCell))
    (someBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context someBranch
      (optionMatchDependentSomeBranchType motive typeParamA))
    (motiveStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive))
    (someBranchMemberIfReachesSome : ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution scrutinee) (optionSomeCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive)
              (RawTerm.subst substitution scrutinee))
            (applicationCell (RawTerm.subst substitution someBranch) payload)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (optionMatchCell motive noneBranch someBranch scrutinee) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  have scrutineeOptionMember := scrutineeConclusion substitution envReducible
  obtain ⟨resultCandidate, resultReducible⟩ :=
    dependentMotiveResultTypeReducibleAtBounded env bound context motiveConclusion substitution
      envReducible scrutineeOptionMember
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution, subst_optionMatchCell]
  refine optionMatchMemberAtBounded env bound resultReducible
    (optionMemberAtBounded_dataTaitCandidate scrutineeOptionMember)
    (motiveStronglyNormalizing substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc (noneBranchConclusion substitution envReducible))
    (stronglyNormalizing_of_memberAtBoundedSucc (someBranchConclusion substitution envReducible))
    (fun reachesNone => ?_)
    (someBranchMemberIfReachesSome substitution envReducible)
  -- The `none` branch lands directly in the result candidate: transfer along the scrutinee's reduction to `none`
  -- (the dependent codomain reduces in lockstep), the `boolElim`-arm discharge.
  have noneMember := noneBranchConclusion substitution envReducible
  rw [RawTerm.subst0_subst_commute motive optionNoneCell substitution] at noneMember
  exact branchMemberTransferAlongScrutineeReduction env bound noneMember resultReducible reachesNone

end FX1Poly.Typed
