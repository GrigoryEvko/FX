import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedConvArm
import FX1Poly.Core.Eliminators.Core.BoolElimGeneralCandidateMember
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst0ArgumentStar
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Typed.Ledger.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedBoolElimFundamental
    — the bounded DEPENDENT `boolElim` fundamental-theorem engine (DEP-BOOL-BRIDGE, table-independent)

The `boolElim` analogue of `fundamentalPiElimAtBoundedSucc` (the Π-elimination engine in
`DenoteKeyedBoundedPiElimArm`): from the fundamental conclusions of the motive (a type in `context.cons Bool`),
the scrutinee (a `Bool` member), and the two branches (members of the motive instantiated at `true` / `false`),
`boolElim motive scrutinee thenBranch elseBranch` is a `+1`-closing fundamental member of the DEPENDENT result
type `subst0 motive scrutinee`.

Unlike Π-elimination — whose codomain reducibility is bundled INSIDE the Π candidate (`piTypeInversion`) — the
dependent `boolElim` carries the result type in a SEPARATE motive premise: `Bool` itself knows nothing about the
motive.  So this bridge does the dependent plumbing the application rule never needs:

* the result type's bound-reducibility is recovered from the motive's universe membership at the
  scrutinee-EXTENDED environment (`ReducibleEnvAtBounded.cons` + `subst_cons_eq_subst0_lift` + the A2 bridge
  `reducibleTypeAtBoundFromUniverseMemberBounded`), with the `belowBound` gate recovered locally by
  `universeCodeReducibleAtBounded_belowBound`;
* each branch — typed at `subst0 motive true` / `subst0 motive false` — transfers into the result type
  `subst0 motive scrutinee` along the conversion `subst0 motive scrutinee ↞ subst0 motive value`, obtained from
  `scrutinee ↠ value` by the new `StepStar.subst0Argument` argument-congruence + `memberConvAtBounded`.

The Core member `boolElimDependentReducibleMember` (over the head-expansion-closed `dataTaitCandidate`) does the
trichotomy dispatch (value → ι fires, weak-head step → recurse, neutral → stuck member); this file feeds it the
bounded ingredients: the scrutinee `dataTaitCandidate` (via `boolMemberAtBounded_dataTaitCandidate`), the result
candidate's member weak-head expansion (`memberWeakHeadExpansion`) and SN-neutral closure
(`isReducibilityCandidate.memberOfStronglyNormalizingNeutral`), and the two reach-conditioned branch members.

## Scope note (the `+1` index)

`boolElimMemberAtBounded` is stated at a successor closing scope `closingScope + 1` because its result type's
member weak-head expansion (`ReducibleTypeAtBounded.memberWeakHeadExpansion`) and CR1 are stated at `scope + 1`
(the arrow-CR1 var-0 inhabitant).  The `+1`-closing fundamental-theorem motive `FundamentalConclusionAtBounded\
Succ` always closes into `targetScope + 1`, so the FT arm supplies exactly this scope.  The motive's
under-binder strong normalization is the one premise that cannot be read off a sub-conclusion (it would need a
fresh-variable environment at `lift`), so the bridge carries it as `motiveStronglyNormalizing` — exactly as the
`+1` piIntro / genFormationPi arms carry their `codomainSN`; the elim row discharges it from the motive's typing.

## Zero-axiom verification

`boolElimMemberAtBounded` composes the Core `boolElimDependentReducibleMember` with the shipped bounded
`memberWeakHeadExpansion` / `isReducibilityCandidate` / `deterministic` / `boolMemberAtBounded_dataTaitCandidate`.
`fundamentalBoolElimAtBoundedSucc` reshapes via `subst0_subst_commute` / `subst_cons_eq_subst0_lift` /
`subst_boolElimCell` (`rfl`), recovers `belowBound` from `universeCodeReducibleAtBounded_belowBound`, runs the A2
bridge, and converts the branches via `StepStar.subst0Argument` + `Conv.fromStepStar` + `Conv.sym` +
`memberConvAtBounded`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The bounded dependent `boolElim` member arm.**  Given the result type `subst0 motive scrutinee` is
bound-reducible (candidate `resultCandidate`), the scrutinee is a bound-reducible `Bool` member, the motive /
branches are strongly normalizing, and each branch is a result-type member CONDITIONED on the scrutinee
reaching the matching value, the `boolElim` cell is a bound-reducible member of the result type.  Instantiates
the Core `boolElimDependentReducibleMember` at `resultCandidate`: the head-expansion and SN-neutral closures are
the result candidate's `memberWeakHeadExpansion` / `isReducibilityCandidate.memberOfStronglyNormalizingNeutral`,
the scrutinee `dataTaitCandidate` is `boolMemberAtBounded_dataTaitCandidate`, and each conditioned branch member
is transported into `resultCandidate` by `ReducibleTypeAtBounded.deterministic`. -/
theorem boolElimMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)} {scrutinee thenBranch elseBranch : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (resultReducible : ReducibleTypeAtBounded env bound (RawTerm.subst0 motive scrutinee) resultCandidate)
    (scrutineeBoolMember :
      IsReducibleMemberAtBounded env bound (boolTypeCell (scope := closingScope + 1)) scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (thenBranchStronglyNormalizing : IsStronglyNormalizing thenBranch)
    (elseBranchStronglyNormalizing : IsStronglyNormalizing elseBranch)
    (thenBranchMemberIfReachesTrue : StepStar scrutinee boolTrueCell →
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee) thenBranch)
    (elseBranchMemberIfReachesFalse : StepStar scrutinee boolFalseCell →
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee) elseBranch) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (boolElimCell motive scrutinee thenBranch elseBranch) := by
  refine ⟨resultCandidate, resultReducible, ?_⟩
  refine boolElimDependentReducibleMember resultCandidate
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    motiveStronglyNormalizing thenBranchStronglyNormalizing elseBranchStronglyNormalizing
    (boolMemberAtBounded_dataTaitCandidate scrutineeBoolMember)
    (fun reachesTrue => ?_) (fun reachesFalse => ?_)
  · obtain ⟨candidateThen, candidateThenReducible, thenInCandidate⟩ :=
      thenBranchMemberIfReachesTrue reachesTrue
    exact (ReducibleTypeAtBounded.deterministic candidateThenReducible resultReducible thenBranch).mp
      thenInCandidate
  · obtain ⟨candidateElse, candidateElseReducible, elseInCandidate⟩ :=
      elseBranchMemberIfReachesFalse reachesFalse
    exact (ReducibleTypeAtBounded.deterministic candidateElseReducible resultReducible elseBranch).mp
      elseInCandidate

/-- **Generic dependent-eliminator result-type recovery (shared by EVERY dependent data-eliminator bridge).**
From the eliminator's motive conclusion (`motive : universeCodeCell` in `context.cons scrutineeType`) and the
scrutinee's bound-reducible membership at its substituted type, the dependent result type
`subst0 (lift-substituted motive) (substituted scrutinee)` is bound-reducible.  This is the motive-side plumbing
common to bool / nat / option / either / list / idJ: instantiate the motive's universe membership at the
scrutinee-EXTENDED environment, read off `belowBound`, run the A2 bridge
`reducibleTypeAtBoundFromUniverseMemberBounded`, reshape to `subst0` form.  Generic over `scrutineeType` — the
per-eliminator bridge supplies the scrutinee membership.  (Lives here transitionally; relocates to the neutral
generic-elim-bridge file once that lands.) -/
theorem dependentMotiveResultTypeReducibleAtBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {scrutineeType : RawTerm scope} {motive : RawTerm (scope + 1)} {scrutinee : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons scrutineeType) motive (universeCodeCell levelExpr flag))
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnvAtBounded env bound context substitution)
    (scrutineeMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution scrutineeType) (RawTerm.subst substitution scrutinee)) :
    IsReducibleTypeAtBounded env bound
      (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive)
        (RawTerm.subst substitution scrutinee)) := by
  have motiveUniverseMember :
      IsReducibleMemberAtBounded env bound (universeCodeCell levelExpr flag)
        (RawTerm.subst (RawTermSubst.cons (RawTerm.subst substitution scrutinee) substitution) motive) := by
    have member := motiveConclusion
      (RawTermSubst.cons (RawTerm.subst substitution scrutinee) substitution)
      (ReducibleEnvAtBounded.cons envReducible scrutineeMember)
    rw [subst_universeCodeCell] at member
    exact member
  obtain ⟨motiveUniverseCandidate, motiveUniverseReducible, motiveInUniverse⟩ := motiveUniverseMember
  have belowBound : LevelExpr.denote levelExpr env < bound :=
    universeCodeReducibleAtBounded_belowBound motiveUniverseReducible
  have base := reducibleTypeAtBoundFromUniverseMemberBounded env bound
    ⟨motiveUniverseCandidate, motiveUniverseReducible, motiveInUniverse⟩ belowBound
  rw [RawTerm.subst_cons_eq_subst0_lift motive (RawTerm.subst substitution scrutinee) substitution] at base
  exact base

/-- **Generic dependent-eliminator branch transfer (shared by EVERY dependent data-eliminator bridge).**  A
branch typed at the result type instantiated at a CONSTRUCTOR value (`subst0 motiveLifted value`) transfers into
the result type instantiated at the SCRUTINEE (`subst0 motiveLifted scrutineeValue`) along the scrutinee's
reduction `scrutineeValue ↠ value`: the dependent codomain reduces in lockstep
(`StepStar.subst0Argument`), giving a `Conv` the branch member rides via `memberConvAtBounded`.  The per-branch
idiom each dependent eliminator's value handler repeats (bool true/false, nat zero/succ, …); generic over the
lifted motive, the value, and the scrutinee value.  (Lives here transitionally; relocates with the generic
bridge.) -/
theorem branchMemberTransferAlongScrutineeReduction {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {motiveLifted : RawTerm (scope + 1)} {scrutineeValue value branch : RawTerm scope}
    {resultCandidate : RawTerm scope → Prop}
    (branchMember : IsReducibleMemberAtBounded env bound (RawTerm.subst0 motiveLifted value) branch)
    (resultReducible :
      ReducibleTypeAtBounded env bound (RawTerm.subst0 motiveLifted scrutineeValue) resultCandidate)
    (reaches : StepStar scrutineeValue value) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motiveLifted scrutineeValue) branch :=
  memberConvAtBounded env bound branchMember ⟨resultCandidate, resultReducible⟩
    (Conv.sym (Conv.fromStepStar (StepStar.subst0Argument motiveLifted reaches)))

/-- **The `+1`-closing dependent `boolElim` fundamental-theorem arm (table-independent engine).**  From the
motive's universe membership in `context.cons Bool`, the scrutinee's `Bool` membership, the branches'
memberships at `subst0 motive true` / `subst0 motive false`, and the motive's under-binder strong
normalization, `boolElim motive scrutinee thenBranch elseBranch` satisfies the `+1`-closing fundamental
conclusion at the dependent result type `subst0 motive scrutinee`.  The `boolElim` analogue of
`fundamentalPiElimAtBoundedSucc`; the elim-FT row (DEP-BOOL-ROW) wires it from the rule's obligation IHs. -/
theorem fundamentalBoolElimAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons (boolTypeCell (scope := scope))) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee
      (boolTypeCell (scope := scope)))
    (thenBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context thenBranch
      (RawTerm.subst0 motive (boolTrueCell (scope := scope))))
    (elseBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context elseBranch
      (RawTerm.subst0 motive (boolFalseCell (scope := scope))))
    (motiveStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (boolElimCell motive scrutinee thenBranch elseBranch) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  -- The scrutinee is a bound-reducible `Bool` member under the closing substitution (`Bool` is substitution-fixed).
  have scrutineeBoolMember :
      IsReducibleMemberAtBounded env bound (boolTypeCell (scope := _targetScope + 1))
        (RawTerm.subst substitution scrutinee) :=
    scrutineeConclusion substitution envReducible
  -- The dependent result type is bound-reducible: the shared motive-side recovery (generic over the scrutinee
  -- type), fed bool's scrutinee membership.
  have resultTypeReducible :
      IsReducibleTypeAtBounded env bound
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive)
          (RawTerm.subst substitution scrutinee)) :=
    dependentMotiveResultTypeReducibleAtBounded env bound context motiveConclusion substitution
      envReducible scrutineeBoolMember
  obtain ⟨resultCandidate, resultReducible⟩ := resultTypeReducible
  -- The two branches transfer into the result type along the lockstep reduction of the dependent codomain.
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution, subst_boolElimCell]
  refine boolElimMemberAtBounded env bound resultReducible scrutineeBoolMember
    (motiveStronglyNormalizing substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc (thenBranchConclusion substitution envReducible))
    (stronglyNormalizing_of_memberAtBoundedSucc (elseBranchConclusion substitution envReducible))
    (fun reachesTrue => ?_) (fun reachesFalse => ?_)
  · have thenMember := thenBranchConclusion substitution envReducible
    rw [RawTerm.subst0_subst_commute motive boolTrueCell substitution] at thenMember
    exact branchMemberTransferAlongScrutineeReduction env bound thenMember resultReducible reachesTrue
  · have elseMember := elseBranchConclusion substitution envReducible
    rw [RawTerm.subst0_subst_commute motive boolFalseCell substitution] at elseMember
    exact branchMemberTransferAlongScrutineeReduction env bound elseMember resultReducible reachesFalse

end FX1Poly.Typed
