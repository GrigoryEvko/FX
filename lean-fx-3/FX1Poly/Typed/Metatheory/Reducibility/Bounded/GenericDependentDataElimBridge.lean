import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedConvArm
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedCodomainOpenSN
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst0ArgumentStar
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Typed.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/GenericDependentDataElimBridge
    — the eliminator-INDEPENDENT ingredients shared by EVERY dependent data-eliminator bounded FT bridge/row

A dependent data eliminator (`boolElim` / `natElim` / `natRec` / `optionMatch` / `eitherMatch` / `idJ` /
`idStrictRec` / `fst` / `snd` / `listElim`) carries its result type in a SEPARATE motive premise — unlike
Π-elimination, whose codomain reducibility is bundled inside the Π candidate.  The dependent plumbing that
premise forces is the SAME for every such eliminator, and lives here ONCE:

  * `dependentMotiveResultTypeReducibleAtBounded` — recover the dependent result type's bound-reducibility from
    the motive's universe membership at the scrutinee-EXTENDED environment (the A2 bridge, reshaped to `subst0`);
  * `branchMemberTransferAlongScrutineeReduction` — transfer a branch typed at the result type instantiated at a
    constructor value into the result type instantiated at the scrutinee, along the scrutinee's reduction;
  * `dependentMotiveUnderBinderStronglyNormalizing` — reflect the bridge's one premise that is NOT on a
    sub-conclusion (the motive's under-binder strong normalization) from the motive + scrutinee obligation IHs,
    by filling the scrutinee binder with its reducible member.

What is NOT here, and CANNOT be folded into one generic theorem, is the per-eliminator dispatch
(`<elim>MemberAtBounded`) and the branch wiring: the branch ARITY and constructor instantiations are
irreducibly heterogeneous (bool=2 at true/false, nat=2 with recursion, fst/snd=0, idJ=1, option/either=applied),
exactly the heterogeneity `ElimRule.obligations` encodes.  So each eliminator's bridge/row is a THIN consumer of
these three ingredients plus its own dispatch — these three are the factoring ceiling, not a missing
table-keyed super-bridge.

## Zero-axiom verification

Direct compositions of shipped bounded-reducibility lemmas (the A2 bridge
`reducibleTypeAtBoundFromUniverseMemberBounded`, `memberConvAtBounded`, `StepStar.subst0Argument`,
`codomainOpenStronglyNormalizing_ofBoundedFilledMember`, the cons/lift subst commutes).  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTypedFundamentalBounded.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **Generic dependent-eliminator result-type recovery (shared by EVERY dependent data-eliminator bridge).**
From the eliminator's motive conclusion (`motive : universeCodeCell` in `context.cons scrutineeType`) and the
scrutinee's bound-reducible membership at its substituted type, the dependent result type
`subst0 (lift-substituted motive) (substituted scrutinee)` is bound-reducible.  This is the motive-side plumbing
common to bool / nat / option / either / list / idJ: instantiate the motive's universe membership at the
scrutinee-EXTENDED environment, read off `belowBound`, run the A2 bridge
`reducibleTypeAtBoundFromUniverseMemberBounded`, reshape to `subst0` form.  Generic over `scrutineeType` — the
per-eliminator bridge supplies the scrutinee membership. -/
theorem dependentMotiveResultTypeReducibleAtBoundedValue {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {scrutineeType : RawTerm scope} {motive : RawTerm (scope + 1)}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons scrutineeType) motive (universeCodeCell levelExpr flag))
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnvAtBounded env bound context substitution)
    {value : RawTerm (targetScope + 1)}
    (valueMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution scrutineeType) value) :
    IsReducibleTypeAtBounded env bound
      (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive) value) := by
  have motiveUniverseMember :
      IsReducibleMemberAtBounded env bound (universeCodeCell levelExpr flag)
        (RawTerm.subst (RawTermSubst.cons value substitution) motive) := by
    have member := motiveConclusion
      (RawTermSubst.cons value substitution)
      (ReducibleEnvAtBounded.cons envReducible valueMember)
    rw [subst_universeCodeCell] at member
    exact member
  obtain ⟨motiveUniverseCandidate, motiveUniverseReducible, motiveInUniverse⟩ := motiveUniverseMember
  have belowBound : LevelExpr.denote levelExpr env < bound :=
    universeCodeReducibleAtBounded_belowBound motiveUniverseReducible
  have base := reducibleTypeAtBoundFromUniverseMemberBounded env bound
    ⟨motiveUniverseCandidate, motiveUniverseReducible, motiveInUniverse⟩ belowBound
  rw [RawTerm.subst_cons_eq_subst0_lift motive value substitution] at base
  exact base

/-- **Generic dependent-eliminator result-type recovery at the SCRUTINEE (shared by EVERY dependent
data-eliminator bridge).**  The `scrutinee`-instantiated special case of
`dependentMotiveResultTypeReducibleAtBoundedValue` (value := the substituted scrutinee).  This is the form bool's
non-recursive bridge consumes — its single result candidate is the motive at the scrutinee.  The recursive
eliminators (nat / list) consume the value-general form directly (the motive at each reachable constructor
value). -/
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
        (RawTerm.subst substitution scrutinee)) :=
  dependentMotiveResultTypeReducibleAtBoundedValue env bound context motiveConclusion substitution
    envReducible scrutineeMember

/-- **Generic dependent-eliminator branch transfer (shared by EVERY dependent data-eliminator bridge).**  A
branch typed at the result type instantiated at a CONSTRUCTOR value (`subst0 motiveLifted value`) transfers into
the result type instantiated at the SCRUTINEE (`subst0 motiveLifted scrutineeValue`) along the scrutinee's
reduction `scrutineeValue ↠ value`: the dependent codomain reduces in lockstep
(`StepStar.subst0Argument`), giving a `Conv` the branch member rides via `memberConvAtBounded`.  The per-branch
idiom each dependent eliminator's value handler repeats (bool true/false, nat zero/succ, …); generic over the
lifted motive, the value, and the scrutinee value. -/
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

/-- **Generic dependent-eliminator motive under-binder strong normalization (shared by EVERY dependent
data-eliminator ROW).**  The one bridge premise that cannot be read off a sub-conclusion: from the motive
obligation IH (`motive : universeCodeCell` in `context.cons scrutineeType`) and the scrutinee obligation IH,
the lift-substituted motive is strongly normalizing — fill the scrutinee binder with the scrutinee's reducible
member (`ReducibleEnvAtBounded.cons`), reshape the filled membership (`subst_cons_eq_subst0_lift`), and reflect
open-body SN (`codomainOpenStronglyNormalizing_ofBoundedFilledMember`).  Generic over `scrutineeType`; the
pathLam / genFormationPi recipe each elim row repeats. -/
theorem dependentMotiveUnderBinderStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {scrutineeType : RawTerm scope} {motive : RawTerm (scope + 1)} {scrutinee : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons scrutineeType) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee scrutineeType)
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnvAtBounded env bound context substitution) :
    IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  have scrutineeMember := scrutineeConclusion substitution envReducible
  have motiveFilled := motiveConclusion
    (RawTermSubst.cons (RawTerm.subst substitution scrutinee) substitution)
    (ReducibleEnvAtBounded.cons envReducible scrutineeMember)
  rw [RawTerm.subst_cons_eq_subst0_lift motive (RawTerm.subst substitution scrutinee) substitution]
    at motiveFilled
  exact codomainOpenStronglyNormalizing_ofBoundedFilledMember motiveFilled

end FX1Poly.Typed
