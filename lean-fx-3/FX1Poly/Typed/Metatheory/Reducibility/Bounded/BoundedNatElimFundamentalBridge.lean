import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedNatElimFundamental
import FX1Poly.Typed.Cell.NatElimDependentSuccType

/-! # FX1Poly/Typed/BoundedNatElimFundamentalBridge
    — the `+1`-closing dependent recursive `natElim` / `natRec` fundamental-theorem arms (DEP-NAT-WIRE)

The recursive analogue of `fundamentalBoolElimAtBoundedSucc` (`BoundedBoolElimFundamental`).  Where `boolElim`
lands in a single result candidate, the genuinely dependent recursive `natElim` cannot — the succ-ι reduct recurses
at the PREDECESSOR, whose cell has type `subst0 motive predecessor`, NOT convertible to `subst0 motive scrutinee`.
The shipped engine `natElimMemberAtBounded` (instantiating the value-indexed candidate family) does the recursion;
this bridge threads the closing-substitution `∀` and discharges the engine's seven hypotheses from the four
obligation fundamental conclusions, the two strong-normalization premises (succ branch + the standing
contractum-termination residue), and the shipped de Bruijn identities.

The keystone is the `succBranchSubstClosed` discharge — the two-binder fill.  The succ obligation's fundamental
conclusion, instantiated at the closing substitution extended by the recursive call (`var 0`) and the predecessor
(`var 1`), yields a member of `subst (cons recursiveCall (cons predecessor substitution))
(natElimDependentSuccBranchType motive)`.  The shipped identities collapse this to the engine's conclusion:
`subst_natElimDependentSuccBranchType_general` carries the TYPE to `subst0 (subst (lift substitution) motive)
(natSucc predecessor)`, and `subst_consSingleton_substLiftLift` carries the SUBJECT to the succ-ι reduct
`subst (cons recursiveCall (singleton predecessor)) (subst (lift (lift substitution)) succBranch)`.

## The `iterateLiftRaw` / `lift` reconciliation

`subst_natElimCell` distributes the closing substitution as `iterateLiftRaw substitution 1` / `2` over the motive /
succ branch — definitionally equal to `RawTermSubst.lift substitution` / `lift (lift substitution)` but not
syntactically.  We PIN the engine's implicit motive / succ branch to the `.lift` forms (`refine natElimMemberAt\
Bounded (motive := …) (succBranch := …)`); the goal's `iterateLiftRaw` cell subject unifies up to definitional
equality, and the inner identity rewrites then match the `.lift`-stated lemmas syntactically.

## Scope note

Stated at the bridge's `scope`; the engine fires at `closingScope := targetScope` (the `+1`-closing scope the
fundamental conclusion supplies), so the closing substitution's motive lands at `targetScope + 1 + 1`, the succ
branch at `targetScope + 1 + 2`.  The motive's under-binder strong normalization is recovered from its obligation
via `dependentMotiveUnderBinderStronglyNormalizing`; the succ branch's is threaded as a premise (the table-coupled
elim row discharges it from the succ obligation by a two-binder under-binder reflection), exactly as the bool
bridge threads its motive SN.

## Zero-axiom verification

`natElimMemberAtBounded` / `natRecMemberAtBounded` (the engines) composed with the shipped bridge ingredients
(`dependentMotiveResultTypeReducibleAtBoundedValue`, `dependentMotiveUnderBinderStronglyNormalizing`,
`natMemberAtBounded_ofDataTaitCandidate`, `ReducibleEnvAtBounded.cons`) and the de Bruijn identities
(`subst0_subst_commute`, `subst_natZeroCell`, `subst_cons_eq_subst0_lift`,
`subst_natElimDependentSuccBranchType_general`, `subst_consSingleton_substLiftLift`).  No induction, no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The two-binder succ-branch under-binders strong normalization (the elim ROW's `succBranchStronglyNormalizing`
discharge).**  The recursive twin of `dependentMotiveUnderBinderStronglyNormalizing`: where the motive sits under
ONE binder (the scrutinee value), a recursive eliminator's succ branch sits under TWO (the predecessor and the
recursive-result), and its open strong normalization `subst (lift² substitution) succBranch` is what the bridge's
`succBranchStronglyNormalizing` premise demands.  The discharge needs NO binder-lifted reducible environment and NO
renaming-stability of the bounded relation (both obstructed for the non-Kripke candidate); instead it fills both
binders with CONCRETE reducible members and reflects strong normalization along substitution — a candidate-free
operation:

  * the predecessor binder is filled with the scrutinee's reducible member (`subst substitution scrutinee`);
  * the recursive-result binder is filled with the variable `var 0`, a member of the dependent motive at the
    predecessor by CR3 (`IsReducibilityCandidate.containsVariable` on
    `dependentMotiveResultTypeReducibleAtBoundedValue`);
  * the succ obligation's fundamental conclusion at this doubly-filled environment yields a reducible member, hence
    a strongly-normalizing subject `subst (cons recVar (cons predValue substitution)) succBranch`;
  * `subst_consSingleton_substLiftLift` factors that subject as
    `subst (cons recVar (singleton predValue)) (subst (lift² substitution) succBranch)`, and
    `IsStronglyNormalizing.ofSubst` reflects its SN back to the open `subst (lift² substitution) succBranch`.

Generic over `scrutineeType` / `motive` / `succBranch` / its conclusion classifier — the two-binder recipe every
recursive dependent eliminator's row repeats (nat now; list's cons branch reuses it). -/
theorem dependentSuccBranchUnderTwoBindersStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {scrutineeType : RawTerm scope} {motive : RawTerm (scope + 1)} {scrutinee : RawTerm scope}
    {succBranch succBranchType : RawTerm (scope + 2)}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons scrutineeType) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee scrutineeType)
    (succBranchConclusion : FundamentalConclusionAtBoundedSucc env bound
      ((context.cons scrutineeType).cons motive) succBranch succBranchType)
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnvAtBounded env bound context substitution) :
    IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch) := by
  have predMember := scrutineeConclusion substitution envReducible
  obtain ⟨motiveCandidate, motiveCandReducible⟩ :=
    dependentMotiveResultTypeReducibleAtBoundedValue env bound context motiveConclusion substitution
      envReducible predMember
  have rrMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst (RawTermSubst.cons (RawTerm.subst substitution scrutinee) substitution) motive)
      (RawTerm.mkGen Generator.gen_var ⟨0, Nat.succ_pos targetScope⟩ RawTermChildren.childNil) := by
    refine ⟨motiveCandidate, ?_,
      motiveCandReducible.isReducibilityCandidate.containsVariable ⟨0, Nat.succ_pos targetScope⟩⟩
    rw [RawTerm.subst_cons_eq_subst0_lift motive (RawTerm.subst substitution scrutinee) substitution]
    exact motiveCandReducible
  have filled := succBranchConclusion
    (RawTermSubst.cons (RawTerm.mkGen Generator.gen_var ⟨0, Nat.succ_pos targetScope⟩ RawTermChildren.childNil)
      (RawTermSubst.cons (RawTerm.subst substitution scrutinee) substitution))
    (ReducibleEnvAtBounded.cons (ReducibleEnvAtBounded.cons envReducible predMember) rrMember)
  have subjectStronglyNormalizing := stronglyNormalizing_of_memberAtBoundedSucc filled
  rw [← subst_consSingleton_substLiftLift succBranch
      (RawTerm.mkGen Generator.gen_var ⟨0, Nat.succ_pos targetScope⟩ RawTermChildren.childNil)
      (RawTerm.subst substitution scrutinee) substitution] at subjectStronglyNormalizing
  exact IsStronglyNormalizing.ofSubst subjectStronglyNormalizing

/-- **The `+1`-closing dependent recursive `natElim` fundamental-theorem arm (table-independent engine).**  From
the motive's universe membership (a type under `Nat`), the scrutinee's `Nat` membership, the zero branch's
membership at `subst0 motive natZero`, the succ branch's membership at the dependent two-binder succ type
`natElimDependentSuccBranchType motive`, the succ branch's under-two-binders strong normalization, and the standing
contractum-termination residue, `natElim motive zeroBranch succBranch scrutinee` is a `+1`-closing fundamental
member of the dependent result type `subst0 motive scrutinee`.  The `natElim` twin of
`fundamentalBoolElimAtBoundedSucc`; the elim-FT row wires it from `natElimRule`'s obligation IHs. -/
theorem fundamentalNatElimAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons (natTypeCell (scope := scope))) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee
      (natTypeCell (scope := scope)))
    (zeroBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context zeroBranch
      (RawTerm.subst0 motive (natZeroCell (scope := scope))))
    (succBranchConclusion : FundamentalConclusionAtBoundedSucc env bound
      ((context.cons (natTypeCell (scope := scope))).cons motive) succBranch
      (natElimDependentSuccBranchType motive))
    (succBranchStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
    (succContractumTerminates : ∀ {targetScope : Nat}
        (currentMotive : RawTerm (targetScope + 1 + 1)) (currentSucc : RawTerm (targetScope + 1 + 2))
        (predecessor currentZero : RawTerm (targetScope + 1)), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (natElimCell motive zeroBranch succBranch scrutinee) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution]
  refine natElimMemberAtBounded env bound
    (motive := RawTerm.subst (RawTermSubst.lift substitution) motive)
    (scrutinee := RawTerm.subst substitution scrutinee)
    (zeroBranch := RawTerm.subst substitution zeroBranch)
    (succBranch := RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch)
    (fun {value} structured =>
      dependentMotiveResultTypeReducibleAtBoundedValue env bound context motiveConclusion substitution
        envReducible (natMemberAtBounded_ofDataTaitCandidate structured))
    (scrutineeConclusion substitution envReducible)
    (dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion scrutineeConclusion
      substitution envReducible)
    (succBranchStronglyNormalizing substitution envReducible)
    (@succContractumTerminates _targetScope)
    ?zeroMember
    ?succClosed
  case zeroMember =>
    have zeroMem := zeroBranchConclusion substitution envReducible
    rw [RawTerm.subst0_subst_commute motive natZeroCell substitution, subst_natZeroCell] at zeroMem
    exact zeroMem
  case succClosed =>
    intro predecessor predStructured recCallMember
    have predMember : IsReducibleMemberAtBounded env bound
        (RawTerm.subst substitution (natTypeCell (scope := scope))) predecessor :=
      natMemberAtBounded_ofDataTaitCandidate predStructured
    have recCallRetyped :
        IsReducibleMemberAtBounded env bound (RawTerm.subst (RawTermSubst.cons predecessor substitution) motive)
          (natElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
            (RawTerm.subst substitution zeroBranch)
            (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch)) := by
      rw [RawTerm.subst_cons_eq_subst0_lift motive predecessor substitution]
      exact recCallMember
    have envFilled := ReducibleEnvAtBounded.cons (ReducibleEnvAtBounded.cons envReducible predMember) recCallRetyped
    have filled := succBranchConclusion
      (RawTermSubst.cons (natElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
        (RawTerm.subst substitution zeroBranch)
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
        (RawTermSubst.cons predecessor substitution)) envFilled
    rw [subst_natElimDependentSuccBranchType_general motive
        (natElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
          (RawTerm.subst substitution zeroBranch)
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
        predecessor substitution] at filled
    rw [← subst_consSingleton_substLiftLift succBranch
        (natElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
          (RawTerm.subst substitution zeroBranch)
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
        predecessor substitution] at filled
    exact filled

/-- **The `+1`-closing dependent recursive `natRec` fundamental-theorem arm** — the `gen_natRec` twin of
`fundamentalNatElimAtBoundedSucc`.  Identical wiring of the value-indexed engine `natRecMemberAtBounded`, with the
`natRecCellSpine` / `natRecCell` formers; the succ-branch type `natElimDependentSuccBranchType motive` and both
de Bruijn identities (`subst_natElimDependentSuccBranchType_general` / `subst_consSingleton_substLiftLift`) are
SHARED — the recursor's succ MOTIVE re-basing is identical for `natElim` and `natRec`; only the cell head differs. -/
theorem fundamentalNatRecAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons (natTypeCell (scope := scope))) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee
      (natTypeCell (scope := scope)))
    (zeroBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context zeroBranch
      (RawTerm.subst0 motive (natZeroCell (scope := scope))))
    (succBranchConclusion : FundamentalConclusionAtBoundedSucc env bound
      ((context.cons (natTypeCell (scope := scope))).cons motive) succBranch
      (natElimDependentSuccBranchType motive))
    (succBranchStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
    (succContractumTerminates : ∀ {targetScope : Nat}
        (currentMotive : RawTerm (targetScope + 1 + 1)) (currentSucc : RawTerm (targetScope + 1 + 2))
        (predecessor currentZero : RawTerm (targetScope + 1)), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (natRecCell motive zeroBranch succBranch scrutinee) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution]
  refine natRecMemberAtBounded env bound
    (motive := RawTerm.subst (RawTermSubst.lift substitution) motive)
    (scrutinee := RawTerm.subst substitution scrutinee)
    (zeroBranch := RawTerm.subst substitution zeroBranch)
    (succBranch := RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch)
    (fun {value} structured =>
      dependentMotiveResultTypeReducibleAtBoundedValue env bound context motiveConclusion substitution
        envReducible (natMemberAtBounded_ofDataTaitCandidate structured))
    (scrutineeConclusion substitution envReducible)
    (dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion scrutineeConclusion
      substitution envReducible)
    (succBranchStronglyNormalizing substitution envReducible)
    (@succContractumTerminates _targetScope)
    ?zeroMember
    ?succClosed
  case zeroMember =>
    have zeroMem := zeroBranchConclusion substitution envReducible
    rw [RawTerm.subst0_subst_commute motive natZeroCell substitution, subst_natZeroCell] at zeroMem
    exact zeroMem
  case succClosed =>
    intro predecessor predStructured recCallMember
    have predMember : IsReducibleMemberAtBounded env bound
        (RawTerm.subst substitution (natTypeCell (scope := scope))) predecessor :=
      natMemberAtBounded_ofDataTaitCandidate predStructured
    have recCallRetyped :
        IsReducibleMemberAtBounded env bound (RawTerm.subst (RawTermSubst.cons predecessor substitution) motive)
          (natRecCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
            (RawTerm.subst substitution zeroBranch)
            (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch)) := by
      rw [RawTerm.subst_cons_eq_subst0_lift motive predecessor substitution]
      exact recCallMember
    have envFilled := ReducibleEnvAtBounded.cons (ReducibleEnvAtBounded.cons envReducible predMember) recCallRetyped
    have filled := succBranchConclusion
      (RawTermSubst.cons (natRecCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
        (RawTerm.subst substitution zeroBranch)
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
        (RawTermSubst.cons predecessor substitution)) envFilled
    rw [subst_natElimDependentSuccBranchType_general motive
        (natRecCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
          (RawTerm.subst substitution zeroBranch)
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
        predecessor substitution] at filled
    rw [← subst_consSingleton_substLiftLift succBranch
        (natRecCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) predecessor
          (RawTerm.subst substitution zeroBranch)
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
        predecessor substitution] at filled
    exact filled

end FX1Poly.Typed
