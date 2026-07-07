import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedUnionBindingTypeReducible
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedNeutralMember
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Core.Metatheory.Normalization.Core.StronglyNormalizingSubst

/-! # FX1Poly/Typed/NativeUnionOpenStronglyNormalizing
    — ★ the NATIVE-UNION open strong-normalization keystone (Tier B retirement critical path)

The native-union twin of the grown open-SN cone (`Corpus/Smoke/OpenStronglyNormalizing*.lean`,
`Engine/WfContext/ReducibleEnvOfWfContext.lean`).  Every kernel-union-typed subject in a `WfContextUnion`-well-formed
context is strongly normalizing — UNCONDITIONALLY, zero-axiom, over the SHIPPED `HasTypeUnion` engine.  This is what
lets the ~23 open-SN consumers that currently ride the grown `HasTypeDescPi` engine be re-homed onto the native union
engine (that re-homing is a later Tier-C wave; this file only builds the native open SN so they CAN be re-homed).

## The three bricks (mirroring the grown template exactly)

  1. `reducibleEnvOfWfContextUnion` — the reducible closing environment from a union-well-formed context.  Telescope
     induction on `TypingContext` with the "var-0 head" trick (each context variable maps to a neutral `var 0` in
     scope 1), SUM (not `max`) bounds via `Nat.le_add_*`.  The `cons` arm reads the binding's universe typing off the
     wf's own `.2.1` (`UnionClassifierIsType`) and feeds `HasTypeUnion.subjectReducibleAsTypeUnderEnv`.  The `lockCons`
     arm is the ONLY non-verbatim step: `WfContextUnion.lockCons` carries an EQUALITY `dimensionType =
     intervalTypeCell` (the #1886 non-fibrant dimension, no universe typing), so the interval's bound-reducibility is
     built directly from its own step-normal-form via `ReducibleTypeStepBounded.neutral` (candidate
     `IsStronglyNormalizing`), not from a universe derivation.
  2. `HasTypeUnion.stronglyNormalizingOfReducibleEnv` — the CONDITIONAL open SN (three-step Tait chain): discharged
     native FT → scope+1 bounded CR1 → Core SN-reflection through the closing substitution.
  3. `HasTypeUnion.stronglyNormalizingOfWfContextUnion` — the UNCONDITIONAL open SN: `BoundExceedsUnion.existsBound`
     for the derivation + `reducibleEnvOfWfContextUnion` for the env, both lifted to a common SUM bound
     (`monotoneInBound` + member `cumulative`), fed to brick 2.

## Zero-axiom verification

A composition of shipped zero-axiom results.  SUM bounds throughout (`Nat.le_add_right`/`Nat.le_add_left`; `Nat.le_max_*`
would leak `propext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `funext`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The reducible closing environment for a UNION-well-formed context.**  Native twin of
`reducibleEnvOfWfContextDescPi`: telescope induction on `TypingContext`, the var-0 head, SUM bounds.  The `cons`
arm reads the binding's universe typing off `WfContextUnion`'s `.2.1` component and feeds
`HasTypeUnion.subjectReducibleAsTypeUnderEnv`; the `lockCons` arm builds the interval's bound-reducibility
directly from its step-normal-form (`ReducibleTypeStepBounded.neutral`, candidate `IsStronglyNormalizing`), since
the #1886 non-fibrant dimension has no universe typing. -/
theorem reducibleEnvOfWfContextUnion {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContextUnion context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty =>
      intro _wf
      exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih wf.1
      obtain ⟨levelExpr, flag, bindingTyped⟩ := wf.2.1
      obtain ⟨boundBinding, budget⟩ := BoundExceedsUnion.existsBound (env := env) bindingTyped
      have envRestLifted :
          ReducibleEnvAtBounded env (boundRest + boundBinding) restContext substRest :=
        fun index => (envRest index).cumulative (Nat.le_add_right boundRest boundBinding)
      have budgetLifted : BoundExceedsUnion env (boundRest + boundBinding) bindingTyped :=
        BoundExceedsUnion.monotoneInBound (Nat.le_add_left boundBinding boundRest) budget
      have typeReducible : IsReducibleTypeAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType) :=
        HasTypeUnion.subjectReducibleAsTypeUnderEnv bindingTyped budgetLifted envRestLifted
      have headMember : IsReducibleMemberAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType)
          (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) :=
        IsReducibleMemberAtBounded.ofVariable ⟨0, Nat.zero_lt_one⟩ typeReducible
      exact ⟨boundRest + boundBinding,
        RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) substRest,
        ReducibleEnvAtBounded.cons envRestLifted headMember⟩
  | lockCons restContext dimensionType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih wf.1
      have dimensionIsInterval : dimensionType = intervalTypeCell := wf.2
      subst dimensionIsInterval
      have intervalReducibleStronglyNormalizing :
          ReducibleTypeAtBounded env boundRest (RawTerm.subst substRest intervalTypeCell)
            IsStronglyNormalizing :=
        ReducibleTypeStepBounded.neutral
          (fun reduct weakHeadStep =>
            RawTerm.isStepNormalForm_blocks_step
              (show RawTerm.isStepNormalForm (RawTerm.subst substRest intervalTypeCell) from rfl)
              reduct weakHeadStep.toStep)
          (fun rootEquation => nomatch rootEquation)
          (fun rootEquation => nomatch rootEquation)
          (fun rootEquation => nomatch rootEquation)
          rfl
      have intervalTypeReducible : IsReducibleTypeAtBounded env boundRest
          (RawTerm.subst substRest intervalTypeCell) :=
        ⟨IsStronglyNormalizing, intervalReducibleStronglyNormalizing⟩
      have headMember : IsReducibleMemberAtBounded env boundRest
          (RawTerm.subst substRest intervalTypeCell)
          (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) :=
        IsReducibleMemberAtBounded.ofVariable ⟨0, Nat.zero_lt_one⟩ intervalTypeReducible
      exact ⟨boundRest,
        RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) substRest,
        ReducibleEnvAtBounded.lockCons envRest headMember⟩

/-- **Conditional native open SN.**  Any kernel-union derivation, given a `BoundExceedsUnion` budget and a
bound-reducible closing environment for its (arbitrary) context, has a strongly-normalizing subject.  Native twin
of `HasTypeDescPi.stronglyNormalizingOfReducibleEnv`: discharged native FT
(`HasTypeUnion.fundamentalAtBoundedSucc`) → scope+1 bounded CR1 (`stronglyNormalizing_of_memberAtBoundedSucc`) →
Core SN-reflection (`StepStar.stronglyNormalizing_of_subst`). -/
theorem HasTypeUnion.stronglyNormalizingOfReducibleEnv {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (d : HasTypeUnion profile context subject classifier)
    (budget : BoundExceedsUnion env bound d)
    {substitution : RawTermSubst scope (targetScope + 1)}
    (envReducible : ReducibleEnvAtBounded env bound context substitution) :
    StepStar.IsStronglyNormalizing subject :=
  StepStar.stronglyNormalizing_of_subst substitution subject
    (stronglyNormalizing_of_memberAtBoundedSucc
      (HasTypeUnion.fundamentalAtBoundedSucc env bound d budget substitution envReducible))

/-- **★ NATIVE open SN: every kernel-union-typed subject in a union-well-formed context is strongly
normalizing.**  `WfContextUnion Γ → HasTypeUnion Γ subject classifier → IsStronglyNormalizing subject`,
unconditionally and zero-axiom, over the SHIPPED native engine.  Native twin of
`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`: the reducible closing environment from
`reducibleEnvOfWfContextUnion`, the derivation budget from `BoundExceedsUnion.existsBound`, both lifted to a
common SUM bound (`monotoneInBound` + member `cumulative`) and fed to the conditional native open SN, which
reflects SN through the substitution internally.  The keystone unblocking the Tier-C re-homing of the open-SN
consumers off the grown `HasTypeDescPi` engine onto the native union engine. -/
theorem HasTypeUnion.stronglyNormalizingOfWfContextUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextUnion context)
    (d : HasTypeUnion profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨boundDerivation, budgetDerivation⟩ := BoundExceedsUnion.existsBound (env := fun _ => 0) d
  obtain ⟨boundEnvironment, substitution, environmentReducible⟩ :=
    reducibleEnvOfWfContextUnion (fun _ => 0) context contextWellFormed
  exact HasTypeUnion.stronglyNormalizingOfReducibleEnv d
    (BoundExceedsUnion.monotoneInBound (Nat.le_add_right boundDerivation boundEnvironment) budgetDerivation)
    (fun index => (environmentReducible index).cumulative
      (Nat.le_add_left boundEnvironment boundDerivation))

end FX1Poly.Typed
