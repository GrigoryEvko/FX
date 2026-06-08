import FX1Poly.Typed.BoundedBindingTypeReducible
import FX1Poly.Typed.BoundedNeutralMember
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeDescClosedForms

/-! Probe (NEVER committed): OB-3 — the reducible closing environment for a well-formed context.
    Telescope induction; the "var 0 head" trick collapses σ to var 0 ∈ scope 1, sidestepping renaming
    closure (OB-1 admits any variable; SN reflects through any substitution). Global max-bound via
    cumulative (env lift) + monotoneInBound (budget lift). -/

namespace FX1Poly.Typed.Spike
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

theorem reducibleEnvOfWfContext {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContext context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty =>
      intro _wf
      exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih (WfContext.tailWellFormed wf)
      obtain ⟨levelExpr, flag, hasTypeDeriv⟩ := WfContext.headIsType wf
      have descPiDeriv : HasTypeDescPi profile restContext bindingType (universeCodeCell levelExpr flag) :=
        (HasType.toHasTypeDesc hasTypeDeriv).toHasTypeDescPi
      obtain ⟨boundBinding, budget⟩ := BoundExceedsPi.existsBound (env := env) descPiDeriv
      have envRestLifted :
          ReducibleEnvAtBounded env (boundRest + boundBinding) restContext substRest :=
        fun index => (envRest index).cumulative (Nat.le_add_right boundRest boundBinding)
      have budgetLifted : BoundExceedsPi env (boundRest + boundBinding) descPiDeriv :=
        BoundExceedsPi.monotoneInBound (Nat.le_add_left boundBinding boundRest) budget
      have typeReducible : IsReducibleTypeAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType) :=
        descPiDeriv.subjectReducibleAsTypeUnderEnv budgetLifted envRestLifted
      have headMember : IsReducibleMemberAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType)
          (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) :=
        IsReducibleMemberAtBounded.ofVariable ⟨0, Nat.zero_lt_one⟩ typeReducible
      exact ⟨boundRest + boundBinding,
        RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) substRest,
        ReducibleEnvAtBounded.cons envRestLifted headMember⟩

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.reducibleEnvOfWfContext
