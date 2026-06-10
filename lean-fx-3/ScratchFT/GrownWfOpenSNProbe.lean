import FX1Poly.Typed.ReducibleEnvOfWfContext
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.WfContextDescPi

/-! Probe: STR-8b enabling brick — open SN under the GROWN context well-formedness
(`WfContextDescPi`).  The shipped open SN (`stronglyNormalizingOfWfContextDesc`) is keyed on the
FORMATION wf (`WfContextDesc`), which the pinned-reflection motive does NOT carry (grown wf does
not imply formation wf).  Mirror of `reducibleEnvOfWfContextDesc` where the head binding's grown
typing reads directly off the grown wf's cons component — no formation→grown embedding. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

theorem reducibleEnvOfWfContextDescPi {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContextDescPi context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty =>
      intro _wf
      exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih (WfContextDescPi.tailWellFormed wf)
      obtain ⟨levelExpr, flag, descPiDeriv⟩ := WfContextDescPi.headIsType wf
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

theorem HasTypeDescPi.stronglyNormalizingOfWfContextDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDescPi context)
    (d : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨boundDerivation, budgetDerivation⟩ := BoundExceedsPi.existsBound (env := fun _ => 0) d
  obtain ⟨boundEnvironment, substitution, environmentReducible⟩ :=
    reducibleEnvOfWfContextDescPi (fun _ => 0) context contextWellFormed
  exact d.stronglyNormalizingOfReducibleEnv
    (BoundExceedsPi.monotoneInBound (Nat.le_add_right boundDerivation boundEnvironment) budgetDerivation)
    (fun index => (environmentReducible index).cumulative
      (Nat.le_add_left boundEnvironment boundDerivation))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.reducibleEnvOfWfContextDescPi
#print axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDescPi
