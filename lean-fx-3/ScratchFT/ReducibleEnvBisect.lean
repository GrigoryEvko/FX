import FX1Poly.Typed.BoundedBindingTypeReducible
import FX1Poly.Typed.BoundedNeutralMember
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeDescClosedForms
namespace FX1Poly.Typed.Spike
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar
-- bisectC: through OB-2 (typeReducible), then sorry.
theorem bisectC {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContext context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty => intro _wf; exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih (WfContext.tailWellFormed wf)
      obtain ⟨levelExpr, flag, hasTypeDeriv⟩ := WfContext.headIsType wf
      have descPiDeriv : HasTypeDescPi profile restContext bindingType (universeCodeCell levelExpr flag) :=
        (HasType.toHasTypeDesc hasTypeDeriv).toHasTypeDescPi
      obtain ⟨boundBinding, budget⟩ := BoundExceedsPi.existsBound (env := env) descPiDeriv
      have envRestLifted : ReducibleEnvAtBounded env (max boundRest boundBinding) restContext substRest :=
        fun index => (envRest index).cumulative (Nat.le_max_left boundRest boundBinding)
      have budgetLifted : BoundExceedsPi env (max boundRest boundBinding) descPiDeriv :=
        BoundExceedsPi.monotoneInBound (Nat.le_max_right boundRest boundBinding) budget
      have typeReducible : IsReducibleTypeAtBounded env (max boundRest boundBinding)
          (RawTerm.subst substRest bindingType) :=
        descPiDeriv.subjectReducibleAsTypeUnderEnv budgetLifted envRestLifted
      sorry
end FX1Poly.Typed.Spike
#print axioms FX1Poly.Typed.Spike.bisectC
