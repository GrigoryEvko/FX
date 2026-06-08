import FX1Poly.Typed.OpenStronglyNormalizing
import FX1Poly.Typed.ReducibleEnvOfWfContext

/-! Probe (NEVER committed): OB-5 — open SN-043, the unconditional wire.
    existsBound(d) + reducibleEnvOfWfContext (OB-3) + sum-bound coordination
    + stronglyNormalizingOfReducibleEnv (reflects SN internally). -/

namespace FX1Poly.Typed.Spike
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

theorem openStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (d : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨boundDerivation, budgetDerivation⟩ := BoundExceedsPi.existsBound (env := fun _ => 0) d
  obtain ⟨boundEnvironment, substitution, environmentReducible⟩ :=
    reducibleEnvOfWfContext (fun _ => 0) context contextWellFormed
  exact d.stronglyNormalizingOfReducibleEnv
    (BoundExceedsPi.monotoneInBound (Nat.le_add_right boundDerivation boundEnvironment) budgetDerivation)
    (fun index => (environmentReducible index).cumulative
      (Nat.le_add_left boundEnvironment boundDerivation))

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.openStronglyNormalizing
