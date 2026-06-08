import FX1Poly.Typed.DependentPiOverNeutralDomain
import FX1Poly.Core.BetaRedexCompoundPreservation

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Concrete fully-closed DEPENDENT type:  Pi (x : A). P x   (A = var domVar, P = var familyVar, both neutral).
-- The codomain  app (weaken (var P)) (var 0)  genuinely mentions the bound variable, yet every instantiation
-- subst0 cod arg = app (var P) arg  is neutral, so the unconditional neutral-codomain arm fires with NO
-- reducibility hypotheses.
theorem concreteDependentPi_isReducibleType_probe {scope : Nat} (domVar familyVar : Fin scope) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_var domVar .childNil)
          (.childCons
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
                (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
            .childNil))) := by
  have codEq : ∀ arg : RawTerm scope,
      RawTerm.subst0
          (.mkGen .gen_app ()
            (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
              (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
          arg =
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_var familyVar .childNil) (.childCons arg .childNil))) := by
    intro arg
    rw [RawTerm.subst0_app_reduces,
        show RawTerm.subst0 (RawTerm.weaken (.mkGen .gen_var familyVar .childNil)) arg
          = (.mkGen .gen_var familyVar .childNil : RawTerm scope)
          from RawTerm.weaken_subst_singleton _ _,
        RawTerm.subst0_var_zero]
  have neutralInstantiation : ∀ arg : RawTerm scope,
      IsNeutral (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_var familyVar .childNil) (.childCons arg .childNil))) :=
    fun arg => IsNeutral.app (IsNeutral.var familyVar)
  exact IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain
    (fun _reduct => (IsNeutral.var domVar).noWeakHeadStep _)
    (IsNeutral.var domVar).rootGenerator_ne_piTyCode
    (IsNeutral.var domVar).rootGenerator_ne_universeCode
    (fun {arg} _member => by
      rw [codEq arg]
      exact (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        (neutralInstantiation arg).noWeakHeadStep
        (neutralInstantiation arg).rootGenerator_ne_piTyCode
        (neutralInstantiation arg).rootGenerator_ne_universeCode).atAllPositiveLevels)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.concreteDependentPi_isReducibleType_probe
