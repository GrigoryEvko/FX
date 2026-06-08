import FX1Poly.Typed.DenoteKeyedPiFormationFromExistence
import FX1Poly.Core.RawTermSubstConsCommute

/-! Scratch: the universe-domain Π-formation FT arm UNDER A CLOSING SUBSTITUTION (impredicative twin of
piFormationUnderClosingSubstitution). The domain is a closed universe code, so `subst σ` leaves it fixed; the
codomain bridges via subst_cons_eq_subst0_lift into universeDomainPi_reducibleFromCodomainExistence. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Probe (a): subst distributes over Π(universeCode)C, leaving the closed domain fixed.
example {scope targetScope : Nat} (σ : RawTermSubst scope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (codomainCode : RawTerm (scope + 1)) :
    RawTerm.subst σ
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil)))
      = .mkGen .gen_piTyCode ()
          (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
            (.childCons (RawTerm.subst (RawTermSubst.lift σ) codomainCode) .childNil)) := by
  rfl

-- Probe (b): the full universe-domain binder arm under substitution.
theorem universeDomainPiFormationUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    {substitution : RawTermSubst scope targetScope}
    (codomainReducible : ∀ argument : RawTerm targetScope,
      (IsStronglyNormalizing argument ∧
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
      IsReducibleTypeAtAllDenoteLevels env
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    IsReducibleTypeAtAllDenoteLevels env
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode ()
          (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
            (.childCons codomainCode .childNil)))) := by
  show IsReducibleTypeAtAllDenoteLevels env
    (.mkGen .gen_piTyCode ()
      (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
  refine universeDomainPi_reducibleFromCodomainExistence env levelExpr flag
    (fun argument argumentInUniverse => ?_)
  rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
  exact codomainReducible argument argumentInUniverse

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeDomainPiFormationUnderClosingSubstitution
