import FX1Poly.Typed.DenoteKeyedUniformReducible
import FX1Poly.Typed.DenoteKeyedNonDependentArrow

/-! Scratch v2: uniform-motive non-dependent arrow. Let the candidate be INFERRED (the `_` second component of
the existential) from the piType output, exactly as the shipped all-levels version does, rather than providing
it explicitly (which forced a propositional-equality cast → propext). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem UniformlyReducibleAboveDenote.nonDependentArrow {scope : Nat} (env : Nat → Nat)
    {domainCode codomainBase : RawTerm scope}
    (domainUniform : UniformlyReducibleAboveDenote env domainCode)
    (codomainUniform : UniformlyReducibleAboveDenote env codomainBase) :
    UniformlyReducibleAboveDenote env (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) := by
  obtain ⟨domThreshold, domainCandidate, domainReducible⟩ := domainUniform
  obtain ⟨codomainThreshold, codomainCandidate, codomainReducible⟩ := codomainUniform
  refine ⟨domThreshold + codomainThreshold,
    (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))),
    fun level habove => ?_⟩
  refine ReducibleTypeStepDenote.piType (domainCandidate := domainCandidate)
    (fun _argument => codomainCandidate)
    (domainReducible level (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) habove))
    (fun argument _argumentInDomain => ?_)
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainReducible level (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) habove)

theorem UniformlyReducibleAboveDenote.universeDomainNonDependentArrow {scope : Nat} (env : Nat → Nat)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {codomainBase : RawTerm scope}
    (codomainUniform : UniformlyReducibleAboveDenote env codomainBase) :
    UniformlyReducibleAboveDenote env
      (piTyCodeCell (universeCodeCell levelExpr flag) (RawTerm.weaken codomainBase)) :=
  UniformlyReducibleAboveDenote.nonDependentArrow env
    (UniformlyReducibleAboveDenote.ofUniverseCode env levelExpr flag) codomainUniform

end FX1Poly.Typed

#print axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.nonDependentArrow
#print axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.universeDomainNonDependentArrow
