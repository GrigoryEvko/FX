import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! Scratch: denote port of the fuel `IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain`.
A non-dependent arrow `domainCode → codomainBase` (= piTyCodeCell domainCode (weaken codomainBase)) is reducible
at ALL denote levels from domain + codomain all-levels reducibility ALONE — NO domain-candidate uniformity, NO
member-extension, NO piArm. The weaken-cancellation `subst0 (weaken codomainBase) arg = codomainBase` collapses
the piType codomain obligation to the constant codomain fact, so the (possibly composite, possibly drifting)
domain candidate is never consumed per-argument. An unconditional slice of #752 (the non-dependent-codomain case
for arbitrary domains). Denote port is cleaner than fuel — no `cases level` split (denote is level-uniform). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain {scope : Nat} (env : Nat → Nat)
    {domainCode codomainBase : RawTerm scope}
    (domainAllLevels : IsReducibleTypeAtAllDenoteLevels env domainCode)
    (codomainAllLevels : IsReducibleTypeAtAllDenoteLevels env codomainBase) :
    IsReducibleTypeAtAllDenoteLevels env (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) := by
  intro level
  obtain ⟨_domainCandidate, domainReducible⟩ := domainAllLevels level
  obtain ⟨codomainCandidate, codomainReducible⟩ := codomainAllLevels level
  refine ⟨_, ReducibleTypeStepDenote.piType (fun _argument => codomainCandidate) domainReducible
    (fun argument _argumentInDomain => ?_)⟩
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainReducible

theorem IsReducibleTypeAtAllDenoteLevels.universeDomainNonDependentArrow {scope : Nat} (env : Nat → Nat)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {codomainBase : RawTerm scope}
    (codomainAllLevels : IsReducibleTypeAtAllDenoteLevels env codomainBase) :
    IsReducibleTypeAtAllDenoteLevels env
      (piTyCodeCell (universeCodeCell levelExpr flag) (RawTerm.weaken codomainBase)) :=
  IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain env
    (IsReducibleTypeAtAllDenoteLevels.ofUniverseCode env levelExpr flag) codomainAllLevels

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain
#print axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.universeDomainNonDependentArrow
