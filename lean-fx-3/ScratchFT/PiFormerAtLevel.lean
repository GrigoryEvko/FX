import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! Probe: the single-level piType assembly primitive + the universe-domain instance
    (which becomes TRIVIAL at a single level — universe codes are reducible at every
    level, so no threshold-split is needed, unlike the all-level route). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem piFormerReducibleAtLevel {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainReducible : IsReducibleTypeAtDenote env level domainCode)
    (codomainReducible : ∀ argument : RawTerm scope,
      IsReducibleMemberAtDenote env level domainCode argument →
      IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    domainReducible.reducibleMemberCandidate
    (fun argument argumentInDomain =>
      (codomainReducible argument argumentInDomain).reducibleMemberCandidate)⟩

theorem universeDomainPiFormerReducibleAtLevel {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainReducible : ∀ argument : RawTerm scope,
      IsReducibleMemberAtDenote env level
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) argument →
      IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil))) :=
  piFormerReducibleAtLevel env level
    (universeCode_isReducibleAtDenote env level levelExpr flag) codomainReducible

end FX1Poly.Typed

#print axioms FX1Poly.Typed.piFormerReducibleAtLevel
#print axioms FX1Poly.Typed.universeDomainPiFormerReducibleAtLevel
