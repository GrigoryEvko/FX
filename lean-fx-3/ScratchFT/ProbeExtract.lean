import FX1Poly.Typed.FormerChildrenReducible
import FX1Poly.Typed.TelescopeReducible

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: does `TelescopeReducible flag 0 2 …` at the concrete 2-cons-nil shape reduce so its
`.1` / `.2` projections typecheck, feeding the `FormerChildrenReducible` bundle? -/
theorem FormerChildrenReducible.ofTelescopeReducible {scope targetScope : Nat}
    (predLevel : Nat) {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr}
    (telescopeReducible :
      TelescopeReducible flag 0 2 substitution (domainLevel :: codomainLevel :: [])
        (.childCons domainCode (.childCons codomainCode .childNil))) :
    FormerChildrenReducible predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel :=
  ⟨telescopeReducible.1 predLevel, telescopeReducible.1 (predLevel + 1),
    fun {_memberLevel} argument argumentMember =>
      (telescopeReducible.2 argument argumentMember).1 predLevel⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.FormerChildrenReducible.ofTelescopeReducible
