import FX1Poly.Typed.DescTelescopeInversion

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- Probe: extract BOTH component typings from a 2-child formation telescope (the typing companion to the
shipped twoChildLevels, which gives only the levels). Generator-agnostic — factors the telescope-walk half
of the bespoke inversionPiCodeComponents/inversionSigmaCodeComponents. -/
theorem DescTelescope.twoChildComponents {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0, 1] baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levels flag children) :
    ∃ (child0 : RawTerm baseScope) (child1 : RawTerm (baseScope + 1))
      (domainLevel codomainLevel : LevelExpr),
      levels = [domainLevel, codomainLevel] ∧
      HasTypeDesc profile context child0 (universeCodeCell domainLevel flag) ∧
      HasTypeDesc profile (context.cons child0) child1 (universeCodeCell codomainLevel flag) := by
  cases telescope with
  | cons _context head domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _context2 head2 codomainLevel _restLevels2 _flag2 _rest2 codomainTyped tailTelescope =>
          cases tailTelescope with
          | nil => exact ⟨head, head2, domainLevel, codomainLevel, rfl, domainTyped, codomainTyped⟩

#print axioms FX1Poly.Typed.DescTelescope.twoChildComponents

end FX1Poly.Typed
