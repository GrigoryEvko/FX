import FX1Poly.Typed.ValidTypingTermArms

/-! Scratch: the GENERAL non-universe discriminator the SN-027 assembly needs to discharge the
lookupNotUniverse / resultNotUniverse obligation of the var / piElim refined-motive arms for ANY
non-universe-rooted classifier (term variables, data types, ...), not just Pi codes. Generalises
piTyCodeCell_ne_universeCodeCell from the Pi root to an arbitrary root-generator disequality. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **A non-universe-rooted term is no universe code (the general value-case discriminator).**  If a term's
root generator is not `gen_universeCode`, it differs from every `universeCodeCell levelExpr flag` — the form
the `var` / `piElim` refined-motive arms consume as `lookupNotUniverse` / `resultNotUniverse`.  Generalises
`piTyCodeCell_ne_universeCodeCell` (which fixes the Pi root) to an arbitrary root-disequality, so the
assembly discharges the non-universe obligation for term variables, data classifiers, and any other
non-universe-rooted classifier by one root-generator inspection. -/
theorem ne_universeCodeCell_of_headGenerator {scope : Nat} {typeCode : RawTerm scope}
    (notUniverse : typeCode.headGenerator ≠ Generator.gen_universeCode) :
    ∀ (levelExpr : LevelExpr) (flag : UniverseFlag), typeCode ≠ universeCodeCell levelExpr flag := by
  intro levelExpr flag equ
  have headEq := congrArg RawTerm.headGenerator equ
  rw [headGenerator_universeCodeCell] at headEq
  exact notUniverse headEq

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ne_universeCodeCell_of_headGenerator
