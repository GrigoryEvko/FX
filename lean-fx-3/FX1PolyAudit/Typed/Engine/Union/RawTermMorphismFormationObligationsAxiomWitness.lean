import FX1Poly.Typed.Engine.Union.RawTermMorphismFormationObligations
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations

/-! # FX1PolyAudit.Typed.Engine.Union.RawTermMorphismFormationObligationsAxiomWitness
    — INDEPENDENT `#print axioms` witness for the raw-term-morphism push family

`#assert_no_axioms` (the mirror shards) is a fuel-based elaborator check.  This file is the
INDEPENDENT confirmation by Lean's own kernel-level `#print axioms`, on a fresh import
surface: the four generic push theorems, the morphism action and its closed-cell bricks,
AND the eight renaming / substitution twins that are now instantiations of them — so the
migration is witnessed axiom-clean from BOTH the generic and the twin side.

Each line must report `does not depend on any axioms`. -/

namespace FX1PolyAudit

-- The morphism action and the closed-cell bricks it satisfies.
#print axioms FX1Poly.Typed.RawTerm.applyMorphism
#print axioms FX1Poly.Typed.RawTermChildren.applyMorphism
#print axioms FX1Poly.Typed.rename_eq_applyMorphism
#print axioms FX1Poly.Typed.subst_eq_applyMorphism
#print axioms FX1Poly.Typed.renameChildren_eq_applyMorphism
#print axioms FX1Poly.Typed.substChildren_eq_applyMorphism
#print axioms FX1Poly.Typed.applyMorphism_universeCodeCell
#print axioms FX1Poly.Typed.applyMorphism_emptyTypeCell

-- The four generic push theorems (the single content).
#print axioms FX1Poly.Typed.flatFormationObligations_pushMorphism
#print axioms FX1Poly.Typed.termIndexedEndpointObligations_pushMorphism
#print axioms FX1Poly.Typed.cumulativeFormationObligations_pushMorphism
#print axioms FX1Poly.Typed.FormationRule.obligations_pushMorphism

-- The eight migrated twins: EXACT names, EXACT types, now instantiations.
#print axioms FX1Poly.Typed.flatFormationObligations_pushSubst
#print axioms FX1Poly.Typed.termIndexedEndpointObligations_pushSubst
#print axioms FX1Poly.Typed.cumulativeFormationObligations_pushSubst
#print axioms FX1Poly.Typed.FormationRule.obligations_pushSubst
#print axioms FX1Poly.Typed.flatFormationObligations_pushRename
#print axioms FX1Poly.Typed.termIndexedEndpointObligations_pushRename
#print axioms FX1Poly.Typed.cumulativeFormationObligations_pushRename
#print axioms FX1Poly.Typed.FormationRule.obligations_pushRename

end FX1PolyAudit
