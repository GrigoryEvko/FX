import FX1Poly.Typed.Engine.Union.RawTermMorphismSubjectUsability
import FX1Poly.Typed.Engine.Union.HasTypeUnionWeakening
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution

/-! # FX1PolyAudit.Typed.Engine.Union.RawTermMorphismSubjectUsabilityAxiomWitness
    — INDEPENDENT `#print axioms` witness for the usability transport family

`#assert_no_axioms` (the mirror shards) is a fuel-based elaborator check.  This file is the
INDEPENDENT confirmation by Lean's own kernel-level `#print axioms`, on a fresh import surface:
the five generic theorems, the generic non-variable cell brick they rest on, the renaming side's
variable-image bridge, AND the ten renaming / substitution twins that are now instantiations of
them — so the migration is witnessed axiom-clean from BOTH the generic and the twin side.

Each line must report `does not depend on any axioms`. -/

namespace FX1PolyAudit

-- The generic non-variable cell brick (the collapse's exact boundary).
#print axioms FX1Poly.Typed.RawTerm.applyMorphism_mkGen_of_ne_var

-- The five generic theorems.
#print axioms FX1Poly.Typed.subjectUsabilityPreservedUnderMorphism
#print axioms FX1Poly.Typed.flatFormationObligations_usable_pushMorphism
#print axioms FX1Poly.Typed.termIndexedEndpointObligations_usable_pushMorphism
#print axioms FX1Poly.Typed.cumulativeFormationObligations_usable_pushMorphism
#print axioms FX1Poly.Typed.FormationRule.obligationsUsable_pushMorphism

-- The renaming side's variable-image bridge (the priced asymmetry).
#print axioms FX1Poly.Typed.renameVariableImagesUsable

-- The five RENAMING twins, now instantiations.
#print axioms FX1Poly.Typed.subjectUsabilityPreservedUnderRename
#print axioms FX1Poly.Typed.flatFormationObligations_usable_pushRename
#print axioms FX1Poly.Typed.termIndexedEndpointObligations_usable_pushRename
#print axioms FX1Poly.Typed.cumulativeFormationObligations_usable_pushRename
#print axioms FX1Poly.Typed.FormationRule.obligationsUsable_pushRename

-- The five SUBSTITUTION twins, now instantiations.
#print axioms FX1Poly.Typed.subjectUsabilityPreservedUnderSubst
#print axioms FX1Poly.Typed.flatFormationObligations_usable_pushSubst
#print axioms FX1Poly.Typed.termIndexedEndpointObligations_usable_pushSubst
#print axioms FX1Poly.Typed.cumulativeFormationObligations_usable_pushSubst
#print axioms FX1Poly.Typed.FormationRule.obligationsUsable_pushSubst

end FX1PolyAudit
