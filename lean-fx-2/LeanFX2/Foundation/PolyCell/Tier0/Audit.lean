import LeanFX2.Foundation.PolyCell.Tier0.FireTriangle
import LeanFX2.Foundation.PolyCell.Tier0.RepresentableMapCategory
import LeanFX2.Foundation.PolyCell.Tier0.CwRExtension
/-!
# PolyCell Tier 0 — Zero-Axiom Audit Gate

Every shipped theorem in Foundation/PolyCell/ MUST appear here with
`#print axioms`. The build target `LeanFX2Audit` elaborates this file;
any axiom leak fails the build.

This is the PolyCell-specific enforcement of the zero-axiom discipline.
-/

-- Tier0/AxisObligation.lean
#print axioms LeanFX2.Foundation.PolyCell.Tier0.MetatheoreticCapabilities.meet_comm
#print axioms LeanFX2.Foundation.PolyCell.Tier0.MetatheoreticCapabilities.meet_idempotent

-- Tier0/FireTriangle.lean
#print axioms LeanFX2.Foundation.PolyCell.Tier0.FireTriangleConfig.allThree_not_admissible
#print axioms LeanFX2.Foundation.PolyCell.Tier0.FireTriangleConfig.twoLegs_admissible_subst_depElim
#print axioms LeanFX2.Foundation.PolyCell.Tier0.FireTriangleConfig.twoLegs_admissible_subst_effects
#print axioms LeanFX2.Foundation.PolyCell.Tier0.FireTriangleConfig.twoLegs_admissible_depElim_effects
#print axioms LeanFX2.Foundation.PolyCell.Tier0.FireTriangleConfig.fromRestriction_admissible
#print axioms LeanFX2.Foundation.PolyCell.Tier0.fxDefaultNavigation_admissible
#print axioms LeanFX2.Foundation.PolyCell.Tier0.fxAxesCombined_admissible

-- Tier0/RepresentableMapCategory.lean
#print axioms LeanFX2.Foundation.PolyCell.Tier0.CwRMorphism.identity
#print axioms LeanFX2.Foundation.PolyCell.Tier0.CwRExtension.compose
#print axioms LeanFX2.Foundation.PolyCell.Tier0.CwRExtension.identity
#print axioms LeanFX2.Foundation.PolyCell.Tier0.CwRExtension.typeFormerCount
