import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineCongruence

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.PathLamInnerAffineCongruence — zero-axiom gate

The per-declaration `#assert_no_axioms` gate for the inner-affine invariant and its beta-stability
congruence: the mutual `AllInnerPathLamAffine` invariant + spine version, the downward-closure reification,
the `childClosed` inversion, the `pathLam`-body affine extraction, the `pathApp`-row uniqueness, the guarded
root obligation, and the headline `appScaledDimensionGrade_step_le_ofSitesAffine` (App-scaled beta-stability
under the invariant — the unconditional mechanism isolating the typed residual to one A1-SUBST-OPEN bridge). -/

namespace FX1PolyAudit

-- The structural invariant (mutual term + spine)
#assert_no_axioms FX1Poly.Typed.AllInnerPathLamAffine
#assert_no_axioms FX1Poly.Typed.AllInnerPathLamAffineChildren

-- Downward closure + inversions
#assert_no_axioms FX1Poly.Typed.AllInnerPathLamAffineChildren.toAllSatisfy
#assert_no_axioms FX1Poly.Typed.allInnerPathLamAffine_childClosed
#assert_no_axioms FX1Poly.Typed.allInnerPathLamAffine_pathLamBodyAffine

-- The pathApp-row discriminator + the guarded root obligation
#assert_no_axioms FX1Poly.Typed.pathAppRowIsPathBeta
#assert_no_axioms FX1Poly.Typed.allInnerPathLamAffine_rootGuarded

-- ★ The headline: App-scaled beta-stability under the inner-affine invariant (unconditional)
#assert_no_axioms FX1Poly.Typed.appScaledDimensionGrade_step_le_ofSitesAffine

end FX1PolyAudit
