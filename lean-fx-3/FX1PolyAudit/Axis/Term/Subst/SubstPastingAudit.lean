import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Subst.SubstPasting

/-! # FX1PolyAudit.Axis.Term.Subst.SubstPastingAudit — zero-axiom gate for the OMEGA-7 r1 identification
(OMEGA-7 r1, B1).

Per-declaration `#assert_no_axioms` on the substitution-monoid anchor (`substCompose_assoc` = kernel
`subst_compose`; the two unit laws), the generic associative-composition shape, the byte-for-byte Steiner
pasting shadow (`steinerPasting_isAssociativeComposition` = `addCoordinates_assoc`), the homomorphism leg
and the pasting associativity carried through `linearize`, the paired anchor `substLemma_is_pastingAssoc`,
and the four non-vacuity witnesses (concrete linearized vcomp / vcomp associativity / real two-substitution
fusion). -/

namespace FX1PolyAudit

-- SubstPasting.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.substCompose_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.substCompose_identity_left
#assert_no_axioms FX1Poly.Polygraph.Omega.substCompose_identity_right
#assert_no_axioms FX1Poly.Polygraph.Omega.IsAssociativeComposition
#assert_no_axioms FX1Poly.Polygraph.Omega.steinerPasting_isAssociativeComposition
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_vcomp_eq_pasting
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_vcomp_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.substLemma_is_pastingAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.substPasting_linearizeVcomp_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.Omega.substPasting_vcompAssoc_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.Omega.substFusion_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.Omega.substFusion_computes

end FX1PolyAudit
