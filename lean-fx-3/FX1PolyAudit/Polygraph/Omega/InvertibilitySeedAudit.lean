import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.InvertibilitySeed

/-! # FX1PolyAudit.Polygraph.Omega.InvertibilitySeedAudit — zero-axiom gate for the ω-carrier invertibility seed
(OMEGA-6 r1, B3).

Per-declaration `#assert_no_axioms` on the ω-cell structure (`omegaCellStructure` and its operator / SN / folk
sets), the hypothesis-free one-way inclusion (`omegaSnInvertible_subset_folkInvertible`), the conditional
well-founded collapse recall (`omegaFixpointsAgree_of_wellFounded`), and the placeholder-gap witnesses (folk
inhabited, SN empty at the object cell, the strict-gap conjunction). -/

namespace FX1PolyAudit

-- InvertibilitySeed.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.OmegaCell
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaCellStructure
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaInvertibilityOperator
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaSnInvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaFolkInvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaSnInvertible_subset_folkInvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaFixpointsAgree_of_wellFounded
#assert_no_axioms FX1Poly.Polygraph.Omega.cell_folkInvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.objectCell_folkInvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.objectCell_not_snInvertible
#assert_no_axioms FX1Poly.Polygraph.Omega.placeholderGap_folkStrictlyBiggerThanSn

end FX1PolyAudit
