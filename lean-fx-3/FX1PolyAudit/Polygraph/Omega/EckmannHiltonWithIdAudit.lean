import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.EckmannHiltonWithId

/-! # FX1PolyAudit/Polygraph/Omega/EckmannHiltonWithIdAudit — zero-axiom gate (OMEGA-3 r2, B4).

Per-declaration `#assert_no_axioms` on the conv-form Eckmann-Hilton: the whisker-by-identity-1-cell unit
rows, their single-vector soundness, the interchange collapse and commutativity lemmas (identity-boundary
hypotheses), and the crown / two-generator non-vacuity witnesses. -/

namespace FX1PolyAudit

-- EckmannHiltonWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerUnitRel
#assert_no_axioms FX1Poly.Polygraph.Omega.strictWithWhiskerUnits
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_whiskerUnitRel
#assert_no_axioms FX1Poly.Polygraph.Omega.godementComp_conv_vcomp_ofIdBoundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.vcomp_comm_conv_ofIdBoundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.crownGodement_conv_vcomp
#assert_no_axioms FX1Poly.Polygraph.Omega.ehGenComm

end FX1PolyAudit
