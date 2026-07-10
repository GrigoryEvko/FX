import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.StrictAxioms

/-! # FX1PolyAudit.Polygraph.Omega.CongruenceAudit — zero-axiom gate for the OMEGA-1 r1 congruence + strict
axioms.

Per-declaration `#assert_no_axioms` on the dimension-generic saturated congruence, its eliminator, and the
strict-axiom row family.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega` — including `SaturatedConvOver.recInto` (the invariant fold that OMEGA-2's
Steiner soundness instantiates). -/

namespace FX1PolyAudit

-- Congruence.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.CellRelOver
#assert_no_axioms FX1Poly.Polygraph.Omega.SaturatedConvOver
#assert_no_axioms FX1Poly.Polygraph.Omega.IsSaturatedCongruence
#assert_no_axioms FX1Poly.Polygraph.Omega.SaturatedConvOver.recInto
#assert_no_axioms FX1Poly.Polygraph.Omega.DecidableSaturatedConvOver

-- StrictAxioms.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.StrictAxiomRel
#assert_no_axioms FX1Poly.Polygraph.Omega.unionCellRel
#assert_no_axioms FX1Poly.Polygraph.Omega.freeStrictCongruence
#assert_no_axioms FX1Poly.Polygraph.Omega.emptyPresentation

-- StrictAxioms.lean — the derived `*_k` operations (OMEGA-1 r2, B4)
#assert_no_axioms FX1Poly.Polygraph.Omega.godementComp
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerByLowerId
#assert_no_axioms FX1Poly.Polygraph.Omega.godementComp_size
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerByLowerId_congruence

end FX1PolyAudit
