import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.SaturatedOver — zero-axiom gate for the GENERIC per-presentation
saturated 2-cell congruence (WP-AMALG r3, piece 1)

Per-declaration zero-axiom gate for: the law-relation shape (`CellRel`), the generic saturated convertibility
(`SaturatedConvOver`) and its free lift (`SaturatedConvOver.ofConv`), the universal property (`IsSaturatedCongruence`
/ `SaturatedConvOver.recInto`), the decision interface (`DecidableSaturatedConvForRel`), the empty law relation and
the trivial thin instance (`emptyCellRel` / `saturatedLocallyThinDecider` / `involutionSaturatedThinDecider`), and
the INT-SIG-ALIGN #2079 monad exemplar (`MonadLawRel`, the two directions + `monadSaturated_iff_generic`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.CellRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.ofConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.IsSaturatedCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.recInto
#assert_no_axioms FX1Poly.Polygraph.Amalgam.DecidableSaturatedConvForRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.emptyCellRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedLocallyThinDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionSaturatedThinDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.MonadLawRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturated_to_generic
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturatedIsCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.generic_to_monadSaturated
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturated_iff_generic
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSaturatedConvOver

end FX1PolyAudit
