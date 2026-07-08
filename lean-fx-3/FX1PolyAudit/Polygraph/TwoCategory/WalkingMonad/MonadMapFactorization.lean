import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMapFactorization

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadMapFactorization — zero-axiom gate (the map-factorization engine)

Per-declaration zero-axiom gate for the walking-monad map-factorization engine: the fold lands every free 2-cell
in a genuine Δ₊ morphism (`monadRunMonoCell_mapsInto`), the map length is fold-invariant, the incoming map
post-composes (`monadRunMonoCell_mapFactor`), and — the consequence — `monadMonotoneMapOf` is a functor on
vertical composition (`monadMonotoneMapOf_vcomp`), discharging the two vcomp-congruence cases of `mapEqOfConv`.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_mapsInto_gen
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_mapsInto
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_map_length
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_mapFactor_gen
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_mapFactor
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_vcomp_map
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_vcomp
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_vcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_vcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasMapFactorizationAndVcompCongruence

end FX1PolyAudit
