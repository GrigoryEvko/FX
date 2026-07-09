import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ConvFullFunctor — zero-axiom gate for the free 2-cell functor's
structural functoriality (WP-AMALG r5, residual P1)

Per-declaration zero-axiom gate for: the cast helper kit (`castBoundaryCongr`, `convFull_of_cellEq`,
`castBoundary_id` / `castBoundary_vcomp` / `castBoundary_trans`, `whiskerLeft_castBoundary` /
`whiskerRight_castBoundary`, `whiskerLeft_pathCongr` / `whiskerRight_pathCongr`), the `mapCellAlong` per-constructor
and double-whisker reduction lemmas, `mapCellAlong_hcomp`, and the three-tier structural functoriality
(`mapTwoCellStep` / `mapTwoCellConv` / `mapTwoCellConvFull`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.TwoCellConvFull.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.convFull_of_cellEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.castBoundary_id
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.castBoundary_vcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.castBoundary_trans
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.whiskerLeft_castBoundary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.whiskerRight_castBoundary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.whiskerLeft_pathCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawTwoCellExpr.whiskerRight_pathCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_id
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_vcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_hcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_whiskerLeft_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_whiskerRight_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_whiskerLeft_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_whiskerRight_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapTwoCellStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapTwoCellConvFull
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasStructuralFunctoriality

end FX1PolyAudit
