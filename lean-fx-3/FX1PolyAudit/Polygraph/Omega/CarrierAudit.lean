import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Carrier
import FX1Poly.Polygraph.Omega.NonVacuity

/-! # FX1PolyAudit.Polygraph.Omega.CarrierAudit — zero-axiom gate for the OMEGA-1 r1 carrier + non-vacuity.

Per-declaration `#assert_no_axioms` on every carrier / structural-equality / non-vacuity declaration.  Following
the shipped `AuditAll` discipline (per-decl gates, NOT `#audit_namespace` whole-namespace sweeps — the sweep can
silently pass an under-imported namespace as "0 declarations"; naming each decl fails LOUDLY if it vanishes).
Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- Carrier.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.OmegaComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.CellExpr
#assert_no_axioms FX1Poly.Polygraph.Omega.cellSize
#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryMotive
#assert_no_axioms FX1Poly.Polygraph.Omega.boundarySourceTotal
#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryTargetTotal
#assert_no_axioms FX1Poly.Polygraph.Omega.boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.IsGlobularCarrier
#assert_no_axioms FX1Poly.Polygraph.Omega.IsParallelPair
#assert_no_axioms FX1Poly.Polygraph.Omega.IsComposablePair
#assert_no_axioms FX1Poly.Polygraph.Omega.IsGlobularCell
#assert_no_axioms FX1Poly.Polygraph.Omega.GlobularLegs
#assert_no_axioms FX1Poly.Polygraph.Omega.globularLegs_of_isGlobularCell
#assert_no_axioms FX1Poly.Polygraph.Omega.isGlobularCarrier_onWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.CellSkeleton
#assert_no_axioms FX1Poly.Polygraph.Omega.toSkeleton
#assert_no_axioms FX1Poly.Polygraph.Omega.skeletonBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.cellBeq

-- NonVacuity.lean (the four r1 non-vacuity witnesses + their demo substrate)
#assert_no_axioms FX1Poly.Polygraph.Omega.demoComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.demoModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.demoGenBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.objectCell
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellGen
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellId
#assert_no_axioms FX1Poly.Polygraph.Omega.twoCellGen
#assert_no_axioms FX1Poly.Polygraph.Omega.twoCellId
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerCell
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCellGen
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCellVcomp
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCellVcomp_size
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerCell_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerCell_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.nonVacuousInterchangeConv
#assert_no_axioms FX1Poly.Polygraph.Omega.interchange_sides_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCell_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCell_reflexive
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellGen_isGlobular
#assert_no_axioms FX1Poly.Polygraph.Omega.twoCellGen_isGlobular
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCellGen_isGlobular
#assert_no_axioms FX1Poly.Polygraph.Omega.threeCellGen_globularLegs
#assert_no_axioms FX1Poly.Polygraph.Omega.derivedGodementDimThree
#assert_no_axioms FX1Poly.Polygraph.Omega.derivedGodementDimThree_size
#assert_no_axioms FX1Poly.Polygraph.Omega.derivedWhiskerDimThree
#assert_no_axioms FX1Poly.Polygraph.Omega.derivedWhiskerDimThree_size

end FX1PolyAudit
