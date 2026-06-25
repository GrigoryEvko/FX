import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.MilestoneAParityMatrix
import FX1PolyAudit.SnTriangulationBundle
import FX1PolyAudit.HonestCapstoneSignoff

/-! # FX1PolyAudit.Core.ParityMatrix.CoreCellsParityAudit

Zero-axiom audit shard mirroring kernel module `FX1PolyAudit.MilestoneAParityMatrix`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- SN triangulation bundle: "SN proven once (Tait), triangulated twice" consolidated against the parity
-- ledger. snColumnIsHonest pins the SN column = (provenIndependent, bridgedToTait, partialFragment) by rfl;
-- snPrimaryTait is Leg 1 (Tait, the one independent proof); snConfirmSconingBridged is Leg 2 (sconing = Tait
-- object, proof irrelevance); snConfirmRpoFragment + snRpoBetaBoundary are Leg 3 (ι∪η fragment SN, Tait-free,
-- with β provably non-orientable so β stays Tait-imported).
#assert_no_axioms FX1Poly.Core.ParityMatrix.snColumnIsHonest

#assert_no_axioms FX1Poly.Core.ParityMatrix.snPrimaryTait

#assert_no_axioms FX1Poly.Core.ParityMatrix.snConfirmSconingBridged

#assert_no_axioms FX1Poly.Core.ParityMatrix.snConfirmRpoFragment

#assert_no_axioms FX1Poly.Core.ParityMatrix.snRpoBetaBoundary

-- Honest capstone sign-off: the honest Milestone-A criterion (Tait proves all 3 endpoints; SN triangulated
-- twice — sconing bridged + RPO fragment) is MET (honestCapstoneMet_holds, rfl on the ledger), WHILE the naive
-- three-independent-ways criterion is NOT (and cannot be, per the SN NO-GOs) —
-- honestCapstone_met_while_threeWay_unreachable. The sconing-consistency cell is now bridgedToTait (the honesty
-- fix), so the ledger column stays honest.
#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstoneMet

#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstoneMet_holds

#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstone_met_while_threeWay_unreachable

-- ★ PARITY-MATRIX: the 3-leg (Tait / sconing-via-STC / RPO-word) × 3-endpoint (SN / canonicity /
-- consistency) ledger + the HONEST three-way-capstone criterion.  parityCell is the honest 9-cell status
-- table; capstone_currentlyClosedOneWay (rfl): exactly ONE leg (Tait) is fully+independently proven across
-- all three endpoints; threeWayCapstone_not_yet_met (decide): the three-way capstone is NOT yet closed
-- (sconing SN bridged-to-Tait, RPO leg owns only the SN endpoint — Tait-free ι∪η, β imported, canon/consist
-- open).  rpoStrongNormalizationEndpoint: NON-VACUOUS witness (the operational-SN theorem behind the RPO×SN cell).
#assert_no_axioms FX1Poly.Core.ParityMatrix.capstone_currentlyClosedOneWay

#assert_no_axioms FX1Poly.Core.ParityMatrix.legBreakdown

#assert_no_axioms FX1Poly.Core.ParityMatrix.threeWayCapstone_not_yet_met

#assert_no_axioms FX1Poly.Core.ParityMatrix.rpoStrongNormalizationEndpoint

end FX1PolyAudit
