import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.MultiplierStructureClass

/-! # FX1PolyAudit/AuditAxisModeMultiplierStructureClass — zero-axiom gate for mode-2

Per-declaration zero-axiom gate for `mode-2`'s deliverable (`FX1Poly/Axis/Mode/MultiplierStructureClass.lean`):
the multiplier structure-class taxonomy (the mode-axis DIM-CLASS) — the four classes
(`MultiplierStructureClass`) with their strength + structural-consequence predicates, the refinement order
(reflexive + transitive), the certified `MultiplierCertificate`, the named interval multipliers + their
classification + ledger, the refinement chain, and the non-degeneracy witnesses.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The structure classes + their predicates + the refinement order
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.structuralStrength
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.supportsDiagonal
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.supportsConnections
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.supportsReversal
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.refines
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.refines_refl
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.refines_trans

-- The certificate
#assert_no_axioms FX1Poly.Axis.MultiplierCertificate
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.certificate

-- The named interval multipliers + the classification + ledger
#assert_no_axioms FX1Poly.Axis.IntervalMultiplierName
#assert_no_axioms FX1Poly.Axis.IntervalMultiplierName.structureClassOf
#assert_no_axioms FX1Poly.Axis.IntervalMultiplierName.certificate
#assert_no_axioms FX1Poly.Axis.affineInterval_isAffine
#assert_no_axioms FX1Poly.Axis.cartesianInterval_isCartesian
#assert_no_axioms FX1Poly.Axis.dedekindInterval_isDedekind
#assert_no_axioms FX1Poly.Axis.deMorganInterval_isDeMorgan

-- The refinement chain + non-degeneracy
#assert_no_axioms FX1Poly.Axis.multiplierLadder
#assert_no_axioms FX1Poly.Axis.affine_ne_deMorgan
#assert_no_axioms FX1Poly.Axis.deMorgan_not_refines_affine
#assert_no_axioms FX1Poly.Axis.deMorgan_supportsReversal
#assert_no_axioms FX1Poly.Axis.affine_not_supportsReversal

-- The structure-class lattice (how modal structure-classes combine)
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.join
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.meet
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.join_idem
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.join_comm
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.join_assoc
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.meet_idem
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.meet_comm
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.meet_assoc
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.join_meet_absorb
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.meet_join_absorb
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.refines_join_left
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.refines_join_right
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.join_isLeastUpperBound

-- The full Nuyts property table (Fig 7/9)
#assert_no_axioms FX1Poly.Axis.MultiplierProperty
#assert_no_axioms FX1Poly.Axis.MultiplierStructureClass.hasProperty
#assert_no_axioms FX1Poly.Axis.hasProperty_cartesian
#assert_no_axioms FX1Poly.Axis.hasProperty_connections
#assert_no_axioms FX1Poly.Axis.hasProperty_reversal
#assert_no_axioms FX1Poly.Axis.affine_quantifiable
#assert_no_axioms FX1Poly.Axis.affine_pointed
#assert_no_axioms FX1Poly.Axis.affineClass_isCopointed_lacksDiagonal
#assert_no_axioms FX1Poly.Axis.hasProperty_mono
#assert_no_axioms FX1Poly.Axis.reversal_gained

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasMultiplierEndofunctorRealization
#assert_no_axioms FX1Poly.Axis.fxMode_hasMultiplierModalConsequences
#assert_no_axioms FX1Poly.Axis.fxMode_hasFullMultiplierPropertyTable

end FX1PolyAudit
