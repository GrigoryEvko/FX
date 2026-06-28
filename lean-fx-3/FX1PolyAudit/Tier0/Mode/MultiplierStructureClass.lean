import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.MultiplierStructureClass

/-! # FX1PolyAudit/AuditTier0ModeMultiplierStructureClass — zero-axiom gate for mode-2

Per-declaration zero-axiom gate for `mode-2`'s deliverable (`FX1Poly/Tier0/Mode/MultiplierStructureClass.lean`):
the multiplier structure-class taxonomy (the mode-axis DIM-CLASS) — the four classes
(`MultiplierStructureClass`) with their strength + structural-consequence predicates, the refinement order
(reflexive + transitive), the certified `MultiplierCertificate`, the named interval multipliers + their
classification + ledger, the refinement chain, and the non-degeneracy witnesses.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The structure classes + their predicates + the refinement order
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.structuralStrength
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.supportsDiagonal
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.supportsConnections
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.supportsReversal
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.refines
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.refines_refl
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.refines_trans

-- The certificate
#assert_no_axioms FX1Poly.Tier0.MultiplierCertificate
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.certificate

-- The named interval multipliers + the classification + ledger
#assert_no_axioms FX1Poly.Tier0.IntervalMultiplierName
#assert_no_axioms FX1Poly.Tier0.IntervalMultiplierName.structureClassOf
#assert_no_axioms FX1Poly.Tier0.IntervalMultiplierName.certificate
#assert_no_axioms FX1Poly.Tier0.affineInterval_isAffine
#assert_no_axioms FX1Poly.Tier0.cartesianInterval_isCartesian
#assert_no_axioms FX1Poly.Tier0.dedekindInterval_isDedekind
#assert_no_axioms FX1Poly.Tier0.deMorganInterval_isDeMorgan

-- The refinement chain + non-degeneracy
#assert_no_axioms FX1Poly.Tier0.multiplierLadder
#assert_no_axioms FX1Poly.Tier0.affine_ne_deMorgan
#assert_no_axioms FX1Poly.Tier0.deMorgan_not_refines_affine
#assert_no_axioms FX1Poly.Tier0.deMorgan_supportsReversal
#assert_no_axioms FX1Poly.Tier0.affine_not_supportsReversal

-- The structure-class lattice (how modal structure-classes combine)
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.join
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.meet
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.join_idem
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.join_comm
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.join_assoc
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.meet_idem
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.meet_comm
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.meet_assoc
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.join_meet_absorb
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.meet_join_absorb
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.refines_join_left
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.refines_join_right
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.join_isLeastUpperBound

-- The full Nuyts property table (Fig 7/9)
#assert_no_axioms FX1Poly.Tier0.MultiplierProperty
#assert_no_axioms FX1Poly.Tier0.MultiplierStructureClass.hasProperty
#assert_no_axioms FX1Poly.Tier0.hasProperty_cartesian
#assert_no_axioms FX1Poly.Tier0.hasProperty_connections
#assert_no_axioms FX1Poly.Tier0.hasProperty_reversal
#assert_no_axioms FX1Poly.Tier0.affine_quantifiable
#assert_no_axioms FX1Poly.Tier0.affine_pointed
#assert_no_axioms FX1Poly.Tier0.affineClass_isCopointed_lacksDiagonal
#assert_no_axioms FX1Poly.Tier0.hasProperty_mono
#assert_no_axioms FX1Poly.Tier0.reversal_gained

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMultiplierEndofunctorRealization
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMultiplierModalConsequences
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFullMultiplierPropertyTable

end FX1PolyAudit
