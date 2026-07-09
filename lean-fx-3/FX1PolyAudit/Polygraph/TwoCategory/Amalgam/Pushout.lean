import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.Pushout

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.Pushout — zero-axiom gate for the mode-signature pushout

Per-declaration zero-axiom gate for the WP-AMALG-1 pushout construction: propext-free plumbing, the shared-mode
transport, the tagged 1-generator sum, the pushout computad + shape smokes, component tagging, the two
coprojections, and the copairing (easy direction of the universal property).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- propext-free plumbing
#assert_no_axioms FX1Poly.Polygraph.Amalgam.lengthAppend
#assert_no_axioms FX1Poly.Polygraph.Amalgam.lengthMap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.addSubCancel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.getValCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.getAppendLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.getAppendRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.getMap

-- shared-mode transport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castFinAcrossCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castFinAcrossCount_val
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castFinAcrossCount_roundTrip

-- tagged generator sum + pushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.combinedModalityGenerators
#assert_no_axioms FX1Poly.Polygraph.Amalgam.combinedModalityGenerators_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedLeftLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedRightLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.retagLeftTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.retagRightTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutShared
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutShared_modeCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutShared_modalityGenerators
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutShared_twoCellCount

-- component tagging
#assert_no_axioms FX1Poly.Polygraph.Amalgam.combinedGeneratorComponent
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedLeftLetter_component
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedRightLetter_component

-- morphisms + coprojections + copairing
#assert_no_axioms FX1Poly.Polygraph.Amalgam.ComputadMorphism
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.copairOnGenerators
#assert_no_axioms FX1Poly.Polygraph.Amalgam.copairOnGenerators_left
#assert_no_axioms FX1Poly.Polygraph.Amalgam.copairOnGenerators_right
#assert_no_axioms FX1Poly.Polygraph.Amalgam.copairMorphism
#assert_no_axioms FX1Poly.Polygraph.Amalgam.copairMorphism_restrictsLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.copairMorphism_restrictsRight

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSignaturePushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSignaturePushoutUniqueness

end FX1PolyAudit
