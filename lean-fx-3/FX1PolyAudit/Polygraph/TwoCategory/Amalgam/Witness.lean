import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.Witness

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.Witness — zero-axiom gate for the involution + monad witness

Per-declaration zero-axiom gate for the concrete witness pushout: the two component `ModeComputad` presentations,
their pushout, the letters, the block decomposition of the alternating word `s t s t t` (proven by `rfl`), the
three NF invariants at the witness word, and the disjoint-generator precondition holding by `rfl`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- component computads + pushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadSameModes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadPushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadSplit

-- profile faithfulness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionComputad_profile
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputad_profile
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadPushout_profile

-- letters + component tags
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sLetter_component
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tLetter_component

-- block decomposition on the witness word
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessWordDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessRecomposeSound
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessAlternates
#assert_no_axioms FX1Poly.Polygraph.Amalgam.witnessBlocksNonempty

-- dispatch precondition
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadPushout_disjoint

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWitnessPushout

end FX1PolyAudit
