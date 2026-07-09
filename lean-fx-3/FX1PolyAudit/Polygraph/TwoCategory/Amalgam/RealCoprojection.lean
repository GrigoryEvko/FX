import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojection

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.RealCoprojection — zero-axiom gate for the genuine-generator
coprojection (WP-AMALG r6, P2)

Per-declaration zero-axiom gate for the real right coprojection `onTwoCell`: the `Option.map` plumbing, the
interpreter cons-form helper, the load-bearing interpreter-commutation `interpretWordFrom_map`, the coprojection
mode-injectivity, the 2-generator embedding + get-alignment, the real coprojection `inclusionRightTwoReal`, and the
monad-unit non-vacuity witness.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- Option.map plumbing
#assert_no_axioms FX1Poly.Polygraph.Amalgam.optionMapSome
#assert_no_axioms FX1Poly.Polygraph.Amalgam.optionMapNone
#assert_no_axioms FX1Poly.Polygraph.Amalgam.optionMapMap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.optionMapCongr

-- the interpreter cons-form helper + the load-bearing commutation
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interpretWordFrom_cons_of_get
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interpretWordFrom_map

-- coprojection mode-injectivity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castFinAcrossCount_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionRight_onModes_injective

-- the 2-generator right embedding + get-alignment
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedRightTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutTwoGenGetRight

-- the real coprojection + non-vacuity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionRightTwoReal
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadReconstructedT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadReconstructsUnit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.inclusionRightTwoReal_onUnit_index

-- the flipped flag + the shipped marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealGeneratorCoprojection
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealGeneratorCoprojectionShipped

end FX1PolyAudit
