import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.MonadReseat

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.MonadReseat — zero-axiom gate for the FIXED-pair walking-monad
reseat (MODE-ADMIT r3)

Per-declaration zero-axiom gate for the forward reseat functor: the 1-cell functor (`reseatPath` + its two
reduction smokes + the homomorphism law `reseatPath_composePath`), the dependent-witness collapse
(`reseatInterp`), the boundary cast (`castMonadTwoCell`), THE CRUX `reseatGen` (the `twoCellEquiv` forward half)
with its two boundary inversions and generator-image verifications (`monadTwoCellAtUnit_isEta` /
`reseatGen_unit_isEta`, `monadComputadReconstructedTT` / `monadComputadReconstructsMult` / `reseatPath_reconTT` /
`monadTwoCellAtMult_isMu` / `reseatGen_mult_isMu`), the free 2-cell functor `reseatCell` (+ its `gen` smoke), and
the three honesty markers.

The `cases` on the indexed `MonadTwoCell` in the two inversions stays propext-free (the `nil`/`cons` boundary
noConfusion discharges the impossible generator without a `propext` leak).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- The 1-cell functor + its reduction smokes + the homomorphism law
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPath_nil
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPath_reconT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPath_composePath

-- The dependent-witness collapse + the boundary cast
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatInterp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castMonadTwoCell

-- THE CRUX: the forward generator translation + its non-vacuity on both generators
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadTwoCellAtUnit_isEta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGen_unit_isEta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadReconstructedTT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadReconstructsMult
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatPath_reconTT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadTwoCellAtMult_isMu
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatGen_mult_isMu

-- The free 2-cell functor + its gen smoke
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reseatCell_gen

-- The honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasForwardReseatFunctor
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasReseatConvTransport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasWiredInheritancePipeline

end FX1PolyAudit
