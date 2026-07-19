import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.AbsorptionFlip

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.AbsorptionFlip — zero-axiom gate
(the within-spider leg-permutation engine + THE WIRING WALL + absorption partials)

Per-declaration zero-axiom gate for the leg-permutation brick: the mid-layer kit
(`zxaMidLayer` + arity lemmas + wire-block reshaping + the bare-move firing helper),
MIDDLE-PAIR FISSION/FUSION at every position both sides both colours
(`zxaMidMergeFuseZ/X` input side, `zxaMidForkFuseZ/X` output side — corner / assoc-
coassoc / exchange three-case recursions), SINGLE-CROSSING ABSORPTION at every
adjacent leg pair (`zxaCrossingAbsorb{Input,Output}{Z,X}`), ARBITRARY CROSSING WALKS
on one spider's legs (`ZxaSwapWalk` + WF + `zxaWalkAbsorb{Input,Output}{Z,X}`), two
fresh fires + the kernel negative control, THE WIRING WALL minted owner-false at its
two minimal instances (`zxaCounitSlideStatement`, `zxaSigmaInvolutionStatement`,
span-soundness pins, `zxaCrossingSlideIsProven := false`), the (B) absorption
statement owner-false (`zxaAbsorptionStatement`, `zxaAbsorptionIsProven := false`)
with the boundary-0 base case and the zero-generator fire landing on
`zxnNormalForm`, and the honest (C) outcome (`zxaHasFullDecision := false` —
`zxeCompletenessStatement` stays owner-false in its home file, byte-intact).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidLayerDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidLayerCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWiresWiresCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCatMidCells
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWiresConsWire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaShuffleFront
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMoveConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidMergeFuseZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidMergeFuseX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidForkFuseZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaMidForkFuseX

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCrossingAbsorbInputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCrossingAbsorbInputX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCrossingAbsorbOutputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCrossingAbsorbOutputX

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxaSwapWalk
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxaSwapWalk.nil
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxaSwapWalk.cons
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaSwapWalkWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWalkAbsorbOutputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWalkAbsorbOutputX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWalkAbsorbInputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWalkAbsorbInputX

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWalkOutputZFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaWalkInputXFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaPassiveCrossingSpanDistinct
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaPassiveCrossingNotConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCounitSlideStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaSigmaInvolutionStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCounitSlideSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaSigmaInvolutionSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaCrossingSlideIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaAbsorptionStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaAbsorptionIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaEmptyDiagramAbsorbed
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaKillCreateAbsorbedFire

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaHasLegPermutationEngine
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxaHasFullDecision

end FX1PolyAudit
