import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadVcompMult

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadVcompMult — zero-axiom gate (vcomp word-mult monad-law core)

Per-declaration zero-axiom gate for the vcomp-word-multiplicativity sub-lemmas: the Godement-product congruences,
the two-cell Godement EXCHANGE, the uniform mu-tree LEFT peel (`gadgetSucc`, the RIGHT-unit law), and the
gadget-absorb BASE (`gadgetAbsorb_zero`, the LEFT-unit law firing at arbitrary merge width).  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.hcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.hcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.godementExchange
#assert_no_axioms FX1Poly.Polygraph.gadgetSucc
#assert_no_axioms FX1Poly.Polygraph.gadgetAbsorb_zero
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasVcompUnitAdjacencies

end FX1PolyAudit
