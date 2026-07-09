import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadHcompMult

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadHcompMult — zero-axiom gate (hcomp associativity + word hcomp)

Per-declaration zero-axiom gate for the horizontal-composite associativity `hcompAssoc` and the HORIZONTAL word
multiplicativity `wordMul_hcomp` (with the right-factor Godement congruence + the appended-word codomain boundary).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.hcompAssoc
#assert_no_axioms FX1Poly.Polygraph.MonadSaturatedTwoCellConv.hcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.monadTPower_length_consAppend
#assert_no_axioms FX1Poly.Polygraph.wordMul_hcomp

end FX1PolyAudit
