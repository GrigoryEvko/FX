import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Order.AlmostFull

/-! # Zero-axiom gate: constructive almost-full relations

Per-declaration freeness from `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` for the almost-full kit: the structural Boolean order on `Nat`
(`afNatBle` with reflexivity, totality, transitivity, boundary lemma), the disjunction
helpers, the `AlmostFull` inductive and both constructors, the always-true lemma,
weakening/monotonicity, pullback closure, the degenerate product fragment, the staged proof
`afNatLeStage` then `afNat`, and the marker `fxNet4_dicksonWall`.  The AF intersection/product
theorem is walled (source header), so `dicksonLemma` is undeclared. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.afNatBle
#assert_no_axioms FX1Poly.ComputerAlgebra.afNatBleRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.afNatBleTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.afNatBleTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.afNatSuccFalseLe
#assert_no_axioms FX1Poly.ComputerAlgebra.afOrTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.afOrElim
#assert_no_axioms FX1Poly.ComputerAlgebra.afOrIntroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.afOrIntroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.AlmostFull
#assert_no_axioms FX1Poly.ComputerAlgebra.AlmostFull.now
#assert_no_axioms FX1Poly.ComputerAlgebra.AlmostFull.later
#assert_no_axioms FX1Poly.ComputerAlgebra.afAlwaysTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.afWeaken
#assert_no_axioms FX1Poly.ComputerAlgebra.afMono
#assert_no_axioms FX1Poly.ComputerAlgebra.afPullback
#assert_no_axioms FX1Poly.ComputerAlgebra.afProductTrivialFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.afNatLeStage
#assert_no_axioms FX1Poly.ComputerAlgebra.afNat
#assert_no_axioms FX1Poly.ComputerAlgebra.fxNet4_dicksonWall

end FX1PolyAudit
