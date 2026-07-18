import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Order.AlmostFull

/-! # FX1PolyAudit/ComputerAlgebra/Order/AlmostFull — zero-axiom gate
    (NET-4 brick: constructive almost-full relations)

Per-declaration zero-axiom gate for the constructive almost-full kit: the structural
Boolean order on `Nat` (`afNatBle` + reflexivity / totality / transitivity / the boundary
lemma), the Boolean disjunction helpers, the `AlmostFull` higher-order `Prop` inductive
(with both constructors), the always-true smoke lemma, weakening / monotonicity, pullback
closure, the degenerate product fragment, the staged proof that `Nat`'s order is
almost-full (`afNatLeStage` → `afNat`), and the Dickson-wall marker.

The AF-product / intersection theorem (`afInter` / `afProduct`) — the crux of Dickson's
lemma — is WALLED (see the source header): its both-`later` case demands a non-structural,
well-founded tree recursion that `WellFounded.fix` would supply, which is forbidden here.
`dicksonLemma` is left undeclared; the marker `fxNet4_dicksonWall = false` records the wall.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

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
