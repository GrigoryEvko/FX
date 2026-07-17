import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialSubsetEnumeratorComplete

/-! # FX1PolyAudit/.../IntPolynomialSubsetEnumeratorComplete — zero-axiom gate

Per-declaration zero-axiom gate for the k-subset enumerator completeness (the seventh brick of the
char-matrix → invariant-factors layer, WP-ENDO #2255): every order-preserving `k`-element sublist is
enumerated by `kSublists` (`kSublistsComplete`) — load-bearing, since it proves the general
determinantal-divisor engine's `d_k = GCD over kSubsets` misses no minor.

Locally-copied propext-free `List.Mem` kit (`subsetEnumMemAppendOfLeft/Right/MapOfMem`) + the
`IsOrderedSubset` inductive + structural induction on the subset proof.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.subsetEnumMemAppendOfLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.subsetEnumMemAppendOfRight
#assert_no_axioms FX1Poly.ComputerAlgebra.subsetEnumMemMapOfMem
#assert_no_axioms FX1Poly.ComputerAlgebra.IsOrderedSubset
#assert_no_axioms FX1Poly.ComputerAlgebra.kSublistsComplete
#assert_no_axioms FX1Poly.ComputerAlgebra.kSubsetsComplete
#assert_no_axioms FX1Poly.ComputerAlgebra.orderedSubsetZeroTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.orderedSubsetZeroTwoIsEnumerated
#assert_no_axioms FX1Poly.ComputerAlgebra.kSublistsTwoOfZeroOneTwoIsPairs
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasSubsetEnumeratorCompleteness

end FX1PolyAudit
