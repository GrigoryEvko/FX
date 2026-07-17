import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisorGeneral

/-! # FX1PolyAudit/.../IntPolynomialDeterminantalDivisorGeneral — zero-axiom gate

Per-declaration zero-axiom gate for the uniform general-n determinantal-divisor engine (the sixth brick of
the char-matrix → invariant-factors layer, WP-ENDO #2255): the `k`-subset index enumerator
(`indicesBelow`/`kSublists`/`kSubsets`/`selectionOf`) instantiating the already-general `polyGcdList ∘
charMatrixMinor` fold at arbitrary dimension (`charDeterminantalDivisor`, `determinantalDivisorSignature`),
cross-validated to reproduce the hand-rolled r34/r36 values and reaching the full dim-3 signatures
`[0,0,3]/[0,1,3]/[1,2,3]` that separate all three `(x−2)³` classes.

The `++`/`List.map`/`List.flatMap` used are DATA CONSTRUCTORS (only their equation/decision lemmas leak
`propext`), so this gate also confirms the enumerator stays axiom-free.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.indicesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.kSublists
#assert_no_axioms FX1Poly.ComputerAlgebra.kSubsets
#assert_no_axioms FX1Poly.ComputerAlgebra.selectionOf
#assert_no_axioms FX1Poly.ComputerAlgebra.allCharMinorsOfSize
#assert_no_axioms FX1Poly.ComputerAlgebra.charDeterminantalDivisor
#assert_no_axioms FX1Poly.ComputerAlgebra.determinantalDivisorSignature
#assert_no_axioms FX1Poly.ComputerAlgebra.indicesBelowFourIsRange
#assert_no_axioms FX1Poly.ComputerAlgebra.kSubsetsOneTwoIsSingletons
#assert_no_axioms FX1Poly.ComputerAlgebra.kSubsetsTwoThreeIsPairs
#assert_no_axioms FX1Poly.ComputerAlgebra.kSubsetsTwoFourIsSixPairs
#assert_no_axioms FX1Poly.ComputerAlgebra.generalDivisorAgreesWithHandRolledTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.generalDivisorAgreesWithHandRolledThree
#assert_no_axioms FX1Poly.ComputerAlgebra.fullSignatureSeparatesCubicClasses
#assert_no_axioms FX1Poly.ComputerAlgebra.DissimilarBySignature
#assert_no_axioms FX1Poly.ComputerAlgebra.generalEngineSeparatesAllThreeCubicClasses
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasGeneralDeterminantalDivisorEngine

end FX1PolyAudit
