import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AcyclicSystemTruncationCertificate

/-! # FX1PolyAudit/Polygraph/Homology/AcyclicSystemTruncationCertificate — zero-axiom gate (the
    general-graph census-zero closed form (c) + the eventual-exactness assembly (d), TOWER-ANICK r14, #2145)

Per-declaration zero-axiom gate for the r14 truncation certificate: the two `List.Mem` -> Bool bridges
(`natEqBoolRefl`, `natListContainsOfMem`), the letters-in-alphabet bridge (`memMapConsSplit`,
`memFlatMapWordsOverAlphabetLettersInAlphabet`, `memWordsOverAlphabetLettersInAlphabet`), the general-graph
census-zero closed form `acyclicCensusZeroAboveAlphabetLength` (c), the eventual-exactness assembly
`acyclicSystemExactAboveAlphabetLength` (d), the end-to-end witness, and the ledger marker.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing decls are ALSO checked with the core `#print axioms` command (which does not truncate) — each
must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the List.Mem -> natListContains-Bool bridges
#assert_no_axioms FX1Poly.Polygraph.Homology.natEqBoolRefl
#assert_no_axioms FX1Poly.Polygraph.Homology.natListContainsOfMem

-- the letters-in-alphabet bridge (the n-ary analog of r12's length bridge)
#assert_no_axioms FX1Poly.Polygraph.Homology.memMapConsSplit
#assert_no_axioms FX1Poly.Polygraph.Homology.memFlatMapWordsOverAlphabetLettersInAlphabet
#assert_no_axioms FX1Poly.Polygraph.Homology.memWordsOverAlphabetLettersInAlphabet

-- (c) the census-zero closed form + (d) the eventual-exactness assembly + witness + ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicCensusZeroAboveAlphabetLength
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicSystemExactAboveAlphabetLength
#assert_no_axioms FX1Poly.Polygraph.Homology.dagChainExactAtDegreeFourViaAcyclicity
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicSystemTruncationCertificateIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.acyclicCensusZeroAboveAlphabetLength
#print axioms FX1Poly.Polygraph.Homology.acyclicSystemExactAboveAlphabetLength
#print axioms FX1Poly.Polygraph.Homology.memWordsOverAlphabetLettersInAlphabet

end FX1PolyAudit
