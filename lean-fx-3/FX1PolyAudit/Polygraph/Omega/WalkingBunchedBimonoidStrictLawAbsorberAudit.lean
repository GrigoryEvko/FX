import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStrictLawAbsorber

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStrictLawAbsorberAudit — zero-axiom gate for the BI
cash-out: the three verbatim Node-A components assembled at the matrix level, and the honest refutation of the
unconditional cell-level strict-law absorber over the free carrier (WP-PROP r6, #2033).

Per-declaration `#assert_no_axioms` on: the three matrix-level component assemblies; the mis-declared datum + the
refutation theorem + the well-typed positive instance; and the B4 markers (including the two `= false`
residual / wall markers).

Independent `#print axioms` on the refutation theorem (the decisive finding) and the positive instance closes the
gate. -/

namespace FX1PolyAudit

-- The three matrix-level component assemblies.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrictUnitLawsAssembleAtMatrixLevel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrictAssocAssemblesAtMatrixLevel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrictBlockLawAssemblesAtMatrixLevel

-- The free-carrier obstruction: the mis-declared datum + the refutation + the positive instance.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuBreaksVcompUnitLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWellTypedMuVcompUnitLeftRespected

-- The B4 markers (three-components + refutation + residual + no-fabricated-flip + ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_biThreeComponentsAssembleAtMatrixLevel
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_freeCarrierStrictLawLiftRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_strictLawCellAbsorberNeedsWellTypedPredicate
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_strictLawExtensionStaysFalseNoFabricatedFlip
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_biCashOutRoundSixLedgerShipped

-- Independent (non-fuel) axiom prints on the refutation + the positive instance.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuBreaksVcompUnitLeft
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWellTypedMuVcompUnitLeftRespected

end FX1PolyAudit
