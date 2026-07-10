import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.Reconstruct

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/Reconstruct — zero-axiom gate (OMEGA-2 r3)

Per-declaration `#assert_no_axioms` on the r3 CROWN completeness leg: the clean Nat helpers, the generic
`vcompPow` backbone, the single-endo-generator crown carrier, the atom-word fragment, the arithmetic
roundtrip, the conv leg, the crown iff, the Decidable decision, the n=3/n=4 census witnesses, and the r3
honesty markers.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Clean Nat helpers
#assert_no_axioms FX1Poly.Polygraph.Omega.natZeroAddClean
#assert_no_axioms FX1Poly.Polygraph.Omega.natSuccAddClean
#assert_no_axioms FX1Poly.Polygraph.Omega.natOneAddClean

-- The generic vcomp-power backbone
#assert_no_axioms FX1Poly.Polygraph.Omega.vcompPow
#assert_no_axioms FX1Poly.Polygraph.Omega.vcompPow_add

-- The crown carrier
#assert_no_axioms FX1Poly.Polygraph.Omega.crownComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.crownBaseCell
#assert_no_axioms FX1Poly.Polygraph.Omega.crownAtom
#assert_no_axioms FX1Poly.Polygraph.Omega.crownValuation

-- The atom-word fragment + linearize invariant
#assert_no_axioms FX1Poly.Polygraph.Omega.IsAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.atomCount
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_atomWord

-- The arithmetic roundtrip (B1)
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_vcompPow_count
#assert_no_axioms FX1Poly.Polygraph.Omega.listHeadCount
#assert_no_axioms FX1Poly.Polygraph.Omega.reconstructCrown
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_reconstructCrown_roundtrip

-- The conv leg (B2)
#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryTarget_atomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.atomWord_vcompPow
#assert_no_axioms FX1Poly.Polygraph.Omega.reconstructCrown_conv_atomWord

-- The crown decision (B3)
#assert_no_axioms FX1Poly.Polygraph.Omega.atomWord_conv_of_linearize_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.atomWord_conv_iff_linearize_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.decideAtomWordConv

-- n=3 census witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.word3Right
#assert_no_axioms FX1Poly.Polygraph.Omega.word3Left
#assert_no_axioms FX1Poly.Polygraph.Omega.word3One
#assert_no_axioms FX1Poly.Polygraph.Omega.word3Right_isAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.word3Left_isAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.word3One_isAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.word3_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.word3_not_conv

-- n=4 census witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.word4Right
#assert_no_axioms FX1Poly.Polygraph.Omega.word4Left
#assert_no_axioms FX1Poly.Polygraph.Omega.word4Two
#assert_no_axioms FX1Poly.Polygraph.Omega.word4Right_isAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.word4Left_isAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.word4Two_isAtomWord
#assert_no_axioms FX1Poly.Polygraph.Omega.word4_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.word4_not_conv

-- The r3 honesty markers (B4)
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_reconstructRoundtripShippedR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_completenessScopedSingleGeneratorAtomWordFragmentR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_completenessGeneralOpenTwoObstructionsR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omegaThreeSuspendTableHandoffR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omega2R3Complete

end FX1PolyAudit
