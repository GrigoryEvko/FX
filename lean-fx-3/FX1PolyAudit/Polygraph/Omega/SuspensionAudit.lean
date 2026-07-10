import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Suspension

/-! # FX1PolyAudit.Polygraph.Omega.SuspensionAudit — zero-axiom gate for OMEGA-3 r1 suspension (B1+B2+B3).

Per-declaration `#assert_no_axioms` on every suspension / arithmetic-reflection / Eckmann-Hilton declaration
and its non-vacuity witnesses.  Following the shipped `AuditAll` discipline (per-decl gates, NOT
`#audit_namespace`).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — in particular the shifting-motive `suspendCell` recursion and the
`SuspendBoundaryCommutes` induction must stay propext-clean. -/

namespace FX1PolyAudit

-- Suspension.lean — the three maps + homomorphism lemmas (B1)
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_vcomp
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_id
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_cellSize

-- boundary commutation (B1)
#assert_no_axioms FX1Poly.Polygraph.Omega.SuspendBoundaryCommutes
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendBoundaryCommutes_all
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendCell_boundaryTarget

-- preservation of the free strict congruence (B1)
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendStrictRow
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendPreservesStrictConv

-- suspended valuation + linearize_suspend + table reflection (B2)
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendGenValue
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendGenValue_length
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendValuation
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_suspend
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendTable
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendTable_injective
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_reflects_along_suspend

-- convertibility reflection on the atom-word fragment (B2)
#assert_no_axioms FX1Poly.Polygraph.Omega.suspend_reflects_atomWordConv
#assert_no_axioms FX1Poly.Polygraph.Omega.suspend_faithful_atomWord

-- Eckmann-Hilton as structure (B3)
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_godementComp_eq_vcomp
#assert_no_axioms FX1Poly.Polygraph.Omega.godementComp_linearize_comm
#assert_no_axioms FX1Poly.Polygraph.Omega.vcomp_linearize_comm

-- non-vacuity witnesses (B1)
#assert_no_axioms FX1Poly.Polygraph.Omega.suspended_demoTwoCell_size
#assert_no_axioms FX1Poly.Polygraph.Omega.suspended_demoTwoCell_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.suspended_demoTwoCell_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.suspended_cellThreeA_table

-- honesty markers (B5)
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_suspensionPreservationShippedR1
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_suspensionArithmeticReflectionShippedR1
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_eckmannHiltonArithmeticShippedR1
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omega3Complete

end FX1PolyAudit
