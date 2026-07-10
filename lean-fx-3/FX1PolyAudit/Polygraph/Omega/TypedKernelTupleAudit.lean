import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.TypedKernelTuple

/-! # FX1PolyAudit.Polygraph.Omega.TypedKernelTupleAudit — zero-axiom gate for the typed kernel-as-value tuple
(OMEGA-7 r3, B1+B2).

Per-declaration `#assert_no_axioms` on the typed admitted table, the kernel-as-value tuple type, the canonical
boundary tower + its dimension proof, the dimension-seating constructor, the demo tuple over the real kernel
rows, the dim-2 / dim-3 firing + admissibility + boundary-dimension witnesses, the non-degenerate dim-3 full
witness, the load-bearing rejection, and the forgetful map back to the r1 seed shape. -/

namespace FX1PolyAudit

-- TypedKernelTuple.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.AdmittedTable
#assert_no_axioms FX1Poly.Polygraph.Omega.TypedKernel
#assert_no_axioms FX1Poly.Polygraph.Omega.starTower
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeDim_starTower
#assert_no_axioms FX1Poly.Polygraph.Omega.admittedTableAtDim
#assert_no_axioms FX1Poly.Polygraph.Omega.demoTypedKernel
#assert_no_axioms FX1Poly.Polygraph.Omega.demoTypedKernel_dim2_rowFires
#assert_no_axioms FX1Poly.Polygraph.Omega.demoTypedKernel_dim3_rowFires
#assert_no_axioms FX1Poly.Polygraph.Omega.demoTypedKernel_dim3_admissible
#assert_no_axioms FX1Poly.Polygraph.Omega.demoTypedKernel_dim3_boundaryDim
#assert_no_axioms FX1Poly.Polygraph.Omega.demoDim3AdmittedTableFull
#assert_no_axioms FX1Poly.Polygraph.Omega.demoDim3AdmittedTableFull_fullnessHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.demoDim3AdmittedTableFull_rowFires
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeMissingMiddle_notAdmitted
#assert_no_axioms FX1Poly.Polygraph.Omega.typedKernelForget
#assert_no_axioms FX1Poly.Polygraph.Omega.typedKernelForget_sharesRow
#assert_no_axioms FX1Poly.Polygraph.Omega.typedKernelForget_admissible

end FX1PolyAudit
