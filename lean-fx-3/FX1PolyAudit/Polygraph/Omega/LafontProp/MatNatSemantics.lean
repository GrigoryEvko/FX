import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.MatNatSemantics

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.MatNatSemantics — zero-axiom gate (LAFONT-PROP r1, brick A)

Per-declaration zero-axiom gate for the greenfield Nat-matrix semantics kit of the Lafont re-founding:
the entries representation, structural summation, matrix product, block-diagonal direct sum, the five
generator matrices of [Lafont2003] Section 3, the rectangle-agreement checker, and the kit smoke fires
(including the machine-checked FAILURE of the Z2-specific relation mu.delta = eta.epsilon over N — the
relation-diff witness that the N presentation excludes it).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  All recursion is structural on `Nat` bounds; all fires are kernel `rfl`.
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.MatrixEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.identityEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.sumBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.composeEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.directSumEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.addGenEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zeroGenEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyGenEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.discardGenEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapGenEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.doEntriesAgreeOnRow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.doEntriesAgreeOnRows
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.doEntriesAgreeUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.swapComposeSwapAgreesWithIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.copyThenAddDoublesNotIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.zSpecificRelationFailsOverNat
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.identityComposeAddAgreesWithAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.directSumOfIdentitiesAgreesWithIdentity

end FX1PolyAudit
