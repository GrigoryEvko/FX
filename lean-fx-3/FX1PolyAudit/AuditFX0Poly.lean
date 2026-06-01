import FX1PolyAudit.DependencyAudit
import FX0Poly.StructuralRecheck
import FX0Poly.CertRecheck
import FX0Poly.CertRecheckSound

/-! # FX1PolyAudit/AuditFX0Poly
   — per-declaration zero-axiom gate for the FX0Poly minimal external checker

`FX0Poly` (the Metamath-Zero–flavored re-checker) deliberately does NOT import the `#assert_no_axioms`
macro — it stays independent of the FX1Poly stack so a reader can audit FX0Poly without trusting FX1Poly.
The zero-axiom gate therefore lives HERE, in the audit lib (which may import anything): the audit imports
the checker, not the other way round.  This keeps the trust direction correct while still holding FX0Poly
to the same per-declaration zero-axiom discipline as the rich kernel.

Each gate fails the build if its declaration depends on `propext` / `Quot.sound` / `Classical` / `sorry` /
`native_decide` / `omega`.
-/

/-! ### FX0Poly per-node structural admission rule (the trusted-core re-check step) -/

#assert_no_axioms FX0Poly.recheckNode
#assert_no_axioms FX0Poly.recheckNode_none_malformed
#assert_no_axioms FX0Poly.wasAccepted_ite_accepted_malformed
#assert_no_axioms FX0Poly.recheckNode_some_wasAccepted_eq
#assert_no_axioms FX0Poly.recheckNode_smoke_accepted
#assert_no_axioms FX0Poly.recheckNode_smoke_arityMismatch
#assert_no_axioms FX0Poly.recheckNode_smoke_childRejected

/-! ### FX0Poly recursive certificate re-check driver (folds the per-node rule over a certificate tree) -/

#assert_no_axioms FX0Poly.Cert
#assert_no_axioms FX0Poly.Cert.recheck
#assert_no_axioms FX0Poly.Cert.recheckChildren
#assert_no_axioms FX0Poly.Cert.recheckChildren_length
#assert_no_axioms FX0Poly.Cert.recheck_smoke_leafAccepted
#assert_no_axioms FX0Poly.Cert.recheck_smoke_unknownTag
#assert_no_axioms FX0Poly.Cert.recheck_smoke_recursiveAccepted
#assert_no_axioms FX0Poly.Cert.recheck_smoke_recursiveRejected

/-! ### FX0Poly recursive re-check soundness (the driver accepts exactly the structurally-valid trees) -/

#assert_no_axioms FX0Poly.Cert.isValidB
#assert_no_axioms FX0Poly.Cert.allValidB
#assert_no_axioms FX0Poly.Cert.recheck_wasAccepted_eq_isValidB
#assert_no_axioms FX0Poly.Cert.recheckChildren_all_wasAccepted_eq_allValidB
#assert_no_axioms FX0Poly.Cert.isValidB_smoke_valid
