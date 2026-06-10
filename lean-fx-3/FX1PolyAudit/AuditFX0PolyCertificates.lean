import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.FX0Bridge
import FX1PolyAudit.FX0CrossCheck
import FX1PolyAudit.FX0CrossCheckCertified
import FX1PolyAudit.FX0CrossCheckCorpus
import FX1Poly.Core.CertifyRawCellExact
import FX1Poly.Core.InferRawCellGeneral
import FX1Poly.Core.CertifiedTerm
import FX0Poly.StructuralRecheck
import FX0Poly.CertRecheck
import FX0Poly.CertRecheckSound
import FX0Poly.KernelArity
import FX0Poly.CertSerialize
import FX0Poly.CertDeserialize

/-! # FX1PolyAudit/AuditFX0PolyCertificates — FX0Poly minimal-checker zero-axiom gates, shard 01 of 2 (split from the AuditFX0Poly monolith for parallel gate elaboration).  Covers the per-node structural admission rule, the recursive certificate re-check driver + soundness, the concrete kernel-fragment arity model, and the .fx0c serializer + deserializer round-trip.  The full import block is replicated verbatim so the per-decl gates see every loaded constant. -/

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

/-! ### FX0Poly concrete kernel-fragment arity model + end-to-end cell re-check (var/universe/Π/Σ) -/

#assert_no_axioms FX0Poly.fxArity
#assert_no_axioms FX0Poly.recheck_fxArity_wasAccepted_eq_isValidB
#assert_no_axioms FX0Poly.recheck_fxArity_smoke_var
#assert_no_axioms FX0Poly.recheck_fxArity_smoke_universe
#assert_no_axioms FX0Poly.recheck_fxArity_smoke_pi
#assert_no_axioms FX0Poly.recheck_fxArity_smoke_sigma
#assert_no_axioms FX0Poly.recheck_fxArity_smoke_piWrongArity
#assert_no_axioms FX0Poly.recheck_fxArity_smoke_unknownTag

-- CertSerialize.lean — the .fx0c binary certificate serializer (FX0-PC.2 serializer half). The flat,
-- self-delimiting List Nat encoding (tag :: childCount :: children...) is difference-list / accumulator-
-- threaded (cons-only, NO List.append — whose core append_assoc/append_nil are not propext-free), so the
-- serializer + its INJECTIVITY (Cert.encode_injective: distinct certs ⟹ distinct byte streams ⟹ unambiguous
-- external decode) stay zero-axiom. Injectivity is mutual structural injection + Nat.noConfusion.
#assert_no_axioms FX0Poly.Cert.encodeAux
#assert_no_axioms FX0Poly.Cert.encodeChildrenAux
#assert_no_axioms FX0Poly.Cert.encode
#assert_no_axioms FX0Poly.Cert.encodeAux_inj
#assert_no_axioms FX0Poly.Cert.encodeChildrenAux_inj
#assert_no_axioms FX0Poly.Cert.encode_injective
#assert_no_axioms FX0Poly.Cert.encode_smoke
#assert_no_axioms FX0Poly.Cert.encode_distinguishes

-- CertDeserialize.lean — the .fx0c parser (FX0-PC.2 parser half). The Cert decoder is STRUCTURAL ON A FUEL
-- Nat (every recursive call, incl. per-child, decrements it), so it compiles to recursors — propext/
-- Quot.sound-free AND rfl-computing — UNLIKE a WellFounded.fix decoder, which leaks both and does not reduce.
-- Cert.budget is a SUM-based fuel measure (avoids the propext-tainted Nat.max). ★ Cert.decode_encode is the
-- round-trip: decode c.budget (encode c) = some (c, []) — encode then decode is the identity.
#assert_no_axioms FX0Poly.Cert.decode
#assert_no_axioms FX0Poly.Cert.decodeChildren
#assert_no_axioms FX0Poly.Cert.decode_smoke
#assert_no_axioms FX0Poly.Cert.budget
#assert_no_axioms FX0Poly.Cert.childrenBudget
#assert_no_axioms FX0Poly.Cert.decode_encodeAux
#assert_no_axioms FX0Poly.Cert.decodeChildren_encodeChildrenAux
#assert_no_axioms FX0Poly.Cert.decode_encode
