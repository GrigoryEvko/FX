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

/-! ### FX0Bridge — the rich→minimal certificate bridge (FX0-PC.7).  `encodeCell` maps a rich `FX1Poly.RawTerm`
to a flat `FX0Poly.Cert` (native `Generator.toNat` tag + structurally-encoded children); `bridgeArity` is the
checker's arity model pinned to FX1Poly's native tags (via `Generator.fromTag`); ★ `encodeCell_recheck_accepted`
is the structural soundness — the independent minimal checker ACCEPTS the encoding of every well-formed cell,
because the `RawTermChildren generator.binderShifts` index discipline forces each node's child count to match
its `bridgeArity`.  This file (FX1PolyAudit-side, the only library seeing both stacks) holds the bridge to the
same per-decl zero-axiom discipline as the rest of the checker. -/

#assert_no_axioms FX1Poly.FX0Bridge.encodeCell
#assert_no_axioms FX1Poly.FX0Bridge.encodeCellChildren
#assert_no_axioms FX1Poly.FX0Bridge.bridgeArity
#assert_no_axioms FX1Poly.FX0Bridge.bridgeArity_toNat
#assert_no_axioms FX1Poly.FX0Bridge.natBeqSelfTrue
#assert_no_axioms FX1Poly.FX0Bridge.encodeCellChildren_length
#assert_no_axioms FX1Poly.FX0Bridge.encodeCell_isValidB
#assert_no_axioms FX1Poly.FX0Bridge.encodeCellChildren_allValidB
#assert_no_axioms FX1Poly.FX0Bridge.verdict_eq_accepted_of_wasAccepted
#assert_no_axioms FX1Poly.FX0Bridge.encodeCell_recheck_accepted
#assert_no_axioms FX1Poly.FX0Bridge.bridgeArity_smoke_var
#assert_no_axioms FX1Poly.FX0Bridge.bridgeArity_smoke_lam
#assert_no_axioms FX1Poly.FX0Bridge.bridgeArity_smoke_piTyCode
#assert_no_axioms FX1Poly.FX0Bridge.bridgeArity_smoke_unknownTag
#assert_no_axioms FX1Poly.FX0Bridge.encodeCell_smoke_universeCode
#assert_no_axioms FX1Poly.FX0Bridge.encodeCell_smoke_piTyCode
#assert_no_axioms FX1Poly.FX0Bridge.recheck_smoke_universeCode

/-! ### FX0CrossCheck — the end-to-end external-verification pipeline (FX0-PC.5).  `externalVerify bytes fuel`
decodes a `.fx0c` stream and re-checks the recovered cert against `bridgeArity`; ★ `externalVerify_encodeCell`
is the end-to-end soundness — the standalone external verifier accepts the serialized encoding of EVERY
well-formed cell (composing the `Cert.decode_encode` round-trip with the bridge soundness), closing the
structural FX0 cross-check loop through the actual byte channel.  Negative smokes show it discriminates
(wrong arity / unknown tag / truncated → malformed); positive fixtures run `var 0` and a universe-code cell
end to end. -/

#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_encodeCell
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_smoke_rejectsWrongArity
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_smoke_rejectsUnknownTag
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_smoke_rejectsTruncated
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_var0
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_universeCode

/-! ### FX0CrossCheckCertified — the FX0 cross-check of SN-certified terms (SN-148).  ★
`externalVerify_accepts_certified` pairs the structural acceptance (`externalVerify_encodeCell`) with open
SN-043 (`stronglyNormalizingOfWfContextDesc`): every term the rich kernel CERTIFIES is BOTH strongly
normalizing AND accepted by the independent external verifier — the two Metamath-Zero trust guarantees jointly.
The companion shows the typing hypothesis is essential (Ω is accepted structurally yet is not SN). -/

#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_certified
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_omega_but_omega_notStronglyNormalizing

/-! ### FX0CrossCheckCorpus — the cross-check on the kernel's flagship CERTIFIED TYPED terms (FX0-PC.8).
The generic `externalVerify_accepts_certified` instantiated on the Church-boolean + Church-numeral
encodings: the independent external verifier accepts the serialized encodings of the kernel's actual
certified `λ`-terms, and they are strongly normalizing.  Connects the typed-derivation thread to the
external-verifier soundness — an A₀-release ingredient (#464). -/

#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchTrue
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchFalse
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchOne
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchTwo
-- FX0-PC.8 corpus extension: ★ externalVerify_accepts_churchNumeral lifts the cross-check to EVERY Church
-- numeral (∀ n, via churchNumeralLambda_hasTypeDescPi #1007) — the whole infinite numeral family in one theorem.
-- externalVerify_accepts_polymorphicIdentity adds the dependent identity λA.λx.x (a distinct λ-shape).
-- externalVerify_accepts_churchNatType adds the Church Nat TYPE code (a piTyCode-headed type FORMER typed at a
-- universe, not a λ-term) — broadening from term introductions to the type-code encoding path.
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchNumeral
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_polymorphicIdentity
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchNatType

/-! ### FX0-PC.1 — the HOST-MINIMAL gate on the Layer-1 certifier (★ closes #220)

`#assert_host_minimal` (DependencyAudit) walks the target's FULL transitive constant closure
EXHAUSTIVELY (truncation is a build error, unlike the fuel-silent statistics walk) and fails the
build if the closure contains: an axiom, a constant from any non-`Init`/`FX1Poly`/`FX0Poly` module
(no `Lean.*`, no `Std.*`, no `IO`), an `unsafe` or `partial` definition, an opaque constant, or a
quotient primitive.  Tactic-mode SOURCE in the closure is irrelevant — the gate audits the
ELABORATED kernel artifact.

Calibrated result (the honest prelude slice, reported by the gate on every build): the certifier
closure is ~1330–1360 constants touching exactly `Init.Prelude`, `Init.Core`, `Init.WF`,
`Init.SimpLemmas`, `Init.Data.Nat.Basic` (+ `Init.Data.List.Basic` for the wrapper/`Certified`).
That slice — not the aspirational "Init.Prelude only" — is what the external verifier spec
(FX0-PC.4) must model.  NOT checked (stated, not absorbed): `@[extern]` bindings on `Init`
primitives (e.g. `Nat` arithmetic) live in the trusted Lean RUNTIME, outside the kernel-checked
closure; eliminating that trust is exactly the external C/Rust re-checker's job (FX0-PC.6).

CERTIFICATE-NOTION CAVEAT (post O-STACK #1194): this gates the sort-DISCIPLINED structural
certifier, which provably does not cover all typed subjects
(`typedDoesNotFactorThroughCertification`); the sort-agnostic FX0 re-checker above is the
A0 external-verification leg. -/

#assert_host_minimal FX1Poly.Core.certifyRawCellExact?
#assert_host_minimal FX1Poly.Core.certifyRawCellExactFueled?
#assert_host_minimal FX1Poly.Core.inferRawCellGeneral?
#assert_host_minimal FX1Poly.Core.Certified
