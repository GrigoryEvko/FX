import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.FX0Bridge
import FX1PolyAudit.FX0CrossCheck
import FX1PolyAudit.FX0CrossCheckCertified
import FX1PolyAudit.FX0CrossCheckCorpus
import FX1Poly.Core.CertifyRawCellExact
import FX1Poly.Core.CertifyRawCellExactSound
import FX1Poly.Core.CertifyRawCellExactShape
import FX1Poly.Core.CertifyRawCellExactCompHRejects
import FX1Poly.Core.InferRawCellGeneral
import FX1Poly.Core.InferRawCellGeneralSound
import FX1Poly.Core.PolyCellErasure
import FX1Poly.Core.CertifiedTerm
import FX0Poly.StructuralRecheck
import FX0Poly.CertRecheck
import FX0Poly.CertRecheckSound
import FX0Poly.KernelArity
import FX0Poly.CertSerialize
import FX0Poly.CertDeserialize

/-! # FX1PolyAudit/AuditFX0PolyBridge — FX0Poly minimal-checker zero-axiom gates, shard 02 of 2 (split from the AuditFX0Poly monolith for parallel gate elaboration).  Covers the FX0Bridge rich→minimal certificate bridge, the FX0CrossCheck external-verification pipeline + certified/corpus cross-checks, and the FX0-PC.1 host-minimal gate on the Layer-1 certifier.  The full import block is replicated verbatim so the per-decl gates see every loaded constant. -/

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

/-! ### FX0-PC.3 — Layer-1 SOUNDNESS under the host-minimal closure (★ closes #222)

The Layer-1 no-false-positives guarantee, gated at the same trust tier as the certifier itself:
every theorem below has its FULL transitive closure (statement constants + elaborated proof term)
verified axiom-free / foreign-free / unsafe-free / opaque-free / quotient-free by
`#assert_host_minimal`.  The family:

* `certifyRawCellExact?_sound` — the type-level no-laundering headline (term-mode `rfl`): an
  accepted certification's cell erases (`PolyCell.raw`) to EXACTLY the raw input, because the
  raw-INDEXED return type pins the rawCell index structurally.
* `PolyCell.raw` — the erasure extractor the statement is phrased over.
* `certifyRawCellExact?_compH_rejects` — the rejection-branch behavioral pin (compH is total-off).
* `certifyRawCellExact?_identityCell_boundary` + the two `_accepted_implies_inner_certs` pins —
  the behavioral half: the dispatcher's accepting arms are not short-circuited (acceptance forces
  the recursive sub-certifications), so a dispatch regression cannot hide behind the type-level pin.
* `inferRawCellGeneral?_sound` — the existential-ingress variant (HEq raw-equality).

Together with the certifier gates above this closes FX0-PC.3 (polycell.md §12.6.5 Layer 1): the
Lean-side soundness evidence lives entirely inside the calibrated `Init` prelude slice that the
external re-checker (FX0-PC.4/6) must model.  The Lean proofs are the CONFIDENCE layer, not the
trust base — the trust base is the external cross-check (FX0-PC.6/8).

Tactic-mode source in the shape pins is irrelevant here: the gate audits the ELABORATED kernel
artifact (the proof terms the kernel actually checks), which is the honest reading of the
"term-mode under host-minimal" requirement — what matters is what lands in the checked closure,
not the surface syntax that produced it. -/

#assert_host_minimal FX1Poly.Core.certifyRawCellExact?_sound
#assert_host_minimal FX1Poly.Core.PolyCell.raw
#assert_host_minimal FX1Poly.Core.certifyRawCellExact?_compH_rejects
#assert_host_minimal FX1Poly.Core.certifyRawCellExact?_identityCell_boundary
#assert_host_minimal
  FX1Poly.Core.certifyRawCellExact?_verticalComposite_accepted_implies_inner_certs
#assert_host_minimal
  FX1Poly.Core.certifyRawCellExact?_generatingCell_accepted_implies_inner_certs
#assert_host_minimal FX1Poly.Core.inferRawCellGeneral?_sound
