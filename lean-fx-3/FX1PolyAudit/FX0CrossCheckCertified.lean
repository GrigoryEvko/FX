import FX1PolyAudit.FX0CrossCheck
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.UntypedOmegaNotStronglyNormalizing

/-!
# FX1PolyAudit/FX0CrossCheckCertified — the FX0 cross-check of SN-certified terms (SN-148)

`FX0CrossCheck` proves the standalone external verifier accepts the serialized encoding of EVERY well-formed
cell (`externalVerify_encodeCell`) — but that is purely STRUCTURAL: it holds for any `RawTerm`, including ones
the rich kernel would reject as ill-typed and non-normalizing.  This file LAYERS the kernel's correctness
guarantee on top, restricting to the terms the rich kernel actually CERTIFIES (well-typed in a well-formed
context) and pairing structural acceptance with strong normalization.

`externalVerify_accepts_certified` is the headline (SN-148): a term carrying a `HasTypeDescPi` derivation in a
`WfContextDesc`-well-formed context is BOTH strongly normalizing (`StepStar.IsStronglyNormalizing`, via the
open SN-043 theorem `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`) AND accepted by the independent
minimal external verifier (via `externalVerify_encodeCell`).  So every certificate the rich kernel emits
denotes a term that the small, independently-auditable verifier accepts and that genuinely terminates — the
two guarantees the Metamath-Zero trust split is meant to deliver, jointly.

The typing hypothesis is NOT cosmetic.  `externalVerify_accepts_omega_but_omega_notStronglyNormalizing`
exhibits `Ω = (λx. x x)(λx. x x)`: the external verifier ACCEPTS Ω's encoding (Ω is structurally well-formed),
yet Ω is NOT strongly normalizing (it β-steps to itself — SN-NECESSITY).  So the conjunction in the headline
would be FALSE without the certificate: structural acceptance alone does not imply termination, and the rich
typing derivation is exactly what adds the SN guarantee the external structural check cannot.

## Zero-axiom verification

Both theorems are direct pairings of already-zero-axiom results — `externalVerify_encodeCell` (the structural
soundness) with `HasTypeDescPi.stronglyNormalizingOfWfContextDesc` (open SN-043) / `omegaCombinator`'s
`omegaCombinator_notStronglyNormalizing` (its self-loop refutes accessibility).  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX1Poly.FX0CrossCheck

open FX1Poly.Core (RawTerm PolyProfile)
open FX1Poly.FX0Bridge (encodeCell)
open FX1Poly.Typed (HasTypeDescPi WfContextDesc omegaCombinator omegaCombinator_notStronglyNormalizing)
open FX1Poly.Core.StepStar (IsStronglyNormalizing)

/-- ★ **The FX0 cross-check of SN-certified terms (SN-148).**  Every term the rich kernel certifies — a
`HasTypeDescPi` derivation in a `WfContextDesc`-well-formed context — is BOTH strongly normalizing AND accepted
by the independent minimal external verifier.  The two halves of the Metamath-Zero trust guarantee, jointly:
the structural acceptance (`externalVerify_encodeCell`) says the small auditable verifier agrees on the
emitted bytes; the strong normalization (open SN-043, `stronglyNormalizingOfWfContextDesc`) says the term
genuinely terminates. -/
theorem externalVerify_accepts_certified {profile : PolyProfile} {scope : Nat}
    {context : FX1Poly.Typed.TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    externalVerify (FX0Poly.Cert.encode (encodeCell subject)) (encodeCell subject).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing subject :=
  ⟨externalVerify_encodeCell subject,
   HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed⟩

/-- **The typing hypothesis is ESSENTIAL (non-vacuity).**  The external verifier accepts the encoding of
`Ω = (λx. x x)(λx. x x)` — Ω is structurally well-formed — yet Ω is NOT strongly normalizing (it β-steps to
itself).  So the SN conjunct of `externalVerify_accepts_certified` genuinely requires the rich typing
certificate: structural acceptance alone does not imply termination (cf. SN-NECESSITY). -/
theorem externalVerify_accepts_omega_but_omega_notStronglyNormalizing :
    externalVerify (FX0Poly.Cert.encode (encodeCell omegaCombinator)) (encodeCell omegaCombinator).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ ¬ IsStronglyNormalizing omegaCombinator :=
  ⟨externalVerify_encodeCell omegaCombinator, omegaCombinator_notStronglyNormalizing⟩

end FX1Poly.FX0CrossCheck
