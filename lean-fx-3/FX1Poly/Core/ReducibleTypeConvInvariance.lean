import FX1Poly.Core.ReducibleTypeForwardStepStar
import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/ReducibleTypeConvInvariance
    — conversion-invariance of the dependent reducibility relation

The keystone the entire commutation-diamond / forward-closure development was built for: CONVERTIBLE
types denote the SAME reducibility candidate.  `Conv` (= `StepStar.Join`) is the common-reduct relation —
`Conv typeLeft typeRight` means both reduce to a shared `commonReduct`.  Forward closure
(`ReducibleType.forwardStepStar`) carries each side's candidate down to that common reduct, where
functionality (`ReducibleType.deterministic`) forces the two candidates to coincide pointwise.

`ReducibleType.convInvariant` is that coincidence (`PointwiseIff`); `ReducibleType.convTransfer` is the
membership form the fundamental theorem's `conv` arm consumes directly — a term reducible at a type's
candidate is reducible at the candidate of any convertible type.  Both are UNCONDITIONAL: `forwardStepStar`
has no fragment restriction (its `neutral` arm rests on the fully proved weak-head-normality preservation),
so conversion-invariance holds for arbitrary type codes — neutral, Π, or weak-head-reducible.

## Zero-axiom verification

Destructure the `Conv` Join, transport each candidate to the common reduct by `forwardStepStar`, equate by
`ReducibleType.deterministic`; the transfer corollary is one `PointwiseIff` application.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Conversion-invariance of the dependent reducibility relation.**  Convertible types denote pointwise-
equivalent candidates: if `typeLeft` and `typeRight` are each reducible and `Conv typeLeft typeRight`, the
two candidates agree on every term.  Forward closure carries both candidates to the shared reduct of the
`Conv` Join, where `ReducibleType.deterministic` equates them. -/
theorem ReducibleType.convInvariant {scope : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleType typeLeft candidateLeft)
    (reducibleRight : ReducibleType typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    PointwiseIff candidateLeft candidateRight := by
  obtain ⟨_commonReduct, chainLeft, chainRight⟩ := conv
  exact ReducibleType.deterministic
    (reducibleLeft.forwardStepStar chainLeft)
    (reducibleRight.forwardStepStar chainRight)

/-- **Reducibility transfers across conversion.**  A term in the candidate of `typeLeft` lies in the
candidate of any convertible `typeRight` — the membership form the fundamental theorem's `conv` typing
arm consumes. -/
theorem ReducibleType.convTransfer {scope : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleType typeLeft candidateLeft)
    (reducibleRight : ReducibleType typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  (ReducibleType.convInvariant reducibleLeft reducibleRight conv term).mp membership

end FX1Poly.Core
