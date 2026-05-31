import FX1Poly.Core.StratifiedReducibleTypeForwardClosure
import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeConvInvariance
    — conversion-invariance of the stratified (Tarski-universe) reducibility relation

The stratified port of `ReducibleType.convInvariant`: CONVERTIBLE types denote the SAME reducibility
candidate.  `Conv` (= `StepStar.Join`) exposes a shared `commonReduct` reached from each side; forward
closure (`ReducibleTypeStep.forwardStepStar`) carries each side's candidate down to that reduct, where
functionality (`ReducibleTypeStep.deterministic`) forces the two candidates to coincide pointwise.

This is the conversion-arm unblocker the entire stratified Tarski-universe construction was built for, AND
the co-requisite for the dependent-arrow CR3 in the eventual non-universe CR bundle: it lets the codomain
candidate at a reduced Π-code be identified with the one at the original.  Note the proof needs NO backward
closure — both endpoints arrive ALREADY reducible (the fundamental theorem's `conv` arm supplies the right
type's reducibility from its well-formedness premise), so only forward transport plus determinism is used.

The four theorems mirror the pure-SN file at both layers:

  * `ReducibleTypeStep.convInvariant` / `.convTransfer` — parametric over the lower relation.
  * `ReducibleTypeAt.convInvariant` / `.convTransfer` — through the `Nat` recursion (both cases by defeq;
    explicit `ReducibleTypeStep.*` to avoid a self-recursive dot resolution).

## Zero-axiom verification

Destructure the `Conv` Join, transport each candidate by `forwardStepStar`, equate by `deterministic`; the
transfer corollaries are one `PointwiseIff` application.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Conversion-invariance of the stratified reducibility relation.**  If `typeLeft` and `typeRight` are
each reducible (at the SAME lower relation) and convertible, their candidates agree on every term.  Forward
closure carries both candidates to the shared reduct of the `Conv` Join, where `deterministic` equates
them — no backward closure required. -/
theorem ReducibleTypeStep.convInvariant {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeStep lowerReducible typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeStep lowerReducible typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    PointwiseIff candidateLeft candidateRight := by
  obtain ⟨_commonReduct, chainLeft, chainRight⟩ := conv
  exact ReducibleTypeStep.deterministic
    (ReducibleTypeStep.forwardStepStar reducibleLeft chainLeft)
    (ReducibleTypeStep.forwardStepStar reducibleRight chainRight)

/-- **Reducibility transfers across conversion (stratified).**  A term in the candidate of `typeLeft` lies
in the candidate of any convertible reducible `typeRight` — the membership form the fundamental theorem's
`conv` typing arm consumes. -/
theorem ReducibleTypeStep.convTransfer {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeStep lowerReducible typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeStep lowerReducible typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  (ReducibleTypeStep.convInvariant reducibleLeft reducibleRight conv term).mp membership

/-- **Conversion-invariance, level-indexed.**  `ReducibleTypeStep.convInvariant` through the `Nat` recursion
of `ReducibleTypeAt` (both cases by defeq).  Explicit `ReducibleTypeStep.convInvariant` avoids a
self-recursive resolution to `ReducibleTypeAt.convInvariant`. -/
theorem ReducibleTypeAt.convInvariant {scope : Nat} {level : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeAt level typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeAt level typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    PointwiseIff candidateLeft candidateRight := by
  cases level with
  | zero => exact ReducibleTypeStep.convInvariant reducibleLeft reducibleRight conv
  | succ predLevel => exact ReducibleTypeStep.convInvariant reducibleLeft reducibleRight conv

/-- **Reducibility transfers across conversion, level-indexed.**  The membership form at every fuel level. -/
theorem ReducibleTypeAt.convTransfer {scope : Nat} {level : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeAt level typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeAt level typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  (ReducibleTypeAt.convInvariant reducibleLeft reducibleRight conv term).mp membership

end FX1Poly.Core
