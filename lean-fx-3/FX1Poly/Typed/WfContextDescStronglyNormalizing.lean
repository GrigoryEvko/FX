import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.HasTypeDescStronglyNormalizing

/-! # FX1Poly/Typed/WfContextDescStronglyNormalizing — classifier SN over WfContextDesc (HasType-free)

`HasTypeDesc.classifierStronglyNormalizing` (`HasTypeDescStronglyNormalizing.lean`) — the classifier of any
formation-typed cell is strongly normalizing — is proved over the bespoke `WfContext`, so it inherits that
file's `HasType` coupling through `classifierIsTypeDesc`'s var-arm `toHasTypeDesc`.

This file ships the HasType-FREE twin over the `WfContextDesc` substrate: it routes through the native
`HasTypeDesc.classifierIsTypeDescNative` (`WfContextDescValidity.lean`, whose proof contains no `HasType`)
instead of `classifierIsTypeDesc`, then the type-level SN projection `IsTypeDesc.isStronglyNormalizing`
normalizes the resulting `IsTypeDesc`.  This is both the first CONSUMER of the native validity (confirming the
migration target is usable, not merely gated) and the SN leg of the formation-engine decouple's classifier
metatheory.

## Zero-axiom verification

`classifierIsTypeDescNative` (HasType-free formation validity) ∘ `IsTypeDesc.isStronglyNormalizing` (the
type-level SN projection).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Classifier strong normalization over `WfContextDesc`, HasType-free.**  The classifier of a
`HasTypeDesc`-typed cell is strongly normalizing, under the `IsTypeDesc`-based well-formedness `WfContextDesc`.
The native twin of `HasTypeDesc.classifierStronglyNormalizing`: native validity
(`classifierIsTypeDescNative`, no `HasType`) turns the classifier into an `IsTypeDesc`, then
`IsTypeDesc.isStronglyNormalizing` normalizes it.  The first consumer of the native validity target. -/
theorem HasTypeDesc.classifierStronglyNormalizingNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing classifier :=
  (typed.classifierIsTypeDescNative wellFormed).isStronglyNormalizing

end FX1Poly.Typed
