import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.HasTypeDescStronglyNormalizing

/-! # FX1Poly/Typed/WfContextDescStronglyNormalizing — classifier SN over WfContextDesc

`HasTypeDesc.classifierStronglyNormalizingNative`: the classifier of any formation-typed cell is strongly
normalizing, over the `WfContextDesc` substrate.  It routes through the native
`HasTypeDesc.classifierIsTypeDescNative` (`WfContextDescValidity.lean`), then the type-level SN projection
`IsTypeDesc.isStronglyNormalizing` normalizes the resulting `IsTypeDesc`.  The SN leg of the formation-engine
classifier metatheory.

## Zero-axiom verification

`classifierIsTypeDescNative` (formation validity) ∘ `IsTypeDesc.isStronglyNormalizing` (the
type-level SN projection).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Classifier strong normalization over `WfContextDesc`.**  The classifier of a
`HasTypeDesc`-typed cell is strongly normalizing, under the `IsTypeDesc`-based well-formedness `WfContextDesc`.
Native validity (`classifierIsTypeDescNative`) turns the classifier into an `IsTypeDesc`, then
`IsTypeDesc.isStronglyNormalizing` normalizes it. -/
theorem HasTypeDesc.classifierStronglyNormalizingNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing classifier :=
  (typed.classifierIsTypeDescNative wellFormed).isStronglyNormalizing

end FX1Poly.Typed
