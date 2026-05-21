import LeanFX2.Term.PartialStrengthen.Dispatcher

/-! # Term/StrengtheningImage/AggregatorTotalCore

Universal strengthening-totality predicate retained for the few places that
still need to quantify over arbitrary context strengthenings.  The old 78
per-constructor wrappers were deleted after the renaming-image API became the
consumer-facing surface.
-/

namespace LeanFX2

namespace Term

/-- Universal totality over arbitrary context strengthenings.

`IsAggregatorTotal sourceTerm` says that, whenever the type and raw indices can
be strengthened through an arbitrary `ContextStrengthening`, the typed
dispatcher succeeds.  Most downstream consumers should prefer the renaming-image
API (`strengthenTyped?_rename_some` /
`rename_image_iff_strengthenTyped?_some`), which is strictly narrower and
matches the actual call sites. -/
def IsAggregatorTotal {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) : Prop :=
  ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {targetSourceType : Ty level targetScope}
    {targetSourceRaw : RawTerm targetScope},
    sourceType.partialStrengthen? strengthening.back =
        some targetSourceType →
    sourceRaw.partialStrengthen? strengthening.back =
        some targetSourceRaw →
    (partialStrengthenTyped? sourceTerm strengthening).isSome

end Term

end LeanFX2
