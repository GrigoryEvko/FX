import LeanFX2.Term.StrengtheningImage.AggregatorSoundUniversal

/-! # Term/StrengtheningImage/ImageCore

Core image soundness lemmas for successful typed strengthening.
-/

namespace LeanFX2

namespace Term

/-! ## Image theorem trio — weaken / strengthen invertibility

Three closure theorems on the image of `Term.weaken` under
`partialStrengthenTyped?`:

* `weaken_inv_of_strengthenTyped?_some` — right-inverse soundness:
  any successful strengthening produces a target whose forward-renamed
  form is heterogeneously equal to the source.  Direct corollary of
  the universal aggregator headline.
* `strengthenTyped?_some_of_weaken` — completeness on the weaken
  image: strengthening a `Term.weaken` source always succeeds.  Shipped
  later via `Term.unweaken?`-based totality.
* `weaken_image_iff_strengthenTyped?_some` — headline iff combining
  Steps 1 and 2.
-/

/-- Image Step 1 — right-inverse soundness for ANY successful
strengthening.  When `partialStrengthenTyped?` returns `some result`,
the recovered target's forward-renamed form is heterogeneously equal
to the source term.

The result is a direct corollary of the universal aggregator headline:
the per-arm dispatcher wrappers compose into
`isAggregatorSound_universal`, which when applied to a specific
strengthening/result pair yields the `StrengtheningSoundness` record
whose `termRenames` field is the desired HEq.

Consumed by Step 3 (`weaken_image_iff_strengthenTyped?_some`) and by
the Step.eta cascade SR proofs in Phase B+ per `extended-roadmap.md`
Day 32. -/
theorem weaken_inv_of_strengthenTyped?_some {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening sourceTerm)
    (success : partialStrengthenTyped? sourceTerm strengthening
        = some result) :
    HEq sourceTerm result.renamedTarget :=
  (isAggregatorSound_universal sourceTerm strengthening result success).termRenames

/-- Rename-image soundness for successful typed strengthening.

Any successful `partialStrengthenTyped?` result exposes a target-context
term whose forward rename is heterogeneously equal to the original
source-context term.  This is the forward, already-available half of the
planned T3 rename-image iff; the reverse direction still needs a
universal T1 dispatcher packaging over the 67 Eq-form and 11 HEq-form
rename-totality cases. -/
theorem rename_image_of_strengthenTyped?_some {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening sourceTerm)
    (success : partialStrengthenTyped? sourceTerm strengthening = some result) :
    ∃ (targetType : Ty level targetScope)
      (targetRaw : RawTerm targetScope)
      (targetTerm : Term targetCtx targetType targetRaw),
      HEq sourceTerm (Term.rename strengthening.toTermRenaming targetTerm) := by
  exact ⟨result.targetType, result.targetRaw, result.targetTerm,
    weaken_inv_of_strengthenTyped?_some strengthening result success⟩

end Term

end LeanFX2
