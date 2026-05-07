/-! # Modal/Cohesive

Day 0 scaffold for cohesive modalities.

## Status

**BLOCKED on Phase 12.A.6+ infrastructure** (tracker #1331 D4.4).
The cohesive `♭` (flat) and `♯` (sharp) modalities form a
fundamentally cross-mode pair:

* `♭ : Modality .software .ghost` — flat / discrete reflection
  (forgets continuous structure, lands in pointwise/static mode)
* `♯ : Modality .ghost .software` — sharp / codiscrete coreflection
  (lifts discrete content to continuous mode trivially)

Required prerequisites:

1. **Cross-mode `Modality` ctors** — `.flat` and `.sharp` (currently
   `Modality` carries only same-mode endomorphic ctors).
2. **Cross-mode `compose`** — extending the 9-case same-mode
   composition table to handle heterogeneous source/target modes.
3. **TwoCell** — to express `♭ ⊣ ♯` as adjunction with η/ε natural
   transformations.

## What WILL ship when prerequisites land

* `Modality.flat : Modality .software .ghost`
* `Modality.sharp : Modality .ghost .software`
* `flatAdjSharp : Adjoint Modality.flat Modality.sharp`
* Idempotency: `compose flat (compose sharp flat) = flat` and
  symmetric for sharp.
* Discrete and codiscrete reflection laws.

## Deliverable until then

Documented placeholder.  See `Modal/Adjunction.lean` for the full
Phase 12.A.6+ prerequisite catalogue.
-/

namespace LeanFX2
namespace Modal

end Modal
end LeanFX2
