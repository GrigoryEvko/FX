import LeanFX2.Modal.Foundation

/-! # Modal/Cohesive — cohesive ♭ (flat) and ♯ (sharp) modalities

The cohesive flat and sharp modalities form a fundamentally
cross-mode pair encoding discrete reflection and codiscrete
coreflection.  Per Shulman's *Real Cohesion* (2018,
arXiv:1509.07584) and Sikkel POPL'25 (BiSikkel, presheaf
cohesion):

* `Modality.flat : Modality Mode.software Mode.ghost` — discrete
  reflection.  Forgets continuous structure and lands in the
  static / pointwise mode.
* `Modality.sharp : Modality Mode.ghost Mode.software` — codiscrete
  coreflection.  Lifts discrete content into the continuous mode
  trivially.

Both ctors live in `Modal/Foundation.lean` (Modality inductive,
Phase 12.A.6 cross-mode extension).  The full adjoint chain
`♭ ⊣ ◇ ⊣ □ ⊣ ♯` is incremental — pentagon coherence + counit/
unit triangles ship when `Modal/Adjunction.lean`'s TwoCell
infrastructure lands.

## What ships here (Phase 12.A.6 — cross-mode constructor handles)

* `flat_uniqueness` — every `Modality Mode.software Mode.ghost`
  equals `Modality.flat`.  Constructor-uniqueness theorem
  established by full case enumeration; impossible-by-index
  ctors (identity / boxK / diamondK / sharp) discharged by
  Lean's structural matcher without propext.
* `sharp_uniqueness` — symmetric statement for sharp.
* Smoke samples confirming type assignments.

## Constructor uniqueness — why it matters

`Modality Mode.software Mode.ghost` is the type of cross-mode
arrows from software to ghost.  Among the five Modality ctors,
only `flat` inhabits this index pair:

| Ctor       | Source mode  | Target mode  | Inhabits .software .ghost? |
|------------|--------------|--------------|----------------------------|
| identity m | m            | m            | NO (would need m = software AND m = ghost) |
| boxK m     | m            | m            | NO (same reason)           |
| diamondK m | m            | m            | NO (same reason)           |
| flat       | software     | ghost        | YES                        |
| sharp      | ghost        | software     | NO (wrong direction)       |

Hence `flat_uniqueness`.  Symmetric reasoning gives
`sharp_uniqueness`.  These are the structural foundation for
later adjoint-chain reasoning: any cross-mode handle in either
direction MUST be the canonical ctor — no anonymous cross-mode
modalities exist at the kernel level.

## What is NOT shipped here

Cross-mode `compose` and the adjoint-chain laws (`flat ⊣ sharp`
unit / counit / triangles) require:

1. **TwoCell** — to express η/ε as natural transformations rather
   than 1-cell label equalities.  Documented in
   `Modal/Adjunction.lean` docstring.
2. **Cross-mode `composeOpen`** — generalising the same-mode
   `compose : Modality m m → Modality m m → Modality m m` to
   `Modality s m → Modality m t → Modality s t`.  Decisions on
   the cross-mode table (e.g. `compose flat sharp = ?`) are
   adjunction-determined; without TwoCells we cannot disambiguate.

These ship in subsequent Phase 12.A.6 increments (D4.2, D4.5).

## Dependencies

* `Modal/Foundation.lean` — provides `Modality` and the
  `flat` / `sharp` cross-mode ctors.

## Downstream consumers

* `Modal/Adjunction.lean` — `flat ⊣ sharp` adjunction (pending
  TwoCell).
* `Modal/Bridge.lean` — strict / observational / univalent
  transfer (pending mode-bridge equivalences).

## Root status

* Layer: typed-derived
* Load-bearing for: Smoke/AuditPhase12A6CohesiveCtors
* Axiom budget: zero (verified via `#assert_no_axioms` in Tools/AuditAll/)
-/

namespace LeanFX2

namespace Modality

/-! ## Cross-mode constructor uniqueness

`Modality.flat` is the unique inhabitant of
`Modality Mode.software Mode.ghost`; `Modality.sharp` is the
unique inhabitant of `Modality Mode.ghost Mode.software`.  Proved
by full case enumeration on the five Modality ctors. -/

/-- The flat modality is the unique inhabitant of
`Modality Mode.software Mode.ghost`.

Proof: full case-on-modality.  The same-mode ctors
(`identity` / `boxK` / `diamondK`) are parametric in a single
`someMode`, so inhabiting `Modality Mode.software Mode.ghost`
would require `someMode = Mode.software ∧ someMode = Mode.ghost`,
contradicting the closed-enum disjointness.  `sharp`'s index
pair is the reverse direction.  Only `flat` matches the target
index pair, giving `rfl`. -/
theorem flat_uniqueness (someModality : Modality Mode.software Mode.ghost) :
    someModality = Modality.flat := by
  match someModality with
  | Modality.flat => rfl

/-- The sharp modality is the unique inhabitant of
`Modality Mode.ghost Mode.software`.

Symmetric to `flat_uniqueness`. -/
theorem sharp_uniqueness (someModality : Modality Mode.ghost Mode.software) :
    someModality = Modality.sharp := by
  match someModality with
  | Modality.sharp => rfl

/-! ## Type-level smoke samples

These confirm the ctor's mode signature is exactly as declared. -/

/-- `Modality.flat` has source mode `software`, target mode
`ghost`. -/
example : Modality.flat = (Modality.flat : Modality Mode.software Mode.ghost) := rfl

/-- `Modality.sharp` has source mode `ghost`, target mode
`software`. -/
example : Modality.sharp = (Modality.sharp : Modality Mode.ghost Mode.software) := rfl

/-- Round-trip through the uniqueness theorem at flat. -/
example : flat_uniqueness Modality.flat = rfl := rfl

/-- Round-trip through the uniqueness theorem at sharp. -/
example : sharp_uniqueness Modality.sharp = rfl := rfl

end Modality

end LeanFX2
