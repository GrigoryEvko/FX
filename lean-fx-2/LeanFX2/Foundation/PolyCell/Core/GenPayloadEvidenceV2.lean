import LeanFX2.Foundation.PolyCell.Core.GeneratorCore

/-! # Foundation/PolyCell/Core/GenPayloadEvidenceV2 — payload admission

This file ships the v2 per-generator payload-evidence layer:
`GenPayloadEvidence generator scope payload : Type`.  The discipline
is honest about what v2's payload-TYPE-level structure already enforces
versus what genuine evidence would need to add.

## What the payload type already enforces (no evidence needed)

Under v2, `Generator.payload : Generator → Nat → Type` selects one of
three payload shapes per generator:

* `gen_var → Fin scope` — scope safety is **structural by
  construction**.  `Fin scope` has no out-of-bounds inhabitants, so
  v1's `index < scope` side condition has no v2 analog.  The polycell.md
  §4 spec confirms this explicitly: *"var's index < scope is now
  structural via the Fin scope payload"*.

* `gen_universeCode → Nat` (universe level for `Universe ℓ` codes) and
  `gen_truncIntro / gen_truncCoh / gen_truncRec → Nat` (truncation
  level).  Any natural number is admissible under the default
  `fxProfile`.  Future restricted profiles may add bounds:
  `maxUniverse < 64` for safety-critical embedded targets, or
  `truncLevel ≥ -2` for h-level discipline (encoded as `Nat`).

* All other 188 generators have `Unit` payload — only one inhabitant,
  trivially admissible.

## Why GenPayloadEvidence is still a parameter on PolyCellV2.gen

Even though the current discipline is trivial, `PolyCellV2.gen` keeps
the `GenPayloadEvidence` parameter as an explicit permission slot.
This decouples the certified-cell signature from the per-profile
discipline: a restricted profile refines the `GenPayloadEvidence` body
without changing the constructor signature, the certifier, or any
downstream consumer.

## Design: Type-valued, currently Unit

Under `fxProfile`, the discipline is trivial — no payload constraint
beyond the type-level shape.  So `GenPayloadEvidence` is `Type`-valued
and defined as `Unit`.

**Why Type-Unit and not Prop-True**: `Option` (used in
`genPayloadEvidence?`) requires a `Type` argument, not a `Prop` — so
the `?` decision wrapper forces the Type universe.  `Unit` has exactly
one inhabitant (`()`), giving us the same "trivially admissible"
semantics as `True` would in Prop, while keeping `Option ...`
well-formed.  When a future restricted profile genuinely needs
discrimination, this lifts cleanly to a multi-constructor inductive in
the same Type universe.

**Consistency with `SupportedGeneratorV2`**: both admission layers now
live at Type (`SupportedGeneratorV2 : Generator → Type` and
`GenPayloadEvidence : ... → Type`).  The certifier's interface is
uniform across the two layers.

## Two decision interfaces

* `genPayloadEvidence` is the total, fxProfile-default constructor —
  every payload admitted, returns the trivial witness `()`.

* `genPayloadEvidence?` is the Option-valued decision (#142).  Under
  fxProfile, always `some ()`.  Restricted profiles return `none` for
  rejected payloads.  Wrapping in Option keeps the certifier's
  per-profile interface uniform.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Per-generator payload-admission Type, parameterized by
`(generator, scope, payload)`.  Trivially `Unit` under the default
`fxProfile` (the payload TYPE-level discipline is the only current
constraint).  Future restricted profiles refine the body to a real
multi-constructor inductive without changing the `PolyCellV2.gen`
signature.

The `@[reducible]` attribute lets downstream code unfold this
definition during type-checking, so `genPayloadEvidence` returning
`()` and `genPayloadEvidence?` returning `some ()` both reduce to
canonical forms without manual unfolding. -/
@[reducible] def GenPayloadEvidence (generator : Generator) (scope : Nat)
    (_payload : generator.payload scope) : Type :=
  Unit

/-- The total fxProfile-default constructor: every payload is admitted.

Currently returns `()` — the unique inhabitant of `Unit`.  Under a
restricted profile this becomes a partial function and the case
analysis lives in `genPayloadEvidence?`.  Naming follows the
`SupportedGeneratorV2`/`supportedGeneratorV2` pair — the un-`?`'d form
is the unconditional admission, the `?` form is the Option wrapper. -/
@[reducible] def genPayloadEvidence {generator : Generator} {scope : Nat}
    (payload : generator.payload scope) :
    GenPayloadEvidence generator scope payload :=
  ()

/-- Option-valued payload-admission decision (#142).  Under
`fxProfile`, always `some ()` (every payload admitted).  Restricted
profiles return `none` for rejected payloads.

Returning `Option` rather than a bare witness keeps the certifier's
contract uniform across profiles: `match genPayloadEvidence? payload
with | some evidence => admit ... | none => reject .badPayload`.  For
the current default, the `none` branch is dead code, but the interface
is forward-compatible without a rewrite when a future profile adds
constraints. -/
@[reducible] def genPayloadEvidence? {generator : Generator} {scope : Nat}
    (payload : generator.payload scope) :
    Option (GenPayloadEvidence generator scope payload) :=
  some (genPayloadEvidence payload)

/-- The payload-admission decision is always `some` under the default
`fxProfile`.  Proof: `rfl` — both `genPayloadEvidence?` and `.isSome`
reduce definitionally on `some _`.  Future restricted-profile variants
of this lemma will instead state which payloads admit (a refined
predicate or per-Generator case analysis); the trivial lemma here
locks in fxProfile's current "all admitted" behavior. -/
theorem genPayloadEvidence?_isSome {generator : Generator} {scope : Nat}
    (payload : generator.payload scope) :
    (genPayloadEvidence? payload).isSome = true :=
  rfl

end LeanFX2.Foundation.PolyCell.Core
