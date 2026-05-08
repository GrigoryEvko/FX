import LeanFX2.Modal.Foundation

/-! # Modal/Ghost — the ghost (compile-time-only) modality

The ghost modality marks data as **compile-time only** — present in
typing but erased at runtime.  It is the canonical static-layer
modality of FX's two-level type theory (per `fx_design.md` §6.3 and
the 2LTT layering documented in `Modal/TwoLevel.lean`).

## What ships here (Phase 12.A.4 — D4.7-Ghost)

* `Modality.ghost : Modality Mode.ghost Mode.ghost` — the ghost
  modality as `Modality.boxK Mode.ghost`.  Same-mode endomorphic
  necessitation at the static layer.
* Idempotency `ghost ; ghost = ghost` (by `rfl` — inherited from
  `compose_boxK_idempotent`).
* Identity-composition laws (`ghost ; identity = ghost`,
  `identity ; ghost = ghost`).
* Diamond-absorption smoke (`ghost ; diamondK ghost = ghost` —
  `boxK` wins from the left per the composition table in
  `Modal/Foundation.lean`).

## Why same-mode

Per `Modal/Foundation.lean` Phase 12.A.5 commitment: cross-mode
modalities (`flat : ghost → software`, `sharp : software → ghost`)
ship in Phase 12.A.6 alongside the full adjoint chain
`♭ ⊣ ◇ ⊣ □ ⊣ ♯`.  The ghost-erase adjunction stated in the
previous-iteration Ghost.lean docstring is one of those cross-mode
pairs and is intentionally NOT shipped here.

What ships here is the SAME-MODE handle — the `Mode.ghost` instance
of `boxK` — usable by any code that needs to denote "necessitate at
the ghost layer" without waiting for the cross-mode infrastructure.

## Erasure semantics

In compiled FX, values of type `Ty.modal Modality.ghost innerTy`
are *not emitted* — they exist only at typing time.  This
corresponds to fx_design.md's "ghost" effect (§9.4) and to the
ghost grade (Appendix C, `0` in the usage semiring).  The
`Mode.ghost` mode tag carries the layer-static discipline forward
to consumers.

## Dependencies

* `Modal/Foundation.lean` — provides `Modality` and
  `Modality.compose` plus the laws this file inherits.

## Downstream consumers

* `Modal/2LTT.lean` — 2LTT layer separation references ghost (per
  the `TwoLevel.lean` docstring's "ghost is the unique static
  mode" claim).
* User-level erased proofs / compile-time annotations once
  `Term.modal` ships.

Zero-axiom verified per declaration (`#assert_no_axioms` via the
namespace sweep `#audit_namespace LeanFX2`).

## Root status

* Layer: typed-derived
* Load-bearing for: none — pure-derivation file (currently only re-exposed via Rich.lean aggregation)
* Axiom budget: zero (verified via `#assert_no_axioms` in Tools/AuditAll/)
-/

namespace LeanFX2

namespace Modality

/-- The ghost modality: same-mode necessitation at `Mode.ghost`.
Erased at runtime; lives only in the typing layer.

Defined as `boxK Mode.ghost` so all the box-class laws (idempotency,
identity laws, absorption) lift to ghost without re-proof. -/
def ghost : Modality Mode.ghost Mode.ghost :=
  Modality.boxK Mode.ghost

/-- The ghost modality is idempotent under composition.

`ghost ; ghost = ghost` — boxing twice is the same as boxing once.
Inherited from `compose_boxK_idempotent` and discharged by `rfl`. -/
theorem ghost_idempotent :
    compose ghost ghost = ghost :=
  rfl

/-- Composing the ghost modality with the identity on the right
returns ghost. -/
theorem ghost_compose_identity_right :
    compose ghost (Modality.identity Mode.ghost) = ghost :=
  rfl

/-- Composing the identity on the left with the ghost modality
returns ghost. -/
theorem ghost_compose_identity_left :
    compose (Modality.identity Mode.ghost) ghost = ghost :=
  rfl

/-- The ghost modality absorbs `diamondK` to its right.

Per the composition table in `Modal/Foundation.lean`, `boxK`
absorbs from the left: `boxK ; X = boxK` for any `X`.  Specialised
to `X = diamondK Mode.ghost` and rewriting `boxK Mode.ghost` to
`ghost` gives this absorption smoke. -/
theorem ghost_absorbs_diamond :
    compose ghost (Modality.diamondK Mode.ghost) = ghost :=
  rfl

end Modality

/-! ## Smoke samples -/

/-- The ghost modality is `boxK Mode.ghost` definitionally. -/
example : Modality.ghost = Modality.boxK Mode.ghost := rfl

/-- Ghost is idempotent — direct application of the idempotency
theorem. -/
example :
    Modality.compose Modality.ghost Modality.ghost = Modality.ghost :=
  Modality.ghost_idempotent

/-- Ghost composed with itself three times remains ghost (associativity
plus idempotency). -/
example :
    Modality.compose
      (Modality.compose Modality.ghost Modality.ghost)
      Modality.ghost
      = Modality.ghost := rfl

end LeanFX2
