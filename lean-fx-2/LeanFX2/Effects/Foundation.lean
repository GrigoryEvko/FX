import LeanFX2.Foundation.Effect

/-! # Effects/Foundation — effect labels, rows, and subset preorder

The effect-row primitives live in `LeanFX2.Foundation.Effect` so the
raw-aware `Term` kernel can require row-permission evidence without an
upward import into the richer `Effects` layer.

This module is the Effects-layer re-export point.  Row-level operational
semantics live in `Effects.Step`; handlers live in `Effects.Handlers`.

## What defers

* Full `Ty.effect` row schema and `effectHandle` beta rules — the
  term-level `effectPerform` constructor already requires row permission
  evidence, but the type-level effect tag is still raw.
* User-defined effects, effect handlers with continuations, and
  per-platform effect availability.
-/
