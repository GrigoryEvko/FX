import LeanFX2.Foundation.PolyCell.Core.RawCell

/-! # Foundation/PolyCell/Core/HasEqualDim — value-level dim reconciliation

This file ships the propext-free dim-equality predicate used by the
certified `PolyCell.generatingCell` constructor to reconcile source
and target endpoints of a dim-(n+1) generating cell.  The whole point
of v2's un-indexed raw layer (`RawCell scope` carries no dim type
index) is that dim is a COMPUTED value (`RawCell.dim : ... → Nat`),
so dim equality reduces to `Nat` equality, decidable by `Nat.decEq`.

## The SPIKE-1 pattern (recapped)

v1's `PolyTerm profile : Nat → Type` was dim-indexed.  Reconciling two
cells' dims at the type level required equation-compiler reasoning on
the Nat index, which leaked `propext` through `noConfusion` over
constructor-vs-index mismatches.  Two attempts (TCB.7d / TCB.7f) hit
this wall.

v2 dissolves the trap by un-indexing the raw layer: `RawCell` carries
no dim index, dim is `def RawCell.dim : RawCell scope → Nat` (a
computed function), and "two cells have the same dim" is
`source.dim = target.dim` — vanilla `Nat` equality.  `Nat.decEq` is
zero-axiom; the resulting `Decidable (HasEqualDim ...)` instance is
zero-axiom; downstream `▸` transports built from this proof are
zero-axiom.

The SPIKE-1 spike confirmed empirically (see `SpikeDimTransport.lean`)
that value-level `(boundary, cert)` transport over this equality is
propext-clean.  This file ships the predicate that the spike
demonstrated.

## Why a named predicate rather than just `Eq` directly

Three reasons:

1. **Spec alignment.**  `polycell.md` §4's `PolyCell.generatingCell`
   constructor takes `HasEqualDim source target` as an explicit
   parameter, not raw `source.dim = target.dim`.  The name makes the
   intent explicit at the call site.

2. **Forward-compat per-profile.**  A future profile may refine
   `HasEqualDim` to also require sort agreement or scope coercibility.
   The named predicate gives one refinement point that flows through
   every downstream consumer; raw `Eq` would require global edits.

3. **Readability discipline.**  Per the WORKING_RULES.md telling-word
   rule, predicates start with `has`/`is`/etc. — `HasEqualDim` reads as
   a sentence fragment in the type signature.

## Why `@[reducible]` and `Prop`

* `@[reducible]` lets downstream code transparently unfold to the
  underlying `Eq` when needed (e.g., for `▸` transport in the SPIKE-1
  pattern), without manual unfolding.  The abstraction is a NAMING
  choice, not a strict barrier.

* `Prop` not `Type` because dim equality has no computational content
  worth tracking — the proof is proof-irrelevant (only one inhabitant
  exists for any true `n = n`).  The decision lives in the `Decidable`
  instance, which is the standard Lean idiom for decidable
  propositions.

## The decision interface

`Decidable (HasEqualDim source target)`, not `Option`-valued, because
the Lean idiom for "decidable Prop" is `Decidable` — it returns the
decision *and* the proof when true.  The instance reduces to
`Nat.decEq source.dim target.dim`; `Nat.decEq` is zero-axiom.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Two raw cells at the same scope have equal computed dimension.

Defined as `Nat` equality on `RawCell.dim`.  The certified
`PolyCell.generatingCell` constructor takes this as a parameter so
that source and target endpoints (both raw, computed dims potentially
distinct) can be uniformly typed at `source.dim` in the certified
layer — the equation enables a `▸` transport.

`@[reducible]` lets `▸` transports built from this equation reduce
through downstream code without explicit unfolding. -/
@[reducible] def HasEqualDim {scope : Nat}
    (source target : RawCell scope) : Prop :=
  source.dim = target.dim

/-- `HasEqualDim` is decidable: it's `Nat` equality on the computed
dims, decided by `Nat.decEq` which is zero-axiom.  This is the
SPIKE-1 propext-clean discipline made concrete — no equation-compiler
on a Nat type index, just value-level `Nat.decEq`. -/
instance hasEqualDim_decidable {scope : Nat}
    (source target : RawCell scope) :
    Decidable (HasEqualDim source target) :=
  Nat.decEq source.dim target.dim

/-- Reflexivity.  Every cell has equal dim with itself.

Proof: `rfl` on the underlying `Eq`.  Useful for downstream code that
constructs an `HasEqualDim cell cell` witness without unfolding. -/
theorem HasEqualDim.refl {scope : Nat} (cell : RawCell scope) :
    HasEqualDim cell cell :=
  rfl

/-- Symmetry.  Flips source and target without losing the equation.

Useful when the certifier wants to apply `▸` in the reverse direction
(transport from target's dim to source's dim instead of the other
way).

`Eq.symm` is named explicitly rather than via dot notation because the
`HasEqualDim` namespace shadows `Eq` for dot-resolution, which would
make `equation.symm` self-recursive on `HasEqualDim.symm` (the thing
we're defining) before falling back to `Eq.symm`. -/
theorem HasEqualDim.symm {scope : Nat}
    {source target : RawCell scope}
    (equation : HasEqualDim source target) :
    HasEqualDim target source :=
  Eq.symm equation

/-- Transitivity.  Chains equations through an intermediate cell.

Useful when a certifier sub-call returns `HasEqualDim a b` and another
returns `HasEqualDim b c`, and we need `HasEqualDim a c` to certify a
3-cell composite.

`Eq.trans` is named explicitly for the same dot-resolution-shadowing
reason as `HasEqualDim.symm`. -/
theorem HasEqualDim.trans {scope : Nat}
    {firstCell middleCell lastCell : RawCell scope}
    (firstToMiddle : HasEqualDim firstCell middleCell)
    (middleToLast : HasEqualDim middleCell lastCell) :
    HasEqualDim firstCell lastCell :=
  Eq.trans firstToMiddle middleToLast

/-- Identity over `RawCell.dim`: two cells have equal `HasEqualDim`
exactly when their computed dims are equal.

This is `Iff.rfl` since `HasEqualDim` IS `source.dim = target.dim` by
`@[reducible]` unfolding — but the named lemma documents the
relationship for readers and gives a citation point for downstream
proofs that want to rewrite from `HasEqualDim` into raw `Eq` on dims
or vice versa. -/
theorem HasEqualDim.iff_dim_eq {scope : Nat}
    (source target : RawCell scope) :
    HasEqualDim source target ↔ source.dim = target.dim :=
  Iff.rfl

end LeanFX2.Foundation.PolyCell.Core
