import FX.Kernel.Grade.Tier

/-!
# Provenance (dimension 8) — data origin tracking

Per `fx_design.md` §6.3 (dim 8).  Tier S (infinite carrier).

The design spells the lattice as `Source(name)`,
`Derived(parent, transform)`, `Aggregated(list)`, `Unknown`.
The Phase-1 kernel simplifies the shape as follows:

  * `source n`       — data came from origin named by index `n`.
                       Names are interned into a registry at
                       elaboration time; the kernel only sees
                       the `Nat` index.
  * `derived p`      — computed from data whose provenance is
                       `p`.  The design's `transform` field is
                       **deferred in Phase 1** — the kernel does
                       not reason about transforms (they are
                       opaque, like `Derived(parent, _)` with
                       the transform hidden), so carrying the
                       transform here buys nothing at this
                       layer.  Phase 2+ will thread transform
                       identities when provenance-aware
                       optimizations need them.
  * `aggregated ps`  — combined from multiple origins.  The
                       strict-positivity on `List Provenance` is
                       fine (only appears in the `aggregated`
                       constructor).
  * `unknown`        — untracked; the top of the lattice.

## Combining — `add`

Parallel combine joins provenance chains.

  * `unknown` is absorbing (top of the lattice): combining any
    provenance with `unknown` produces `unknown`.  Data with no
    traceable origin stays that way.
  * Every other pair `a, b` aggregates to `aggregated [a, b]`
    **without flattening and without idempotence**.  This is a
    deliberate Phase-1 simplification: `Provenance` cannot
    derive `DecidableEq` (the recursion through
    `List Provenance` would require a mutual `DecidableEq`
    derivation), so `add` cannot cheaply test `a = b`.  The
    result is that `add (source 0) (source 0)` is
    `aggregated [source 0, source 0]`, not `source 0` —
    structurally different, but semantically equivalent (both
    say "comes from source 0").  A normalization pass (flatten
    + dedupe) is expected at elaboration time, not inside this
    algebra.

Functions requiring known provenance (`requires provenance !=
unknown`) reject the `unknown` top.

## Subsumption `LessEq`

  * `refl`  — every provenance is `≤` itself.
  * `leTop` — every provenance is `≤ unknown`.

At the kernel level the lattice is shallow; deeper structural
reasoning (e.g., `source s ≤ derived (source s)` when the
elaborator knows the transform preserves origin identity) is
left to the elaborator, which supplies extra hypotheses.
-/

namespace FX.Kernel

/--
A provenance tag.  The recursion through `List Provenance` is
strictly positive (only in `aggregated`), so Lean accepts the
declaration.

Note: `DecidableEq` is intentionally not derived — see the
module docstring on non-idempotent `add`.
-/
inductive Provenance : Type where
  | source     : Nat → Provenance
  | derived    : Provenance → Provenance
  | aggregated : List Provenance → Provenance
  | unknown    : Provenance
  deriving Repr

namespace Provenance

/--
Structural equality as a `Bool`.  We do not derive `DecidableEq`
because the recursion through `List Provenance` inside the
`aggregated` constructor would require a mutual derivation that
Lean's auto-deriver cannot produce.  Downstream callers
(`Grade.beq`, kernel conversion) invoke this explicitly.

`partial` because structural termination across `List.zipAll`
is not seen by the checker; every call strictly decreases the
tree height, so termination is trusted.
-/
partial def beq : Provenance → Provenance → Bool
  | .source leftIndex,      .source rightIndex      => leftIndex == rightIndex
  | .derived leftInner,     .derived rightInner     => beq leftInner rightInner
  | .aggregated leftChain, .aggregated rightChain =>
    leftChain.length == rightChain.length ∧
      (leftChain.zip rightChain).all (fun pair => beq pair.1 pair.2)
  | .unknown,       .unknown       => true
  | _,              _              => false

/--
`BEq` instance so downstream users can write `p == q` directly.
Equality is structural; see `beq`'s docstring for why there is
no `DecidableEq`.
-/
instance : BEq Provenance := ⟨beq⟩

/--
Parallel combine.

  * `unknown` is absorbing (top of the lattice).
  * Any other pair aggregates into a two-element list.

No flattening, no idempotence — see module docstring.  The
kernel accepts structurally-distinct-but-semantically-equivalent
aggregates; elaborator-level normalization is responsible for
canonicalization.
-/
def add : Provenance → Provenance → Provenance
  | unknown, _ => unknown
  | _, unknown => unknown
  | leftProvenance, rightProvenance => aggregated [leftProvenance, rightProvenance]

/-- Sequential combine — same aggregation. -/
def mul : Provenance → Provenance → Provenance := add

/--
Subsumption: reflexive plus `≤ unknown` absorption.  The kernel
does not enumerate structural embedding of `derived` or
`aggregated`; the elaborator supplies those as hypotheses.
-/
inductive LessEq : Provenance → Provenance → Prop where
  | refl  : ∀ provenance, LessEq provenance provenance
  | leTop : ∀ provenance, LessEq provenance unknown

instance : LE Provenance := ⟨LessEq⟩

theorem LessEq.trans {lower middle upper : Provenance} (hypLowerMiddle : lower ≤ middle) (hypMiddleUpper : middle ≤ upper) :
    lower ≤ upper := by
  cases hypLowerMiddle with
  | refl  => exact hypMiddleUpper
  | leTop =>
    cases hypMiddleUpper with
    | refl  => exact LessEq.leTop _
    | leTop => exact LessEq.leTop _

/-! ### Absorption laws for `unknown` -/

theorem unknown_add (provenance : Provenance) : add unknown provenance = unknown := by
  cases provenance <;> rfl

theorem add_unknown (provenance : Provenance) : add provenance unknown = unknown := by
  cases provenance <;> rfl

/-- `mul` is the same join, so absorption transports unchanged. -/
theorem unknown_mul (provenance : Provenance) : mul unknown provenance = unknown := unknown_add provenance

theorem mul_unknown (provenance : Provenance) : mul provenance unknown = unknown := add_unknown provenance

end Provenance

/-! ## GradeCarrier instance (no TierS — see T6a audit)

Provenance CANNOT instance even the base `TierS` class: its Phase-1
`add` is non-commutative (`aggregated [a, b] ≠ aggregated [b, a]`)
and has no additive identity (nothing `ε` satisfies `add ε x = x`
for arbitrary `x` — `unknown` absorbs, not identifies).  The spec
§6.3 classifies Provenance as Tier S, but the current kernel realises
only a carrier preorder (plus aggregation), not the algebraic
laws `TierS` demands.

Phase 2 can tighten the kernel toward the spec: either swap the
ordered-list carrier for a multiset (restoring commutativity and an
empty-multiset identity) or treat `aggregated`'s list as a
canonicalized sorted form (restoring both).  Until then, Provenance
provides `GradeCarrier` only; any tier-generic aggregate theorem
over `TierS` will need a separate, Provenance-specific instantiation. -/
instance : GradeCarrier Provenance where
  default  := Provenance.unknown
  le       := Provenance.LessEq
  le_refl  := Provenance.LessEq.refl
  le_trans := Provenance.LessEq.trans

end FX.Kernel
