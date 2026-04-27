/-!
# Grade tier classes — spec §6.3 reconciled against actual kernel shape

Per `fx_design.md` §6.3 the 21 grade dimensions split across FIVE
distinct algebraic tiers:

  * **Tier S** (15 dims): claimed "commutative semiring" in the spec.
    T6a audit (see docstrings below) discovered that only ONE of the
    fifteen — Usage — actually satisfies the strict semiring laws
    (`0 * x = 0` annihilation).  The other fourteen are lattice-shaped
    or additive-monoid-shaped in the kernel.  This file reflects that
    reality via a hierarchy: `TierS ⊂ TierSComm ⊂ TierSIdem / TierSRing`.
  * **Tier L** (2 dims): lattice with validity predicate.
  * **Tier T** (1 dim): typestate — transitions; no grade arithmetic laws.
  * **Tier F** (2 dims): foundational — discharged by elaboration.
    No class (by design — blocking meta-theorems that quantify over
    "every tier" from claiming anything about Type / Refinement).
  * **Tier V** (1 dim): versioned lattice with adapter edges.

## T6a — why Tier S is a hierarchy, not a single class

Of the 15 spec-Tier-S dimensions, the actual kernel shapes are:

```
Usage (3)         {0,1,ω} tables               TierSRing  (strict semiring)
Effect (4)        pointwise OR on 8-tuple       TierSIdem  (add=mul=join)
Security (5)      2-elt join                    TierSIdem  (add=mul=join)
Trust (9)         5-elt min (meet)              TierSIdem  (add=mul=meet)
Observability(11) 2-elt meet                    TierSIdem  (add=mul=meet)
FpOrder (17)      2-elt max                     TierSIdem  (add=mul=join)
Mutation (18)     4-elt join                    TierSIdem  (add=mul=join)
Reentrancy (19)   2-elt join                    TierSIdem  (add=mul=join)
Complexity (13)   Nat, (+,+)                    TierSComm  (no idem, no annihilator)
Precision (14)    Nat, (+,+)                    TierSComm  (same)
Space (15)        Nat, (+,+)                    TierSComm  (same)
Size (20)         (max, +) over ω∪Nat          TierSComm  (asymmetric; no annihilator)
Overflow (16)     partial join                  TierL      (reclassified — partial)
Lifetime (7)      join-to-static, NO unit       NO instance (class requires zero)
Provenance (8)    ordered-list aggregate        TierS       (non-commutative mul)
```

Rationale for each demotion from the spec's strict TierSRing:

  * **The 7 `TierSIdem` dims** all set `mul := add := join-or-meet`.  Their
    identity element is NOT a mul-annihilator — for a join lattice
    `0 ∨ x = x`, not `0`.  A strict `zero_mul` claim would fail.  But
    they DO satisfy idempotence and `mul = add`, which the idem subclass
    captures.

  * **The 4 `TierSComm` dims** (Complexity/Precision/Space/Size) use Nat
    arithmetic with `mul := add`.  They have an additive identity
    (`0`/`finite 0`) but no mul-annihilator (`0 + x = x`, not `0`).
    Size is asymmetric: `add := max`, `mul := Nat.+`; both idempotent
    for add, neither admits annihilation.  All four live in `TierSComm`
    but deliberately do NOT satisfy `TierSIdem`'s `mul_eq_add` in the
    Size case, or `add_idem` in the Nat-trio case.

  * **Usage** is the ONE true `TierSRing`.  `{0, 1, ω}` with distinct
    `+` and `*` tables.  `0 * x = 0` genuinely.

  * **Lifetime** cannot be instanced at Tier S level because its `add`
    has no unit: `static + x = static` (absorbing), and `var n` has no
    right identity.  Treated as a semilattice; tier-S membership is
    nominal.

  * **Provenance** in Phase 1 uses ordered-list aggregation
    (`aggregated [a, b] ≠ aggregated [b, a]`).  Non-commutative.
    Lives in `TierS` (base class with no mul_comm) only.

The design doc's §6.3 classification ("15 Tier S dims") thus
over-states soundness for the 14 non-Usage dims.  This file honestly
exposes the algebraic structure as tier-class membership; future spec
refinement (or Phase 2+ kernel upgrades) can add strict annihilation
laws to specific dims and tighten the tier membership.

## Axiom footprint

Zero.  Type classes + universally-quantified propositions over the
methods.  Not a Mathlib dependency.  The kernel audit invariant
(no axioms outside AXIOMS.md's 33-entry allowlist) is preserved.

## Instancing discipline

  * A dim's instance declaration should be the STRONGEST tier class
    its kernel actually satisfies.  `Usage` instances `TierSRing`;
    `Effect` instances `TierSIdem`; `Complexity` instances `TierSComm`;
    `Provenance` instances only `TierS`.
  * The `extends` chain means each stronger class automatically
    provides all weaker classes' fields — so generic theorems over
    `TierS` also apply to `TierSRing`-instanced dims.
  * Aggregate theorems in `Grade.lean` (T7) should target the widest
    applicable class.  `Grade.add_comm` targets `TierS`; a strict
    `Grade.add_zero_mul` would target `TierSRing` and apply only to
    Usage's component.

## What does NOT belong here

  * Instances — those are T2-T5 in per-dim files.
  * Aggregate theorems — those go in Grade.lean (T7).
  * Decidable instances beyond what `extends GradeCarrier` provides.
  * Antisymmetry — preorder is the base; partial order is per-dim.
-/

namespace FX.Kernel

/-- Tier tag — useful as a reflection helper or for case analysis
    over tiers when quantifying meta-theorems.  Typical code
    dispatches via the tier *classes* below rather than this tag
    directly; the enum is for diagnostics and tooling. -/
inductive Tier : Type where
  /-- Commutative semiring family — strict `S_Ring`, idempotent
      `S_Idem`, nat-monoid `S_Comm`, non-commutative `S_Base`. -/
  | S : Tier
  /-- Lattice with validity predicate. -/
  | L : Tier
  /-- Typestate — transition relation, no semiring laws. -/
  | T : Tier
  /-- Foundational — elaboration-discharged, no grade arithmetic. -/
  | F : Tier
  /-- Versioned lattice with adapter edges. -/
  | V : Tier
  deriving DecidableEq, Repr

/-- Every grade dimension carries a preorder on its carrier for
    §H.9 subsumption checks, plus a canonical "most-restrictive"
    default used at every §1.2 deny-by-default binding.

    This is the base class every tier extends — no dim can be a
    tier member without these. -/
class GradeCarrier (α : Type) where
  /-- Most-restrictive default — the §1.2 deny-by-default
      baseline.  `Grade.default` is the pointwise aggregate of
      these. -/
  default    : α
  /-- Subsumption preorder — `le a b` when `a` is at most as
      permissive as `b`, permitting substitution of a-graded
      values in b-graded positions (§H.9 T-sub). -/
  le         : α → α → Prop
  /-- Reflexivity — required for `Grade.LessEq.refl`. -/
  le_refl    : ∀ a : α, le a a
  /-- Transitivity — required for `Grade.LessEq.trans`. -/
  le_trans   : ∀ {a b c : α}, le a b → le b c → le a c

/-- **Tier S base** — weakest of the Tier-S hierarchy.

    Provides: `(R, +, 0)` commutative monoid; `(R, *)` monoid.
    Does NOT require `mul_comm`, distribution, or annihilation.

    Instances: Provenance (Phase-1 non-commutative aggregate).

    This is the common-denominator that every §6.3 Tier-S dim
    satisfies when its kernel has at least an additive identity.
    (Lifetime, whose kernel has no additive unit, cannot instance
    even this class — §6.3 "Tier S" membership is nominal there.) -/
class TierS (α : Type) extends GradeCarrier α where
  /-- Parallel combine (§6.2 If rule). -/
  add         : α → α → α
  /-- Sequential combine (§6.2 App rule scaling). -/
  mul         : α → α → α
  /-- Additive identity. -/
  zero        : α
  -- Commutative monoid on add
  add_comm    : ∀ a b, add a b = add b a
  add_assoc   : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero    : ∀ a, add a zero = a
  zero_add    : ∀ a, add zero a = a
  -- Monoid on mul (commutativity optional — see TierSComm)
  mul_assoc   : ∀ a b c, mul (mul a b) c = mul a (mul b c)

/-- **Tier S with commutative multiplication** — 13 of 15 spec-
    Tier-S dims qualify (all except Provenance, whose Phase-1 kernel
    uses ordered-list aggregation that is non-commutative, and
    Lifetime, which has no additive unit at all).

    Code that quantifies over `TierSComm` picks up
    `∀ a b, mul a b = mul b a` uniformly.  Strict-semiring laws
    (distributivity, annihilation) live in `TierSRing` — only Usage
    satisfies them.

    Instances: Complexity, Precision, Space, Size (non-idempotent
    Nat-shaped dims).  Idempotent dims refine to `TierSIdem`. -/
class TierSComm (α : Type) extends TierS α where
  /-- Multiplication commutes. -/
  mul_comm    : ∀ a b, mul a b = mul b a

/-- **Tier S idempotent** — 7 of 15 spec-Tier-S dims qualify.

    Witnesses the shape where both parallel and sequential combine
    are the same idempotent join-lattice operation (or, dually,
    meet — Trust and Observability use meet, others use join;
    structurally identical at this class level).

    Defining laws:
      * `add_idem : add a a = a` — idempotence.
      * `mul_eq_add : mul a b = add a b` — `mul` and `add` coincide.

    Together these imply `mul_idem`, degenerate `left_distrib`/
    `right_distrib` (both sides collapse to a three-way join by
    idempotence), and that the identity is ALSO the mul-unit.

    The strict semiring law `zero_mul : mul zero a = zero` does NOT
    hold here (a join lattice's bottom is the additive unit, not a
    mul-annihilator).  Dims requiring annihilation must refine to
    `TierSRing`.

    Instances: Effect, Security, Trust, Observability, FpOrder,
    Mutation, Reentrancy.  (Overflow structurally fits but its
    kernel is partial — classified as Tier L.) -/
class TierSIdem (α : Type) extends TierSComm α where
  /-- Idempotence of add (and, via mul_eq_add, of mul). -/
  add_idem     : ∀ a, add a a = a
  /-- The join/meet lattice shape: mul and add are the same op. -/
  mul_eq_add   : ∀ a b, mul a b = add a b

/-- **Tier S commutative semiring** — STRICT reading of §6.1, with
    genuine multiplicative identity `one`, distributivity, and the
    annihilation property `zero * x = 0`.

    Under the T6a audit, only ONE of the spec's 15 Tier-S dims
    qualifies: **Usage** (the `{0, 1, ω}` semiring with distinct
    `+` and `*` tables).

    All other Tier-S dims either collapse `add = mul` (the 7
    `TierSIdem` dims) or use `mul = add = Nat.+` (Complexity,
    Precision, Space) or use asymmetric `(max, +)` (Size).  None
    of those admit `zero * x = zero` — the additive identity is
    not a multiplicative annihilator.

    A tier-generic theorem requiring strict annihilation (e.g. a
    "ghost computation on secret erases" result per §12.7) should
    quantify over `TierSRing` and will apply only to Usage's
    grade component in `Grade`. -/
class TierSRing (α : Type) extends TierSComm α where
  /-- Multiplicative identity. -/
  one           : α
  /-- `one` is a left mul-unit. -/
  one_mul       : ∀ a, mul one a = a
  /-- `one` is a right mul-unit. -/
  mul_one       : ∀ a, mul a one = a
  /-- Left distribution. -/
  left_distrib  : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  /-- Right distribution (mul may be non-commutative in base `TierS`,
      so both sides are stated independently). -/
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  /-- Zero is the left mul-annihilator — the strict semiring axiom
      that most spec-Tier-S dims fail. -/
  zero_mul      : ∀ a, mul zero a = zero
  /-- Zero is the right mul-annihilator. -/
  mul_zero      : ∀ a, mul a zero = zero

/-- Tier L — lattice with validity.  Per §6.3, 2 dimensions
    qualify: Representation (dim 10), Clock (dim 12).

    `joinOpt` / `meetOpt` return `Option α`: `none` when the
    validity predicate fails (`repr(C)` vs `repr(packed)`,
    `sync(a)` vs `sync(b)` with `a ≠ b`).  Validity is encoded in
    the return type rather than exposed as a separate `valid : α
    → α → Bool` — consumers case-analyse the `Option` at join
    sites.

    Overflow (dim 16) structurally fits this tier even though
    §6.3 classifies it as Tier S; its kernel already uses the
    partial-op shape.  The mismatch is a spec gap (§6.8 catalog
    will reclassify in Phase 2).

    Idempotence is required because §H.8 Grade-lattice says
    `x ∨ x = x` at every lattice point — a lattice without
    idempotence is a weaker structure.  Meet idempotence is
    likewise true but we only require join-idem here to keep the
    class minimal; dims that prove meet-idem expose it as a
    per-dim theorem. -/
class TierL (α : Type) extends GradeCarrier α where
  /-- Parallel combine — lattice join, partial. -/
  joinOpt        : α → α → Option α
  /-- Sequential combine — lattice meet, partial. -/
  meetOpt        : α → α → Option α
  /-- Join commutes. -/
  joinOpt_comm   : ∀ a b, joinOpt a b = joinOpt b a
  /-- Join is idempotent (validity reflexive at every point). -/
  joinOpt_idem   : ∀ a, joinOpt a a = some a
  /-- Meet commutes. -/
  meetOpt_comm   : ∀ a b, meetOpt a b = meetOpt b a

/-- Tier T — typestate.  Per §6.3, 1 dimension qualifies:
    Protocol (dim 6).

    Minimal interface — only a partial combine.  No commutativity
    / associativity / idempotence laws are required in the class.
    Session-type transitions are directional and the Phase-6 kernel
    refinement will add structured transition relations.  The
    Phase-1 kernel carrier `{consumed, active}` happens to be
    commutative but that's an implementation simplification the
    class does NOT promise.

    The deliberate sparsity is the point — claiming Tier T has
    semiring or lattice laws would over-commit to a Phase-1
    simplification and break when typestate transitions land. -/
class TierT (α : Type) extends GradeCarrier α where
  /-- Combine two typestate values — partial.  Returns `none`
      when the states are incompatible. -/
  combineOpt     : α → α → Option α

/-- Tier V — versioned lattice with adapter edges.  Per §6.3,
    1 dimension qualifies: Version (dim 21).

    `meet` is a total operation — no validity failure at the
    kernel level.  Adapter resolution (§15.6) happens at
    elaboration time, not in the grade algebra — the class is the
    kernel-level interface and adapter-edge resolution sits above
    it in the elaborator.

    `consistent a b` is the kernel-level check "can a producer at
    `a` flow into a consumer at `b` without adapter application".
    Adapter edges (§15.4) turn inconsistent pairs into consistent
    ones via transformation functions. -/
class TierV (α : Type) extends GradeCarrier α where
  /-- Version-lattice meet (combine). -/
  meet           : α → α → α
  /-- Meet commutes. -/
  meet_comm      : ∀ a b, meet a b = meet b a
  /-- Meet is associative. -/
  meet_assoc     : ∀ a b c, meet (meet a b) c = meet a (meet b c)
  /-- Flow consistency without adapters.  `true` iff producer at
      `a` directly satisfies consumer at `b` (same label or
      sub-label per the version preorder).  Elaborator consults
      adapter graph when this returns `false`. -/
  consistent     : α → α → Bool
  /-- Reflexivity of `consistent` (T6): every version flows to
      itself without adapter — the identity path in the version
      lattice.  This makes `consistent` a reflexive relation, and
      lets the elaborator discharge the "same version" case at
      zero cost.  Required by the class because a `consistent`
      that rejects `a a` is not a preorder and breaks §15.4
      refinement resolution (a v2 value at `v2` must satisfy a
      consumer bound to `v2` without an adapter). -/
  consistent_refl : ∀ a, consistent a a = true

/-! ## Tier-generic theorems (T7)

Generic theorems that derive from tier-class abstract laws.  These
apply to every type instancing the class — the point of the tier
hierarchy is that such theorems compose.  Tier.lean is the natural
home because both the class definition and its generic consequences
live side-by-side.

Each generic theorem follows a uniform shape: state the property in
terms of the class's methods, prove it by combining the class's
axioms (the laws listed in the class body).  No per-dim case
analysis — a `decide` or direct equality chain suffices. -/

namespace TierSIdem

/-- In any `TierSIdem`, multiplication is idempotent.  Derived from
    `mul_eq_add` and `add_idem`: since mul coincides with add, and
    add is idempotent, mul is idempotent. -/
theorem mul_idem {α : Type} [inst : TierSIdem α] (a : α) :
    inst.mul a a = a := by
  rw [inst.mul_eq_add]
  exact inst.add_idem a

/-- In any `TierSIdem`, multiplication is commutative.  This is
    already demanded by the inherited `TierSComm` parent; this
    theorem re-exports it at the TierSIdem level for discoverability
    in proof contexts that have bound a `TierSIdem` instance. -/
theorem mul_comm' {α : Type} [inst : TierSIdem α] (a b : α) :
    inst.mul a b = inst.mul b a :=
  inst.mul_comm a b

/-- Cross-commutation: `mul a b = add a b` because both are the
    same operation in a TierSIdem.  Useful as a rewrite rule when
    reasoning about contexts that mix the two. -/
theorem mul_eq_add' {α : Type} [inst : TierSIdem α] (a b : α) :
    inst.mul a b = inst.add a b :=
  inst.mul_eq_add a b

/-- Double-mul-to-self via idempotence + mul_eq_add.  `(a * a) * a
    = a` in any TierSIdem.  Witnesses that idempotent ops don't
    grow under iteration. -/
theorem mul_mul_self {α : Type} [inst : TierSIdem α] (a : α) :
    inst.mul (inst.mul a a) a = a := by
  rw [mul_idem, mul_idem]

end TierSIdem

namespace TierSRing

/-- In any `TierSRing`, `0 * 0 = 0`.  Direct consequence of
    annihilation.  Trivial but named for discoverability. -/
theorem zero_mul_zero {α : Type} [inst : TierSRing α] :
    inst.mul inst.zero inst.zero = inst.zero :=
  inst.zero_mul inst.zero

/-- Distribution via the zero annihilator: `mul 0 (add b c) = 0`.
    Combines `zero_mul` with `left_distrib` to show any sum
    multiplied by zero is zero.  Useful for simplifying graded
    expressions involving ghost-scaled values (grade 0). -/
theorem zero_mul_add {α : Type} [inst : TierSRing α] (b c : α) :
    inst.mul inst.zero (inst.add b c) = inst.zero := by
  rw [inst.left_distrib, inst.zero_mul, inst.zero_mul, inst.zero_add]

/-- Dual: `mul (add b c) 0 = 0`. -/
theorem add_mul_zero {α : Type} [inst : TierSRing α] (b c : α) :
    inst.mul (inst.add b c) inst.zero = inst.zero := by
  rw [inst.right_distrib, inst.mul_zero, inst.mul_zero, inst.add_zero]

end TierSRing

namespace TierSComm

/-- In any `TierSComm`, `add` followed by `mul` can have its args
    reordered uniformly.  `mul (add a b) c = mul c (add a b)` —
    trivial by mul_comm, but named here so it can be applied as
    a rewrite in proofs over the aggregate Grade vector. -/
theorem mul_add_comm {α : Type} [inst : TierSComm α] (a b c : α) :
    inst.mul (inst.add a b) c = inst.mul c (inst.add a b) :=
  inst.mul_comm (inst.add a b) c

end TierSComm

namespace TierV

/-- In any `TierV`, a version is trivially consistent with itself
    — the identity path in the version lattice.  Direct
    re-export of `consistent_refl` for discoverability in
    proof/refactor contexts that quantify over a bound TierV
    instance rather than a specific dim instance.

    Named at the namespace level (mirrors `TierSIdem.mul_idem`,
    `TierSRing.zero_mul_zero`) so proof assistants find it via
    dot lookup on the tier. -/
theorem consistent_refl' {α : Type} [inst : TierV α] (a : α) :
    inst.consistent a a = true :=
  inst.consistent_refl a

end TierV

end FX.Kernel
