import FX.Kernel.Grade.Tier

/-!
# Lifetime (dimension 7) — region annotations

Per `fx_design.md` §6.3 (dim 7) and §8.1.  Tier S in the spec.
The "semiring" classification is nominal: the carrier is
infinite (arbitrarily many region variables) and the algebraic
operations are lattice-like rather than ring-like.

## Regions

A region is either:

  * `static` — the permanent region; outlives every other.
  * `var n`  — a region variable with de-Bruijn-style index `n`.

Phase 1 does not elaborate region inference.  The design (§6.3
dim 7 and Appendix E) is explicit: **FX does not infer
lifetimes** (rigor-first — every `pub fn`, every let-binding
holding a reference, every type application carrying a region
must name it explicitly).  The kernel accepts region variables
in grade positions but makes no semantic claim about their
relative ordering beyond:

  * Every region is `≤ static` (`static` is the top, outlives
    everything — `LessEq.leStatic`).
  * Every region is `≤` itself (`LessEq.refl`).

Non-trivial region orderings (e.g., `'a ≤ 'b` when `'a`
outlives `'b` because `'a` is declared in a scope strictly
enclosing `'b`) become elaborator-supplied hypotheses: they
are added to the kernel context as `LessEq`-facts at the use site,
not derived from this `LessEq` relation.  The kernel `LessEq` captures
only the two facts that hold unconditionally regardless of
which regions the elaborator introduced.

## Algebra — `add` and `mul`

`add` (parallel combine) coalesces non-equal region variables
to `static`.  This is a deliberate Phase-1 **sound
over-approximation**:

  * Soundness:  `static` is the top of the outlives preorder.
    A value annotated `static` is usable wherever any region is
    expected, so promoting `add (var a) (var b)` to `static`
    never admits a program that the true (elaborator-supplied)
    outlives order would reject — it can only pessimistically
    reject programs the elaborator would have accepted if it
    knew `'a ≤ 'b` or `'b ≤ 'a`.
  * Information loss:  the coalesce discards the knowledge that
    two region variables were being combined.  A later query
    "is this region still just `var a`?" sees `static` and
    assumes the worst.  Phase 2 will thread elaborator
    outlives-facts through `add` to preserve the tighter region.

`mul` (sequential combine) is the same join.  Parallel vs.
sequential makes no difference for regions: the relevant
question is "which region does this reference live in?", and
that doesn't depend on evaluation order.

## Subsumption `LessEq`

`x ≤ y` means "a reference at region `x` is usable where
region `y` is expected" — i.e., `x` outlives `y`.  Only two
rules hold unconditionally:

  * `LessEq.refl`     — any region outlives itself.
  * `LessEq.leStatic` — `static` outlives every region (equivalently,
                    every region is `≤ static`).

`decLe` decides `LessEq` by enumerating: `LessEq x y` iff `x = y` or
`y = static`.
-/

namespace FX.Kernel

/-- A region: the static region or a de-Bruijn region variable. -/
inductive Region : Type where
  | static : Region
  | var    : Nat → Region
  deriving DecidableEq, Repr

namespace Region

/-- Parallel combine.  Coalesces non-equal regions to `static`
    (sound over-approximation; see module docstring). -/
def add : Region → Region → Region
  | static, _ => static
  | _, static => static
  | var leftIndex, var rightIndex =>
      if leftIndex = rightIndex then var leftIndex else static

/-- Sequential combine — same join. -/
def mul : Region → Region → Region := add

/-- Outlives preorder.  `static` is the top; everything else is
    reflexive-only at the kernel level (the elaborator supplies
    further `LessEq` facts as hypotheses when the scope structure of
    the source program establishes non-trivial outlives
    relations between region variables). -/
inductive LessEq : Region → Region → Prop where
  | refl     : ∀ region, LessEq region region
  | leStatic : ∀ region, LessEq region static

instance : LE Region := ⟨LessEq⟩

theorem LessEq.trans {x y z : Region} (leftStep : x ≤ y) (rightStep : y ≤ z) : x ≤ z := by
  cases leftStep with
  | refl     => exact rightStep
  | leStatic =>
    cases rightStep with
    | refl     => exact LessEq.leStatic _
    | leStatic => exact LessEq.leStatic _

/-- Decidability of `LessEq`.  `LessEq x y` holds iff `x = y` or `y = static`. -/
instance decLe : (x y : Region) → Decidable (LessEq x y) := fun leftRegion rightRegion =>
  match equalityDecision : decEq leftRegion rightRegion with
  | isTrue equal => isTrue (equal ▸ LessEq.refl _)
  | isFalse notEqual =>
    match rightRegion with
    | static => isTrue (LessEq.leStatic _)
    | var _index  =>
      isFalse (fun leProof => by
        cases leProof with
        | refl => exact notEqual rfl)

/-! ### Algebraic laws -/

theorem add_comm (x y : Region) : add x y = add y x := by
  cases x with
  | static => cases y <;> rfl
  | var leftIndex =>
    cases y with
    | static => rfl
    | var rightIndex =>
      simp only [add]
      by_cases indicesEqual : leftIndex = rightIndex
      · subst indicesEqual; rfl
      · have flippedNotEqual : rightIndex ≠ leftIndex :=
          fun flippedEqual => indicesEqual flippedEqual.symm
        rw [if_neg indicesEqual, if_neg flippedNotEqual]

theorem add_idem (region : Region) : add region region = region := by
  cases region with
  | static => rfl
  | var _index  => simp [add]

theorem static_add (region : Region) : add static region = static := by
  cases region <;> rfl

theorem add_static (region : Region) : add region static = static := by
  cases region <;> rfl

/-- Helper: `add (var i) (var j)` equals `var i` when `i = j`,
    else `static`.  Explicit form of the `if` inside `add`.  -/
theorem add_var_var (leftIndex rightIndex : Nat) :
    add (var leftIndex) (var rightIndex)
      = (if leftIndex = rightIndex then var leftIndex else static) := by
  rfl

/-- Associativity.  Coalesce-to-static is associative: any
    `static` input propagates through, and equal-var triples
    stay equal.  The three-var subcase analyzes the two pairwise
    equalities (leftIndex = midIndex, midIndex = rightIndex)
    and observes that both sides compute the same final
    value. -/
theorem add_assoc (x y z : Region) : add (add x y) z = add x (add y z) := by
  cases x with
  | static =>
    -- add (add static y) z = add static z = static
    -- add static (add y z) = static
    rfl
  | var leftIndex =>
    cases y with
    | static =>
      -- add (add (var l) static) z = add static z = static
      -- add (var l) (add static z) = add (var l) static = static
      cases z <;> rfl
    | var midIndex =>
      cases z with
      | static =>
        -- add (add (var l) (var m)) static = static
        -- add (var l) (add (var m) static) = add (var l) static = static
        cases h : add (var leftIndex) (var midIndex) with
        | static => rfl
        | var _ => rfl
      | var rightIndex =>
        -- Three-var subcase.
        rw [add_var_var, add_var_var]
        by_cases leftEqMid : leftIndex = midIndex
        · -- l = m
          subst leftEqMid
          rw [if_pos rfl]
          by_cases leftEqRight : leftIndex = rightIndex
          · subst leftEqRight
            rw [if_pos rfl]
          · rw [if_neg leftEqRight, add_var_var, if_neg leftEqRight]
            rfl
        · -- l ≠ m
          rw [if_neg leftEqMid]
          by_cases midEqRight : midIndex = rightIndex
          · subst midEqRight
            rw [if_pos rfl, add_var_var, if_neg leftEqMid]
            rfl
          · rw [if_neg midEqRight]
            rfl

/-- `mul` is the same join, so all `add` laws transport to `mul`. -/
theorem mul_comm (leftRegion rightRegion : Region) :
    mul leftRegion rightRegion = mul rightRegion leftRegion :=
  add_comm leftRegion rightRegion

theorem mul_idem (region : Region) : mul region region = region :=
  add_idem region

theorem static_mul (region : Region) : mul static region = static :=
  static_add region

theorem mul_static (region : Region) : mul region static = static :=
  add_static region

theorem mul_assoc (x y z : Region) : mul (mul x y) z = mul x (mul y z) :=
  add_assoc x y z

end Region

/-! ## GradeCarrier instance (no TierS — see T6a audit)

Region (the Lifetime dim's carrier) CANNOT instance `TierS`: its
`add` is a join-to-static coalesce with NO additive unit.  `add
static x = static` absorbs; there is no element `ε` such that `add ε
x = x` for every `x` (the module docstring above is explicit: "The
'semiring' classification is nominal: the carrier is infinite and
the algebraic operations are lattice-like rather than ring-like").

The §6.3 "Tier S" classification is therefore nominal.  Region
provides `GradeCarrier` with the reflexive-plus-static outlives
preorder; tier-generic theorems over `TierS` don't apply to this
dim. -/
instance : GradeCarrier Region where
  default  := Region.static
  le       := Region.LessEq
  le_refl  := Region.LessEq.refl
  le_trans := Region.LessEq.trans

end FX.Kernel
