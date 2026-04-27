import FX.Kernel.Grade.Tier

/-!
# Mutation (dimension 18) — write permission ladder

Per `fx_design.md` §6.3 (dim 18).  Four-element chain:

    immutable < appendOnly < monotonic < readWrite

  * `immutable`  — no mutation (default).
  * `appendOnly` — may add to tail, never overwrite or remove.
  * `monotonic`  — may change forward along a declared partial order.
  * `readWrite`  — arbitrary mutation.

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 18 and §4.6:

  * (no annotation)              → `immutable`   (default — deny mutation)
  * `ref append`                 → `appendOnly`  (grant — tail extension only)
  * `ref monotonic(order: ord)`  → `monotonic`   (grant — forward-only changes)
  * `ref mut`                    → `readWrite`   (grant — arbitrary mutation)

## Combining

Parallel/sequential combine is **join** (max): if any part of an
expression requires `readWrite`, the whole expression is at that
level.  `immutable` is the unit.

## Algebra

4-element idempotent commutative monoid for both ops = join with
`immutable` as bottom identity and `readWrite` as top absorber.
-/

namespace FX.Kernel

inductive Mutation : Type where
  | immutable  : Mutation
  | appendOnly : Mutation
  | monotonic  : Mutation
  | readWrite  : Mutation
  deriving DecidableEq, Repr

namespace Mutation

/-- Rank into `Nat` for computable join via `Nat.max`. -/
def rank : Mutation → Nat
  | immutable  => 0
  | appendOnly => 1
  | monotonic  => 2
  | readWrite  => 3

/-- Recover the `Mutation` constructor from a rank.  Defined for
    all `Nat` to keep it total; out-of-range maps to `readWrite`
    (the top of the chain). -/
def ofRank : Nat → Mutation
  | 0 => immutable
  | 1 => appendOnly
  | 2 => monotonic
  | _ => readWrite

theorem ofRank_rank (mutation : Mutation) : ofRank (rank mutation) = mutation := by
  cases mutation <;> rfl

/-- `rank` is injective on `Mutation` — the four constructors map
    to four distinct naturals.  Corollary of `ofRank_rank`. -/
theorem rank_injective {leftMutation rightMutation : Mutation}
    (ranksEqual : rank leftMutation = rank rightMutation) : leftMutation = rightMutation := by
  have recovered : ofRank (rank leftMutation) = ofRank (rank rightMutation) := by rw [ranksEqual]
  rw [ofRank_rank, ofRank_rank] at recovered
  exact recovered

/-- Join (max over the chain). -/
def add : Mutation → Mutation → Mutation
  | readWrite,  _           => readWrite
  | _,          readWrite   => readWrite
  | monotonic,  _           => monotonic
  | _,          monotonic   => monotonic
  | appendOnly, _           => appendOnly
  | _,          appendOnly  => appendOnly
  | immutable,  immutable   => immutable

/-- Sequential combine — identical to `add` (both are join). -/
def mul : Mutation → Mutation → Mutation := add

/--
Subsumption: `x ≤ y` iff `x` grants *no more* than `y`.

The ladder is oriented bottom-to-top so stronger grants subsume
weaker ones.  A function asking for `ref mut` may accept anything
(every Mutation grade is `≤ readWrite`); a function asking for
`immutable` accepts only `immutable`.
-/
def LessEq (leftMutation rightMutation : Mutation) : Prop :=
  rank leftMutation ≤ rank rightMutation

instance : LE Mutation := ⟨LessEq⟩

theorem LessEq.refl (mutation : Mutation) : mutation ≤ mutation := Nat.le_refl _

theorem LessEq.trans {leftMutation middleMutation rightMutation : Mutation}
    (leftLeMiddle : leftMutation ≤ middleMutation)
    (middleLeRight : middleMutation ≤ rightMutation) :
    leftMutation ≤ rightMutation :=
  Nat.le_trans leftLeMiddle middleLeRight

/-- Antisymmetry — `LessEq` is a genuine partial order. -/
theorem LessEq.antisymm {leftMutation rightMutation : Mutation}
    (leftLeRight : leftMutation ≤ rightMutation)
    (rightLeLeft : rightMutation ≤ leftMutation) : leftMutation = rightMutation :=
  rank_injective (Nat.le_antisymm leftLeRight rightLeLeft)

instance decLe (leftMutation rightMutation : Mutation) : Decidable (LessEq leftMutation rightMutation) :=
  inferInstanceAs (Decidable (rank leftMutation ≤ rank rightMutation))

/-! ### Idempotent commutative monoid laws -/

theorem add_comm (leftMutation rightMutation : Mutation) :
    add leftMutation rightMutation = add rightMutation leftMutation := by
  cases leftMutation <;> cases rightMutation <;> rfl

theorem add_assoc (leftMutation middleMutation rightMutation : Mutation) :
    add (add leftMutation middleMutation) rightMutation
      = add leftMutation (add middleMutation rightMutation) := by
  cases leftMutation <;> cases middleMutation <;> cases rightMutation <;> rfl

theorem add_idem (mutation : Mutation) : add mutation mutation = mutation := by
  cases mutation <;> rfl

/-- `immutable` is the identity for `add` (bottom of the chain). -/
theorem immutable_add (mutation : Mutation) : add immutable mutation = mutation := by
  cases mutation <;> rfl

theorem add_immutable (mutation : Mutation) : add mutation immutable = mutation := by
  cases mutation <;> rfl

/-- `readWrite` absorbs under `add` (top of the chain). -/
theorem readWrite_add (mutation : Mutation) : add readWrite mutation = readWrite := by
  cases mutation <;> rfl

theorem add_readWrite (mutation : Mutation) : add mutation readWrite = readWrite := by
  cases mutation <;> rfl

theorem mul_assoc (leftMutation middleMutation rightMutation : Mutation) :
    mul (mul leftMutation middleMutation) rightMutation
      = mul leftMutation (mul middleMutation rightMutation) :=
  add_assoc leftMutation middleMutation rightMutation

/-- Mutation mul is commutative.  `mul := add` and `add_comm`
    is proven above, so this is a definitional re-export.
    Used by `Grade.mul_comm_of_same_provenance` (Q48). -/
theorem mul_comm (leftMutation rightMutation : Mutation) :
    mul leftMutation rightMutation = mul rightMutation leftMutation :=
  add_comm leftMutation rightMutation

theorem mul_idem (mutation : Mutation) : mul mutation mutation = mutation := add_idem mutation

theorem immutable_mul (mutation : Mutation) : mul immutable mutation = mutation :=
  immutable_add mutation

theorem mul_immutable (mutation : Mutation) : mul mutation immutable = mutation :=
  add_immutable mutation

/-- Idempotent distributivity collapses. -/
theorem left_distrib (leftMutation middleMutation rightMutation : Mutation) :
    mul leftMutation (add middleMutation rightMutation)
      = add (mul leftMutation middleMutation) (mul leftMutation rightMutation) := by
  cases leftMutation <;> cases middleMutation <;> cases rightMutation <;> rfl

theorem right_distrib (leftMutation middleMutation rightMutation : Mutation) :
    mul (add leftMutation middleMutation) rightMutation
      = add (mul leftMutation rightMutation) (mul middleMutation rightMutation) := by
  cases leftMutation <;> cases middleMutation <;> cases rightMutation <;> rfl

/-! ### Top / bottom universals -/

/-- `readWrite` is the top: every mutation grade is ≤ `readWrite`. -/
theorem le_readWrite (mutation : Mutation) : LessEq mutation readWrite := by
  cases mutation <;> decide

/-- `immutable` is the bottom: it subsumes into every grade. -/
theorem immutable_le (mutation : Mutation) : LessEq immutable mutation := by
  cases mutation <;> decide

/-! ### Monotonicity of `add` -/

theorem add_mono_left {leftMutation leftMutation' : Mutation} (rightMutation : Mutation)
    (leftLe : LessEq leftMutation leftMutation') :
    LessEq (add leftMutation rightMutation) (add leftMutation' rightMutation) := by
  have rankLeftLe : rank leftMutation ≤ rank leftMutation' := leftLe
  cases leftMutation <;> cases leftMutation' <;> cases rightMutation <;>
    first
      | (exact LessEq.refl _)
      | (show LessEq _ _; decide)
      | (exfalso; simp [rank] at rankLeftLe)

theorem add_mono_right {rightMutation rightMutation' : Mutation} (leftMutation : Mutation)
    (rightLe : LessEq rightMutation rightMutation') :
    LessEq (add leftMutation rightMutation) (add leftMutation rightMutation') := by
  rw [add_comm leftMutation rightMutation, add_comm leftMutation rightMutation']
  exact add_mono_left leftMutation rightLe

/-- Monotonicity of `mul` — inherited from `add` since `mul = add`. -/
theorem mul_mono_left {leftMutation leftMutation' : Mutation} (rightMutation : Mutation)
    (leftLe : LessEq leftMutation leftMutation') :
    LessEq (mul leftMutation rightMutation) (mul leftMutation' rightMutation) :=
  add_mono_left rightMutation leftLe

theorem mul_mono_right {rightMutation rightMutation' : Mutation} (leftMutation : Mutation)
    (rightLe : LessEq rightMutation rightMutation') :
    LessEq (mul leftMutation rightMutation) (mul leftMutation rightMutation') :=
  add_mono_right leftMutation rightLe

end Mutation

/-! ## TierSIdem instance (T2)

Mutation fits the idempotent join-lattice shape over the 4-element
chain `immutable < appendOnly < monotonic < readWrite`.
`add = mul = join`, `immutable` is the bottom identity, `readWrite`
absorbs.  No strict annihilator. -/
instance : TierSIdem Mutation where
  default      := Mutation.immutable
  le           := Mutation.LessEq
  le_refl      := Mutation.LessEq.refl
  le_trans     := Mutation.LessEq.trans
  add          := Mutation.add
  mul          := Mutation.mul
  zero         := Mutation.immutable
  add_comm     := Mutation.add_comm
  add_assoc    := Mutation.add_assoc
  add_zero     := Mutation.add_immutable
  zero_add     := Mutation.immutable_add
  mul_assoc    := Mutation.mul_assoc
  mul_comm     := Mutation.mul_comm
  add_idem     := Mutation.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel
