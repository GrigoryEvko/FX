/-! # mode-3 floor — the block-rotation permutation (the matching keystone's renaming witness, arithmetic core)

The Joyal–Street / Schanuel–Street word-problem keystone (decidable 2-cell equality of the walking adjunction)
reduces, on the boundary-connectivity matching carrier, to constructing the node-id renaming `sigma` between the
two Godement run orders.  Both orders run the common `cellAlpha` prefix identically; let `lo` be the fresh-id
allocation counter after `cellAlpha`.  The redex then runs `cellAlphaUpper` (allocating a CONTIGUOUS range of
`w1` fresh ids `[lo, lo+w1)`) then `cellBeta` (allocating `[lo+w1, lo+w1+w2)`); the reduct runs `cellBeta` first
(`[lo, lo+w2)`) then `cellAlphaUpper` (`[lo+w2, lo+w2+w1)`).  The fresh-id COUNT each block allocates is a
STRUCTURAL property of the cell (independent of run order) — only the starting counter differs.  So `sigma`
(mapping redex ids to reduct ids) is the BLOCK ROTATION permuting the two sub-blocks of the window `[lo, lo+w1+w2)`.

This file is the fully-standalone arithmetic core (imports only `Init`): `blockRotate` and its key properties —
INJECTIVITY (via the explicit left inverse `blockRotate lo w2 w1`, the same rotation with the two block widths
swapped), it FIXES every id `< lo` (the boundary + `cellAlpha` ids), and FIXES every id `≥ lo+w1+w2` (the future
tail).  It is a bijection of the window `[lo, lo+w1+w2)` that swaps the two sub-blocks `[lo, lo+w1)` and
`[lo+w1, lo+w1+w2)`.  Truncated subtraction (`x - w1`) is handled by the standing window bounds.

Zero-axiom: structural `Nat` case-analysis (`Nat.lt_or_ge`), `if_pos`/`if_neg`, and the core `Nat` order/arith
lemmas — no `omega`, no `Nat.add_mul`, no `Nat.le_max_*`, no `decide` on open terms. -/

namespace FX1Poly.Polygraph

/-- ★ **The block-rotation permutation.**  On the window `[lo, lo+w1+w2)` it swaps the two sub-blocks: the first
sub-block `[lo, lo+w1)` shifts up by `w2` (to `[lo+w2, lo+w1+w2)`), the second sub-block `[lo+w1, lo+w1+w2)`
shifts down by `w1` (to `[lo, lo+w2)`); everything `< lo` (the boundary) and everything `≥ lo+w1+w2` (the future
tail) is fixed.  The redex's `cellAlphaUpper` fresh range `[lo, lo+w1)` maps to the reduct's `cellAlphaUpper`
range `[lo+w2, lo+w2+w1)`, and the redex's `cellBeta` range `[lo+w1, lo+w1+w2)` maps to the reduct's `cellBeta`
range `[lo, lo+w2)`. -/
def blockRotate (lo w1 w2 x : Nat) : Nat :=
  if x < lo then x
  else if x < lo + w1 then x + w2
  else if x < lo + w1 + w2 then x - w1
  else x

/-! ## Branch read-offs -/

/-- Below the window: `blockRotate` is the identity. -/
theorem blockRotate_below (lo w1 w2 x : Nat) (h : x < lo) : blockRotate lo w1 w2 x = x := by
  unfold blockRotate; rw [if_pos h]

/-- On the first sub-block `[lo, lo+w1)`: `blockRotate` shifts up by `w2`. -/
theorem blockRotate_firstBlock (lo w1 w2 x : Nat) (hlo : lo ≤ x) (hhi : x < lo + w1) :
    blockRotate lo w1 w2 x = x + w2 := by
  unfold blockRotate
  rw [if_neg (Nat.not_lt.mpr hlo), if_pos hhi]

/-- On the second sub-block `[lo+w1, lo+w1+w2)`: `blockRotate` shifts down by `w1`. -/
theorem blockRotate_secondBlock (lo w1 w2 x : Nat) (hlo : lo + w1 ≤ x) (hhi : x < lo + w1 + w2) :
    blockRotate lo w1 w2 x = x - w1 := by
  unfold blockRotate
  have hbelow : lo ≤ x := Nat.le_trans (Nat.le_add_right lo w1) hlo
  rw [if_neg (Nat.not_lt.mpr hbelow), if_neg (Nat.not_lt.mpr hlo), if_pos hhi]

/-- Above the window: `blockRotate` is the identity. -/
theorem blockRotate_above (lo w1 w2 x : Nat) (h : lo + w1 + w2 ≤ x) : blockRotate lo w1 w2 x = x := by
  unfold blockRotate
  have hbelow : lo ≤ x :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right lo w1) (Nat.le_add_right (lo + w1) w2)) h
  have hmid : lo + w1 ≤ x := Nat.le_trans (Nat.le_add_right (lo + w1) w2) h
  rw [if_neg (Nat.not_lt.mpr hbelow), if_neg (Nat.not_lt.mpr hmid), if_neg (Nat.not_lt.mpr h)]

/-! ## The standing fixing facts the witness consumes -/

/-- `blockRotate` FIXES every id strictly below the window (the bottom boundary + the `cellAlpha` ids). -/
theorem blockRotate_fixesBelow (lo w1 w2 x : Nat) (h : x < lo) : blockRotate lo w1 w2 x = x :=
  blockRotate_below lo w1 w2 x h

/-- `blockRotate` FIXES every id at or above the window (the future-allocation tail). -/
theorem blockRotate_fixesAbove (lo w1 w2 x : Nat) (h : lo + w1 + w2 ≤ x) : blockRotate lo w1 w2 x = x :=
  blockRotate_above lo w1 w2 x h

/-! ## `propext`-free `Nat` cancellation helpers (the core lemmas leak `propext`) -/

/-- `(n + m) - m = n` — reproved by hand (`Nat.add_sub_cancel` leaks `propext`).  Structural on `m`, the successor
case via the clean `Nat.succ_sub_succ`. -/
theorem addSubCancelRight : (n m : Nat) → (n + m) - m = n
  | _, 0 => rfl
  | n, m + 1 => by
      show Nat.succ (n + m) - Nat.succ m = n
      rw [Nat.succ_sub_succ]
      exact addSubCancelRight n m

/-- `(n - m) + m = n` when `m ≤ n` — reproved by hand (`Nat.sub_add_cancel` leaks `propext`).  Joint structural
recursion on `m` and `n`, the successor case via the clean `Nat.succ_sub_succ` / `Nat.le_of_succ_le_succ`. -/
theorem subAddCancel : (m n : Nat) → m ≤ n → (n - m) + m = n
  | 0, _, _ => rfl
  | m + 1, 0, h => absurd h (Nat.not_succ_le_zero m)
  | m + 1, n + 1, h => by
      show (Nat.succ n - Nat.succ m) + Nat.succ m = Nat.succ n
      rw [Nat.succ_sub_succ]
      show Nat.succ ((n - m) + m) = Nat.succ n
      rw [subAddCancel m n (Nat.le_of_succ_le_succ h)]

/-! ## Injectivity, via the explicit left inverse -/

/-- ★ **The block rotation with its two block widths swapped is a LEFT INVERSE.**  Running `blockRotate lo w2 w1`
after `blockRotate lo w1 w2` returns the identity: each of the four regions (below / first block / second block /
above) lands in a disjoint region whose inverse rotation undoes the shift.  The two truncated subtractions are
exact under the standing window bounds (`Nat.add_sub_cancel`, `Nat.sub_add_cancel`).  Case analysis on the four
regions via `Nat.lt_or_ge`. -/
theorem blockRotate_leftInverse (lo w1 w2 : Nat) :
    ∀ x, blockRotate lo w2 w1 (blockRotate lo w1 w2 x) = x := by
  intro x
  cases Nat.lt_or_ge x lo with
  | inl hbelow =>
      rw [blockRotate_below lo w1 w2 x hbelow, blockRotate_below lo w2 w1 x hbelow]
  | inr hlo =>
      cases Nat.lt_or_ge x (lo + w1) with
      | inl hfirst =>
          -- first sub-block: image `x + w2` lands in `[lo+w2, lo+w2+w1)`, the inverse's second sub-block.
          rw [blockRotate_firstBlock lo w1 w2 x hlo hfirst]
          have hlo2 : lo + w2 ≤ x + w2 := Nat.add_le_add_right hlo w2
          have hhi2 : x + w2 < lo + w2 + w1 := by
            have hstep : x + w2 < lo + w1 + w2 := Nat.add_lt_add_right hfirst w2
            rw [Nat.add_right_comm lo w1 w2] at hstep
            exact hstep
          rw [blockRotate_secondBlock lo w2 w1 (x + w2) hlo2 hhi2, addSubCancelRight x w2]
      | inr hmid =>
          cases Nat.lt_or_ge x (lo + w1 + w2) with
          | inl hsecond =>
              -- second sub-block: image `x - w1` lands in `[lo, lo+w2)`, the inverse's first sub-block.
              rw [blockRotate_secondBlock lo w1 w2 x hmid hsecond]
              have hw1lex : w1 ≤ x := Nat.le_trans (Nat.le_add_left w1 lo) hmid
              have hlo1 : lo ≤ x - w1 := Nat.not_lt.mp (by
                intro hcontra
                have hstep : (x - w1) + w1 < lo + w1 := Nat.add_lt_add_right hcontra w1
                rw [subAddCancel w1 x hw1lex] at hstep
                exact absurd hstep (Nat.not_lt.mpr hmid))
              have hhi1 : x - w1 < lo + w2 := by
                have hstep : (x - w1) + w1 < (lo + w2) + w1 := by
                  rw [subAddCancel w1 x hw1lex, Nat.add_right_comm lo w2 w1]
                  exact hsecond
                exact Nat.lt_of_add_lt_add_right hstep
              rw [blockRotate_firstBlock lo w2 w1 (x - w1) hlo1 hhi1, subAddCancel w1 x hw1lex]
          | inr habove =>
              have habove' : lo + w2 + w1 ≤ x := by rw [← Nat.add_right_comm lo w1 w2]; exact habove
              rw [blockRotate_above lo w1 w2 x habove, blockRotate_above lo w2 w1 x habove']

/-- ★ **`blockRotate` is INJECTIVE** — immediate from the left inverse (`blockRotate lo w2 w1`): applying it to
both sides of `blockRotate lo w1 w2 a = blockRotate lo w1 w2 b` collapses to `a = b`. -/
theorem blockRotate_inj (lo w1 w2 : Nat) :
    ∀ a b, blockRotate lo w1 w2 a = blockRotate lo w1 w2 b → a = b := by
  intro a b hEq
  have hRotated : blockRotate lo w2 w1 (blockRotate lo w1 w2 a)
      = blockRotate lo w2 w1 (blockRotate lo w1 w2 b) := congrArg (blockRotate lo w2 w1) hEq
  rw [blockRotate_leftInverse lo w1 w2 a, blockRotate_leftInverse lo w1 w2 b] at hRotated
  exact hRotated

/-! ## Honesty marker -/

/-- **Honesty marker — the block-rotation arithmetic core is proven.**  `blockRotate` is defined and shown
INJECTIVE (`blockRotate_inj`, via the explicit left inverse `blockRotate_leftInverse`), FIXING below the window
(`blockRotate_fixesBelow`) and above it (`blockRotate_fixesAbove`).  It is the concrete renaming witness the
matching Godement residual consumes — the bijection of `[lo, lo+w1+w2)` swapping the two transposed blocks' fresh
ranges.  All zero-axiom (structural `Nat` case-analysis, `if_pos`/`if_neg`, core order/arith lemmas).  `= true`. -/
def fxMode_hasBlockRotationArithmetic : Bool := true

end FX1Poly.Polygraph
