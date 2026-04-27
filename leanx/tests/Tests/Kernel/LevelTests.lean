import FX.Kernel.Level

/-!
# Universe level tests

Covers `fx_design.md` §31.4 and Appendix H.1.

  * Closed-level `eval?` returns the numeric value
  * `var _` makes `eval?` return `none` (opaque on open levels)
  * `LessEq` is vacuous on levels containing a variable
  * `LessEq.refl` / `LessEq.trans` proofs hold
  * `Nat.max` is the join semantics of `Level.max`
-/

namespace Tests.Kernel.LevelTests

open FX.Kernel
open FX.Kernel.Level

/-! ## eval? on closed levels -/

example : eval? zero = some 0 := rfl
example : eval? (succ zero) = some 1 := rfl
example : eval? (succ (succ zero)) = some 2 := rfl

example : eval? (Level.max zero zero) = some 0 := rfl
example : eval? (Level.max zero (succ zero)) = some 1 := rfl
example : eval? (Level.max (succ zero) zero) = some 1 := rfl
example : eval? (Level.max (succ (succ zero)) (succ zero)) = some 2 := rfl

-- Deeper nesting.
example : eval? (Level.max (succ (succ (succ zero))) (succ zero)) = some 3 := rfl

/-! ## eval? on levels with variables — always none -/

example : eval? (var 0) = none := rfl
example : eval? (var 42) = none := rfl
example : eval? (succ (var 0)) = none := rfl
example : eval? (Level.max (var 0) zero) = none := rfl
example : eval? (Level.max zero (var 0)) = none := rfl
example : eval? (succ (Level.max zero (var 0))) = none := rfl

/-! ## `LessEq.refl` for concrete closed levels -/

example : LessEq zero zero := LessEq.refl _
example : LessEq (succ zero) (succ zero) := LessEq.refl _
example : LessEq (Level.max zero zero) (Level.max zero zero) := LessEq.refl _

/-! ## `LessEq.refl` for variable levels is vacuously true

On open levels `eval?` returns `none`, so the universal
`∀ a, eval? u = some a → …` is vacuously satisfied. -/

example : LessEq (var 0) (var 0) := LessEq.refl _
example : LessEq (var 7) zero := fun _ h => by simp [eval?] at h

/-! ## LessEq.trans on closed levels -/

example : LessEq zero (succ zero) := by
  intro a h
  simp [eval?] at h
  exact ⟨1, rfl, by subst h; decide⟩

/-! ## `succ` strict monotonicity witness -/

example : (eval? (succ (succ zero)) = some 2) ∧
          (eval? (succ zero) = some 1) := ⟨rfl, rfl⟩

/-! ## `Level.max` is join -/

-- max (succ zero) (succ (succ zero)) evaluates to 2.
example : eval? (Level.max (succ zero) (succ (succ zero))) = some 2 := rfl

-- Commutative on concrete evaluations (syntactic terms differ).
example : eval? (Level.max (succ zero) (succ (succ zero))) =
          eval? (Level.max (succ (succ zero)) (succ zero)) := rfl

/-! ## Bool-version theorems (Q47)

Named theorems for `leBool` — the kernel's actual decision
procedure used by `subOrConv` — and for the eval/closedness
rewrites. -/

-- `leBool u u = true` — reflexivity at the Bool level.
example : leBool zero zero = true := by native_decide
example : leBool (succ (succ zero)) (succ (succ zero)) = true := by native_decide
example : leBool (var 0) (var 0) = true := by native_decide
-- Named theorem witness:
example : leBool (succ zero) (succ zero) = true := Level.leBool_refl _

-- `leBool` on concrete closed levels: u ≤ v iff u_val ≤ v_val.
example : leBool zero (succ zero) = true := by native_decide
example : leBool (succ zero) (succ (succ zero)) = true := by native_decide
example : leBool (succ zero) zero = false := by native_decide
example : leBool (succ (succ zero)) (succ zero) = false := by native_decide

-- Closed-level transitivity: chain three levels
-- (0 ≤ 1 ≤ 2 ⇒ 0 ≤ 2).
example : leBool zero (succ (succ zero)) = true :=
  Level.leBool_trans_closed zero (succ zero) (succ (succ zero))
    (hLeftClosed := by decide) (hMiddleClosed := by decide)
    (hRightClosed := by decide)
    (hLeftLeMid := by native_decide) (hMidLeRight := by native_decide)

-- Open levels: leBool falls back to syntactic equality.
-- `var 0 = var 0` → leBool = true.
example : leBool (var 0) (var 0) = true := by native_decide
-- `var 0 ≠ var 1` → leBool = false (no cumulativity across vars).
example : leBool (var 0) (var 1) = false := by native_decide
-- Closed vs open always fails (mixed case).
example : leBool zero (var 0) = false := by native_decide
example : leBool (var 0) zero = false := by native_decide

/-! ## eval? rewrites (Q47)

Named rewrites for `eval?` on each Level constructor; `@[simp]`
lemmas let client proofs normalize without re-deriving. -/

example : eval? zero = some 0 := Level.eval?_zero
example : eval? (var 5) = none := Level.eval?_var 5
example : eval? (succ zero) = (eval? zero).map (· + 1) := Level.eval?_succ _

/-! ## Closedness rewrites (Q47) -/

example : closed zero = true := Level.closed_zero
example : closed (var 0) = false := Level.closed_var 0
example : closed (succ (succ zero)) = closed (succ zero) := Level.closed_succ _
example : closed (Level.max zero (var 0)) = (closed zero && closed (var 0)) :=
  Level.closed_max _ _

/-! ## Nat bridge (Q47) -/

example : (Level.ofNat 0).eval? = some 0 := Level.eval?_ofNat 0
example : (Level.ofNat 1).eval? = some 1 := Level.eval?_ofNat 1
example : (Level.ofNat 10).eval? = some 10 := Level.eval?_ofNat 10

example : closed (Level.ofNat 5) = true := Level.closed_ofNat 5

-- ofNat matches the syntactic succ chain from zero.
example : Level.ofNat 0 = zero := rfl
example : Level.ofNat 3 = succ (succ (succ zero)) := rfl

/-! ## Max neutral / idempotence (Q47) -/

-- Zero is the left identity of max on closed levels.
example : eval? (Level.max zero (succ zero)) = eval? (succ zero) :=
  Level.max_zero_left_eval _ (by decide)

-- Zero is the right identity.
example : eval? (Level.max (succ zero) zero) = eval? (succ zero) :=
  Level.max_zero_right_eval _ (by decide)

-- Max is idempotent (at value level).
example : eval? (Level.max (succ (succ zero)) (succ (succ zero)))
            = eval? (succ (succ zero)) :=
  Level.max_idem_eval _ (by decide)

-- Deeper idempotence.
example : eval? (Level.max (Level.ofNat 7) (Level.ofNat 7))
            = eval? (Level.ofNat 7) :=
  Level.max_idem_eval _ (Level.closed_ofNat 7)

end Tests.Kernel.LevelTests
