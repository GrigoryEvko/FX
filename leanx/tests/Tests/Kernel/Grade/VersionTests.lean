import FX.Kernel.Grade.Version

/-!
# Version dimension tests

Code revision label lattice — `Nat`-valued version tags with
`Nat.max` combine.  Adapter chains (§15.4) live above this
grade-level interface; the kernel just enforces that the
combined label is the newer of the two.
-/

namespace Tests.Kernel.Grade.Version

open FX.Kernel
open FX.Kernel.Version

/-! ## Construction -/

example : (Version.mk 0).label   = 0 := rfl
example : (Version.mk 1).label   = 1 := rfl
example : (Version.mk 42).label  = 42 := rfl
example : unversioned.label      = 0 := rfl
example : (⟨1⟩ : Version).label  = 1 := rfl

/-! ## `add` — parallel combine is Nat.max -/

example : add ⟨0⟩ ⟨0⟩ = ⟨0⟩ := by native_decide
example : add ⟨1⟩ ⟨1⟩ = ⟨1⟩ := by native_decide
example : add ⟨1⟩ ⟨2⟩ = ⟨2⟩ := by native_decide
example : add ⟨2⟩ ⟨1⟩ = ⟨2⟩ := by native_decide
example : add ⟨5⟩ ⟨3⟩ = ⟨5⟩ := by native_decide
example : add ⟨0⟩ ⟨7⟩ = ⟨7⟩ := by native_decide

/-! ## `mul` — sequential combine is also Nat.max -/

example : mul ⟨1⟩ ⟨1⟩ = ⟨1⟩ := by native_decide
example : mul ⟨1⟩ ⟨2⟩ = ⟨2⟩ := by native_decide
example : mul ⟨3⟩ ⟨7⟩ = ⟨7⟩ := by native_decide

/-! ## Subsumption — Nat.le on labels

Older versions subsume newer via forward adapter chains.
-/

example : LessEq ⟨1⟩ ⟨2⟩ := by decide
example : LessEq ⟨0⟩ ⟨5⟩ := by decide
example : LessEq ⟨3⟩ ⟨3⟩ := LessEq.refl _
example : LessEq unversioned ⟨42⟩ := unversioned_le _

example : ¬ LessEq ⟨2⟩ ⟨1⟩ := by decide
example : ¬ LessEq ⟨5⟩ ⟨3⟩ := by decide

/-! ## Laws -/

-- Commutativity.
example : add ⟨3⟩ ⟨5⟩ = add ⟨5⟩ ⟨3⟩ := add_comm _ _
example : mul ⟨3⟩ ⟨5⟩ = mul ⟨5⟩ ⟨3⟩ := mul_comm _ _

-- Associativity.
example : add (add ⟨2⟩ ⟨5⟩) ⟨3⟩ = add ⟨2⟩ (add ⟨5⟩ ⟨3⟩) := add_assoc _ _ _
example : mul (mul ⟨2⟩ ⟨5⟩) ⟨3⟩ = mul ⟨2⟩ (mul ⟨5⟩ ⟨3⟩) := mul_assoc _ _ _

-- Idempotence.
example : add ⟨3⟩ ⟨3⟩ = ⟨3⟩ := add_idem _
example : mul ⟨7⟩ ⟨7⟩ = ⟨7⟩ := mul_idem _

-- Unversioned as identity.
example : add unversioned ⟨5⟩ = ⟨5⟩ := unversioned_add _
example : add ⟨5⟩ unversioned = ⟨5⟩ := add_unversioned _
example : mul unversioned ⟨5⟩ = ⟨5⟩ := unversioned_mul _
example : mul ⟨5⟩ unversioned = ⟨5⟩ := mul_unversioned _

-- Concrete reductions.
example : add ⟨1⟩ ⟨1⟩ = ⟨1⟩ := by native_decide
example : add ⟨2⟩ ⟨3⟩ = ⟨3⟩ := by native_decide

/-! ## DecidableEq — used by aggregator `Grade.beq` -/

example : ((⟨1⟩ : Version) == ⟨1⟩) = true  := by native_decide
example : ((⟨1⟩ : Version) == ⟨2⟩) = false := by native_decide
example : (unversioned == (⟨0⟩ : Version)) = true := by native_decide

/-! ## `consistent` (T6) — reflexivity + sub-label direction

The kernel-level `consistent a b` answers "can a producer at `a`
flow into a consumer at `b` without adapter application?".  Per
§15.4 it's `true` when `a = b` OR `a < b` (older version flows
forward via refinement; newer does NOT flow backward without an
explicit adapter declaration).

T6 promoted reflexivity to a class-level law on `TierV` and
Version provides the `consistent_refl` field.  Tests below pin:
  * reflexivity (`a a = true`) at every concrete version.
  * sub-label direction (`1 → 2 = true`, `2 → 1 = false`).
  * `unversioned` (= 0) flows into every non-zero version.
-/

example : consistent ⟨0⟩ ⟨0⟩ = true  := by native_decide
example : consistent ⟨1⟩ ⟨1⟩ = true  := by native_decide
example : consistent ⟨42⟩ ⟨42⟩ = true := by native_decide

-- Forward direction: older version flows into newer consumer.
example : consistent ⟨1⟩ ⟨2⟩ = true  := by native_decide
example : consistent ⟨0⟩ ⟨5⟩ = true  := by native_decide

-- Backward direction: newer version does NOT flow into older
-- consumer without adapter.
example : consistent ⟨2⟩ ⟨1⟩ = false := by native_decide
example : consistent ⟨5⟩ ⟨0⟩ = false := by native_decide

-- The class-level law materializes as a concrete theorem.
example : consistent unversioned unversioned = true :=
  consistent_refl _

-- Generic tier-level re-export discoverability.
example (version : Version) :
    (TierV.consistent_refl' version : TierV.consistent version version = true) =
    TierV.consistent_refl' version := rfl

end Tests.Kernel.Grade.Version
