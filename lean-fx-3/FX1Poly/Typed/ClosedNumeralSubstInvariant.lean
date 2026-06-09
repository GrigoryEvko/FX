import FX1Poly.Typed.NatElimFaithfulArithmetic
import FX1Poly.Core.CompoundSubstPreservation

/-! # FX1Poly/Typed/ClosedNumeralSubstInvariant — the closed numeral is substitution-invariant (the Nat.mul crack)

The load-bearing substrate that breaks the wall blocking native `Nat.mul` faithfulness (HON-13's open piece).

The native multiplication step `mulStep m = λ_.λr.natElim(numeralM, r, copyStep)` embeds the multiplicand numeral
`m` UNDER two λ-binders.  When the step β-reduces, the engine must push a substitution through that embedded
numeral.  For a CONCRETE `m`, `subst` computes definitionally (the numeral unfolds); but for a SYMBOLIC `m`,
`natNumeralCell m` is a stuck recursive `match`, so `subst` cannot compute through it by `rfl` — exactly the
"subst-no-compute wall" diagnosed when the `mulStep` β-step `Step.beta` failed to typecheck against its asserted
reduct.  The fix is this lemma: a closed numeral is FIXED by any substitution, proved by induction on `m`
(not by `rfl`).  With it, the `mulStep` β-reduct is rewritten explicitly rather than relying on stuck
computation, and native `Nat.mul` faithfulness (`natElim(n, 0, mulStep m) ↝* numeral (m·n)`, reusing
`natElimAddFaithful` as the per-step adder) goes through.

  * **`natNumeralAt {scope} : Nat → RawTerm scope`** — the scope-polymorphic closed numeral (`natZero` / iterated
    `natSucc`).  The existing `natNumeralCell` is fixed at scope 0; under `mulStep`'s binders the numeral lives at
    scope 2, so a scope-general builder is required.
  * **`natNumeralAt_subst` (★)** — `subst σ (natNumeralAt m) = natNumeralAt m` for EVERY substitution `σ` and
    every `m`.  Induction on `m`: the `natZero` base is `rfl` (subst over a nullary closed cell); the `natSucc`
    step uses `subst_natSucc_reduces` (definitional) to expose `natSucc (subst σ (natNumeralAt n))` then the IH.
    A closed term has no free variables for `σ` to act on, so it is invariant — but Lean needs the induction
    because the symbolic `natNumeralAt m` does not unfold.
  * **`natNumeralAt_zero_eq_natNumeralCell`** — at scope 0 the scope-general builder agrees with the existing
    `natNumeralCell`, bridging this substrate to `NatElimFaithfulArithmetic.natElimAddFaithful`.

## Zero-axiom

`natNumeralAt_subst` is structural recursion on `m` (`rfl` base + `show` to the `subst_natSucc_reduces`-exposed
form + `rw` the IH); the bridge is a two-arm induction with `congrArg`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The scope-polymorphic closed de Bruijn numeral (`natNumeralCell` is fixed at scope 0; this generalizes for
use under binders, e.g. inside a multiplication step). -/
def natNumeralAt {scope : Nat} : Nat → RawTerm scope
  | 0 => natZeroCell
  | n + 1 => natSuccCell (natNumeralAt n)

/-- **★ A closed numeral is invariant under any substitution.**  `subst σ (natNumeralAt m) = natNumeralAt m` —
the crack in the `Nat.mul` β-reduction wall: a closed numeral has no free variables, so any substitution fixes
it, but the symbolic `natNumeralAt m` does not unfold, so the proof is induction on `m` (not `rfl`). -/
theorem natNumeralAt_subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    ∀ m, RawTerm.subst substitution (natNumeralAt m) = (natNumeralAt m : RawTerm targetScope)
  | 0 => rfl
  | n + 1 => by
      show natSuccCell (RawTerm.subst substitution (natNumeralAt n)) = natSuccCell (natNumeralAt n)
      rw [natNumeralAt_subst substitution n]

/-- At scope 0 the scope-general numeral builder agrees with the existing `natNumeralCell` — bridges this
substrate to `NatElimFaithfulArithmetic.natElimAddFaithful` for the eventual `Nat.mul` assembly. -/
theorem natNumeralAt_zero_eq_natNumeralCell : ∀ m, (natNumeralAt (scope := 0) m) = natNumeralCell m
  | 0 => rfl
  | n + 1 => by
      show natSuccCell (natNumeralAt n) = natSuccCell (natNumeralCell n)
      rw [natNumeralAt_zero_eq_natNumeralCell n]

end FX1Poly.Typed
