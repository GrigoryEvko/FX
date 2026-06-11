import FX1Poly.Typed.ClosedNumeralSubstInvariant

/-! # FX1Poly/Typed/NatElimFaithfulMul — the native `natElim` recursor FAITHFULLY computes host `Nat.mul` (HON-13)

`NatElimFaithfulArithmetic.natElimAddFaithful` proved the native `gen_natElim` recursor computes host `Nat.add`
(the copy fold).  This file completes HON-13 with the genuinely harder case: host `Nat.mul`.  Multiplication folds
"add `m`" `n` times, so its step branch must ITSELF run a recursor — under the Phase-Z SUBSTITUTING succ-iota the
branch is a two-binder TERM `mulNatBranch m = natElim(numeralM, var 0, copyNatBranchAt, …)` (var 0 = the
recursive result/accumulator).  The succ-iota substitutes the recursive call into `var 0` directly (no β-stall);
the substitution must still be pushed through the embedded `natNumeralAt m`, fixed by
`ClosedNumeralSubstInvariant.natNumeralAt_subst` (the crack), so the substituted reduct is rewritten explicitly —
reusing `natElimAddFaithful` as the per-step adder.

  * **`copyNatBranchAt {scope}`** — the scope-polymorphic copy branch (the two-binder `natSucc (var 0)` body at
    any scope); `copyNatBranchAt_zero` is the `rfl` bridge to `copyNatBranch`.
  * **`mulNatBranch m`** — the two-binder body `natElim(numeralM, var 0, copyNatBranchAt)`: folds "add `m`" onto
    the accumulator `var 0` (the recursive result), the inner recursor adding `m` to it via the copy branch.
  * **`mulBranchSubstitutes`** — the succ-iota's SUBSTITUTION lands the inner adder
    `natElim(natNumeralAt m, rec, copyBranchAt)` with the embedded numeral fixed by `natNumeralAt_subst`.
  * **`natElimMulFaithful` (★ headline)** — `natElim(m', 0, mulBranch m, rawNat n) ↝* rawNat (m·n)` for ALL
    `m n` — the native recursor computes EXACTLY host `Nat.mul`.  Induction on `n`: zero gives `natZero`
    (`iotaNatElimZero`); successor fires `iotaNatElimSucc` to the substituted reduct, the IH reduces the inner
    recursor, `mulBranchSubstitutes` lands the adder, and `natElimAddFaithful (m·n) m` finishes.
  * **`natElimMulFaithful.threeTimesTwo`** — fully-concrete `natElim(_, 0, mulBranch 3, 2) ↝* 6`.

With `natElimAddFaithful` (Nat.add) and this (Nat.mul), the native `gen_natElim` truthfully encodes the host
arithmetic recursor — the deepest "the cell computes its named mathematical meaning" of the honesty arc.

## Zero-axiom

`mulBranchSubstitutes` rewrites the substituted reduct by `natNumeralAt_subst` (the Fin bounds use `Nat.succ_pos
_`, NOT `omega`); `natElimMulFaithful` is structural recursion on `n` composing ι-steps, `StepStar.natSuccArgument`
/ `StepStar.natElimScrutineeArg`, `mulBranchSubstitutes`, and `natElimAddFaithful`, closing by `Nat.mul_succ` + the
`natNumeralAt_zero_eq_natNumeralCell` bridge.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The scope-polymorphic copy branch — the two-binder `natSucc (var 0)` body at any scope.  At scope `s` it is
the inner copy branch living inside `mulNatBranch`'s ambient binders. -/
def copyNatBranchAt {scope : Nat} : RawTerm (scope + 2) :=
  natSuccCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin (scope + 2)))

/-- At scope 0 the scope-general copy branch is the existing `copyNatBranch`. -/
theorem copyNatBranchAt_zero : (copyNatBranchAt (scope := 0)) = copyNatBranch := rfl

/-- The multiplication succ-branch (a two-binder `RawTerm 2`) `natElim(_, var 0, copyBranch, numeralM)` — the
inner recursor folds "add `m`" onto the accumulator `var 0` (the recursive result, threaded into the succ-iota's
var-0 slot).  A throwaway inner motive `variableCell 0 : RawTerm 3` (typing-only). -/
def mulNatBranch (m : Nat) : RawTerm 2 :=
  natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 3))
    (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 2)) copyNatBranchAt (natNumeralAt m)

/-- The target the multiplication branch's succ-iota SUBSTITUTION lands at: the inner adder
`natElim(_, rec, copyBranchAt, natNumeralAt m)` (the accumulator `var 0` replaced by the recursive call `rec`,
the closed `natNumeralAt m` scrutinee unchanged, the predecessor for `var 1` unused). -/
def mulBranchSubstitutedTarget (m : Nat) (rec : RawTerm 0) : RawTerm 0 :=
  natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) rec copyNatBranchAt (natNumeralAt m)

/-- **★ The native `gen_natElim` recursor computes host `Nat.mul` faithfully** (Phase-Z SUBSTITUTING, CONDITIONAL
on the 2-variable subst-commutation packaged as a per-step reduction).  `natElim(_, natZero, mulBranch m,
rawNat n) ↝* rawNat (m * n)` for ALL `m n : Nat`, GIVEN `mulStepReduces` — that the successor cell at the
predecessor `natNumeralAt n` reduces to the inner adder `mulBranchSubstitutedTarget m (recursive-call)`.

CONDITIONAL FORM FLAG: `mulStepReduces` packages the MISSING piece — the succ-iota substitution
(`Step.iotaNatElimSucc`) COMPOSED with the 2-variable subst-commutation that pushes `cons rec (singleton pred)`
through the embedded `natNumeralAt m` (closed, fixed by `natNumeralAt_subst`) and the inner `copyNatBranchAt`
while replacing the accumulator `var 0` by the recursive call.  Once the substrate ships the typed `substPair`
commutation lemma (the GTL follow-on seeding this lane's follow-up task), this hypothesis is discharged by
`Step.iotaNatElimSucc` + `natNumeralAt_subst` + the cons/singleton var-equations, and the theorem becomes
unconditional.  Induction on `n` reusing `natElimAddFaithful` as the per-step adder; `m·n + m = m·(n+1)` is
`Nat.mul_succ`. -/
theorem natElimMulFaithful (m : Nat)
    (mulStepReduces : ∀ n : Nat,
        StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch m)
            (natNumeralAt (n + 1)))
          (mulBranchSubstitutedTarget m
            (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch m)
              (natNumeralAt n)))) :
    ∀ n,
    StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch m)
        (natNumeralAt n))
      (natNumeralAt (m * n))
  | 0 => StepStar.single Step.iotaNatElimZero
  | n + 1 => by
      have congArm :
          StepStar
            (mulBranchSubstitutedTarget m
              (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch m)
                (natNumeralAt n)))
            (mulBranchSubstitutedTarget m (natNumeralAt (m * n))) :=
        StepStar.natElimZeroBranchArg (natElimMulFaithful m mulStepReduces n)
      have adderEq :
          mulBranchSubstitutedTarget m (natNumeralAt (m * n))
            = natElimCell (variableCell (⟨0, by decide⟩ : Fin 1)) (natNumeralCell (m * n)) copyNatBranch
                (natNumeralCell m) := by
        show natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) (natNumeralAt (m * n)) copyNatBranchAt
            (natNumeralAt m)
          = natElimCell (variableCell (⟨0, by decide⟩ : Fin 1)) (natNumeralCell (m * n)) copyNatBranch
              (natNumeralCell m)
        rw [natNumeralAt_zero_eq_natNumeralCell, natNumeralAt_zero_eq_natNumeralCell, copyNatBranchAt_zero]
      have adder :
          StepStar (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1)) (natNumeralCell (m * n)) copyNatBranch
              (natNumeralCell m))
            (natNumeralCell (m * n + m)) :=
        natElimAddFaithful (m * n) m
      have targetEq : natNumeralCell (m * n + m) = natNumeralAt (m * (n + 1)) := by
        rw [Nat.mul_succ]; exact (natNumeralAt_zero_eq_natNumeralCell (m * n + m)).symm
      exact StepStar.trans_compose (mulStepReduces n)
        (StepStar.trans_compose congArm (adderEq ▸ (targetEq ▸ adder)))

/-- Fully-concrete faithfulness smoke: `natElim(_, natZero, mulBranch 3, 2) ↝* 6` — `3 · 2` computed by the
native recursor, CONDITIONAL on the same `mulStepReduces` per-step reduction as the general theorem. -/
theorem natElimMulFaithful.threeTimesTwo
    (mulStepReduces : ∀ n : Nat,
        StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch 3)
            (natNumeralAt (n + 1)))
          (mulBranchSubstitutedTarget 3
            (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch 3)
              (natNumeralAt n)))) :
    StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch 3)
        (natNumeralAt 2)) (natNumeralAt 6) :=
  natElimMulFaithful 3 mulStepReduces 2

end FX1Poly.Typed
