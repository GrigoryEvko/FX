import FX1Poly.Core.RawSize
import FX1Poly.Core.Step

/-! # FX1Poly/Core/RecursiveIotaSizeGrowth
    — #1139 (Leg 3): the RECURSIVE ι arm INCREASES `RawTerm.size` by `branchSize + 5`, growing with the
    branch — so the firing-67 size route does NOT extend to the recursive arms; full RPO is necessary

Firing-67 (`IotaNonRecursiveTermination`) proved the 13 NON-recursive ι arms strictly DECREASE
`RawTerm.size`, giving that fragment a clean size-measure SN.  This file establishes the sharp contrast
for the RECURSIVE arms, on the REAL kernel: the natElimSucc reduction

    natElim (natSucc n) z s  ↝  app (app s n) (natElim n z s)

DUPLICATES the branch `s` (it appears in both `app s n` and the recursive `natElim n z s`).  Concretely,
for the scrutinee `natSucc natZero` and branches `natZero` / `branch`:

    (reduct).size = (redex).size + branch.size + 5      (★ `natElimSuccReduct_size_eq`)

so the size INCREASES, and the increase `branch.size + 5` GROWS without bound as the branch grows
(`natElimSucc_size_increase_at_least_branch`).  This refutes `RawTerm.size` — and any flat numeric
measure dominated by it — as a termination measure for the recursive ι: a duplicated branch can carry an
independent eliminator of arbitrary size, so no flat per-eliminator weight survives duplication.

## Why this matters for the Leg-3 roadmap (honest scope correction)

  * Firing-66's `RecursiveEliminatorTermination` RecTerm model terminated via a FLAT
    scrutinee-multiset (Dershowitz-Manna over `Nat.lt`).  That worked only because its `branch` nodes
    duplicated the recursive CALL (`elim k`), never an INDEPENDENT eliminator with an unrelated, possibly
    larger scrutinee.  The real `natElimSucc` duplicates an arbitrary branch `s` — the case the model did
    not capture.  So firing-67's docstring suggestion of "a real multiset measure on actual cells" for the
    recursive arm was over-optimistic: a flat multiset does NOT suffice.
  * The resolution is a full recursive PATH ORDER (RPO) with precedence `eliminator > app`: there,
    `natElim (natSucc n) z s ≻ app (app s n) (natElim n z s)` because `natElim` outranks `app` and every
    proper subterm of the reduct (`s`, `n`, `app s n`, `natElim n z s`) is `≺` the redex — RPO's
    subterm-property tames branch-duplication regardless of `s`'s size.  The shipped single-level
    certificates `wellFounded_of_precedence{Lex,Multiset}Measure` (`RecursivePathOrder`) compare head
    precedence then the immediate-argument multiset, but do NOT recurse into subterms, so they are
    insufficient for the CONGRUENCE-closed recursive ι; a genuine RPO-on-`RawTerm` is the named
    multi-firing build.  The β boundary stays honestly Tait-imported (β is non-SN raw, SN-NECESSITY #950).

## Zero-axiom verification

`Step.iotaNatElimSucc` for the reduction; structural `RawTerm.size` computation via `dsimp`; the symbolic
size equality closes by `simp only [Nat.add_zero, Nat.zero_add]` (axiom-clean — no comm/assoc, no propext
leak), a `generalize` of the shared subterm, two `Nat.add_comm` flips of the stuck `k + c` terms, and a
defeq-`show` + `Nat.add_right_comm`/`add_comm` tail (both sides defeq `succ¹⁰(branchSize + c)`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The natElimSucc redex on scrutinee `natSucc natZero` with zero-branch `natZero` and succ-branch
`branch`. -/
def natElimSuccRedex (branch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natElim ()
    (.childCons (.mkGen .gen_natSucc () (.childCons (.mkGen .gen_natZero () .childNil) .childNil))
      (.childCons (.mkGen .gen_natZero () .childNil) (.childCons branch .childNil)))

/-- Its ι reduct `app (app branch natZero) (natElim natZero natZero branch)` — `branch` DUPLICATED
(once in the `app … branch …`-spine, once in the recursive `natElim … branch`). -/
def natElimSuccReduct (branch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons branch (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))
      (.childCons
        (.mkGen .gen_natElim ()
          (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons (.mkGen .gen_natZero () .childNil) (.childCons branch .childNil))))
        .childNil))

/-- The redex really reduces to the reduct via the real kernel `Step.iotaNatElimSucc` — this is a
genuine reduction of the live `Step` relation, not a contrived pair. -/
theorem natElimSucc_isRealStep (branch : RawTerm 0) :
    Step (natElimSuccRedex branch) (natElimSuccReduct branch) :=
  Step.iotaNatElimSucc

/-- **★ The recursive ι arm INCREASES size by `branchSize + 5`.**  The reduct's size exceeds the
redex's by `branch.size + 5` — the `branch.size` term is the cost of DUPLICATING the branch.  Contrast
`IotaNonRecursiveStep.size_decreases` (firing-67): non-recursive ι strictly decreases size. -/
theorem natElimSuccReduct_size_eq (branch : RawTerm 0) :
    (natElimSuccReduct branch).size = (natElimSuccRedex branch).size + branch.size + 5 := by
  dsimp only [natElimSuccReduct, natElimSuccRedex, RawTerm.size, RawTermChildren.size]
  generalize branch.size = b
  simp only [Nat.add_zero, Nat.zero_add]
  generalize 1 + (b + 1) + 1 = c
  rw [Nat.add_comm 1 c]
  rw [show (1 : Nat) + 1 + 1 + c = c + 3 from by rw [Nat.add_comm (1 + 1 + 1) c]]
  show b + 4 + c + 6 = c + 5 + b + 5
  rw [Nat.add_right_comm b 4 c, Nat.add_right_comm c 5 b, Nat.add_comm c b]

/-- The recursive ι arm strictly increases `RawTerm.size` — so size is NOT a termination measure here. -/
theorem natElimSucc_size_increases (branch : RawTerm 0) :
    (natElimSuccRedex branch).size < (natElimSuccReduct branch).size := by
  rw [natElimSuccReduct_size_eq]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right _ branch.size))
    (Nat.le_add_right _ 4)

/-- **★ The size increase is at least `branch.size` — UNBOUNDED across branches.**  Since `branch` is
arbitrary, the recursive ι reduction's size increase grows without bound, so NO flat measure dominated
by `RawTerm.size` can certify the recursive ι: this is the branch-duplication obstruction that forces a
recursive path order (precedence eliminator > app). -/
theorem natElimSucc_size_increase_at_least_branch (branch : RawTerm 0) :
    (natElimSuccRedex branch).size + branch.size ≤ (natElimSuccReduct branch).size := by
  rw [natElimSuccReduct_size_eq]
  exact Nat.le_add_right _ 5

end FX1Poly.Core
