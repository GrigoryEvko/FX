import FX1Poly.Core.RawSize
import FX1Poly.Core.Step

/-! # FX1Poly/Core/RecursiveIotaSizeGrowth
    — #1139 (Leg 3): the RECURSIVE ι arm INCREASES `RawTerm.size` by `branchSize + 13`, growing with the
    branch — so the firing-67 size route does NOT extend to the recursive arms; full RPO is necessary

Firing-67 (`IotaNonRecursiveTermination`) proved the NON-recursive ι arms strictly DECREASE
`RawTerm.size`, giving that fragment a clean size-measure SN.  This file establishes the sharp contrast
for the RECURSIVE arms, on the REAL kernel.  Under the Phase-Z motive shape the natElimSucc reduction
SUBSTITUTES:

    natElim m z s (natSucc p)  ↝  s[var 0 := natElim m z s p, var 1 := p]

When the step branch `s` uses its induction-hypothesis variable `var 0` TWICE — here the duplicating
branch `app (var 0) (var 0)` — the substitution DUPLICATES the recursive call `natElim m z s p`, and with
it the zero branch `z` it carries.  Concretely, for motive `var 0`, zero-branch `branch`, step branch
`app (var 0) (var 0)`, and scrutinee `natSucc natZero`:

    (reduct).size = (redex).size + branch.size + 13      (★ `natElimSuccReduct_size_eq`)

so the size INCREASES, and the increase `branch.size + 13` GROWS without bound as the zero branch grows
(`natElimSucc_size_increase_at_least_branch`).  This refutes `RawTerm.size` — and any flat numeric
measure dominated by it — as a termination measure for the recursive ι: the duplicated recursive call
carries an independent branch of arbitrary size, so no flat per-eliminator weight survives duplication.

## Why this matters for the Leg-3 roadmap (honest scope correction)

  * Firing-66's `RecursiveEliminatorTermination` RecTerm model terminated via a FLAT
    scrutinee-multiset (Dershowitz-Manna over `Nat.lt`).  That worked only because its `branch` nodes
    duplicated the recursive CALL (`elim k`), never an INDEPENDENT eliminator with an unrelated, possibly
    larger scrutinee.  The real Phase-Z `natElimSucc` substitution duplicates the whole recursive call
    (motive + branches included) — the case the model did not capture.  So firing-67's docstring
    suggestion of "a real multiset measure on actual cells" for the recursive arm was over-optimistic: a
    flat multiset does NOT suffice.
  * Moreover the SUBSTITUTING succ-iota is not even erasure-RPO-orientable (it shares β's
    argument-duplication shape — `betaNotOrientableByErasure`), which is exactly why the Phase-Z re-scope
    moves it to the β-imported boundary (`IotaOrientedHeadStep` keeps only the non-substituting arms);
    typed SN covers it through Tait.  The β boundary stays honestly Tait-imported (β is non-SN raw,
    SN-NECESSITY #950).

## Zero-axiom verification

`Step.iotaNatElimSucc` for the reduction (the hand-written `app(R, R)` reduct is DEFINITIONALLY the
kernel's substitution instance — all pieces concrete except the closed zero branch, which the
substitution never touches); structural `RawTerm.size` computation via `dsimp`; the symbolic size
equality closes by `simp only [Nat.add_zero, Nat.zero_add]` (axiom-clean — no comm/assoc, no propext
leak) plus a `generalize` and explicit `Nat.add_comm`/`Nat.add_right_comm` flips of the stuck sums.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The duplicating step branch `app (var 0) (var 0)` (under the two Phase-Z binders: `var 0` is the
induction hypothesis) — using the IH twice is what makes the substitution duplicate the recursive
call. -/
def natElimDuplicatingSuccBranch : RawTerm 2 :=
  .mkGen .gen_app ()
    (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil)
      (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil) .childNil))

/-- The Phase-Z natElimSucc redex: motive `var 0`, zero-branch `branch` (the unbounded payload),
step branch `app (var 0) (var 0)`, scrutinee `natSucc natZero` LAST. -/
def natElimSuccRedex (branch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natElim ()
    (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
      (.childCons branch
        (.childCons natElimDuplicatingSuccBranch
          (.childCons
            (.mkGen .gen_natSucc ()
              (.childCons (.mkGen .gen_natZero () .childNil) .childNil))
            .childNil))))

/-- The recursive call the substitution plugs in for the IH: the same eliminator on the predecessor
`natZero` (carrying `branch` along). -/
def natElimSuccRecursiveCall (branch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natElim ()
    (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
      (.childCons branch
        (.childCons natElimDuplicatingSuccBranch
          (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))

/-- Its Phase-Z ι reduct `app (natElim … natZero) (natElim … natZero)` — the recursive call (and the
`branch` it carries) DUPLICATED by the substitution, because the step branch uses the IH twice. -/
def natElimSuccReduct (branch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons (natElimSuccRecursiveCall branch)
      (.childCons (natElimSuccRecursiveCall branch) .childNil))

/-- The redex really reduces to the reduct via the real kernel `Step.iotaNatElimSucc` — this is a
genuine reduction of the live `Step` relation, not a contrived pair (the hand-written `app(R, R)` is
definitionally the kernel's substitution instance). -/
theorem natElimSucc_isRealStep (branch : RawTerm 0) :
    Step (natElimSuccRedex branch) (natElimSuccReduct branch) :=
  Step.iotaNatElimSucc

/-- **★ The recursive ι arm INCREASES size by `branchSize + 13`.**  The reduct's size exceeds the
redex's by `branch.size + 13` — the `branch.size` term is the cost of DUPLICATING the recursive call
(which carries the branch).  Contrast `IotaNonRecursiveStep.size_decreases` (firing-67): non-recursive
ι strictly decreases size. -/
theorem natElimSuccReduct_size_eq (branch : RawTerm 0) :
    (natElimSuccReduct branch).size = (natElimSuccRedex branch).size + branch.size + 13 := by
  dsimp only [natElimSuccReduct, natElimSuccRecursiveCall, natElimSuccRedex,
    natElimDuplicatingSuccBranch, RawTerm.size, RawTermChildren.size]
  generalize branch.size = payloadSize
  simp only [Nat.add_zero, Nat.zero_add]
  -- Both sides are sums of payloadSize (twice) and numerals.  Nat.add recurses on
  -- the RIGHT, so closed right-addends fold definitionally but `1 + payloadSize`
  -- is STUCK (and NOT defeq to `payloadSize + 1`): `show` compacts each side to
  -- its canonical stuck form over the `1 + payloadSize` core, one explicit
  -- add_comm flips that core, and two add_right_comm flips (propext-clean,
  -- unlike simp-with-AC) converge both sides to `payloadSize + payloadSize + 27`.
  show 1 + payloadSize + 11 + (1 + payloadSize) + 14
      = 1 + payloadSize + 13 + payloadSize + 13
  rw [Nat.add_comm 1 payloadSize]
  show payloadSize + 12 + payloadSize + 15 = payloadSize + 14 + payloadSize + 13
  rw [Nat.add_right_comm payloadSize 12 payloadSize,
    Nat.add_right_comm payloadSize 14 payloadSize]

/-- The recursive ι arm strictly increases `RawTerm.size` — so size is NOT a termination measure here. -/
theorem natElimSucc_size_increases (branch : RawTerm 0) :
    (natElimSuccRedex branch).size < (natElimSuccReduct branch).size := by
  rw [natElimSuccReduct_size_eq]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right _ branch.size))
    (Nat.le_add_right _ 12)

/-- **★ The size increase is at least `branch.size` — UNBOUNDED across branches.**  Since `branch` is
arbitrary, the recursive ι reduction's size increase grows without bound, so NO flat measure dominated
by `RawTerm.size` can certify the recursive ι: this is the branch-duplication obstruction that (together
with `betaNotOrientableByErasure`) forces the substituting succ-iota to the β-imported boundary. -/
theorem natElimSucc_size_increase_at_least_branch (branch : RawTerm 0) :
    (natElimSuccRedex branch).size + branch.size ≤ (natElimSuccReduct branch).size := by
  rw [natElimSuccReduct_size_eq]
  exact Nat.le_add_right _ 13

end FX1Poly.Core
