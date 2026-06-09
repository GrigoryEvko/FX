import FX1Poly.Typed.ValueElimHostFold
import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.HasTypeDescIdIntro

/-! # FX1Poly/Typed/RecursorHostFold — the last two eliminators compute their host folds (`natRec`, `idStrictRec`)

`ValueElimHostFold` proved the six value-case eliminators (`boolElim ↝ cond`, `fst`/`snd ↝ Prod.fst`/`Prod.snd`,
`optionMatch ↝ Option.elim`, `eitherMatch ↝ Sum.elim`, `idJ ↝ Eq.rec`) compute their host folds, and
`NatElimFaithfulMul` / `ListElimFaithfulLength` did the two recursive ones (`natElim ↝ Nat.mul`,
`listElim ↝ List.length`).  That left exactly two of the ten data eliminators without a host-fold theorem:
the dependent Nat recursor `natRec` and the strict identity recursor `idStrictRec`.  This file closes them,
completing per-eliminator host-fold faithfulness to all ten:

  * **`natRecZeroHostFold`** — `natRec natZero z s ↝ z` (host `Nat.rec` base clause).
  * **`natRecSuccHostFold`** — `natRec (natSucc p) z s ↝ s p (natRec p z s)` (host `Nat.rec` successor clause:
    the step branch applied to the predecessor and the recursive result).  These two ARE the defining clauses
    of the host `Nat.rec` recursor, so `gen_natRec` computes exactly the host dependent Nat recursor.
  * **`idStrictRecHostFold`** — `idStrictRec base (refl w) ↝ base` (host strict `Eq.rec` on `rfl` returns the
    base case) — the strict-recursor twin of `idJHostFold`.

`natRecCell` / `idStrictRecCell` are the eliminator-cell builders (no prior builder existed); their shapes match
the `Step.iotaNatRec{Zero,Succ}` / `Step.iotaIdStrictRecRefl` redex heads, so each host-fold is a single
`StepStar.single` of the matching `Step.iota` rule whose reduct IS the host clause by `rfl`.

Honest strength note: `idStrictRecHostFold` is single-ι branch selection (exactly the strength of `idJHostFold`
and the other value-case folds).  The two `natRec` theorems are the recursor's host computation CLAUSES (the
`Nat.rec` defining equations), the `natRec` twin of `natElim`'s ι rules — NOT a closed-form-on-numerals result
(that stronger shape is `natElim ↝ Nat.mul`, which for `natRec` would hit the same `subst0`-commutation step).

## Zero-axiom

Each theorem is `StepStar.single` of the matching `Step.iota` constructor; the reduct is definitionally the host
clause.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The `natRec` eliminator cell: scrutinee + zero-branch + successor-branch. -/
def natRecCell {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natRec () (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The `idStrictRec` eliminator cell: base-case + scrutinee (the strict identity recursor). -/
def idStrictRecCell {scope : Nat} (baseCase scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idStrictRec () (.childCons baseCase (.childCons scrutinee .childNil))

/-- **★ `natRec` on `natZero` computes the host `Nat.rec` base clause.**  `natRec natZero z s ↝ z` via
`Step.iotaNatRecZero` — the recursor on zero projects the zero-branch, exactly as host `Nat.rec`. -/
theorem natRecZeroHostFold {scope : Nat} (zeroBranch succBranch : RawTerm scope) :
    StepStar (natRecCell natZeroCell zeroBranch succBranch) zeroBranch :=
  StepStar.single Step.iotaNatRecZero

/-- **★ `natRec` on `natSucc` computes the host `Nat.rec` successor clause.**  `natRec (natSucc p) z s ↝
s p (natRec p z s)` via `Step.iotaNatRecSucc` — the step-branch applied to the predecessor and the recursive
call, exactly the host `Nat.rec` successor equation. -/
theorem natRecSuccHostFold {scope : Nat} (predecessor zeroBranch succBranch : RawTerm scope) :
    StepStar (natRecCell (natSuccCell predecessor) zeroBranch succBranch)
      (appCell (appCell succBranch predecessor) (natRecCell predecessor zeroBranch succBranch)) :=
  StepStar.single Step.iotaNatRecSucc

/-- **★ `idStrictRec` on `refl` computes the host strict `Eq.rec` base.**  `idStrictRec base (refl w) ↝ base`
via `Step.iotaIdStrictRecRefl` — strict path induction on reflexivity returns the base case, the strict-recursor
twin of `idJHostFold`. -/
theorem idStrictRecHostFold {scope : Nat} (baseCase witness : RawTerm scope) :
    StepStar (idStrictRecCell baseCase (reflCell witness)) baseCase :=
  StepStar.single Step.iotaIdStrictRecRefl

end FX1Poly.Typed
