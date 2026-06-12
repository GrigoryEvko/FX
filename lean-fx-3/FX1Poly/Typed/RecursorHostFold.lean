import FX1Poly.Typed.ValueElimHostFold

/-! # FX1Poly/Typed/RecursorHostFold — the last two eliminators compute their host folds (`natRec`, `idStrictRec`)

`ValueElimHostFold` proved the six value-case eliminators (`boolElim ↝ cond`, `fst`/`snd ↝ Prod.fst`/`Prod.snd`,
`optionMatch ↝ Option.elim`, `eitherMatch ↝ Sum.elim`, `idJ ↝ Eq.rec`) compute their host folds, and
`NatElimFaithfulMul` / `ListElimFaithfulLength` did the two recursive ones (`natElim ↝ Nat.mul`,
`listElim ↝ List.length`).  That left exactly two of the ten data eliminators without a host-fold theorem:
the dependent Nat recursor `natRec` and the strict identity recursor `idStrictRec`.  This file closes them,
completing per-eliminator host-fold faithfulness to all ten:

  * **`natRecZeroHostFold`** — `natRec m z s natZero ↝ z` (host `Nat.rec` base clause).
  * **`natRecSuccHostFold`** — Phase-Z SUBSTITUTING successor clause: `natRec m z s (natSucc p) ↝
    s[var 0 := natRec m z s p, var 1 := p]` (the host `Nat.rec` successor equation, with the step branch's
    two binders — recursive result + predecessor — filled by SUBSTITUTION rather than application).  These two
    ARE the defining clauses of the host `Nat.rec` recursor, so `gen_natRec` computes exactly the host dependent
    Nat recursor.
  * **`idStrictRecHostFold`** — `idStrictRec motive base (refl w) ↝ base` (host strict `Eq.rec` on `rfl` returns
    the base case; the Phase-Z stored motive is discarded by the refl-ι) — the strict-recursor twin of
    `idJHostFold`.

`natRecCell` / `idStrictRecCell` are the eliminator-cell builders; their shapes match the
`Step.iotaNatRec{Zero,Succ}` / `Step.iotaIdStrictRecRefl` redex heads, so each host-fold is a single
`StepStar.single` of the matching `Step.iota` rule whose reduct IS the host clause by `rfl`.

Honest strength note: `idStrictRecHostFold` is single-ι branch selection (exactly the strength of `idJHostFold`
and the other value-case folds).  The two `natRec` theorems are the recursor's host computation CLAUSES (the
`Nat.rec` defining equations), the `natRec` twin of `natElim`'s ι rules — NOT a closed-form-on-numerals result.

## Zero-axiom

Each theorem is `StepStar.single` of the matching `Step.iota` constructor; the reduct is definitionally the host
clause.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ `natRec` on `natZero` computes the host `Nat.rec` base clause.**  `natRec m z s natZero ↝ z` via
`Step.iotaNatRecZero` — the recursor on zero projects the zero-branch, exactly as host `Nat.rec`. -/
theorem natRecZeroHostFold {scope : Nat} (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    StepStar (natRecCell motive zeroBranch succBranch natZeroCell) zeroBranch :=
  StepStar.single Step.iotaNatRecZero

/-- **★ `natRec` on `natSucc` computes the host `Nat.rec` successor clause** (Phase-Z SUBSTITUTING).
`natRec m z s (natSucc p) ↝ s[var 0 := natRec m z s p, var 1 := p]` via `Step.iotaNatRecSucc` — the step-branch's
two binders (recursive result + predecessor) filled by SUBSTITUTION, exactly the host `Nat.rec` successor
equation. -/
theorem natRecSuccHostFold {scope : Nat} (motive : RawTerm (scope + 1))
    (predecessor zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) :
    StepStar (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
      (natRecSuccContractum motive zeroBranch succBranch predecessor) :=
  StepStar.single Step.iotaNatRecSucc

/-- **★ `idStrictRec` on `refl` computes the host strict `Eq.rec` base.**  `idStrictRec motive base (refl w) ↝
base` via `Step.iotaIdStrictRecRefl` — strict path induction on reflexivity returns the base case (the Phase-Z
stored motive is DISCARDED by the refl-ι), the strict-recursor twin of `idJHostFold`. -/
theorem idStrictRecHostFold {scope : Nat} (motive : RawTerm (scope + 2))
    (baseCase witness : RawTerm scope) :
    StepStar (idStrictRecCell motive baseCase (reflCell witness)) baseCase :=
  StepStar.single Step.iotaIdStrictRecRefl

end FX1Poly.Typed
