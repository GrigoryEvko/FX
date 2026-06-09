import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.HasTypeDescSigmaProjection
import FX1Poly.Typed.HasTypeDescOptionMatch
import FX1Poly.Typed.HasTypeDescEitherMatch
import FX1Poly.Typed.HasTypeDescIdElim

/-! # FX1Poly/Typed/ValueElimHostFold — the value-case eliminators FAITHFULLY compute their HOST folds (HON-14)

`NatElimFaithfulArithmetic` / `NatElimFaithfulMul` (HON-13) and `ListElimFaithfulLength` (HON-12) proved the
RECURSIVE eliminators compute their host recursors (`Nat.add` / `Nat.mul` / `List.length`).  The shipped
`*IotaComputesTyped` theorems for the VALUE-case (non-recursive) eliminators pin only "the eliminator ι-reduces
to its branch by the kernel's own `Step.iota` rule" — they stop at the kernel rule, not at the HOST meaning.
HON-14 closes that per-eliminator "proof of meaning" gap: each value-case eliminator, run on the raw cell of a
HOST scrutinee, reduces to exactly what the corresponding HOST eliminator computes.

  * **`boolElimHostFold`** — `boolElim (rawBool b) t e ↝* cond b t e` (host `Bool.rec` / `cond`).
  * **`fstHostFold` / `sndHostFold`** — `fst (pair p.1 p.2) ↝* p.1` and `snd ↝* p.2` (host `Prod.fst` / `Prod.snd`).
  * **`optionMatchHostFold`** — `optionMatch (rawOption o) n s ↝* o.elim n (s ·)` (host `Option.elim`).
  * **`eitherMatchHostFold`** — `eitherMatch (rawEither e) l r ↝* Sum.elim (l ·) (r ·) e` (host `Sum.elim`).
  * **`idJHostFold`** — `idJ base (refl w) ↝* base` (host `Eq.rec` on `rfl` returns the base case).

Each is a two-case (or one-case) proof: `cases` the host scrutinee, then the matching `Step.iota` rule fires the
ι-reduct, which is DEFINITIONALLY the host eliminator's branch selection (`cond true t e = t`, `Option.elim
(some v) n f = f v`, etc.).  With HON-12/13 (recursive eliminators) this completes the faithfulness coverage:
every native FX eliminator computes its named host meaning — the deepest "the cell truthfully encodes its
mathematical content" of the honesty arc.

  * **`boolElimHostFold.selectsThen` / `optionMatchHostFold.firesSome`** — concrete smokes pinning that the fold
    selects the correct branch on a chosen scrutinee.

## Zero-axiom

Each theorem is `cases` on the host value (`Bool` / `Option` / `Sum`) — or direct for the single-shape
`fst`/`snd`/`idJ` — then `StepStar.single` of the matching `Step.iota` rule, whose reduct is the host fold's
branch by `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The raw bool value cell of a host `Bool`. -/
def rawBoolCell {scope : Nat} : Bool → RawTerm scope
  | true => boolTrueCell
  | false => boolFalseCell

/-- The raw option value cell of a host `Option`. -/
def rawOptionCell {scope : Nat} : Option (RawTerm scope) → RawTerm scope
  | none => optionNoneCell
  | some value => optionSomeCell value

/-- The raw either value cell of a host `Sum`. -/
def rawEitherCell {scope : Nat} : (RawTerm scope) ⊕ (RawTerm scope) → RawTerm scope
  | Sum.inl value => eitherInlCell value
  | Sum.inr value => eitherInrCell value

/-- **★ `boolElim` computes the host `cond` (Bool elimination).**  `boolElim (rawBool b) t e ↝* cond b t e` for
every host `b : Bool` — the native eliminator selects the branch the host `Bool.rec` selects.  Two cases: the
`Step.iotaBoolTrue` / `Step.iotaBoolFalse` reducts are `t` / `e`, which are `cond true t e` / `cond false t e`
definitionally. -/
theorem boolElimHostFold {scope : Nat} (selector : Bool) (thenBranch elseBranch : RawTerm scope) :
    StepStar (boolElimCell (rawBoolCell selector) thenBranch elseBranch)
      (cond selector thenBranch elseBranch) := by
  cases selector
  · exact StepStar.single Step.iotaBoolFalse
  · exact StepStar.single Step.iotaBoolTrue

/-- **★ `fst` computes the host `Prod.fst`.**  `fst (pair p.1 p.2) ↝* p.1` via `Step.iotaFstPair`. -/
theorem fstHostFold {scope : Nat} (pairHost : (RawTerm scope) × (RawTerm scope)) :
    StepStar (fstCell (pairCell pairHost.1 pairHost.2)) (Prod.fst pairHost) :=
  StepStar.single Step.iotaFstPair

/-- **★ `snd` computes the host `Prod.snd`.**  `snd (pair p.1 p.2) ↝* p.2` via `Step.iotaSndPair`. -/
theorem sndHostFold {scope : Nat} (pairHost : (RawTerm scope) × (RawTerm scope)) :
    StepStar (sndCell (pairCell pairHost.1 pairHost.2)) (Prod.snd pairHost) :=
  StepStar.single Step.iotaSndPair

/-- **★ `optionMatch` computes the host `Option.elim`.**  `optionMatch (rawOption o) n s ↝* o.elim n (s ·)` — the
`none` branch projects `n`, the `some v` branch applies `s` to `v`, exactly as host `Option.elim`. -/
theorem optionMatchHostFold {scope : Nat} (scrutinee : Option (RawTerm scope))
    (noneBranch someBranch : RawTerm scope) :
    StepStar (optionMatchCell (rawOptionCell scrutinee) noneBranch someBranch)
      (scrutinee.elim noneBranch (fun value => appCell someBranch value)) := by
  cases scrutinee
  · exact StepStar.single Step.iotaOptionMatchNone
  · exact StepStar.single Step.iotaOptionMatchSome

/-- **★ `eitherMatch` computes the host `Sum.elim`.**  `eitherMatch (rawEither e) l r ↝* Sum.elim (l ·) (r ·) e`
— the `inl a` branch applies `l` to `a`, the `inr b` branch applies `r` to `b`, exactly as host `Sum.elim`. -/
theorem eitherMatchHostFold {scope : Nat} (scrutinee : (RawTerm scope) ⊕ (RawTerm scope))
    (leftBranch rightBranch : RawTerm scope) :
    StepStar (eitherMatchCell (rawEitherCell scrutinee) leftBranch rightBranch)
      (Sum.elim (fun value => appCell leftBranch value)
        (fun value => appCell rightBranch value) scrutinee) := by
  cases scrutinee
  · exact StepStar.single Step.iotaEitherMatchInl
  · exact StepStar.single Step.iotaEitherMatchInr

/-- **★ `idJ` computes the host `Eq.rec` on `rfl`.**  `idJ base (refl w) ↝* base` via `Step.iotaIdJRefl` — path
induction on the reflexivity proof returns the base case, exactly as host `Eq.rec` (J) on `rfl`. -/
theorem idJHostFold {scope : Nat} (baseCase witness : RawTerm scope) :
    StepStar (idJCell baseCase (reflCell witness)) baseCase :=
  StepStar.single Step.iotaIdJRefl

/-! ## Concrete branch-selection smokes -/

/-- `boolElim true t e ↝* t` — the host fold selects the THEN branch (`cond true t e = t`). -/
theorem boolElimHostFold.selectsThen {scope : Nat} (thenBranch elseBranch : RawTerm scope) :
    StepStar (boolElimCell boolTrueCell thenBranch elseBranch) thenBranch :=
  boolElimHostFold true thenBranch elseBranch

/-- `optionMatch (some v) n s ↝* s v` — the host fold applies the SOME branch to the stored value. -/
theorem optionMatchHostFold.firesSome {scope : Nat} (value noneBranch someBranch : RawTerm scope) :
    StepStar (optionMatchCell (optionSomeCell value) noneBranch someBranch) (appCell someBranch value) :=
  optionMatchHostFold (some value) noneBranch someBranch

end FX1Poly.Typed
