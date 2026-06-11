import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/NatElimComputingCanonicity
    — the RECURSIVE eliminator-computing canonicity (the nat analogue of `boolElimValueCanonicity`)

`boolElimValueCanonicity` (#1070/#1138 first brick) shipped the FIRST eliminator-computing canonicity: a closed
`boolElim b t e : Bool` with data-VALUE branches computes by a single ι-step to a bool value.  That case is
NON-recursive — `boolElim`'s branches are themselves values, so one ι-step lands the answer.

`natElim` is the genuinely RECURSIVE eliminator, and it carries the difficulty the bool case sidesteps: its
successor ι-rule (Phase-Z SUBSTITUTING shape)

    natElim m z s (natSucc n)  ↝  s[var 0 := natElim m z s n, var 1 := n]

(1) reintroduces a `natElim` subterm (the recursive call, substituted for `var 0`, must ALSO compute), and
(2) substitutes the predecessor for `var 1` directly into the two-binder successor branch `s`.  "Data-value
branches" do not transfer.  This file closes that recursive case.

## What this ships

  * **`natElimCell`** — the Phase-Z `gen_natElim` cell `natElim(motive, zeroBranch, succBranch, scrutinee)`
    (arity 4, `binderShifts = [1, 0, 2, 0]`, motive under one binder, succ-branch under two, scrutinee LAST).
  * **`natElimSuccContractum`** — the substituting reduct `s[var 0 := natElim m z s n, var 1 := n]`.
  * **`natElimComputesToNumeral` (★)** — the abstract recursive computing canonicity, by induction on the
    scrutinee's `IsNatNumeral` structure.  Zero case: `iotaNatElimZero` projects the zero-branch.  Successor
    case: `iotaNatElimSucc` fires to the SUBSTITUTED reduct, and the step's own computational obligation
    `substitutedReductProduces` — "the substituted succ-branch (the recursive call already threaded into `var 0`,
    the predecessor into `var 1`) reduces to a numeral" — finishes the fold.  This obligation IS the honest
    computational content of a recursive eliminator's substituting function branch (the bool case had no analogue
    because its branches were values, and the OLD natElim split this into an explicit IH + app-chain
    `stepProduces`; the substituting reduct folds both into a single premise).

CONDITIONAL FORM FLAG: the abstract theorem takes `substitutedReductProduces` as an explicit premise because the
typed-engine 2-variable SUBSTITUTION lemma (typing `subst (cons recursiveCall (singleton predecessor)) succBranch`
from the branch + recursive-call typings) is the missing standalone-engine piece — the GTL substitution follow-on.
On CONCRETE closed numerals the substitution COMPUTES, so the concrete instances discharge the premise directly.

## What this is and what remains (honest)

This is the typed-engine RECURSIVE eliminator-computing canonicity — the recursive heart of #1138.  The
abstract theorem captures exactly the recursive structure (IH + ι + the function branch's β-computation); the
two concrete instances prove it non-vacuous, one discarding and one USING the recursive result.  The remaining
integration is the full standalone typed `HasTypeDescNatElimValue` judgment whose successor branch is
grown-typed at the function type `Nat → C → C` (the parallel of `HasTypeDescBoolElimValue`), feeding its grown
typing into `stepProduces` unconditionally — the GTL table-residency follow-on (#832/#1138).  Here the step's
value-production is supplied explicitly (abstract) and discharged for two concrete steps.

## Zero-axiom verification

`natElimComputesToNumeral` is a two-arm `induction` on `IsNatNumeral` composing `StepStar.single` ι-steps,
`StepStar.appArgument` congruence, and `StepStar.trans_compose`.  The concrete instances discharge their
`stepProduces` by `Step.beta` (with `subst0` computing definitionally on closed bodies) plus `StepStar.appFunction`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The natural-number eliminator cell `natElim(motive, zeroBranch, succBranch, scrutinee)` — Phase-Z
`gen_natElim` (arity 4, `binderShifts = [1, 0, 2, 0]`, motive under one binder, succ-branch under two, scrutinee
LAST). -/
def natElimCell {scope : Nat} (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The Phase-Z `natElim` succ-iota SUBSTITUTED reduct:
`succBranch[var 0 := natElim motive zeroBranch succBranch predecessor, var 1 := predecessor]`.  The recursive
call THREADS the same motive and branches at the predecessor. -/
def natElimSuccContractum {scope : Nat} (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) : RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (natElimCell motive zeroBranch succBranch predecessor)
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **★ Recursive eliminator-computing canonicity** (Phase-Z SUBSTITUTING shape).  A closed
`natElim(m, z, s, n)` whose zero-branch `z` is a numeral and whose successor ι-reduct — the SUBSTITUTED
succ-branch (recursive call threaded into `var 0`, predecessor into `var 1`) — reduces to a numeral
(`substitutedReductProduces`) computes (`↝*`) to a numeral, for every closed numeral scrutinee `n`.

Induction on `n`'s `IsNatNumeral`:

  * **zero** — `natElim(m, z, s, natZero) ↝ z` (`Step.iotaNatElimZero`), and `z` is a numeral.
  * **succ p** — `natElim(m, z, s, natSucc p) ↝ s[var 0 := natElim m z s p, var 1 := p]`
    (`Step.iotaNatElimSucc`).  The substituted reduct already contains the recursive call (as the var-0
    substituent); `substitutedReductProduces p` finishes it to a numeral.

CONDITIONAL: `substitutedReductProduces` is an explicit premise — the typed-engine 2-variable substitution lemma
(typing the substituted reduct from the branch + recursive-call typings) is the missing standalone-engine piece.
On concrete numerals the substitution COMPUTES, so the concrete instances discharge it directly. -/
theorem natElimComputesToNumeral {motive : RawTerm 1} {zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (zeroBranchNumeral : IsNatNumeral zeroBranch)
    (substitutedReductProduces : ∀ (predecessor : RawTerm 0),
        IsNatNumeral predecessor →
        ∃ out : RawTerm 0,
          StepStar (natElimSuccContractum motive zeroBranch succBranch predecessor) out ∧
            IsNatNumeral out)
    {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell motive zeroBranch succBranch scrutinee) out ∧ IsNatNumeral out := by
  induction scrutineeNumeral with
  | zero =>
      exact ⟨zeroBranch, StepStar.single Step.iotaNatElimZero, zeroBranchNumeral⟩
  | @succ predecessor _predNumeral _ih =>
      obtain ⟨out, stepChain, outNumeral⟩ := substitutedReductProduces predecessor _predNumeral
      refine ⟨out, ?_, outNumeral⟩
      have iotaStep :
          StepStar (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
            (natElimSuccContractum motive zeroBranch succBranch predecessor) :=
        StepStar.single Step.iotaNatElimSucc
      exact StepStar.trans_compose iotaStep stepChain

/-! ## Concrete instance 1: the constant-zero fold (discards the recursive result) -/

/-- The constant-zero successor branch — the two-binder body `natZero : RawTerm 2`.  Ignores both the
predecessor (`var 1`) and the recursive result (`var 0`), collapsing every fold to `natZero`.  Under the Phase-Z
SUBSTITUTING succ-iota the branch is a two-binder TERM substituted into directly (not a lambda being applied). -/
def constNatZeroBranch : RawTerm 2 := (natZeroCell : RawTerm 2)

/-- **`constNatZeroBranch` produces `natZero`.**  The substituted reduct
`natZero[var 0 := …, var 1 := …]` is `natZero` (a closed nullary cell — `subst` is the identity), a numeral
reached in zero steps.  Discharges the `substitutedReductProduces` obligation for the constant-zero fold (the
substitution COMPUTES because the branch is closed). -/
theorem constNatZeroBranchProduces (motive : RawTerm 1) (predecessor : RawTerm 0)
    (_predecessorNumeral : IsNatNumeral predecessor) :
    ∃ out : RawTerm 0,
      StepStar (natElimSuccContractum motive natZeroCell constNatZeroBranch predecessor) out ∧
        IsNatNumeral out :=
  ⟨natZeroCell, StepStar.refl _, IsNatNumeral.zero⟩

/-- **Constant-zero fold canonicity.**  `natElim(m, natZero, natZero, n)` computes to a numeral (in fact
`natZero`) for every closed numeral `n` — the abstract theorem instantiated at `constNatZeroBranch`.  Genuinely
recursive (the proof recurses on `n`), though this particular branch discards the recursive result. -/
theorem natElimConstZeroComputesToNumeral {motive : RawTerm 1}
    {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell motive natZeroCell constNatZeroBranch scrutinee) out ∧ IsNatNumeral out :=
  natElimComputesToNumeral IsNatNumeral.zero (constNatZeroBranchProduces motive) scrutineeNumeral

/-- Replay a `StepStar` chain in the argument child of a `natSucc` cell.  The single-child analogue of
`StepStar.appArgument`: `argument ↝* updated` lifts to `natSucc argument ↝* natSucc updated` by replaying each
step under `Step.cong .gen_natSucc` at the head child. -/
theorem StepStar.natSuccArgument {scope : Nat}
    {argumentTerm updatedArgumentTerm : RawTerm scope}
    (argumentChain : StepStar argumentTerm updatedArgumentTerm) :
    StepStar (natSuccCell argumentTerm) (natSuccCell updatedArgumentTerm) := by
  induction argumentChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact
        StepStar.trans
          (Step.cong .gen_natSucc ()
            (StepChildren.here
              (.childNil : RawTermChildren [] scope)
              headStep))
          tailIH

/-- Replay a `StepStar` chain in the zero-branch child of a `natElim` cell (spine position 1, after the motive
head).  `zeroBranch ↝* updated` lifts to `natElim m zeroBranch s n ↝* natElim m updated s n` by replaying each
step under `Step.cong .gen_natElim` drilled by a `there`/`here` to the zero-branch child. -/
theorem StepStar.natElimZeroBranchArg {scope : Nat}
    {motive : RawTerm (scope + 1)} {zeroBranch updatedZeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (zeroBranchChain : StepStar zeroBranch updatedZeroBranch) :
    StepStar (natElimCell motive zeroBranch succBranch scrutinee)
      (natElimCell motive updatedZeroBranch succBranch scrutinee) := by
  induction zeroBranchChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact
        StepStar.trans
          (Step.cong .gen_natElim ()
            (StepChildren.there _
              (StepChildren.here _ headStep)))
          tailIH

/-! ## Concrete instance 2: the copy fold (USES the recursive result) -/

/-- The copy/successor branch — the two-binder body `natSucc (var 0) : RawTerm 2`.  `var 0` is the recursive
result (the IH, threaded into the succ-iota's var-0 slot), rewrapped in a `natSucc`.  Folding with base
`natZero` rebuilds the numeral, so this branch genuinely THREADS the recursive result.  Under the Phase-Z
SUBSTITUTING succ-iota, substituting `recursiveCall` for `var 0` yields `natSucc recursiveCall` directly (no
β-redex). -/
def copyNatBranch : RawTerm 2 := natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))

/-- The copy fold's substituted reduct computes to `natSucc (natElim … predecessor)`.  Substituting the
recursive call `natElim motive natZero copyNatBranch predecessor` for `var 0` of `natSucc (var 0)` yields
`natSucc (recursive call)` by definitional `subst` computation (the de Bruijn index `0` selects the consed
head). -/
theorem copyNatBranch_substitutedReduct_eq (motive : RawTerm 1) (predecessor : RawTerm 0) :
    natElimSuccContractum motive natZeroCell copyNatBranch predecessor =
      natSuccCell (natElimCell motive natZeroCell copyNatBranch predecessor) := rfl

/-- **★ Copy fold canonicity (recursive result USED).**  `natElim(m, natZero, natSucc (var 0), n)` computes to a
numeral for every closed numeral `n`.  Direct induction on `n`'s `IsNatNumeral` (NOT via the abstract theorem,
because the succ-iota's substituted reduct now CONTAINS the recursive `natElim` as the var-0 substituent, so the
IH must discharge that inner call): zero projects `natZero`; succ fires the ι, the substituted reduct is
`natSucc (natElim m natZero copyNatBranch p)` (`copyNatBranch_substitutedReduct_eq`), the IH reduces the inner
`natElim` to a numeral `r`, and `StepStar.natSuccArgument` lifts that through the `natSucc` to land
`natSucc r` — a numeral.  Exercises the full recursive-threading machinery: the inner `natElim` must reduce to a
numeral via the IH BEFORE the `natSucc` wraps it. -/
theorem natElimCopyComputesToNumeral {motive : RawTerm 1}
    {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell motive natZeroCell copyNatBranch scrutinee) out ∧ IsNatNumeral out := by
  induction scrutineeNumeral with
  | zero =>
      exact ⟨natZeroCell, StepStar.single Step.iotaNatElimZero, IsNatNumeral.zero⟩
  | @succ predecessor _predNumeral ih =>
      obtain ⟨recResult, recChain, recNumeral⟩ := ih
      refine ⟨natSuccCell recResult, ?_, IsNatNumeral.succ recNumeral⟩
      have iotaStep :
          StepStar (natElimCell motive natZeroCell copyNatBranch (natSuccCell predecessor))
            (natSuccCell (natElimCell motive natZeroCell copyNatBranch predecessor)) :=
        StepStar.single Step.iotaNatElimSucc
      have congStep :
          StepStar (natSuccCell (natElimCell motive natZeroCell copyNatBranch predecessor))
            (natSuccCell recResult) :=
        StepStar.natSuccArgument recChain
      exact StepStar.trans_compose iotaStep congStep

/-- **Fully-concrete non-vacuity smoke**: `natElim(m, natZero, natSucc (var 0), 2)` computes to a numeral — the
copy fold on the closed numeral `2 = succ (succ natZero)`. -/
theorem natElimCopyComputesToNumeral.two {motive : RawTerm 1} :
    ∃ out : RawTerm 0,
      StepStar (natElimCell motive natZeroCell copyNatBranch
        (natSuccCell (natSuccCell natZeroCell))) out ∧
      IsNatNumeral out :=
  natElimCopyComputesToNumeral (IsNatNumeral.succ (IsNatNumeral.succ IsNatNumeral.zero))

end FX1Poly.Typed
