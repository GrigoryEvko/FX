import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepCommute

/-! # FX1Poly/Core/RecursiveEliminatorBaseComputation
    — the recursive eliminators COMPUTE on their base constructor (`natElim`/`natRec` on `zero`, `listElim` on
      `nil`) — the fundamental-free BASE-CASE half

The non-recursive eliminators (`boolElim`, `fst`/`snd`, `idJ`/`idStrictRec`, `optionMatch`/`eitherMatch`) all
have closed-canonical-scrutinee computation theorems: their ι fires once with NO recursive sub-term.  The
recursive eliminators `natElim` / `natRec` / `listElim` SPLIT: on the BASE constructor (`zero` / `nil`) the ι
selects the base branch — non-growing, computable here fundamental-free — but on the STEP constructor (`succ` /
`cons`) the ι reappears the eliminator on the predecessor / tail (`app (app succBranch n) (natElim n …)`),
GROWING the term, and proving that terminates needs the full Tait reducibility argument (the fundamental-gated
machinery).  This file ships the clean base-case half.

* `StepStar.natElimScrutinee` / `natRecScrutinee` / `listElimScrutinee` — the scrutinee-position (head-child)
  chain congruences (`StepStar.congAt` + `Step.cong … (StepChildren.here …)`, as for `boolElim`).
* `natElimZeroScrutineeReducesToBranch` / `natRecZeroScrutineeReducesToBranch` /
  `listElimNilScrutineeReducesToBranch` — the headline: when the scrutinee reduces to the base constructor
  (`zero` / `nil`), the eliminator reduces to the base branch.  The scrutinee congruence carries the
  scrutinee's reduction to `zero` / `nil` under the eliminator, then the base ι (`Step.iotaNatElimZero` /
  `Step.iotaNatRecZero` / `Step.iotaListElimNil`) selects the branch.

## Zero-axiom verification

`StepStar.congAt` (chain induction), `Step.cong` / `StepChildren.here` (the scrutinee congruence step), and the
`Step.iotaNatElimZero` / `iotaNatRecZero` / `iotaListElimNil` base ι constructors, chained by
`StepStar.transLast`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The `natElim` cell over its three children (scrutinee, zero-branch, succ-branch). -/
private abbrev natElimCellOn {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The `natRec` cell over its three children (scrutinee, zero-branch, succ-branch) — same spine as `natElim`. -/
private abbrev natRecCellOn {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natRec ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The `listElim` cell over its three children (scrutinee, nil-branch, cons-branch). -/
private abbrev listElimCellOn {scope : Nat} (scrutinee nilBranch consBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))

/-- **Scrutinee-position chain congruence for `natElim`.**  A reduction chain in the scrutinee lifts to the
whole `natElim` cell (branches fixed), via `StepStar.congAt` + `Step.cong … (here …)` at the head child. -/
theorem StepStar.natElimScrutinee {scope : Nat}
    {scrutinee scrutineeReduct zeroBranch succBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (natElimCellOn scrutinee zeroBranch succBranch)
      (natElimCellOn scrutineeReduct zeroBranch succBranch) :=
  StepStar.congAt
    (fun hole => natElimCellOn hole zeroBranch succBranch)
    (fun stepInScrutinee => Step.cong .gen_natElim () (StepChildren.here _ stepInScrutinee))
    scrutineeChain

/-- **Scrutinee-position chain congruence for `natRec`.**  Symmetric to `StepStar.natElimScrutinee`. -/
theorem StepStar.natRecScrutinee {scope : Nat}
    {scrutinee scrutineeReduct zeroBranch succBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (natRecCellOn scrutinee zeroBranch succBranch)
      (natRecCellOn scrutineeReduct zeroBranch succBranch) :=
  StepStar.congAt
    (fun hole => natRecCellOn hole zeroBranch succBranch)
    (fun stepInScrutinee => Step.cong .gen_natRec () (StepChildren.here _ stepInScrutinee))
    scrutineeChain

/-- **Scrutinee-position chain congruence for `listElim`.**  Symmetric to `StepStar.natElimScrutinee`. -/
theorem StepStar.listElimScrutinee {scope : Nat}
    {scrutinee scrutineeReduct nilBranch consBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (listElimCellOn scrutinee nilBranch consBranch)
      (listElimCellOn scrutineeReduct nilBranch consBranch) :=
  StepStar.congAt
    (fun hole => listElimCellOn hole nilBranch consBranch)
    (fun stepInScrutinee => Step.cong .gen_listElim () (StepChildren.here _ stepInScrutinee))
    scrutineeChain

/-- **`natElim` on a zero-reducing scrutinee computes to the zero-branch.**  The fundamental-free base-case half of
`natElim` canonicity: when the scrutinee reduces to `natZero`, the scrutinee congruence carries that under the
`natElim`, and the base ι `Step.iotaNatElimZero` selects the zero-branch.  (The `succ` step case grows — the ι
reappears `natElim` on the predecessor — and needs Tait.) -/
theorem natElimZeroScrutineeReducesToBranch {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (scrutineeReducesToZero : StepStar scrutinee natZeroCell) :
    StepStar (natElimCellOn scrutinee zeroBranch succBranch) zeroBranch :=
  StepStar.transLast (StepStar.natElimScrutinee scrutineeReducesToZero) Step.iotaNatElimZero

/-- **`natRec` on a zero-reducing scrutinee computes to the zero-branch.**  Symmetric to
`natElimZeroScrutineeReducesToBranch` — same base ι (`Step.iotaNatRecZero`). -/
theorem natRecZeroScrutineeReducesToBranch {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (scrutineeReducesToZero : StepStar scrutinee natZeroCell) :
    StepStar (natRecCellOn scrutinee zeroBranch succBranch) zeroBranch :=
  StepStar.transLast (StepStar.natRecScrutinee scrutineeReducesToZero) Step.iotaNatRecZero

/-- **`listElim` on a nil-reducing scrutinee computes to the nil-branch.**  The fundamental-free base-case half of
`listElim` canonicity: when the scrutinee reduces to `listNil`, the scrutinee congruence carries that under the
`listElim`, and the base ι `Step.iotaListElimNil` selects the nil-branch.  (The `cons` step case grows — the ι
reappears `listElim` on the tail — and needs Tait.) -/
theorem listElimNilScrutineeReducesToBranch {scope : Nat}
    {scrutinee nilBranch consBranch : RawTerm scope}
    (scrutineeReducesToNil : StepStar scrutinee listNilCell) :
    StepStar (listElimCellOn scrutinee nilBranch consBranch) nilBranch :=
  StepStar.transLast (StepStar.listElimScrutinee scrutineeReducesToNil) Step.iotaListElimNil

end FX1Poly.Core
