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

* `StepStar.natElimScrutinee` / `natRecScrutinee` / `listElimScrutinee` — the scrutinee-position chain
  congruences (`StepStar.congAt` + `Step.cong …`).  For `natElim` / `natRec` the scrutinee is the head child
  (`StepChildren.here …`); for the Phase-Z `listElim` it is the LAST child of the 4-child spine, so the cong
  drills a `there`-chain past the motive + both branches (mirroring `boolElim`).
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

/-- The `listElim` cell — `gen_listElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 0, 0]`).  Author order `(motive, scrutinee, nil-branch, cons-branch)`; emitted spine
`(motive, nil-branch, cons-branch, scrutinee)` with the motive a term under one binder and the scrutinee LAST. -/
private abbrev listElimCellOn {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee nilBranch consBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons motive
      (.childCons nilBranch
        (.childCons consBranch
          (.childCons scrutinee .childNil))))

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

/-- **Scrutinee-position chain congruence for `listElim`.**  A reduction chain in the scrutinee lifts to the
whole `listElim` cell (motive + branches fixed), via `StepStar.congAt` + `Step.cong …` drilled by a `there`-chain
to the scrutinee child (the LAST child of the 4-child Phase-Z spine, past the motive + both branches). -/
theorem StepStar.listElimScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee scrutineeReduct nilBranch consBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (listElimCellOn motive scrutinee nilBranch consBranch)
      (listElimCellOn motive scrutineeReduct nilBranch consBranch) :=
  StepStar.congAt
    (fun hole => listElimCellOn motive hole nilBranch consBranch)
    (fun stepInScrutinee =>
      Step.cong .gen_listElim ()
        (StepChildren.there _
          (StepChildren.there _
            (StepChildren.there _
              (StepChildren.here _ stepInScrutinee)))))
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
    {motive : RawTerm (scope + 1)}
    {scrutinee nilBranch consBranch : RawTerm scope}
    (scrutineeReducesToNil : StepStar scrutinee listNilCell) :
    StepStar (listElimCellOn motive scrutinee nilBranch consBranch) nilBranch :=
  StepStar.transLast (StepStar.listElimScrutinee scrutineeReducesToNil) Step.iotaListElimNil

end FX1Poly.Core
