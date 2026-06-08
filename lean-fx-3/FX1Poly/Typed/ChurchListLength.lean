import FX1Poly.Typed.ChurchSuccApplies
import FX1Poly.Typed.ChurchLists
import FX1Poly.Typed.TypedChurchBooleanOperations
import FX1Poly.Typed.TypedChurchNegation
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchListLength — the list-length fold and its iteration-semantics faithfulness

The Church-list arc (#1081-1085) shipped the Boehm-Berarducci encoding and content-folds (isEmpty, any,
all, firstOr).  The numeral arc (#1089-1090) shipped the Church successor `churchSucc` and its operational
iteration `churchSucc n A f x ↝* f (n A f x)`.  This file fuses the two: `length` folds a Church list with
`churchSucc` over `churchZero`, producing the list's length AS a Church numeral, and proves the result is
FAITHFUL through the numeral's own iteration semantics.

  * **`churchListLength list = fold (λhead. λacc. churchSucc acc) churchZero list`** — the length fold.  The
    cons-handler `lengthConsHandler` discards the head and applies `churchSucc` to the accumulator, so folding
    a `k`-element list builds the successor-tower `churchSucc^k churchZero` (= the numeral `k`).
  * **`lengthNil` / `lengthConsNil` / `lengthConsConsNil`** — the length of `[]`, `[h]`, `[h, s]` reduces to
    the successor-towers of 0, 1, 2 respectively.  The depth-2 case lifts the tail-fold (= `length [s]`)
    through `churchSucc ·` via `StepStar.appArgument`.
  * **`succTowerOneParity` / `succTowerTwoParity`** — a successor-tower of height `k`, applied to the parity
    probe `(motive, churchNot, churchTrue)`, ITERATES `churchNot` `k` times from `churchTrue`: height 1 ↦
    `churchFalse` (odd), height 2 ↦ `churchTrue` (even).  This reads the numeral through its Church-iteration
    meaning, not through structural normal-form inspection.
  * **`lengthDistinguishesByParity`** — ★ the capstone.  `length [h]` and `length [h, s]`, each applied to the
    parity probe, are NOT convertible: one computes `churchFalse`, the other `churchTrue`.  So `length`
    genuinely separates lists of different length-parity, witnessed through the numeral iteration semantics
    (and ultimately the `churchTrue ≢ churchFalse` discrimination of #983).

Everything is the raw `Step`/`Conv` relation; no typing derivation is consulted.

## Zero-axiom verification

The two β-reshapes (`lengthConsHandlerInnerSubst`, `lengthConsHandlerOuterSubst`) follow the proven
`succ_step*_reshape` idiom: `unfold subst0` → `show` the fully-distributed substitution → `rw` the
weaken-cancellation lemmas (`subst_lift_singleton_weaken_weaken`, `weaken_subst_singleton`) → trailing `rfl`
to discharge the variable-leaf substitutions (which reduce definitionally but are not closed by `rw`).  Every
reduction lemma chains shipped `StepStar` combinators; every discrimination routes through `Conv.fromStepStar`
+ `churchTrue_notConvertible_churchFalse`.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `churchZero = numeral 0 = λA.λf.λx. x`. -/
def churchZero : RawTerm 0 := churchNumeralLambda 0

/-- `churchZero A f x ↝* x` (the numeral-0 iteration: `iteratedApplication 0 = base`). -/
theorem churchZero_applies (typeA handlerF baseX : RawTerm 0) :
    StepStar (appCell (appCell (appCell churchZero typeA) handlerF) baseX) baseX :=
  churchNumeral_appliedReducesToIterate_general 0 typeA handlerF baseX

/-- `lengthConsHandler = λhead. λacc. churchSucc acc` — adds one to the accumulator, ignoring the head. -/
def lengthConsHandler : RawTerm 0 :=
  lamCell (lamCell (appCell (RawTerm.weaken (RawTerm.weaken churchSucc))
    (variableCell (⟨0, by decide⟩ : Fin 2))))

/-- β1 reshape: substituting the head leaves `churchSucc acc` (head unused, churchSucc collapses one weaken). -/
theorem lengthConsHandlerInnerSubst (head : RawTerm 0) :
    RawTerm.subst0 (lamCell (appCell (RawTerm.weaken (RawTerm.weaken churchSucc))
      (variableCell (⟨0, by decide⟩ : Fin 2)))) head
      = lamCell (appCell (RawTerm.weaken churchSucc) (variableCell (⟨0, by decide⟩ : Fin 1))) := by
  unfold RawTerm.subst0
  show lamCell (appCell
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton head))
        (RawTerm.weaken (RawTerm.weaken churchSucc)))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton head))
        (variableCell (⟨0, by decide⟩ : Fin 2)))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken churchSucc head]
  rfl

/-- β2 reshape: substituting the accumulator yields `churchSucc acc`. -/
theorem lengthConsHandlerOuterSubst (acc : RawTerm 0) :
    RawTerm.subst0 (appCell (RawTerm.weaken churchSucc) (variableCell (⟨0, by decide⟩ : Fin 1))) acc
      = appCell churchSucc acc := by
  unfold RawTerm.subst0
  show appCell (RawTerm.subst (RawTermSubst.singleton acc) (RawTerm.weaken churchSucc))
      (RawTerm.subst (RawTermSubst.singleton acc) (variableCell (⟨0, by decide⟩ : Fin 1)))
      = appCell churchSucc acc
  rw [RawTerm.weaken_subst_singleton churchSucc acc]
  rfl

/-- **`lengthConsHandler head acc ↝* churchSucc acc`** — the handler adds one (applies churchSucc to the
accumulator), discarding the head. -/
theorem lengthConsHandler_reduces (head acc : RawTerm 0) :
    StepStar (appCell (appCell lengthConsHandler head) acc) (appCell churchSucc acc) := by
  have functionBeta : Step (appCell lengthConsHandler head)
      (lamCell (appCell (RawTerm.weaken churchSucc) (variableCell (⟨0, by decide⟩ : Fin 1)))) := by
    rw [← lengthConsHandlerInnerSubst head]; exact Step.beta
  have congStep : Step (appCell (appCell lengthConsHandler head) acc)
      (appCell (lamCell (appCell (RawTerm.weaken churchSucc) (variableCell (⟨0, by decide⟩ : Fin 1)))) acc) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons acc .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell (appCell (RawTerm.weaken churchSucc)
      (variableCell (⟨0, by decide⟩ : Fin 1)))) acc) (appCell churchSucc acc) := by
    rw [← lengthConsHandlerOuterSubst acc]; exact Step.beta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- `length list = fold (λh.λacc. churchSucc acc) churchZero list` — the list length as a Church numeral. -/
def churchListLength (list : RawTerm 0) : RawTerm 0 :=
  churchFold lengthConsHandler churchZero list

/-- `length nil ↝* churchZero` (= 0). -/
theorem lengthNil : StepStar (churchListLength churchNil) churchZero :=
  foldNil lengthConsHandler churchZero

/-- `length [head] ↝* churchSucc churchZero` (= 1). -/
theorem lengthConsNil (head : RawTerm 0) :
    StepStar (churchListLength (churchCons head churchNil)) (appCell churchSucc churchZero) :=
  StepStar.trans_compose
    (foldSingleton head lengthConsHandler churchZero)
    (lengthConsHandler_reduces head churchZero)

/-- **★ `length [head, second] ↝* churchSucc (churchSucc churchZero)`** (= 2): foldCons reaches
`lengthConsHandler head (tail-fold)`; the handler gives `churchSucc (tail-fold)`, and the tail-fold (= length
[second]) reduces to `churchSucc churchZero` (lifted through `churchSucc ·`). -/
theorem lengthConsConsNil (head second : RawTerm 0) :
    StepStar (churchListLength (churchCons head (churchCons second churchNil)))
      (appCell churchSucc (appCell churchSucc churchZero)) :=
  StepStar.trans_compose
    (foldCons head (churchCons second churchNil) lengthConsHandler churchZero)
    (StepStar.trans_compose
      (lengthConsHandler_reduces head
        (churchFold lengthConsHandler churchZero (churchCons second churchNil)))
      (StepStar.appArgument churchSucc (lengthConsNil second)))

/-- `(churchSucc churchZero) motive not true ↝* false` — the succ-tower of 1, applied to (not, true), computes
the PARITY: odd (1) ↦ false. -/
theorem succTowerOneParity (motive : RawTerm 0) :
    StepStar (appCell (appCell (appCell (appCell churchSucc churchZero) motive) churchNotLambda) churchTrueLambda)
      churchFalseLambda :=
  StepStar.trans_compose
    (churchSucc_applies churchZero motive churchNotLambda churchTrueLambda)
    (StepStar.trans_compose
      (StepStar.appArgument churchNotLambda (churchZero_applies motive churchNotLambda churchTrueLambda))
      churchNot_negatesTrue)

/-- `(churchSucc (churchSucc churchZero)) motive not true ↝* true` — the succ-tower of 2 ↦ true (even). -/
theorem succTowerTwoParity (motive : RawTerm 0) :
    StepStar (appCell (appCell (appCell (appCell churchSucc (appCell churchSucc churchZero)) motive)
      churchNotLambda) churchTrueLambda) churchTrueLambda :=
  StepStar.trans_compose
    (churchSucc_applies (appCell churchSucc churchZero) motive churchNotLambda churchTrueLambda)
    (StepStar.trans_compose
      (StepStar.appArgument churchNotLambda (succTowerOneParity motive))
      churchNot_negatesFalse)

/-- `length [head]` applied to the parity-probe `(motive, not, true)` ↝* false (length 1 is odd). -/
theorem lengthOneAppliedParity (head motive : RawTerm 0) :
    StepStar (appCell (appCell (appCell (churchListLength (churchCons head churchNil)) motive)
      churchNotLambda) churchTrueLambda) churchFalseLambda :=
  StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.appFunction (lengthConsNil head))))
    (succTowerOneParity motive)

/-- `length [head, second]` applied to the parity-probe ↝* true (length 2 is even). -/
theorem lengthTwoAppliedParity (head second motive : RawTerm 0) :
    StepStar (appCell (appCell (appCell (churchListLength (churchCons head (churchCons second churchNil))) motive)
      churchNotLambda) churchTrueLambda) churchTrueLambda :=
  StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.appFunction (lengthConsConsNil head second))))
    (succTowerTwoParity motive)

/-- **★ `length` is FAITHFUL via the numeral iteration semantics.**  `length [head]` and `length [head, second]`,
applied to the parity-probe `(motive, churchNot, churchTrue)`, are NOT convertible — length 1 computes the parity
`false`, length 2 computes `true` — so `length` genuinely separates lists of different length-parity.  Through the
Church-numeral ITERATION (apply the numeral to `not` from `true`), not the structural `false ≢ true`. -/
theorem lengthDistinguishesByParity (head second motive : RawTerm 0) :
    ¬ Conv (appCell (appCell (appCell (churchListLength (churchCons head churchNil)) motive)
        churchNotLambda) churchTrueLambda)
      (appCell (appCell (appCell (churchListLength (churchCons head (churchCons second churchNil))) motive)
        churchNotLambda) churchTrueLambda) := by
  intro hConv
  have convResults : Conv churchFalseLambda churchTrueLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar (lengthOneAppliedParity head motive)))
      (Conv.trans hConv (Conv.fromStepStar (lengthTwoAppliedParity head second motive)))
  exact churchTrue_notConvertible_churchFalse (Conv.sym convResults)

end FX1Poly.Typed
