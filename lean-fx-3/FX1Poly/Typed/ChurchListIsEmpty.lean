import FX1Poly.Typed.ChurchLists
import FX1Poly.Typed.TypedChurchBooleans
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchListIsEmpty — the first DEFINED operation on Church lists: the `isEmpty` predicate

`ChurchLists` shipped the Boehm-Berarducci list ENCODING (nil/cons/fold) and proved the fold COMPUTES on both
constructors (`foldNil`: `fold c n nil ↝* n`; `foldCons`: `fold c n (cons h t) ↝* c h (t c n)`; `foldSingleton`:
`fold c n (cons h nil) ↝* c h n`).  This file builds the FIRST defined list FUNCTION on top of that fold — the
`null` / `isEmpty` predicate — demonstrating that the pure Π-fragment encoding supports actual list programming,
not merely constructor faithfulness, and connecting the list encoding to the Church BOOLEAN encoding (#981):

  `isEmpty list = fold (λh. λacc. false) true list`

A list folded with the constant-`false` cons-handler and the `true` nil-handler returns `true` exactly when it is
`nil` (the cons-handler never fires) and `false` as soon as it has a `cons` (the constant handler discards the
head and the recursively-folded tail).  It is the list analogue of `churchIsZero` (`ChurchNat → ChurchBool`,
#1055) — a fold-driven decision procedure over the encoded data.

  * **`isEmptyHandler_const`** — `isEmptyHandler h acc ↝* false` for any `h`, `acc`: the constant-false handler
    discards BOTH arguments (`h` via the #1023 double-weaken collapse `subst_lift_singleton_weaken_weaken`, `acc`
    via the single-weaken `weaken_subst_singleton`).  The handler-side computation `foldSingleton` feeds into.
  * **`isEmptyNil` (★)** — `isEmpty nil ↝* true`, directly via `foldNil` (the nil-handler IS `true`).
  * **`isEmptyConsNil` (★)** — `isEmpty (cons h nil) ↝* false`: `foldSingleton` reaches `isEmptyHandler h true`,
    which `isEmptyHandler_const` reduces to `false`.
  * **`isEmptyDistinguishes` (★)** — `¬ Conv (isEmpty nil) (isEmpty (cons h nil))`: the predicate genuinely
    SEPARATES empty from non-empty.  Were the two convertible, the computed results `true` / `false` would be
    convertible (`Conv.fromStepStar` + transitivity), contradicting the shipped `churchTrue_notConvertible_-
    churchFalse` (#983).  The list-discrimination capstone — the calculus keeps `[]` and `[h]` operationally
    apart, exactly as #983 keeps `true` / `false` and #1020 keeps the two coproduct injections apart.

Everything is the raw `Step` / `Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

`isEmptyHandler_const` mirrors the `ChurchLists` fold reshapes: the β1 reshape `isEmptyHandlerInnerSubst` is a
`show`-push (`subst` through the inner `lamCell`) + `rw [subst_lift_singleton_weaken_weaken]`, then a
function-position congruence lifts it and the outer β cancels the single weaken.  `isEmptyNil` is `foldNil`;
`isEmptyConsNil` is `StepStar.trans_compose` of `foldSingleton` with the handler reduction; `isEmptyDistinguishes`
is `Conv.fromStepStar` / `.trans` / `.sym` to the two values + `churchTrue_notConvertible_churchFalse`.  No
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `isEmptyHandler = λh. λacc. false` — the constant-false cons-handler: discards the head AND the recursive
accumulator, always returning the Church-`false`. -/
def isEmptyHandler : RawTerm 0 :=
  lamCell churchListDomainAnn (lamCell churchListDomainAnn (RawTerm.weaken (RawTerm.weaken churchFalseLambda)))

/-- `isEmpty list = fold (λh.λacc. false) true list` — the list `null` predicate as a right-fold: `nil` returns
`true` (the nil-handler), every `cons` returns `false` (the constant handler). -/
def churchListIsEmpty (list : RawTerm 0) : RawTerm 0 :=
  churchFold isEmptyHandler churchTrueLambda list

/-- β1 reshape: substituting the head into `isEmptyHandler`'s body collapses the doubly-weakened `false` one level
(`subst_lift_singleton_weaken_weaken`, #1023) and discards `h` (the body never mentions it). -/
theorem isEmptyHandlerInnerSubst (head : RawTerm 0) :
    RawTerm.subst0 (lamCell churchListDomainAnn (RawTerm.weaken (RawTerm.weaken churchFalseLambda))) head
      = lamCell churchListDomainAnn (RawTerm.weaken churchFalseLambda) := by
  dsimp only [RawTerm.subst0, churchListDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton head))
      (RawTerm.weaken (RawTerm.weaken churchFalseLambda))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken churchFalseLambda head]

/-- **`isEmptyHandler h acc ↝* false`** for any head and accumulator — the constant-false handler discards both
arguments (`h` via the #1023 double-weaken collapse, `acc` via the single-weaken cancellation).  The handler
computation `foldSingleton` chains into for `isEmptyConsNil`. -/
theorem isEmptyHandler_const (head acc : RawTerm 0) :
    StepStar (appCell (appCell isEmptyHandler head) acc) churchFalseLambda := by
  have functionBeta : Step (appCell isEmptyHandler head)
      (lamCell churchListDomainAnn (RawTerm.weaken churchFalseLambda)) := by
    rw [← isEmptyHandlerInnerSubst head]; exact Step.beta
  have congStep : Step (appCell (appCell isEmptyHandler head) acc)
      (appCell (lamCell churchListDomainAnn (RawTerm.weaken churchFalseLambda)) acc) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons acc .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell churchListDomainAnn (RawTerm.weaken churchFalseLambda)) acc) churchFalseLambda := by
    have cancel : RawTerm.subst0 (RawTerm.weaken churchFalseLambda) acc = churchFalseLambda :=
      RawTerm.weaken_subst_singleton churchFalseLambda acc
    rw [← cancel]; exact Step.beta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- **★ `isEmpty nil ↝* true`** — the empty list is empty, directly via `foldNil` (the nil-handler IS `true`). -/
theorem isEmptyNil : StepStar (churchListIsEmpty churchNil) churchTrueLambda :=
  foldNil isEmptyHandler churchTrueLambda

/-- **★ `isEmpty (cons h nil) ↝* false`** — a one-element list is non-empty: `foldSingleton` reaches
`isEmptyHandler h true`, which the constant handler (`isEmptyHandler_const`) reduces to `false`. -/
theorem isEmptyConsNil (head : RawTerm 0) :
    StepStar (churchListIsEmpty (churchCons head churchNil)) churchFalseLambda :=
  StepStar.trans_compose
    (foldSingleton head isEmptyHandler churchTrueLambda)
    (isEmptyHandler_const head churchTrueLambda)

/-- **★ The `isEmpty` predicate genuinely DISTINGUISHES empty from non-empty.**  `isEmpty nil` and
`isEmpty (cons h nil)` are NOT convertible.  Were they, the two computed results `true` / `false` would be
convertible (`Conv.fromStepStar` + transitivity), contradicting `churchTrue_notConvertible_churchFalse` (#983).
The list-discrimination capstone — the calculus keeps `[]` and `[h]` operationally apart, exactly as #983 keeps
`true` / `false` and #1020 keeps the two coproduct injections apart. -/
theorem isEmptyDistinguishes (head : RawTerm 0) :
    ¬ Conv (churchListIsEmpty churchNil) (churchListIsEmpty (churchCons head churchNil)) := by
  intro hConv
  have convResults : Conv churchTrueLambda churchFalseLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar isEmptyNil))
      (Conv.trans hConv (Conv.fromStepStar (isEmptyConsNil head)))
  exact churchTrue_notConvertible_churchFalse convResults

end FX1Poly.Typed
