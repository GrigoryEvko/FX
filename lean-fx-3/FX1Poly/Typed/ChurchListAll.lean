import FX1Poly.Typed.ChurchLists
import FX1Poly.Typed.ChurchListAny
import FX1Poly.Typed.TypedChurchBooleanOperations
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchListAll — the `all` predicate over a Church list of booleans (the conjunction fold)

`ChurchListAny` shipped `any = fold or false` (∃, true-strict).  This file ships its dual `all = fold and true`
(∀, false-strict) and the capstone proving the two quantifiers GENUINELY DIFFER:

  `all list = fold and true list`

A list folded with the Church-AND cons-handler (#1056) and the `true` nil-handler returns `true` exactly when
EVERY element is `true` — the universal quantifier over a boolean list.  As with `any`, the cons-handler is the
shipped `churchAndLambda` applied directly (no bespoke handler / de Bruijn reshape).

  * **`allNil`** — `all nil ↝* true`: vacuous truth, the empty list satisfies ∀ (directly via `foldNil`).
  * **`allConsTrueNil`** — `all [true] ↝* true`: `foldSingleton` reaches `and true true` (`churchAnd_trueTrue`).
  * **`allConsFalseNil`** — `all [false] ↝* false`: `foldSingleton` reaches `and false true`
    (`churchAnd_falseAnything` — AND is left-strict on `false`).
  * **`allConsFalseConsTrueNil` (★)** — `all [false, true] ↝* false`: the FALSE-strict SHORT-CIRCUIT.  `foldCons`
    reaches `and false (all [true])`, and `churchAnd_falseAnything` reduces `and false _ ↝* false` WITHOUT
    reducing the tail.  The exact dual of `any`'s true-strict short-circuit (#1084 `anyConsFalseConsTrueNil`,
    which reduces the tail because `or false _` is not strict).
  * **`allDistinguishesByContent`** — `¬ Conv (all [true]) (all [false])`: `all` inspects element values
    (same shape, different content), else `true ≡ false` (refuted by #983).
  * **`anyAllDifferOnMixed` (★)** — `¬ Conv (any [false, true]) (all [false, true])`: the EXISTENTIAL and
    UNIVERSAL quantifiers are DISTINCT operations.  On the same mixed list `[false, true]`, ∃ computes `true`
    (#1084) while ∀ computes `false` (this file) — were they convertible, `true ≡ false` (refuted by #983).  The
    completion of the quantifier pair: `any` and `all` are not merely two folds, they genuinely disagree.

Everything is the raw `Step` / `Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

The cons-handler is the shipped `churchAndLambda`, so the computations chain the shipped fold lemmas
(`foldNil` / `foldSingleton` / `foldCons`, #1081/#1082) with the shipped AND reductions (`churchAnd_trueTrue` /
`churchAnd_falseAnything`, #1056) via `StepStar.trans_compose` — no new de Bruijn reshape.  The depth-2 case needs
NO tail reduction (AND short-circuits on `false`).  `allDistinguishesByContent` / `anyAllDifferOnMixed` are
`Conv.fromStepStar` / `.trans` / `.sym` to the computed values + `churchTrue_notConvertible_churchFalse` (#983).
No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `all list = fold and true list` — the conjunction fold: "is every element true?".  The cons-handler is the
shipped `churchAndLambda` (#1056) directly; the nil-handler is `true`. -/
def churchListAll (list : RawTerm 0) : RawTerm 0 :=
  churchFold churchAndLambda churchTrueLambda list

/-- `all nil ↝* true` — vacuous truth: the empty list satisfies ∀, directly via `foldNil`. -/
theorem allNil : StepStar (churchListAll churchNil) churchTrueLambda :=
  foldNil churchAndLambda churchTrueLambda

/-- `all [true] ↝* true` — `foldSingleton` reaches `and true true`, which `churchAnd_trueTrue` reduces to `true`. -/
theorem allConsTrueNil :
    StepStar (churchListAll (churchCons churchTrueLambda churchNil)) churchTrueLambda :=
  StepStar.trans_compose
    (foldSingleton churchTrueLambda churchAndLambda churchTrueLambda)
    churchAnd_trueTrue

/-- `all [false] ↝* false` — `foldSingleton` reaches `and false true`, which `churchAnd_falseAnything` reduces to
`false` (AND is left-strict on `false`). -/
theorem allConsFalseNil :
    StepStar (churchListAll (churchCons churchFalseLambda churchNil)) churchFalseLambda :=
  StepStar.trans_compose
    (foldSingleton churchFalseLambda churchAndLambda churchTrueLambda)
    (churchAnd_falseAnything churchTrueLambda)

/-- **★ `all [false, true] ↝* false`** — the FALSE-strict SHORT-CIRCUIT: `foldCons` reaches `and false (all [true])`,
and `churchAnd_falseAnything` reduces `and false _ ↝* false` WITHOUT reducing the tail.  The exact dual of `any`'s
true-strict short-circuit (#1084), which DOES reduce the tail because `or false _` is not strict. -/
theorem allConsFalseConsTrueNil :
    StepStar (churchListAll (churchCons churchFalseLambda (churchCons churchTrueLambda churchNil)))
      churchFalseLambda :=
  StepStar.trans_compose
    (foldCons churchFalseLambda (churchCons churchTrueLambda churchNil) churchAndLambda churchTrueLambda)
    (churchAnd_falseAnything (churchListAll (churchCons churchTrueLambda churchNil)))

/-- `all` distinguishes by ELEMENT CONTENT: `all [true]` and `all [false]` are NOT convertible (same one-element
shape, different content), else `true ≡ false` (refuted by `churchTrue_notConvertible_churchFalse`, #983). -/
theorem allDistinguishesByContent :
    ¬ Conv (churchListAll (churchCons churchTrueLambda churchNil))
        (churchListAll (churchCons churchFalseLambda churchNil)) := by
  intro hConv
  have convResults : Conv churchTrueLambda churchFalseLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar allConsTrueNil))
      (Conv.trans hConv (Conv.fromStepStar allConsFalseNil))
  exact churchTrue_notConvertible_churchFalse convResults

/-- **★ The existential and universal quantifiers GENUINELY DIFFER.**  `any [false, true]` and `all [false, true]`
are NOT convertible: on the same mixed list, ∃ computes `true` (#1084) while ∀ computes `false` (this file) — were
they convertible, `true ≡ false` (refuted by #983).  The completion of the quantifier pair — `any` and `all` are
not merely two folds, they genuinely disagree on a list that has a `true` but is not all-`true`. -/
theorem anyAllDifferOnMixed :
    ¬ Conv (churchListAny (churchCons churchFalseLambda (churchCons churchTrueLambda churchNil)))
        (churchListAll (churchCons churchFalseLambda (churchCons churchTrueLambda churchNil))) := by
  intro hConv
  have convResults : Conv churchTrueLambda churchFalseLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar anyConsFalseConsTrueNil))
      (Conv.trans hConv (Conv.fromStepStar allConsFalseConsTrueNil))
  exact churchTrue_notConvertible_churchFalse convResults

end FX1Poly.Typed
