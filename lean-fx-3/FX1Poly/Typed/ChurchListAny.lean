import FX1Poly.Typed.ChurchLists
import FX1Poly.Typed.TypedChurchBooleanOperations
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchListAny — the `any` predicate over a Church list of booleans (the disjunction fold)

`ChurchListIsEmpty` shipped the FIRST defined list operation (`isEmpty`, a CONSTANT-handler fold that sees only
list SHAPE).  This file ships the next, qualitatively stronger one — `any`, the disjunction fold "does the list
contain a `true`?":

  `any list = fold or false list`

The cons-handler here is the SHIPPED Church-OR `churchOrLambda` (#1056) applied DIRECTLY (no bespoke handler) and
the nil-handler is `false`: an empty list contributes `false`, and each `cons h t` ORs the head `h` into the
recursively-folded tail.  Unlike `isEmpty`, `any` inspects element VALUES, not just the list's shape — it is the
existential quantifier over a boolean list, the list analogue of a `∃`.

  * **`anyNil`** — `any nil ↝* false`, directly via `foldNil` (the empty list has no `true`).
  * **`anyConsTrueNil` (★)** — `any [true] ↝* true`: `foldSingleton` reaches `or true false`, which
    `churchOr_trueAnything` reduces to `true`.
  * **`anyConsFalseNil`** — `any [false] ↝* false`: `foldSingleton` reaches `or false false`, which
    `churchOr_falseAnything` reduces to the second argument `false`.
  * **`anyConsFalseConsTrueNil` (★)** — `any [false, true] ↝* true`: the RECURSIVE disjunction at depth 2.
    `foldCons` reaches `or false (any [true])`; the inner fold `any [true]` reduces to `true` (lifted through the
    OR's argument position via `StepStar.appArgument`), then `or false true ↝* true`.  Demonstrates the fold
    combines element contributions recursively — `false ∨ (true ∨ false) = true`.
  * **`anyDistinguishesByContent` (★)** — `¬ Conv (any [true]) (any [false])`: `any` distinguishes lists by
    ELEMENT CONTENT, not merely shape.  Both `[true]` and `[false]` are one-element `cons` cells (same shape), yet
    `any` computes them to `true` / `false` — were the results convertible, `true ≡ false`, refuted by #983.  The
    content-sensitivity that separates a genuine fold-over-values from `isEmpty`'s shape-only predicate.

Everything is the raw `Step` / `Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

The handler is `churchOrLambda` itself, so no new de Bruijn reshape is needed — the computations chain the shipped
fold lemmas (`foldNil` / `foldSingleton` / `foldCons`, #1081/#1082) with the shipped OR reductions
(`churchOr_trueAnything` / `churchOr_falseAnything`, #1056) via `StepStar.trans_compose`, lifting the recursive
tail through `StepStar.appArgument` for the depth-2 case.  `anyDistinguishesByContent` is `Conv.fromStepStar` /
`.trans` / `.sym` to the two values + `churchTrue_notConvertible_churchFalse` (#983).  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `any list = fold or false list` — the disjunction fold: "does the list contain a `true`?".  The cons-handler
is the shipped `churchOrLambda` (#1056) directly; the nil-handler is `false`. -/
def churchListAny (list : RawTerm 0) : RawTerm 0 :=
  churchFold churchOrLambda churchFalseLambda list

/-- `any nil ↝* false` — the empty list contains no `true`, directly via `foldNil`. -/
theorem anyNil : StepStar (churchListAny churchNil) churchFalseLambda :=
  foldNil churchOrLambda churchFalseLambda

/-- **★ `any [true] ↝* true`** — a singleton `true` list contains a `true`: `foldSingleton` reaches `or true false`,
which `churchOr_trueAnything` reduces to `true`. -/
theorem anyConsTrueNil :
    StepStar (churchListAny (churchCons churchTrueLambda churchNil)) churchTrueLambda :=
  StepStar.trans_compose
    (foldSingleton churchTrueLambda churchOrLambda churchFalseLambda)
    (churchOr_trueAnything churchFalseLambda)

/-- `any [false] ↝* false` — a singleton `false` list contains no `true`: `foldSingleton` reaches `or false false`,
which `churchOr_falseAnything` reduces to the second argument `false`. -/
theorem anyConsFalseNil :
    StepStar (churchListAny (churchCons churchFalseLambda churchNil)) churchFalseLambda :=
  StepStar.trans_compose
    (foldSingleton churchFalseLambda churchOrLambda churchFalseLambda)
    (churchOr_falseAnything churchFalseLambda)

/-- **★ `any [false, true] ↝* true`** — the RECURSIVE disjunction at depth 2: `foldCons` reaches
`or false (any [true])`; the inner fold `any [true]` reduces to `true` (lifted through the OR's argument position
via `StepStar.appArgument`), then `or false true ↝* true` (`churchOr_falseAnything`).  Demonstrates the fold
combines element contributions recursively — `false ∨ (true ∨ false) = true`. -/
theorem anyConsFalseConsTrueNil :
    StepStar (churchListAny (churchCons churchFalseLambda (churchCons churchTrueLambda churchNil)))
      churchTrueLambda :=
  StepStar.trans_compose
    (foldCons churchFalseLambda (churchCons churchTrueLambda churchNil) churchOrLambda churchFalseLambda)
    (StepStar.trans_compose
      (StepStar.appArgument (appCell churchOrLambda churchFalseLambda) anyConsTrueNil)
      (churchOr_falseAnything churchTrueLambda))

/-- **★ `any` distinguishes by ELEMENT CONTENT, not just shape.**  `any [true]` and `any [false]` are NOT
convertible, even though both lists have the SAME one-element `cons` shape.  The fold genuinely inspects element
values — were the results convertible, `true ≡ false` (refuted by `churchTrue_notConvertible_churchFalse`, #983).
The content-sensitivity that separates a fold-over-values from `isEmpty`'s shape-only predicate. -/
theorem anyDistinguishesByContent :
    ¬ Conv (churchListAny (churchCons churchTrueLambda churchNil))
        (churchListAny (churchCons churchFalseLambda churchNil)) := by
  intro hConv
  have convResults : Conv churchTrueLambda churchFalseLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar anyConsTrueNil))
      (Conv.trans hConv (Conv.fromStepStar anyConsFalseNil))
  exact churchTrue_notConvertible_churchFalse convResults

end FX1Poly.Typed
