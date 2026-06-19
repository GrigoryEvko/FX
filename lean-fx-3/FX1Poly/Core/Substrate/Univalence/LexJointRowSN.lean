import FX1Poly.Core.Substrate.Univalence.DefinitionalUnivalenceRowSN
import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportRowSN
import FX1Poly.Core.Metatheory.Normalization.Orders.RecursivePathOrder

/-! # FX1Poly/Core/Substrate/Univalence/LexJointRowSN
    — the first JOINT strong normalization across the SIZE AXIS: a size-SHRINKING oriented row and a
    size-GROWING oriented row are jointly SN under ONE lexicographic type-complexity measure

`DefinitionalUnivalenceRowSN` proved the univalence row SN by `RawTerm.size` (it shrinks).
`SizeGrowingTransportRowSN` proved the demo row SN by `RawTerm.productFormerCount` (it grows but drops the
former count).  Each alone has a single measure.  The OPEN question was the JOINT SN — the union of a
size-shrinking and a size-growing relation, where neither's measure is monotone for the other (size grows
under the demo; the former-count is untouched by univalence).  A union of two SN relations is NOT
automatically SN.

This file CLOSES that joint SN for this mixed pair, by a lexicographic product `lex(productFormerCount,
size)`.  The load-bearing fact is **`UnivalenceRowStep.preservesProductFormerCount`**: the univalence
rewrite `idCode(universeCode, A, B) ↝ equivCode(A, B)` touches only `idCode`/`equivCode`/`universeCode` —
never `productCode` — so it leaves the product-former count UNCHANGED.  Therefore on the union `R =
UnivalenceRowStep ∪ SizeGrowingTransportDemoStep`:

  * a univalence step:  `productFormerCount` PRESERVED, `size` STRICTLY DROPS  → lex via the 2nd component;
  * a size-growing step: `productFormerCount` STRICTLY DROPS                    → lex via the 1st component.

So every step of the mixed union strictly decreases `lex(productFormerCount, size)`, and the union is
strongly normalizing — the first instantiated joint SN spanning both directions of the size axis.

## What this ships

  * **`wellFounded_of_lexMeasureStrictlyDecreasing` (★)** — the generic `lex(primaryMeasure, RawTerm.size)`
    SN combinator: any relation whose every step drops the primary measure, OR preserves it while dropping
    `size`, is well-founded.  Rides the propext-clean `wellFounded_of_lexPairMeasure` (NOT `Prod.Lex`).
    The lexicographic sibling of `wellFounded_of_natMeasureStrictlyDecreasing`.
  * **`UnivalenceRowStep.preservesProductFormerCount` (★)** — univalence leaves the product-former count
    unchanged (mutual recursor, EQUALITY; the load-bearing compatibility fact).
  * **`unifiedDefinitionalRow_wellFounded` (★)** — the union of the size-shrinking univalence row and the
    size-growing demo row is SN by `lex(productFormerCount, size)`.  The first joint SN across the size axis.

## Honest scope

This is the joint SN of a size-shrinking + a size-growing rule that are MEASURE-COMPATIBLE (univalence
preserves the demo's primary measure).  It is NOT the full joint SN with beta/iota: those DUPLICATE
redex-containing subterms (no everywhere-decreasing measure), so they stay Tait-imported — the lexicographic
trick works precisely because BOTH rows here are non-duplicating and the shrinking row preserves the growing
row's measure.  The general principle on display: a set of oriented rules is jointly SN under a
lexicographic tower of measures when each rule decreases some level and preserves every higher level.

## Zero-axiom verification

The combinator rides `wellFounded_of_lexPairMeasure` (propext-clean by construction); the preservation is an
explicit mutual recursor over a `Prop`-valued equality motive; the union split is a `match` on `Or`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-! ## The generic lexicographic SN-by-(primary, size) combinator -/

/-- **★ The generic `lex(primaryMeasure, RawTerm.size)` strong-normalization combinator.**  Any reduction
relation whose every step EITHER strictly drops `primaryMeasure`, OR preserves it while strictly dropping
`RawTerm.size`, is well-founded.  Rides `wellFounded_of_lexPairMeasure` over `Nat.lt × Nat.lt`.  This is the
lexicographic sibling of `wellFounded_of_natMeasureStrictlyDecreasing`: it lets `size` GROW as long as the
primary measure ties only when size drops — the exact shape that unifies a size-shrinking and a
size-growing rule. -/
theorem wellFounded_of_lexMeasureStrictlyDecreasing
    {stepRelation : {scope : Nat} → RawTerm scope → RawTerm scope → Prop}
    {primaryMeasure : {scope : Nat} → RawTerm scope → Nat}
    (decreasesLex : ∀ {scope : Nat} {source target : RawTerm scope},
      stepRelation source target →
        primaryMeasure target < primaryMeasure source
        ∨ (primaryMeasure target = primaryMeasure source ∧ target.size < source.size))
    {scope : Nat} :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      stepRelation earlierTerm laterTerm) :=
  wellFounded_of_lexPairMeasure
    (measure := fun (term : RawTerm scope) => (primaryMeasure term, term.size))
    (firstWellFounded := Nat.lt_wfRel.wf)
    (secondWellFounded := Nat.lt_wfRel.wf)
    (measureDecreases := fun _source _target step => decreasesLex step)

/-! ## The load-bearing compatibility fact — univalence preserves the product-former count -/

/-- **★ The univalence rewrite preserves the product-former count.**  `idCode(universeCode, A, B) ↝
equivCode(A, B)` touches only `idCode`/`equivCode`/`universeCode` — never `productCode` — and reuses `A`,
`B`, so the count of `gen_productCode` nodes is unchanged.  Explicit mutual recursor over an EQUALITY motive:
root by the concrete shapes (`universeCode` contributes 0, so the only difference is a leading `0 +`,
discharged by `Nat.zero_add`), congruence by additivity.  This is what makes the lexicographic joint SN
compose. -/
theorem UnivalenceRowStep.preservesProductFormerCount {scope : Nat} {source target : RawTerm scope}
    (step : UnivalenceRowStep source target) :
    target.productFormerCount = source.productFormerCount := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      UnivalenceRowStep first second → Prop :=
    fun {_} first second _ => second.productFormerCount = first.productFormerCount
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      UnivalenceRowStepChildren first second → Prop :=
    fun {_} {_} first second _ => second.productFormerCount = first.productFormerCount
  exact
    UnivalenceRowStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} _levelExpr _flag _lhsCode _rhsCode => by
        exact (Nat.zero_add _).symm)
      (fun {_} _gen _payload {children} {children'} _childStep childStepIH => by
        dsimp only [RawTerm.productFormerCount]
        exact congrArg (· + _) childStepIH)
      (fun {_} {_} {_} {head} {head'} rest _childStep childStepIH => by
        dsimp only [RawTermChildren.productFormerCount]
        exact congrArg (· + rest.productFormerCount) childStepIH)
      (fun {_} {_} {_} head {rest} {rest'} _restStep restStepIH => by
        dsimp only [RawTermChildren.productFormerCount]
        exact congrArg (head.productFormerCount + ·) restStepIH)
      step

/-! ## The mixed union and its joint SN -/

/-- The mixed reduction relation: a univalence step (size-shrinking) OR a size-growing demo step.  Each step
fires exactly one of the two rows at one position — the combined reduction over both rows. -/
def UnifiedDefinitionalRowStep {scope : Nat} (source target : RawTerm scope) : Prop :=
  UnivalenceRowStep source target ∨ SizeGrowingTransportDemoStep source target

/-- **★ Every mixed-union step strictly decreases `lex(productFormerCount, size)`.**  A univalence step
preserves the former count and drops size (2nd lex component); a size-growing step drops the former count
(1st lex component). -/
theorem unifiedDefinitionalRow_decreasesLex {scope : Nat} {source target : RawTerm scope}
    (step : UnifiedDefinitionalRowStep source target) :
    target.productFormerCount < source.productFormerCount
    ∨ (target.productFormerCount = source.productFormerCount ∧ target.size < source.size) :=
  match step with
  | Or.inl univalenceStep =>
      Or.inr ⟨UnivalenceRowStep.preservesProductFormerCount univalenceStep,
              UnivalenceRowStep.sizeStrictlyDecreases univalenceStep⟩
  | Or.inr sizeGrowingStep =>
      Or.inl (SizeGrowingTransportDemoStep.productFormerCountStrictlyDecreases sizeGrowingStep)

/-- **★ JOINT strong normalization across the size axis.**  The union of the size-SHRINKING univalence row
and the size-GROWING demo row is strongly normalizing, by the single lexicographic type-complexity measure
`lex(productFormerCount, size)`.  The first instantiated joint SN spanning both directions of the size axis
— landable precisely because univalence preserves the former count
(`UnivalenceRowStep.preservesProductFormerCount`). -/
theorem unifiedDefinitionalRow_wellFounded {scope : Nat} :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      UnifiedDefinitionalRowStep earlierTerm laterTerm) :=
  wellFounded_of_lexMeasureStrictlyDecreasing
    (primaryMeasure := RawTerm.productFormerCount)
    unifiedDefinitionalRow_decreasesLex

/-- Every raw term is jointly strongly normalizing (accessible) under the mixed union. -/
theorem UnifiedDefinitionalRowStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc (fun (laterTerm earlierTerm : RawTerm scope) =>
      UnifiedDefinitionalRowStep earlierTerm laterTerm) sourceTerm :=
  unifiedDefinitionalRow_wellFounded.apply sourceTerm

/-! ## Non-vacuity — the union genuinely contains both directions -/

/-- The union contains the size-SHRINKING univalence row (a univalence congruence step is a mixed step). -/
theorem unifiedDefinitionalRow_containsShrinking {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (lhsCode rhsCode sibling : RawTerm scope) :
    UnifiedDefinitionalRowStep
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_idCode ()
            (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
              (.childCons lhsCode (.childCons rhsCode .childNil))))
          (.childCons sibling .childNil)))
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_equivCode ()
            (.childCons lhsCode (.childCons rhsCode .childNil)))
          (.childCons sibling .childNil))) :=
  Or.inl (univalenceRowStep_congSmoke levelExpr flag lhsCode rhsCode sibling)

/-- The union contains the size-GROWING demo row (a demo congruence step is a mixed step). -/
theorem unifiedDefinitionalRow_containsGrowing {scope : Nat}
    (leftCode rightCode sibling : RawTerm scope) :
    UnifiedDefinitionalRowStep
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_glueElim ()
            (.childCons (.mkGen .gen_productCode ()
              (.childCons leftCode (.childCons rightCode .childNil))) .childNil))
          (.childCons sibling .childNil)))
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons (.mkGen .gen_glueElim () (.childCons leftCode .childNil))
              (.childCons (.mkGen .gen_glueElim () (.childCons rightCode .childNil)) .childNil)))
          (.childCons sibling .childNil))) :=
  Or.inr (sizeGrowingTransportDemo_congSmoke leftCode rightCode sibling)

/-! ## Honest rails -/

/-- **Honesty marker.**  This joint SN genuinely MIXES a size-shrinking row (univalence) and a size-growing
row (the demo) in ONE SN relation.  `= true`. -/
def fxLexJointSN_mixesShrinkingAndGrowing : Bool := true

/-- **Honesty marker.**  The lexicographic measure composes because univalence PRESERVES the product-former
count (`UnivalenceRowStep.preservesProductFormerCount`) — the shrinking row leaves the growing row's primary
measure invariant.  `= true`. -/
def fxLexJointSN_composesViaFormerCountPreservation : Bool := true

/-- **Honesty marker.**  This is NOT the full joint SN with beta/iota — those DUPLICATE redex-containing
subterms, so no everywhere-decreasing measure exists and they stay Tait-imported.  The lexicographic trick
works only because both rows here are non-duplicating.  `= false`. -/
def fxLexJointSN_isJointWithBetaIota : Bool := false

end FX1Poly.Core
