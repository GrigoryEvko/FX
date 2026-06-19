import FX1Poly.Core.Metatheory.Normalization.IotaSN.SizeCompatClosureSN
import FX1Poly.Core.Metatheory.Normalization.Orders.RecursivePathOrder

/-! # FX1Poly/Core/.../IotaSN/ProductFormerLexMeasureSN
    — the type-complexity (product-former count) measure + the generic `lex(primaryMeasure, size)` SN
    combinator: the two reusable ingredients for size-GROWING / mixed-direction oriented rewrite SN

`SizeCompatClosureSN` ships the size-measure and single-`Nat`-measure SN combinators (for size-shrinking and
single-primary-measure rules).  A size-GROWING rule (one whose TERM grows while its driving TYPE structure
shrinks) needs a DIFFERENT measure, and a UNION of a shrinking and a growing rule needs a LEXICOGRAPHIC
measure.  This file collects the two reusable pieces:

  * **`RawTerm.productFormerCount`** — the type-complexity measure: a count of `gen_productCode` nodes.  A
    rewrite that peels one product-former and reuses its components without copying strictly decreases it,
    even as the term grows.
  * **`wellFounded_of_lexMeasureStrictlyDecreasing`** — the generic `lex(primaryMeasure, RawTerm.size)` SN
    combinator: any reduction whose every step EITHER drops `primaryMeasure`, OR preserves it while dropping
    `size`, is well-founded.  Lets `size` GROW as long as the primary measure ties only when size drops —
    the exact shape that unifies a size-shrinking and a size-growing rule.  Rides `wellFounded_of_lexPairMeasure`.

Both are relation-polymorphic / table-agnostic — the per-step decrease is a hypothesis, so a table-native
reduction (`StepOverTable [thisTable]`) reads its SN straight off these combinators by supplying a measure
and a per-step decrease lemma.  (Previously these lived inside the bespoke `SizeGrowingTransportRowSN` /
`LexJointRowSN` scaffolding; relocated here as the generic ingredients those bespoke files were built on.)

## Zero-axiom verification

`productFormerCount` is a plain structural mutual def; `wellFounded_of_lexMeasureStrictlyDecreasing` rides
`wellFounded_of_lexPairMeasure` (propext-clean `LexPair` `∨`-form) over `Nat.lt × Nat.lt`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-! ## The type-complexity measure — a count of `gen_productCode` nodes -/

-- The per-node weight is added on the RIGHT and the children sum is head-first, so the helper equations
-- below hold by `rfl` (the trailing `+ 0` from `childNil` and the `if`-at-a-concrete-generator both reduce
-- definitionally).  (A `/-- -/` doc comment cannot precede `mutual`.)
mutual
  def RawTerm.productFormerCount {scope : Nat} : RawTerm scope → Nat
    | .mkGen generator _payload children =>
        children.productFormerCount + (if generator = .gen_productCode then 1 else 0)
  def RawTermChildren.productFormerCount {shifts : List Nat} {scope : Nat} :
      RawTermChildren shifts scope → Nat
    | .childNil => 0
    | .childCons head tail => head.productFormerCount + tail.productFormerCount
end

/-- A `glueElim` node carries no product-former of its own, so its count is its child's. -/
theorem productFormerCount_glueElim {scope : Nat} (typeCode : RawTerm scope) :
    (RawTerm.mkGen .gen_glueElim () (.childCons typeCode .childNil)).productFormerCount
      = typeCode.productFormerCount := rfl

/-- A `pair` node carries no product-former of its own, so its count is the sum of its components'. -/
theorem productFormerCount_pair {scope : Nat} (leftValue rightValue : RawTerm scope) :
    (RawTerm.mkGen .gen_pair ()
      (.childCons leftValue (.childCons rightValue .childNil))).productFormerCount
      = leftValue.productFormerCount + rightValue.productFormerCount := rfl

/-- A `productCode` node carries exactly ONE product-former plus its components' counts. -/
theorem productFormerCount_productCode {scope : Nat} (leftCode rightCode : RawTerm scope) :
    (RawTerm.mkGen .gen_productCode ()
      (.childCons leftCode (.childCons rightCode .childNil))).productFormerCount
      = leftCode.productFormerCount + rightCode.productFormerCount + 1 := rfl

/-! ## The generic `lex(primaryMeasure, size)` strong-normalization combinator -/

/-- **★ The generic `lex(primaryMeasure, RawTerm.size)` strong-normalization combinator.**  Any reduction
relation whose every step EITHER strictly drops `primaryMeasure`, OR preserves it while strictly dropping
`RawTerm.size`, is well-founded.  Rides `wellFounded_of_lexPairMeasure` over `Nat.lt × Nat.lt`.  The
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

end FX1Poly.Core
