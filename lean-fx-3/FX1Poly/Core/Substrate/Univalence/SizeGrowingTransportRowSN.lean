import FX1Poly.Core.Metatheory.Normalization.IotaSN.SizeCompatClosureSN

/-! # FX1Poly/Core/Substrate/Univalence/SizeGrowingTransportRowSN
    — the first instantiated strong-normalization theorem for a SIZE-GROWING oriented rule, by a
    type-complexity (product-former count) measure that decreases on EVERY step

This is the genuinely-hard half of the DEFUNIV-SN keystone: a rule whose TERM grows while its driving
TYPE structure shrinks.  `DefinitionalUnivalenceRowSN` handled the size-SHRINKING univalence row by
`RawTerm.size`; the RPO route handles the rank-orientable rows.  Neither covers a size-GROWING rule.

The sharp lesson (correcting the original keystone framing): a `lex(typeComplexity, size)` measure does NOT
work for a size-growing rule, because applying the rule INSIDE a subterm (congruence) grows the WHOLE
term's `size`, so `size` cannot be the lexicographic tiebreaker.  SN of a size-growing rule's congruence
closure requires a SINGLE primary measure that strictly decreases on EVERY step — root AND congruence — and
such a measure exists precisely when the rule does NOT DUPLICATE a redex-containing subterm.  Duplication
(beta's argument copy, the natRec/listElim successor rows' substituted recursive call, naive cubical
`transp` copying its path/argument) is exactly what makes raw reduction non-SN and forces the semantic /
Tait route — which is why full cubical SN is proven by reducibility, not a syntactic order.

## The demo rule (synthetic, cubical-flavored — NOT a shipped semantic rule)

`glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)` — a unary Kan-style eliminator distributing over
a binary type former.  It is GENUINELY size-growing (the `pair` + two `glueElim` wrapper is strictly bigger
than one `glueElim`), and it does NOT duplicate: `A` and `B` each appear exactly once in the reduct.  So the
count of `gen_productCode` nodes strictly decreases by exactly 1 on every step (the outer `productCode` is
peeled; `A`, `B` are reused not copied), and that single measure proves SN — with the term growing.

## What this ships

  * `RawTerm.productFormerCount` / `RawTermChildren.productFormerCount` — the type-complexity measure
    (a count of `gen_productCode` nodes), mutual.
  * `SizeGrowingTransportDemoStep` / `…Children` — the compatible closure of the demo rule (mirrors
    `IotaStep`).
  * **`SizeGrowingTransportDemoStep.productFormerCountStrictlyDecreases` (★)** — every step strictly drops
    the product-former count (root by peeling the former, congruence by additivity); explicit mutual
    recursor, core `Nat` arithmetic, no `omega`.
  * **`sizeGrowingTransportDemo_wellFounded` (★)** — the demo's congruence closure is SN, via
    `wellFounded_of_natMeasureStrictlyDecreasing` at `measure := RawTerm.productFormerCount`.  The first
    instantiated `WellFounded` for a SIZE-GROWING oriented row.
  * `sizeGrowingTransportDemo_rootGrowsSize` — the root step strictly GROWS `RawTerm.size` (closed witness),
    so the size combinator provably does NOT apply: the type-complexity measure is essential.

## Honest scope / the boundary

This is SN for the size-growing-but-NON-DUPLICATING fragment.  The SHIPPED size-growing rows
(`natRecSuccIotaRow`, `natElimSuccIotaRow`, `listElimConsIotaRow`) DUPLICATE the recursive call (via
substitution / a retained subterm), so they have NO everywhere-decreasing simple measure — their SN needs
Tait (the markers below pin this).  The cubical `gen_transp`/`gen_hcomp` are reserved (no shipped rules);
when given rules they will copy the path/argument across the components, joining the duplication boundary —
which is the syntactic reason their SN is semantic, not a measure.

## Zero-axiom verification

The measure is a plain structural mutual def; the strict-decrease is the explicit mutual recursor over a
`Prop`-valued motive (propext-clean); the `gen_productCode`-weight `if` is never evaluated in the
congruence arms (same generator both sides) and reduces concretely in the root arm.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
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

/-! ## The demo rule's compatible closure -/

-- The compatible (congruence) closure of the size-growing demo rewrite
-- `glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)`.  Mirrors `IotaStep`/`IotaStepChildren`; the
-- root is BAKED IN.  (A `/-- -/` doc comment cannot precede `mutual`.)
mutual
  inductive SizeGrowingTransportDemoStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
    | fire {scope : Nat} (leftCode rightCode : RawTerm scope) :
        SizeGrowingTransportDemoStep
          (.mkGen .gen_glueElim ()
            (.childCons (.mkGen .gen_productCode ()
              (.childCons leftCode (.childCons rightCode .childNil))) .childNil))
          (.mkGen .gen_pair ()
            (.childCons (.mkGen .gen_glueElim () (.childCons leftCode .childNil))
              (.childCons (.mkGen .gen_glueElim () (.childCons rightCode .childNil)) .childNil)))
    | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
           {children children' : RawTermChildren gen.binderShifts scope}
           (childStep : SizeGrowingTransportDemoStepChildren children children') :
        SizeGrowingTransportDemoStep (.mkGen gen payload children) (.mkGen gen payload children')
  inductive SizeGrowingTransportDemoStepChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
      RawTermChildren binderShifts parentScope →
      RawTermChildren binderShifts parentScope → Prop where
    | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
           {head head' : RawTerm (parentScope + headShift)}
           (rest : RawTermChildren restShifts parentScope)
           (childStep : SizeGrowingTransportDemoStep head head') :
        SizeGrowingTransportDemoStepChildren
          (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest)
    | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
            (head : RawTerm (parentScope + headShift))
            {rest rest' : RawTermChildren restShifts parentScope}
            (restStep : SizeGrowingTransportDemoStepChildren rest rest') :
        SizeGrowingTransportDemoStepChildren
          (RawTermChildren.childCons head rest) (RawTermChildren.childCons head rest')
end

/-- **★ Every demo step strictly decreases the product-former count.**  Root: the rule peels the outer
`productCode` and reuses `A`, `B` without copying, so the count drops by exactly 1.  Congruence: the count
is additive over the spine and the node weight is identical on both sides, so the strict child decrease
lifts.  Explicit mutual recursor; core `Nat` arithmetic, no `omega`. -/
theorem SizeGrowingTransportDemoStep.productFormerCountStrictlyDecreases
    {scope : Nat} {source target : RawTerm scope}
    (step : SizeGrowingTransportDemoStep source target) :
    target.productFormerCount < source.productFormerCount := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      SizeGrowingTransportDemoStep first second → Prop :=
    fun {_} first second _ => second.productFormerCount < first.productFormerCount
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      SizeGrowingTransportDemoStepChildren first second → Prop :=
    fun {_} {_} first second _ => second.productFormerCount < first.productFormerCount
  exact
    SizeGrowingTransportDemoStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} _leftCode _rightCode => by
        exact Nat.lt_succ_self _)
      (fun {_} _gen _payload {children} {children'} _childStep childStepIH => by
        dsimp only [RawTerm.productFormerCount]
        exact Nat.add_lt_add_right childStepIH _)
      (fun {_} {_} {_} {head} {head'} rest _childStep childStepIH => by
        dsimp only [RawTermChildren.productFormerCount]
        exact Nat.add_lt_add_right childStepIH rest.productFormerCount)
      (fun {_} {_} {_} head {rest} {rest'} _restStep restStepIH => by
        dsimp only [RawTermChildren.productFormerCount]
        exact Nat.add_lt_add_left restStepIH head.productFormerCount)
      step

/-- **★ The size-growing demo rule's congruence closure is strongly normalizing — by the type-complexity
(product-former count) measure, while the term GROWS.**  The first instantiated `WellFounded` for a
SIZE-GROWING oriented row, read off the measure-generic combinator
`wellFounded_of_natMeasureStrictlyDecreasing` at `measure := RawTerm.productFormerCount`. -/
theorem sizeGrowingTransportDemo_wellFounded {scope : Nat} :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      SizeGrowingTransportDemoStep earlierTerm laterTerm) :=
  wellFounded_of_natMeasureStrictlyDecreasing (measure := RawTerm.productFormerCount)
    SizeGrowingTransportDemoStep.productFormerCountStrictlyDecreases

/-- Every raw term is demo strongly normalizing (accessible). -/
theorem SizeGrowingTransportDemoStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc (fun (laterTerm earlierTerm : RawTerm scope) =>
      SizeGrowingTransportDemoStep earlierTerm laterTerm) sourceTerm :=
  sizeGrowingTransportDemo_wellFounded.apply sourceTerm

/-- **★ The root step genuinely GROWS `RawTerm.size`** (closed witness at `A = B = unit`: the redex has
size 7, the reduct size 9).  So this is a genuine size-growing SN, NOT a disguised size-shrinking one — the
`wellFounded_of_sizeStrictlyDecreasing` combinator provably does not apply, and the product-former measure
is essential. -/
theorem sizeGrowingTransportDemo_rootGrowsSize :
    (show RawTerm 0 from
      .mkGen .gen_glueElim ()
        (.childCons (.mkGen .gen_productCode ()
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil) .childNil))) .childNil)).size
    < (show RawTerm 0 from
        .mkGen .gen_pair ()
          (.childCons (.mkGen .gen_glueElim () (.childCons (.mkGen .gen_unit () .childNil) .childNil))
            (.childCons (.mkGen .gen_glueElim () (.childCons (.mkGen .gen_unit () .childNil) .childNil))
              .childNil))).size := by decide

/-- **Non-vacuity at the congruence arm.**  The demo rule fires INSIDE the function-position child of
`gen_app` (`cong ∘ here ∘ fire`), so the closure is inhabited beyond the root. -/
theorem sizeGrowingTransportDemo_congSmoke {scope : Nat} (leftCode rightCode sibling : RawTerm scope) :
    SizeGrowingTransportDemoStep
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
  SizeGrowingTransportDemoStep.cong .gen_app ()
    (SizeGrowingTransportDemoStepChildren.here _
      (SizeGrowingTransportDemoStep.fire leftCode rightCode))

/-! ## Honest rails -/

/-- **Honesty marker.**  The demo root step genuinely GROWS `RawTerm.size`
(`sizeGrowingTransportDemo_rootGrowsSize`), so the size combinator does not apply — this is a true
size-growing SN.  `= true`. -/
def fxSizeGrowingDemo_isGenuinelySizeGrowing : Bool := true

/-- **Honesty marker.**  SN here is by a SINGLE primary measure decreasing on EVERY step, NOT a
`lex(measure, size)` — a lex with `size` as tiebreaker fails for size-growing rules because congruence
grows `size`.  `= true`. -/
def fxSizeGrowingDemo_measureDecreasesEveryStep : Bool := true

/-- **Honesty marker.**  The single-measure SN works because the rule is NON-DUPLICATING (`A`, `B` appear
once each in the reduct).  `= true`. -/
def fxSizeGrowingDemo_isNonDuplicating : Bool := true

/-- **Honesty marker.**  The SHIPPED size-growing rows (`natRecSuccIotaRow` / `natElimSuccIotaRow` via
substituted recursive call, `listElimConsIotaRow` via the retained recursive subterm) DUPLICATE, so they
have NO everywhere-decreasing simple measure and their SN needs Tait — NOT covered by this demo.  The
reserved cubical `gen_transp`/`gen_hcomp` will copy the path/argument when given rules, joining the same
boundary (the syntactic reason cubical SN is semantic).  `= true`. -/
def fxShippedSizeGrowingRows_needTait : Bool := true

end FX1Poly.Core
