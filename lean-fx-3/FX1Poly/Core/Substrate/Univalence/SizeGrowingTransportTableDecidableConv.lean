import FX1Poly.Core.Rewriting.Confluence.DefUnivConfluence
import FX1Poly.Core.Rewriting.RuleTables.Tables.TableNormalize
import FX1Poly.Core.Metatheory.Normalization.IotaSN.ProductFormerLexMeasureSN

/-! # FX1Poly/Core/Substrate/Univalence/SizeGrowingTransportTableDecidableConv
    — the SIZE-GROWING definitional rule shipped OVER THE TABLE AS DATA, with decidable conversion

This is the table-native form of the genuinely-hard half of definitional univalence: a rule whose TERM
grows while its driving TYPE structure shrinks.  `UnivalenceTableDecidableConv` shipped the size-SHRINKING
univalence row over the generic `StepOverTable` engine; this file ships its size-GROWING sibling — the
synthetic Kan-distribution rule

    `glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)`

— as the `IotaRuleDesc` row `sizeGrowingTransportDemoRule`, and reads its decision procedure off the SAME
generic engine.  The reduct reaches into the SCRUTINEE's children (`A`, `B` are children of the matched
`productCode`, not direct spine children of `glueElim`), so the row uses the DSL's `scrutineeChildAt`
projector under nested `builtGen` cells — the "nested `builtGen`, expressible" claim made concrete.

Everything but SN is generic: `WfIotaTable` (four `rfl` checks on a singleton), scope-uniformity (the nested
target's constant-unit payloads), confluence (`StepOverTable.confluent`), the reducer / normalizer /
decidable conversion (`ConvOverTable.decidableOfStronglyNormalizing`).  SN is the ONE bespoke-as-data
ingredient — and crucially it is NOT a `RawTerm.size` decrease (the term GROWS): it is a
`RawTerm.productFormerCount` decrease (the rule peels one `gen_productCode` and reuses `A`, `B` without
copying), fed to the generic measure combinator `wellFounded_of_natMeasureStrictlyDecreasing`.  This is the
first table-native `WellFounded` for a SIZE-GROWING oriented row.

The product-former measure and its node-weight lemmas come from the generic `ProductFormerLexMeasureSN`;
the `StepOverTable [transportRow]` relation proved SN here supersedes the retired bespoke
`SizeGrowingTransportDemoStep` inductive.

## Zero-axiom verification

`StepOverTable.confluent` + the `rfl` certificates; the explicit `StepOverTable.rec` measure-decrease (root
by the `firesOn?` head inversion `firesOn?_some_primaryHead` to recover the peeled `productCode`, congruence
by core `Nat` arithmetic on the additive `productFormerCount`); `wellFounded_of_natMeasureStrictlyDecreasing`;
`ConvOverTable.decidableOfStronglyNormalizing`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-- The size-growing definitional rule as DATA: `glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)`.
The reduct's `A`, `B` are the matched `productCode` scrutinee's children, reached by the DSL's
`scrutineeChildAt 0 0` / `scrutineeChildAt 0 1` under two `builtGen .gen_glueElim` cells inside a
`builtGen .gen_pair` cell. -/
def sizeGrowingTransportDemoRule : IotaRuleDesc where
  elimGenerator := .gen_glueElim
  scrutinees := [{ slot := 0, head := .gen_productCode }]
  target := .builtGen .gen_pair (.constantFamily fun _ => ())
    (.spineCons
      (.builtGen .gen_glueElim (.constantFamily fun _ => ())
        (.spineCons (.scrutineeChildAt 0 0) .spineNil))
      (.spineCons
        (.builtGen .gen_glueElim (.constantFamily fun _ => ())
          (.spineCons (.scrutineeChildAt 0 1) .spineNil))
        .spineNil))

/-- The transport row fires on a `productCode`-headed scrutinee and distributes the `glueElim` over the
former's two components. -/
theorem sizeGrowingTransportDemoRule_firesOnProductCode {scope : Nat}
    (leftCode rightCode : RawTerm scope) :
    sizeGrowingTransportDemoRule.firesOn? ()
      (.childCons (.mkGen .gen_productCode ()
        (.childCons leftCode (.childCons rightCode .childNil))) .childNil)
    = some (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_glueElim () (.childCons leftCode .childNil))
          (.childCons (.mkGen .gen_glueElim () (.childCons rightCode .childNil)) .childNil))) := rfl

/-- The transport rule as a SINGLETON table — the table-native form of the size-growing row. -/
abbrev transportTable : List IotaRuleDesc := [sizeGrowingTransportDemoRule]

/-- The singleton transport table is well-formed-orthogonal: one row, all four decidable `WfIotaTable`
checks `rfl`. -/
theorem transportTable_isWf : WfIotaTable transportTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- The transport row is scope-uniform: eliminator head `gen_glueElim` is not the variable generator, its
reduct's nested `gen_pair` / `gen_glueElim` cells all carry scope-invariant constant-unit payloads over
`scrutineeChildAt` projections, and its single guard-free `gen_productCode` scrutinee spec is
scope-uniform. -/
theorem sizeGrowingTransportDemoRule_isScopeUniform :
    sizeGrowingTransportDemoRule.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨⟨fun contra => Generator.noConfusion contra, fun _ _ _ => rfl⟩,
      ⟨⟨fun contra => Generator.noConfusion contra, fun _ _ _ => rfl⟩, ⟨⟩, ⟨⟩⟩,
      ⟨⟨fun contra => Generator.noConfusion contra, fun _ _ _ => rfl⟩, ⟨⟩, ⟨⟩⟩,
      ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform (fun contra => Generator.noConfusion contra)⟩

/-- Every row of the singleton transport table is scope-uniform — the one row. -/
theorem transportTable_isScopeUniform :
    ∀ rule, rule ∈ transportTable → rule.IsScopeUniform := by
  intro rule isRow
  cases isRow with
  | head => exact sizeGrowingTransportDemoRule_isScopeUniform
  | tail _ emptyMem => cases emptyMem

/-- **The singleton transport table is confluent** — generic orthogonal-table confluence. -/
theorem transportTable_isConfluent {scope : Nat} :
    Confluent (fun source target : RawTerm scope => StepOverTable transportTable source target) :=
  StepOverTable.confluent transportTable_isWf transportTable_isScopeUniform

/-- **The root firing strictly decreases the product-former count.**  The firing peels the outer
`gen_productCode` and reuses `A`, `B` without copying, so the count drops by exactly one — while the term
GROWS (the `pair` + two `glueElim` wrappers).  The reduct shape is recovered from `fires` by the head
inversion `firesOn?_some_primaryHead` (pins the slot-0 head to `gen_productCode`) followed by the
`rfl`-computation of `firesOn?` on the concrete spine. -/
theorem sizeGrowingTransportDemoRule_firingProductFormerDrop {scope : Nat}
    (elimPayload : Generator.gen_glueElim.payload scope)
    {spine : RawTermChildren Generator.gen_glueElim.binderShifts scope} {reduct : RawTerm scope}
    (fires : sizeGrowingTransportDemoRule.firesOn? elimPayload spine = some reduct) :
    reduct.productFormerCount < (RawTerm.mkGen .gen_glueElim elimPayload spine).productFormerCount := by
  match spine, fires with
  | .childCons scrutinee .childNil, fires =>
      match scrutinee, fires with
      | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren, fires =>
          have headIsProduct : scrutineeGenerator = Generator.gen_productCode :=
            sizeGrowingTransportDemoRule.firesOn?_some_primaryHead fires rfl rfl
          subst headIsProduct
          match scrutineeChildren, fires with
          | .childCons leftCode (.childCons rightCode .childNil), fires =>
              have reductEq : reduct = .mkGen .gen_pair ()
                  (.childCons (.mkGen .gen_glueElim () (.childCons leftCode .childNil))
                    (.childCons (.mkGen .gen_glueElim () (.childCons rightCode .childNil)) .childNil)) := by
                have firesComputes : sizeGrowingTransportDemoRule.firesOn? elimPayload
                    (.childCons (.mkGen .gen_productCode scrutineePayload
                      (.childCons leftCode (.childCons rightCode .childNil))) .childNil)
                  = some (.mkGen .gen_pair ()
                      (.childCons (.mkGen .gen_glueElim () (.childCons leftCode .childNil))
                        (.childCons (.mkGen .gen_glueElim () (.childCons rightCode .childNil))
                          .childNil))) := rfl
                rw [firesComputes] at fires
                exact (Option.some.inj fires).symm
              subst reductEq
              exact Nat.lt_succ_self _

/-- **★ Every `StepOverTable [transportRow]` step strictly decreases the product-former count.**  Root by
`sizeGrowingTransportDemoRule_firingProductFormerDrop`; congruence by the additive `productFormerCount`
arithmetic (the node weight is identical on both sides of every congruence step).  Explicit mutual recursor;
the singleton membership collapses the row choice to the one row. -/
theorem stepOverTransportTable_productFormerStrictlyDecreases {scope : Nat} {source target : RawTerm scope}
    (step : StepOverTable transportTable source target) :
    target.productFormerCount < source.productFormerCount := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      StepOverTable transportTable first second → Prop :=
    fun {_} first second _ => second.productFormerCount < first.productFormerCount
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      StepOverTableChildren transportTable first second → Prop :=
    fun {_} {_} first second _ => second.productFormerCount < first.productFormerCount
  exact
    StepOverTable.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_rule} isRow elimPayload {_spine} {_reduct} fires => by
        cases isRow with
        | head => exact sizeGrowingTransportDemoRule_firingProductFormerDrop elimPayload fires
        | tail _ emptyMem => cases emptyMem)
      (fun {_} _gen _payload {_children} {_children'} _childStep childStepIH => by
        dsimp only [RawTerm.productFormerCount]
        exact Nat.add_lt_add_right childStepIH _)
      (fun {_} {_} {_} {_head} {_head'} rest _childStep childStepIH => by
        dsimp only [RawTermChildren.productFormerCount]
        exact Nat.add_lt_add_right childStepIH rest.productFormerCount)
      (fun {_} {_} {_} head {_rest} {_rest'} _restStep restStepIH => by
        dsimp only [RawTermChildren.productFormerCount]
        exact Nat.add_lt_add_left restStepIH head.productFormerCount)
      step

/-- **★ The singleton transport table is strongly normalizing — by the type-complexity measure, while the
term GROWS.**  Every term is accessible under the table's reduction successor, by the generic measure
combinator at `measure := RawTerm.productFormerCount`.  The first table-native `WellFounded` for a
SIZE-GROWING oriented row: `RawTerm.size` provably does not apply (the root step grows it), the product-
former count provably does. -/
theorem transportTable_isStronglyNormalizing {scope : Nat} (term : RawTerm scope) :
    Acc (StepOverTable.successorOver transportTable) term :=
  (wellFounded_of_natMeasureStrictlyDecreasing (measure := RawTerm.productFormerCount)
    (stepRelation := fun {_} source target => StepOverTable transportTable source target)
    stepOverTransportTable_productFormerStrictlyDecreases).apply term

/-- **★ The size-growing definitional rule's conversion is DECIDABLE BY COMPUTATION — over the table, as
data.**  Decide `a ⟷*_transport b` by normalizing both over `[sizeGrowingTransportDemoRule]` and comparing.
No bespoke `reduceStep`, no bespoke joinability proof: confluence + the product-former SN witness feed the
generic `ConvOverTable.decidableOfStronglyNormalizing`. -/
def transportTableConv_decidable {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Decidable (ConvOverTable transportTable leftTerm rightTerm) :=
  ConvOverTable.decidableOfStronglyNormalizing transportTable_isConfluent
    (transportTable_isStronglyNormalizing leftTerm)
    (transportTable_isStronglyNormalizing rightTerm)

/-- **Honesty marker.**  The size-growing rule's decidable Conv is shipped OVER THE TABLE as data, and its
SN is genuinely by the product-former measure, NOT `RawTerm.size` (the term grows — see
`sizeGrowingTransportDemo_rootGrowsSize`).  `= true`. -/
def fxSizeGrowingTransportConv_shippedOverTableAsData : Bool := true

end FX1Poly.Core
