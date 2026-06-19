import FX1Poly.Core.Rewriting.Confluence.DefUnivConfluence
import FX1Poly.Core.Rewriting.RuleTables.Tables.TableNormalize
import FX1Poly.Core.Metatheory.Normalization.IotaSN.SizeCompatClosureSN

/-! # FX1Poly/Core/Substrate/Univalence/UnivalenceTableDecidableConv
    — definitional-univalence decidable conversion BY COMPUTATION, shipped OVER THE TABLE AS DATA

This is the table-native replacement for the bespoke `UnivalenceRowDecidableConv` (which is marked TODO
REFACTOR).  Instead of a hand-rolled `UnivalenceRowStep` inductive + a bespoke `univNF` normalizer + a
bespoke joinability decider, the definitional-univalence rule is DATA — the shipped `IotaRuleDesc` row
`univalenceShapedDemoRule` (`idCode(universeCode, A, B) ↝ equivCode(A, B)`) — and the entire decision
procedure is read off the GENERIC `StepOverTable` engine instantiated at the singleton table
`[univalenceShapedDemoRule]`:

  * confluence — `StepOverTable.confluent` from the decidable orthogonality certificate `WfIotaTable` (all
    four checks `rfl` on a singleton) plus the shipped scope-uniformity of the row;
  * the reducer / soundness / completeness / normalizer / decidable conversion — ALL generic over the table
    (`reduceOnceOverTable`, `normalizeOverTable`, `ConvOverTable.decidableOfStronglyNormalizing`);
  * strong normalization — the ONE bespoke ingredient, here a single `RawTerm.size`-decrease lemma over
    `StepOverTable [univalenceShapedDemoRule]` (the univalence rewrite DROPS the `universeCode` child, so its
    reduct is the redex spine's tail — strictly smaller), fed to the generic
    `wellFounded_of_sizeStrictlyDecreasing`.  SN as DATA on the row.

So this file is the worked instance of the "ship over tables as data" playbook: author/reuse the row,
discharge the `rfl` certificates, supply one size-measure lemma, and turn the generic crank.

## Zero-axiom verification

`StepOverTable.confluent` + the `rfl` certificates; the explicit `StepOverTable.rec` size-decrease (root by
the `firesOn?` head inversion `firesOn?_some_primaryHead` + `RawTermChildren.size_lt_childCons_tail`,
congruence by core `Nat` arithmetic); `wellFounded_of_sizeStrictlyDecreasing`;
`ConvOverTable.decidableOfStronglyNormalizing`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-- The definitional-univalence rule as a SINGLETON table — the table-native form of the row. -/
abbrev univalenceTable : List IotaRuleDesc := [univalenceShapedDemoRule]

/-- The singleton univalence table is well-formed-orthogonal: a one-row table trivially passes all four
decidable `WfIotaTable` checks by `rfl`. -/
theorem univalenceTable_isWf : WfIotaTable univalenceTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- Every row of the singleton table is scope-uniform — the one row, via the shipped
`univalenceShapedDemoRule_isScopeUniform`. -/
theorem univalenceTable_isScopeUniform :
    ∀ rule, rule ∈ univalenceTable → rule.IsScopeUniform := by
  intro rule isRow
  cases isRow with
  | head => exact univalenceShapedDemoRule_isScopeUniform
  | tail _ emptyMem => cases emptyMem

/-- **The singleton univalence table is confluent** — generic orthogonal-table confluence
(`StepOverTable.confluent`) from the two `rfl`/shipped certificates, ZERO bespoke critical-pair work. -/
theorem univalenceTable_isConfluent {scope : Nat} :
    Confluent (fun source target : RawTerm scope => StepOverTable univalenceTable source target) :=
  StepOverTable.confluent univalenceTable_isWf univalenceTable_isScopeUniform

/-- **The root firing strictly decreases `RawTerm.size`.**  A `univalenceShapedDemoRule` firing rewrites
`idCode(universeCode, A, B)` to `equivCode(A, B)` — the reduct spine is the redex spine with the
`universeCode` head dropped, so it is strictly smaller by `RawTermChildren.size_lt_childCons_tail`.  The
reduct shape is recovered from `fires` by the head inversion `firesOn?_some_primaryHead` (pins the slot-0
head to `gen_universeCode`) followed by the `rfl`-computation of `firesOn?` on the concrete spine. -/
theorem univalenceShapedDemoRule_firingSizeDrop {scope : Nat}
    (elimPayload : Generator.gen_idCode.payload scope)
    {spine : RawTermChildren Generator.gen_idCode.binderShifts scope} {reduct : RawTerm scope}
    (fires : univalenceShapedDemoRule.firesOn? elimPayload spine = some reduct) :
    reduct.size < (RawTerm.mkGen .gen_idCode elimPayload spine).size := by
  match spine, fires with
  | .childCons scrutinee (.childCons lhsCode (.childCons rhsCode .childNil)), fires =>
      match scrutinee, fires with
      | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren, fires =>
          have headIsUniverse : scrutineeGenerator = Generator.gen_universeCode :=
            univalenceShapedDemoRule.firesOn?_some_primaryHead fires rfl rfl
          subst headIsUniverse
          match scrutineeChildren, scrutineePayload, fires with
          | .childNil, (levelExpr, flag), fires =>
              have reductEq : reduct = .mkGen .gen_equivCode ()
                  (.childCons lhsCode (.childCons rhsCode .childNil)) := by
                have firesComputes : univalenceShapedDemoRule.firesOn? elimPayload
                    (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
                      (.childCons lhsCode (.childCons rhsCode .childNil)))
                  = some (.mkGen .gen_equivCode ()
                      (.childCons lhsCode (.childCons rhsCode .childNil))) := rfl
                rw [firesComputes] at fires
                exact (Option.some.inj fires).symm
              subst reductEq
              dsimp only [RawTerm.size]
              exact Nat.add_lt_add_right (RawTermChildren.size_lt_childCons_tail _ _) 1

/-- **★ Every `StepOverTable [univalenceShapedDemoRule]` step strictly decreases `RawTerm.size`.**  Root by
`univalenceShapedDemoRule_firingSizeDrop`; congruence by the structural `RawSize` arithmetic.  Explicit
mutual recursor (propext-clean); the singleton membership collapses the row choice to the one row. -/
theorem stepOverUnivalenceTable_sizeStrictlyDecreases {scope : Nat} {source target : RawTerm scope}
    (step : StepOverTable univalenceTable source target) : target.size < source.size := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      StepOverTable univalenceTable first second → Prop :=
    fun {_} first second _ => second.size < first.size
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      StepOverTableChildren univalenceTable first second → Prop :=
    fun {_} {_} first second _ => second.size < first.size
  exact
    StepOverTable.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_rule} isRow elimPayload {_spine} {_reduct} fires => by
        cases isRow with
        | head => exact univalenceShapedDemoRule_firingSizeDrop elimPayload fires
        | tail _ emptyMem => cases emptyMem)
      (fun {_} _gen _payload {_children} {_children'} _childStep childStepIH => by
        dsimp only [RawTerm.size]
        exact Nat.add_lt_add_right childStepIH 1)
      (fun {_} {_} {_} {_head} {_head'} rest _childStep childStepIH => by
        dsimp only [RawTermChildren.size]
        exact Nat.add_lt_add_right (Nat.add_lt_add_right childStepIH rest.size) 1)
      (fun {_} {_} {_} head {_rest} {_rest'} _restStep restStepIH => by
        dsimp only [RawTermChildren.size]
        exact Nat.add_lt_add_right (Nat.add_lt_add_left restStepIH head.size) 1)
      step

/-- **★ The singleton univalence table is strongly normalizing** — every term is accessible under the
table's reduction successor, by the generic size combinator on the size-decrease above.  RPO-free,
Tait-free: the univalence rule shrinks `RawTerm.size`. -/
theorem univalenceTable_isStronglyNormalizing {scope : Nat} (term : RawTerm scope) :
    Acc (StepOverTable.successorOver univalenceTable) term :=
  (wellFounded_of_sizeStrictlyDecreasing
    (stepRelation := fun {_} source target => StepOverTable univalenceTable source target)
    stepOverUnivalenceTable_sizeStrictlyDecreases).apply term

/-- **★ Definitional-univalence conversion is DECIDABLE BY COMPUTATION — over the table, as data.**  Decide
`a ⟷*_univalence b` by normalizing both over `[univalenceShapedDemoRule]` and comparing.  No bespoke
`reduceStep`, no `univNF`, no bespoke joinability proof: confluence + the size-SN witness feed the generic
`ConvOverTable.decidableOfStronglyNormalizing`. -/
def univalenceTableConv_decidable {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Decidable (ConvOverTable univalenceTable leftTerm rightTerm) :=
  ConvOverTable.decidableOfStronglyNormalizing univalenceTable_isConfluent
    (univalenceTable_isStronglyNormalizing leftTerm)
    (univalenceTable_isStronglyNormalizing rightTerm)

/-- **Honesty marker.**  Univalence decidable Conv is shipped OVER THE TABLE as data: the rule is the
`IotaRuleDesc` row `univalenceShapedDemoRule`, and every stage but SN is the generic `StepOverTable` engine;
SN is the one size-measure lemma.  No bespoke rewrite relation / normalizer / decider.  `= true`. -/
def fxUnivalenceConv_shippedOverTableAsData : Bool := true

end FX1Poly.Core
