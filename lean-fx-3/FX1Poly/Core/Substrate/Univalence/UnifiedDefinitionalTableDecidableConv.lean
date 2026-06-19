import FX1Poly.Core.Substrate.Univalence.UnivalenceTableDecidableConv
import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportTableDecidableConv
import FX1Poly.Core.Substrate.Univalence.LexJointRowSN

/-! # FX1Poly/Core/Substrate/Univalence/UnifiedDefinitionalTableDecidableConv
    — the FULL definitional-univalence rewrite system, both rules, OVER ONE TABLE, with decidable Conv

The capstone of "ship definitional univalence over tables as data": the table-native replacement for the
bespoke `UnifiedDefinitionalRowConfluence`.  `UnivalenceTableDecidableConv` shipped the size-SHRINKING
univalence row and `SizeGrowingTransportTableDecidableConv` the size-GROWING transport row, each at its own
singleton table.  This file ships their UNION as the two-row table

    `[univalenceShapedDemoRule, sizeGrowingTransportDemoRule]`

and reads the whole system's decision procedure off the generic `StepOverTable` engine.  The two rows have
DISJOINT eliminator heads (`gen_idCode` vs `gen_glueElim`) and disjoint scrutinee heads, so the table is
orthogonal — zero critical pairs — and confluence is again `StepOverTable.confluent` from a `rfl`
`WfIotaTable` plus the two shipped scope-uniformity certificates.

The interesting ingredient is JOINT strong normalization ACROSS THE SIZE AXIS: one rule shrinks the term,
the other grows it, so neither `RawTerm.size` alone nor `RawTerm.productFormerCount` alone is a measure for
the union.  The lexicographic measure `lex(productFormerCount, size)` is — because univalence PRESERVES the
product-former count while dropping size (second lex component) and transport drops the product-former count
(first lex component).  Both components are additive sums over children, so a child's lex decrease lifts to
the parent.  The generic combinator `wellFounded_of_lexMeasureStrictlyDecreasing` turns the per-step lex
decrease into well-foundedness; the generic `ConvOverTable.decidableOfStronglyNormalizing` then decides
conversion over the union by normalization.

The one new firing fact is `univalenceShapedDemoRule_firingPreservesProductFormerCount` (the table twin of
the bespoke `UnivalenceRowStep.preservesProductFormerCount`); the per-row size-drop / former-drop firings
are reused from the two singleton-table files.

## Zero-axiom verification

`StepOverTable.confluent` + the `rfl` certificates; the `StepOverTable.rec` per-step lex decrease (root by
the two firing facts under a singleton-membership row split, congruence by additive `Nat` arithmetic with an
`Or` split on the child's lex disjunction); `wellFounded_of_lexMeasureStrictlyDecreasing`;
`ConvOverTable.decidableOfStronglyNormalizing`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-- **The univalence firing PRESERVES the product-former count.**  `idCode(universeCode, A, B) ↝
equivCode(A, B)` touches only `idCode` / `equivCode` / `universeCode` — never `productCode` — and reuses
`A`, `B`, so the `gen_productCode` count is unchanged (the `universeCode` child contributes a leading `0`,
cleared by `Nat.zero_add`).  The table twin of the bespoke `UnivalenceRowStep.preservesProductFormerCount`;
the load-bearing compatibility fact that lets the lexicographic joint SN compose. -/
theorem univalenceShapedDemoRule_firingPreservesProductFormerCount {scope : Nat}
    (elimPayload : Generator.gen_idCode.payload scope)
    {spine : RawTermChildren Generator.gen_idCode.binderShifts scope} {reduct : RawTerm scope}
    (fires : univalenceShapedDemoRule.firesOn? elimPayload spine = some reduct) :
    reduct.productFormerCount = (RawTerm.mkGen .gen_idCode elimPayload spine).productFormerCount := by
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
              exact (Nat.zero_add _).symm

/-- The full definitional-univalence rewrite system as ONE table: the size-shrinking univalence row and the
size-growing transport row together. -/
abbrev unifiedDefinitionalTable : List IotaRuleDesc :=
  [univalenceShapedDemoRule, sizeGrowingTransportDemoRule]

/-- The two-row table is well-formed-orthogonal: disjoint eliminator heads (`gen_idCode`, `gen_glueElim`)
and disjoint scrutinee heads make all four decidable `WfIotaTable` checks `rfl`. -/
theorem unifiedDefinitionalTable_isWf : WfIotaTable unifiedDefinitionalTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- Both rows of the union are scope-uniform — the two shipped certificates. -/
theorem unifiedDefinitionalTable_isScopeUniform :
    ∀ rule, rule ∈ unifiedDefinitionalTable → rule.IsScopeUniform := by
  intro rule isRow
  cases isRow with
  | head => exact univalenceShapedDemoRule_isScopeUniform
  | tail _ restMem =>
      cases restMem with
      | head => exact sizeGrowingTransportDemoRule_isScopeUniform
      | tail _ emptyMem => cases emptyMem

/-- **The two-row definitional-univalence table is confluent** — generic orthogonal-table confluence: the
disjoint heads give zero critical pairs. -/
theorem unifiedDefinitionalTable_isConfluent {scope : Nat} :
    Confluent (fun source target : RawTerm scope =>
      StepOverTable unifiedDefinitionalTable source target) :=
  StepOverTable.confluent unifiedDefinitionalTable_isWf unifiedDefinitionalTable_isScopeUniform

/-- **★ Every union step strictly decreases `lex(productFormerCount, size)`.**  Root: a univalence firing
preserves the product-former count and drops size (second lex component); a transport firing drops the
product-former count (first lex component).  Congruence: both measures are additive sums over the spine, so
a child's lex decrease lifts to the parent under either branch of the disjunction.  Explicit mutual
recursor; the two-row membership split selects the firing fact; core `Nat` arithmetic. -/
theorem stepOverUnifiedTable_decreasesLex {scope : Nat} {source target : RawTerm scope}
    (step : StepOverTable unifiedDefinitionalTable source target) :
    target.productFormerCount < source.productFormerCount
    ∨ (target.productFormerCount = source.productFormerCount ∧ target.size < source.size) := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      StepOverTable unifiedDefinitionalTable first second → Prop :=
    fun {_} first second _ =>
      second.productFormerCount < first.productFormerCount
      ∨ (second.productFormerCount = first.productFormerCount ∧ second.size < first.size)
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      StepOverTableChildren unifiedDefinitionalTable first second → Prop :=
    fun {_} {_} first second _ =>
      second.productFormerCount < first.productFormerCount
      ∨ (second.productFormerCount = first.productFormerCount ∧ second.size < first.size)
  exact
    StepOverTable.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_rule} isRow elimPayload {_spine} {_reduct} fires => by
        cases isRow with
        | head =>
            exact Or.inr
              ⟨univalenceShapedDemoRule_firingPreservesProductFormerCount elimPayload fires,
                univalenceShapedDemoRule_firingSizeDrop elimPayload fires⟩
        | tail _ restMem =>
            cases restMem with
            | head =>
                exact Or.inl (sizeGrowingTransportDemoRule_firingProductFormerDrop elimPayload fires)
            | tail _ emptyMem => cases emptyMem)
      (fun {_} _gen _payload {_children} {_children'} _childStep childStepIH => by
        dsimp only [RawTerm.productFormerCount, RawTerm.size]
        match childStepIH with
        | Or.inl formerLt => exact Or.inl (Nat.add_lt_add_right formerLt _)
        | Or.inr ⟨formerEq, sizeLt⟩ =>
            exact Or.inr ⟨congrArg (· + _) formerEq, Nat.add_lt_add_right sizeLt 1⟩)
      (fun {_} {_} {_} {_head} {_head'} rest _childStep childStepIH => by
        dsimp only [RawTermChildren.productFormerCount, RawTermChildren.size]
        match childStepIH with
        | Or.inl formerLt =>
            exact Or.inl (Nat.add_lt_add_right formerLt rest.productFormerCount)
        | Or.inr ⟨formerEq, sizeLt⟩ =>
            exact Or.inr ⟨congrArg (· + rest.productFormerCount) formerEq,
              Nat.add_lt_add_right (Nat.add_lt_add_right sizeLt rest.size) 1⟩)
      (fun {_} {_} {_} head {_rest} {_rest'} _restStep restStepIH => by
        dsimp only [RawTermChildren.productFormerCount, RawTermChildren.size]
        match restStepIH with
        | Or.inl formerLt =>
            exact Or.inl (Nat.add_lt_add_left formerLt head.productFormerCount)
        | Or.inr ⟨formerEq, sizeLt⟩ =>
            exact Or.inr ⟨congrArg (head.productFormerCount + ·) formerEq,
              Nat.add_lt_add_right (Nat.add_lt_add_left sizeLt head.size) 1⟩)
      step

/-- **★ The two-row definitional-univalence table is strongly normalizing — across the size axis.**  Every
term is accessible under the table's reduction successor, by the generic lexicographic combinator at
`lex(productFormerCount, size)`.  Neither single measure works (one rule grows the term, the other
shrinks it); the lex measure does, because univalence preserves the product-former count.  The first
table-native joint SN spanning BOTH directions of the size axis. -/
theorem unifiedDefinitionalTable_isStronglyNormalizing {scope : Nat} (term : RawTerm scope) :
    Acc (StepOverTable.successorOver unifiedDefinitionalTable) term :=
  (wellFounded_of_lexMeasureStrictlyDecreasing (primaryMeasure := RawTerm.productFormerCount)
    (stepRelation := fun {_} source target => StepOverTable unifiedDefinitionalTable source target)
    stepOverUnifiedTable_decreasesLex).apply term

/-- **★ The FULL definitional-univalence rewrite system has DECIDABLE conversion BY COMPUTATION — both rules,
over one table, as data.**  Decide `a ⟷*_definitional-univalence b` by normalizing both over
`[univalenceShapedDemoRule, sizeGrowingTransportDemoRule]` and comparing.  No bespoke union `reduceStep`, no
bespoke joinability: orthogonal confluence + the lexicographic joint-SN witness feed the generic
`ConvOverTable.decidableOfStronglyNormalizing`.  The table-native form of the bespoke
`UnifiedDefinitionalRowConfluence` capstone. -/
def unifiedDefinitionalTableConv_decidable {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Decidable (ConvOverTable unifiedDefinitionalTable leftTerm rightTerm) :=
  ConvOverTable.decidableOfStronglyNormalizing unifiedDefinitionalTable_isConfluent
    (unifiedDefinitionalTable_isStronglyNormalizing leftTerm)
    (unifiedDefinitionalTable_isStronglyNormalizing rightTerm)

/-- **Honesty marker.**  The full definitional-univalence system — a size-shrinking AND a size-growing rule
— ships over ONE table as data, jointly strongly normalizing across the size axis by the lexicographic
type-complexity measure, with decidable conversion off the generic engine.  No bespoke union machinery.
`= true`. -/
def fxUnifiedDefinitionalConv_shippedOverOneTableAsData : Bool := true

end FX1Poly.Core
