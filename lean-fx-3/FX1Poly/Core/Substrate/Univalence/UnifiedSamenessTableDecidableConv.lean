import FX1Poly.Core.Substrate.Univalence.UnifiedDefinitionalTableDecidableConv
import FX1Poly.Core.Substrate.Univalence.GelBetaTableDecidableConv

/-! # FX1Poly/Core/Substrate/Univalence/UnifiedSamenessTableDecidableConv
    — the FULL definitional-sameness fragment (univalence + transport + transpension) OVER ONE TABLE

The grand capstone of "ship univalence + transpension over tables as data": the three orthogonal
definitional-sameness rules — the size-shrinking univalence row, the size-growing transport row, and the
transpension gel-β row — unified as ONE three-row table

    `[univalenceShapedDemoRule, sizeGrowingTransportDemoRule, gelBetaIotaRow]`

with decidable conversion read off the generic `StepOverTable` engine.  The three eliminator heads
(`gen_idCode`, `gen_glueElim`, `gen_ungel`) are pairwise DISJOINT and disjoint from every scrutinee head, so
the table is orthogonal — zero critical pairs — and confluence is `StepOverTable.confluent` from a `rfl`
`WfIotaTable`.  This is the concrete object behind OP3-SAMENESS: univalence and parametricity (transpension)
are decided by ONE computation.

JOINT strong normalization is again `lex(productFormerCount, size)`: univalence preserves the product-former
count while dropping size; transport drops the product-former count; and gel-β (a subterm projection) always
drops size while NEVER increasing the product-former count — so it lands in whichever lex branch holds (drop
the count, or tie it and drop size).  The new ingredient is `gelBetaIotaRow_firingProductFormerLe` (the
witness is a subterm, so its product-former count is ≤ the redex's); everything else is reused.

## Zero-axiom verification

`StepOverTable.confluent` + the `rfl` certificates; the `StepOverTable.rec` per-step lexicographic decrease
(root by the three rows' firing facts under a three-way singleton-membership split, gel-β combining its `≤`
product-former bound with its strict size drop via `Nat.lt_of_le_of_ne`; congruence by additive `Nat`
arithmetic); `wellFounded_of_lexMeasureStrictlyDecreasing`; `ConvOverTable.decidableOfStronglyNormalizing`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-- **The gel-β firing does NOT increase the product-former count.**  `ungel(gel a b r) ↝ r` projects the
witness `r`, a subterm of the redex, so its `gen_productCode` count is bounded by the redex's (the `a`, `b`
siblings only ADD product-formers).  The `≤` companion of `gelBetaIotaRow_firingSizeDrop`; lets gel-β join
the lexicographic joint SN. -/
theorem gelBetaIotaRow_firingProductFormerLe {scope : Nat}
    (elimPayload : Generator.gen_ungel.payload scope)
    {spine : RawTermChildren Generator.gen_ungel.binderShifts scope} {reduct : RawTerm scope}
    (fires : gelBetaIotaRow.firesOn? elimPayload spine = some reduct) :
    reduct.productFormerCount ≤ (RawTerm.mkGen .gen_ungel elimPayload spine).productFormerCount := by
  match spine, fires with
  | .childCons scrutinee .childNil, fires =>
      match scrutinee, fires with
      | .mkGen scrutineeGenerator scrutineePayload scrutineeChildren, fires =>
          have headIsGel : scrutineeGenerator = Generator.gen_gel :=
            gelBetaIotaRow.firesOn?_some_primaryHead fires rfl rfl
          subst headIsGel
          match scrutineeChildren, fires with
          | .childCons leftComponent (.childCons rightComponent (.childCons witness .childNil)), fires =>
              have reductEq : reduct = witness := by
                have firesComputes : gelBetaIotaRow.firesOn? elimPayload
                    (.childCons (.mkGen .gen_gel scrutineePayload
                      (.childCons leftComponent (.childCons rightComponent
                        (.childCons witness .childNil)))) .childNil)
                  = some witness := rfl
                rw [firesComputes] at fires
                exact (Option.some.inj fires).symm
              rw [reductEq]
              dsimp only [RawTerm.productFormerCount, RawTermChildren.productFormerCount]
              exact Nat.le_trans
                (Nat.le_add_left witness.productFormerCount rightComponent.productFormerCount)
                (Nat.le_add_left _ leftComponent.productFormerCount)

/-- The full definitional-sameness rewrite system as ONE table: univalence (size-shrinking) + transport
(size-growing) + transpension gel-β (subterm projection). -/
abbrev unifiedSamenessTable : List IotaRuleDesc :=
  [univalenceShapedDemoRule, sizeGrowingTransportDemoRule, gelBetaIotaRow]

/-- The three-row sameness table is well-formed-orthogonal: pairwise-disjoint eliminator heads
(`gen_idCode`, `gen_glueElim`, `gen_ungel`) and disjoint scrutinee heads make all four decidable
`WfIotaTable` checks `rfl`. -/
theorem unifiedSamenessTable_isWf : WfIotaTable unifiedSamenessTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- All three rows of the sameness table are scope-uniform — the three shipped certificates. -/
theorem unifiedSamenessTable_isScopeUniform :
    ∀ rule, rule ∈ unifiedSamenessTable → rule.IsScopeUniform := by
  intro rule isRow
  cases isRow with
  | head => exact univalenceShapedDemoRule_isScopeUniform
  | tail _ rest1 =>
      cases rest1 with
      | head => exact sizeGrowingTransportDemoRule_isScopeUniform
      | tail _ rest2 =>
          cases rest2 with
          | head => exact gelBetaIotaRow_isScopeUniform
          | tail _ emptyMem => cases emptyMem

/-- **The three-row sameness table is confluent** — generic orthogonal-table confluence: pairwise-disjoint
heads give zero critical pairs. -/
theorem unifiedSamenessTable_isConfluent {scope : Nat} :
    Confluent (fun source target : RawTerm scope =>
      StepOverTable unifiedSamenessTable source target) :=
  StepOverTable.confluent unifiedSamenessTable_isWf unifiedSamenessTable_isScopeUniform

/-- **★ Every sameness-table step strictly decreases `lex(productFormerCount, size)`.**  Root: univalence
preserves the former count and drops size; transport drops the former count; gel-β never raises the former
count and always drops size, so it lands in whichever lex branch the count comparison gives.  Congruence:
both measures are additive over the spine, so a child's lex decrease lifts.  Explicit mutual recursor;
three-way membership split selects the firing fact; core `Nat` arithmetic. -/
theorem stepOverSamenessTable_decreasesLex {scope : Nat} {source target : RawTerm scope}
    (step : StepOverTable unifiedSamenessTable source target) :
    target.productFormerCount < source.productFormerCount
    ∨ (target.productFormerCount = source.productFormerCount ∧ target.size < source.size) := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      StepOverTable unifiedSamenessTable first second → Prop :=
    fun {_} first second _ =>
      second.productFormerCount < first.productFormerCount
      ∨ (second.productFormerCount = first.productFormerCount ∧ second.size < first.size)
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      StepOverTableChildren unifiedSamenessTable first second → Prop :=
    fun {_} {_} first second _ =>
      second.productFormerCount < first.productFormerCount
      ∨ (second.productFormerCount = first.productFormerCount ∧ second.size < first.size)
  exact
    StepOverTable.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_rule} isRow elimPayload {spine} {reduct} fires => by
        cases isRow with
        | head =>
            exact Or.inr
              ⟨univalenceShapedDemoRule_firingPreservesProductFormerCount elimPayload fires,
                univalenceShapedDemoRule_firingSizeDrop elimPayload fires⟩
        | tail _ rest1 =>
            cases rest1 with
            | head =>
                exact Or.inl (sizeGrowingTransportDemoRule_firingProductFormerDrop elimPayload fires)
            | tail _ rest2 =>
                cases rest2 with
                | head =>
                    exact
                      (if formerEq :
                          reduct.productFormerCount
                            = (RawTerm.mkGen .gen_ungel elimPayload spine).productFormerCount then
                        Or.inr ⟨formerEq, gelBetaIotaRow_firingSizeDrop elimPayload fires⟩
                      else
                        Or.inl (Nat.lt_of_le_of_ne
                          (gelBetaIotaRow_firingProductFormerLe elimPayload fires) formerEq))
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

/-- **★ The three-row sameness table is strongly normalizing — across the size axis.**  Every term is
accessible under the table's reduction successor, by the generic lexicographic combinator at
`lex(productFormerCount, size)`.  Univalence, transport, AND transpension gel-β all decrease this measure. -/
theorem unifiedSamenessTable_isStronglyNormalizing {scope : Nat} (term : RawTerm scope) :
    Acc (StepOverTable.successorOver unifiedSamenessTable) term :=
  (wellFounded_of_lexMeasureStrictlyDecreasing (primaryMeasure := RawTerm.productFormerCount)
    (stepRelation := fun {_} source target => StepOverTable unifiedSamenessTable source target)
    stepOverSamenessTable_decreasesLex).apply term

/-- **★ The FULL definitional-sameness fragment has DECIDABLE conversion BY COMPUTATION — univalence,
transport, AND transpension, over ONE table, as data.**  Decide `a ⟷*_sameness b` by normalizing both over
`[univalenceShapedDemoRule, sizeGrowingTransportDemoRule, gelBetaIotaRow]` and comparing.  Orthogonal
confluence + the lexicographic joint-SN witness feed the generic
`ConvOverTable.decidableOfStronglyNormalizing`.  The concrete object behind OP3-SAMENESS: univalence and
parametricity are one decided computation. -/
def unifiedSamenessTableConv_decidable {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Decidable (ConvOverTable unifiedSamenessTable leftTerm rightTerm) :=
  ConvOverTable.decidableOfStronglyNormalizing unifiedSamenessTable_isConfluent
    (unifiedSamenessTable_isStronglyNormalizing leftTerm)
    (unifiedSamenessTable_isStronglyNormalizing rightTerm)

/-- **Honesty marker.**  The full definitional-sameness fragment — univalence (size-shrinking) + transport
(size-growing) + transpension gel-β (subterm projection) — ships over ONE table as data, jointly strongly
normalizing across the size axis by `lex(productFormerCount, size)`, with decidable conversion off the
generic engine.  No bespoke machinery for any of the three.  `= true`. -/
def fxUnifiedSamenessConv_shippedOverOneTableAsData : Bool := true

end FX1Poly.Core
