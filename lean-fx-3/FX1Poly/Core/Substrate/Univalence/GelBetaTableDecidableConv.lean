import FX1Poly.Core.Rewriting.Confluence.DefUnivConfluence
import FX1Poly.Core.Rewriting.RuleTables.Tables.TableNormalize
import FX1Poly.Core.Metatheory.Normalization.IotaSN.SizeCompatClosureSN

/-! # FX1Poly/Core/Substrate/Univalence/GelBetaTableDecidableConv
    — TRANSPENSION (gel-β) shipped OVER THE TABLE AS DATA, with decidable conversion by computation

This is the transpension half of "ship univalence + transpension over tables as data".  Transpension at the
affine multiplier IS the relational `gen_gel` former (internal parametricity, Bernardy-Coquand-Moulin /
Cavallo-Harper); its β-rule — the relation-witness projection

    `ungel(gel a b r) ↝ r`

— is the shipped `IotaRuleDesc` row `gelBetaIotaRow` (`elimGenerator := gen_ungel`, scrutinee `gen_gel`,
`target := scrutineeChildAt 0 2`).  The reduct `r` is the matched `gel` cell's third child, a pure
scrutinee-child projection at shift 0 — the `fst`/`snd` shape — so it is SIZE-SHRINKING (the reduct is a
strict subterm of the redex), exactly like the size-shrinking univalence row.  This file reads its decision
procedure straight off the GENERIC `StepOverTable` engine at the singleton table `[gelBetaIotaRow]`:

  * `WfIotaTable` (four `rfl` checks on a singleton) + scope-uniformity (constant target, non-`var` heads);
  * confluence — `StepOverTable.confluent`;
  * the reducer / normalizer / decidable conversion — all generic
    (`ConvOverTable.decidableOfStronglyNormalizing`);
  * strong normalization — the ONE bespoke-as-data ingredient: a `RawTerm.size`-decrease lemma over
    `StepOverTable [gelBetaIotaRow]` (the projection drops the `ungel` + `gel` wrappers and two siblings, so
    the witness is strictly smaller), fed to the generic `wellFounded_of_sizeStrictlyDecreasing`.

Note on scope: this ships the SHIPPED simple gel-β (`ungel(gel a b r) ↝ r`, scrutinee `gen_gel` directly).
The fuller dimension-abstracted boundary form (`ungel(pathLam(gel a b r)) ↝ r`), whose reduct must strengthen
out the fresh interval binder, needs the affine/fresh-substitution `ReductTemplate` node (TRANSP-DSL) and is
a separate row — not required here, because the witness already lives at the redex scope.

## Zero-axiom verification

`StepOverTable.confluent` + the `rfl` certificates; the explicit `StepOverTable.rec` size-decrease (root by
the `firesOn?` head inversion `firesOn?_some_primaryHead` + a `RawTermChildren.size_lt_childCons_*` /
`Nat.lt_succ_self` transitivity chain, congruence by core `Nat` arithmetic);
`wellFounded_of_sizeStrictlyDecreasing`; `ConvOverTable.decidableOfStronglyNormalizing`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-- The transpension gel-β rule as a SINGLETON table — the relation-witness projection as data. -/
abbrev gelBetaTable : List IotaRuleDesc := [gelBetaIotaRow]

/-- The singleton gel-β table is well-formed-orthogonal: one row, all four decidable `WfIotaTable` checks
`rfl`. -/
theorem gelBetaTable_isWf : WfIotaTable gelBetaTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- Every row of the singleton gel-β table is scope-uniform — the one row, via the shipped
`gelBetaIotaRow_isScopeUniform` (IotaTableEquivarianceSubstrate). -/
theorem gelBetaTable_isScopeUniform :
    ∀ rule, rule ∈ gelBetaTable → rule.IsScopeUniform := by
  intro rule isRow
  cases isRow with
  | head => exact gelBetaIotaRow_isScopeUniform
  | tail _ emptyMem => cases emptyMem

/-- **The singleton gel-β table is confluent** — generic orthogonal-table confluence. -/
theorem gelBetaTable_isConfluent {scope : Nat} :
    Confluent (fun source target : RawTerm scope => StepOverTable gelBetaTable source target) :=
  StepOverTable.confluent gelBetaTable_isWf gelBetaTable_isScopeUniform

/-- **The root firing strictly decreases `RawTerm.size`.**  `ungel(gel a b r) ↝ r` projects the matched
`gel` cell's witness child, dropping the `ungel` head, the `gel` head, and the `a`, `b` siblings — so the
witness is strictly smaller.  The reduct shape is recovered from `fires` by the head inversion
`firesOn?_some_primaryHead` (pins the slot-0 head to `gen_gel`) then the `rfl`-computation of `firesOn?`; the
size drop is a `RawTermChildren.size_lt_childCons_*` / `Nat.lt_succ_self` transitivity chain through the two
nesting levels. -/
theorem gelBetaIotaRow_firingSizeDrop {scope : Nat}
    (elimPayload : Generator.gen_ungel.payload scope)
    {spine : RawTermChildren Generator.gen_ungel.binderShifts scope} {reduct : RawTerm scope}
    (fires : gelBetaIotaRow.firesOn? elimPayload spine = some reduct) :
    reduct.size < (RawTerm.mkGen .gen_ungel elimPayload spine).size := by
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
              calc witness.size
                  < (RawTermChildren.childCons witness RawTermChildren.childNil).size :=
                      RawTermChildren.size_lt_childCons_head witness _
                _ < (RawTermChildren.childCons rightComponent
                      (RawTermChildren.childCons witness RawTermChildren.childNil)).size :=
                      RawTermChildren.size_lt_childCons_tail rightComponent _
                _ < (RawTermChildren.childCons leftComponent
                      (RawTermChildren.childCons rightComponent
                        (RawTermChildren.childCons witness RawTermChildren.childNil))).size :=
                      RawTermChildren.size_lt_childCons_tail leftComponent _
                _ < (RawTerm.mkGen .gen_gel scrutineePayload
                      (RawTermChildren.childCons leftComponent
                        (RawTermChildren.childCons rightComponent
                          (RawTermChildren.childCons witness RawTermChildren.childNil)))).size :=
                      Nat.lt_succ_self _
                _ < (RawTermChildren.childCons
                      (RawTerm.mkGen .gen_gel scrutineePayload
                        (RawTermChildren.childCons leftComponent
                          (RawTermChildren.childCons rightComponent
                            (RawTermChildren.childCons witness RawTermChildren.childNil))))
                      RawTermChildren.childNil).size :=
                      RawTermChildren.size_lt_childCons_head _ _
                _ < (RawTerm.mkGen .gen_ungel elimPayload
                      (RawTermChildren.childCons
                        (RawTerm.mkGen .gen_gel scrutineePayload
                          (RawTermChildren.childCons leftComponent
                            (RawTermChildren.childCons rightComponent
                              (RawTermChildren.childCons witness RawTermChildren.childNil))))
                        RawTermChildren.childNil)).size :=
                      Nat.lt_succ_self _

/-- **★ Every `StepOverTable [gelBetaIotaRow]` step strictly decreases `RawTerm.size`.**  Root by
`gelBetaIotaRow_firingSizeDrop`; congruence by the additive `RawSize` arithmetic.  Explicit mutual recursor;
the singleton membership collapses the row choice to the one row. -/
theorem stepOverGelBetaTable_sizeStrictlyDecreases {scope : Nat} {source target : RawTerm scope}
    (step : StepOverTable gelBetaTable source target) : target.size < source.size := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      StepOverTable gelBetaTable first second → Prop :=
    fun {_} first second _ => second.size < first.size
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      StepOverTableChildren gelBetaTable first second → Prop :=
    fun {_} {_} first second _ => second.size < first.size
  exact
    StepOverTable.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_rule} isRow elimPayload {_spine} {_reduct} fires => by
        cases isRow with
        | head => exact gelBetaIotaRow_firingSizeDrop elimPayload fires
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

/-- **★ The singleton gel-β table is strongly normalizing** — every term is accessible under the table's
reduction successor, by the generic size combinator on the size-decrease above. -/
theorem gelBetaTable_isStronglyNormalizing {scope : Nat} (term : RawTerm scope) :
    Acc (StepOverTable.successorOver gelBetaTable) term :=
  (wellFounded_of_sizeStrictlyDecreasing
    (stepRelation := fun {_} source target => StepOverTable gelBetaTable source target)
    stepOverGelBetaTable_sizeStrictlyDecreases).apply term

/-- **★ Transpension gel-β conversion is DECIDABLE BY COMPUTATION — over the table, as data.**  Decide
`a ⟷*_gel-β b` by normalizing both over `[gelBetaIotaRow]` and comparing.  No bespoke reducer / joinability
proof: confluence + the size-SN witness feed the generic `ConvOverTable.decidableOfStronglyNormalizing`. -/
def gelBetaTableConv_decidable {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Decidable (ConvOverTable gelBetaTable leftTerm rightTerm) :=
  ConvOverTable.decidableOfStronglyNormalizing gelBetaTable_isConfluent
    (gelBetaTable_isStronglyNormalizing leftTerm)
    (gelBetaTable_isStronglyNormalizing rightTerm)

/-- **Honesty marker.**  Transpension (gel-β, transpension-at-affine = the relational universe) decidable
Conv is shipped OVER THE TABLE as data: the rule is the `IotaRuleDesc` row `gelBetaIotaRow`, every stage but
SN is the generic `StepOverTable` engine, SN is the one size-measure lemma.  `= true`. -/
def fxTranspensionGelBetaConv_shippedOverTableAsData : Bool := true

end FX1Poly.Core
