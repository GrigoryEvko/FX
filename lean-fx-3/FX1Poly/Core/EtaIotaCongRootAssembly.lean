import FX1Poly.Core.EtaIotaScrutineeDichotomy
import FX1Poly.Core.EtaIotaRootCommutation

/-! # EtaIotaCongRootAssembly — ETA-T5 increment 4.4c: cong-eta before
a root iota firing reorders (or exhibits the duality)

The second quadrant of the quasi-commutation: an eta step INSIDE the
eliminator spine followed by the row firing at the root.  The
scrutinee dichotomy either arms the backward-firing brick — the row
fires on the PRE-eta spine and the source reduct eta-stars to the
target reduct (definedness + forward stability), giving one fronted
iota step and a right-only union star — or it surfaces the
`HasEtaDualityAt` witness (an eta redex sitting at a scrutinee slot,
head-matching the pattern), which is dispatched per intro/elim row
pair downstream and escapes here as the explicit second disjunct.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaCongRootAssembly.lean`. -/

namespace FX1Poly.Core

/-! ## Union-star bricks -/

/-- Prepend a right step to a union star (mirror of
`UnionStar.headLeft`). -/
theorem UnionStar.headRight {Alpha : Type}
    {reduceLeft reduceRight : Alpha → Alpha → Prop} {a b c : Alpha}
    (firstStep : reduceRight a b)
    (restStar : UnionStar reduceLeft reduceRight b c) :
    UnionStar reduceLeft reduceRight a c := by
  induction restStar with
  | refl => exact .tailRight (.refl _) firstStep
  | tailLeft _ stepToReduct ih => exact .tailLeft ih stepToReduct
  | tailRight _ stepToReduct ih => exact .tailRight ih stepToReduct

/-- An eta star embeds into the union star as right-only steps,
against ANY left relation. -/
theorem StepEtaOverTableStar.toUnionStarRight
    {etaTable : List EtaRuleDesc} {scope : Nat}
    {source target : RawTerm scope}
    (etaStar : StepEtaOverTableStar etaTable source target)
    (reduceLeft : RawTerm scope → RawTerm scope → Prop) :
    UnionStar reduceLeft (StepEtaOverTable etaTable) source target := by
  induction etaStar with
  | refl term => exact .refl term
  | head firstStep _restStar ih => exact UnionStar.headRight firstStep ih

/-! ## The assembly -/

/-- ★ **Cong-eta quasi-commutes over a root iota firing** (or exhibits
the duality): if the eliminator spine takes one table-eta step and the
row then fires on the post-eta spine, then EITHER the row already
fires on the pre-eta spine — one fronted iota step whose reduct
eta-stars (right-only union star) to the original target — OR some
declared scrutinee slot of the pre-eta spine holds an eta redex
contracting to the fired cell, the per-pair duality dispatched
downstream. -/
theorem congEtaQuasiCommutesOverRootIota
    {iotaTable : List IotaRuleDesc} {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} {rule : IotaRuleDesc} (isRow : rule ∈ iotaTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineStep : StepEtaOverTableChildren etaTable spine spine')
    {target : RawTerm scope}
    (fires' : rule.firesOn? elimPayload spine' = some target) :
    (∃ commonReduct : RawTerm scope,
      StepOverTable iotaTable
        (.mkGen rule.elimGenerator elimPayload spine) commonReduct
      ∧ UnionStar (StepOverTable iotaTable (scope := scope))
          (StepEtaOverTable etaTable) commonReduct target)
    ∨ rule.HasEtaDualityAt etaTable spine spine' := by
  have spinePointwise := EtaChildrenPointwise.ofChildrenStep spineStep
  have allFire' := rule.firesOn?_some_scrutineesFire fires'
  cases rule.scrutineePattern_etaDichotomy spinePointwise allFire' with
  | inr duality => exact Or.inr duality
  | inl goodCase =>
      obtain ⟨allFire, cellsRelated⟩ := goodCase
      have spineStarRelated :=
        EtaChildrenPointwiseStar.ofChildrenStep spineStep
      obtain ⟨commonReduct, fires, reductStar⟩ :=
        rule.firesOn?_etaReflected rowsAreScopeSafe elimPayload
          spineStarRelated allFire cellsRelated fires'
      exact Or.inl ⟨commonReduct,
        .tableRedex isRow elimPayload fires,
        reductStar.toUnionStarRight (StepOverTable iotaTable)⟩

end FX1Poly.Core
