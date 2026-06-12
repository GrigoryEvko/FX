import FX1Poly.Core.StepTable
import FX1Poly.Core.IotaTableOrthogonality
import FX1Poly.Typed.GenElimIotaComputation
import FX1Poly.Typed.HasTypeDescGeneralElim
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/IotaElimTypedLink — IOTA-T7: pairing the ι table with the elim typing tables

One semantic unit = one OPERATIONAL row (`IotaRuleDesc`, the ι table)
+ one STATIC row (the elimination typing tables) + the SR proof linking
them.  This file ships the pairing and the generic typed table-redex
subject reduction:

  * **Row filters + pins** — `iotaRowsAtElim` (the ι rows headed by a
    generator) with the canonical pins: `gen_app` carries exactly β,
    `gen_pathApp` exactly endpoint-β.  `iotaRowAtAppIsBeta` /
    `iotaRowAtPathAppIsPathBeta` are the dispatch bricks every typed
    consumer routes through instead of a per-row split.
  * **Decidable coherence gates** — the static↔operational agreement,
    re-decided when any table grows: every ι row whose eliminator
    carries a typing row scrutinizes a TYPED INTRODUCER at slot 0
    (`typedElimIotaRowsCohere` for the GTL-17 table,
    `gradedElimIotaRowsCohere` for the v2 two-row table — the
    elim/intro tables and the ι table name the same generators in the
    same slots).
  * ★ **The generic typed table-redex SR**
    (`HasTypeDescPi.tableRedexSubjectReduction`): a TYPED cell on which
    a TABLE ROW FIRES has its reduct typed at the same classifier —
    quantified over the ι row and the elim typing row, the ONE table
    arm that replaces the per-iota typed-SR family.  Today the typed
    eliminator table is `{gen_app}`, so the dispatch lands on β and the
    engine is the unconditional master SR (whose β arm is the
    substitution lemma); a new typed eliminator extends the dispatch by
    one case, never a new theorem shape.
  * **The legacy-table master SR** — the full master subject reduction
    restated over `StepOverTable legacyIotaRuleTable` (one-liners via
    the IOTA-T1 adequacy), the migration seam the IOTA-T9 flip's typed
    consumers move through.

## Zero-axiom verification

Hand-rolled list filter with `rfl` pins, the established membership
dispatch (18 `cases` with `Generator.noConfusion` on concrete head
equations), Bool coherence gates closing by `rfl`, and composition of
shipped theorems (`betaRowFiringToStep`, the master
`HasTypeDescPi.subjectReduction`, `stepOverLegacyTable_iff_step`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaElimTypedLink.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## Row filters + the canonical pins -/

/-- The ι rows headed by a given eliminator (hand-rolled filter — the
per-generator view of the ι table). -/
def iotaRowsAtElim (generator : Generator) : List IotaRuleDesc :=
  listFilterByElim generator iotaRuleTable
where
  /-- The underlying filter, recursion-friendly. -/
  listFilterByElim (generator : Generator) :
      List IotaRuleDesc → List IotaRuleDesc
    | [] => []
    | rule :: restRows =>
        if rule.elimGenerator = generator then
          rule :: listFilterByElim generator restRows
        else listFilterByElim generator restRows

/-- `gen_app` heads exactly the β row. -/
theorem iotaRowsAtElim_app : iotaRowsAtElim .gen_app = [betaIotaRow] := rfl

/-- `gen_pathApp` heads exactly the endpoint-β row. -/
theorem iotaRowsAtElim_pathApp :
    iotaRowsAtElim .gen_pathApp = [pathBetaIotaRow] := rfl

/-- **The app-head dispatch brick**: a table row eliminating `gen_app`
IS the β row.  Every typed consumer routes through this instead of its
own 18-way split. -/
theorem iotaRowAtAppIsBeta {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    (isAppHead : rule.elimGenerator = .gen_app) : rule = betaIotaRow := by
  cases isRow with
  | head => rfl
  | tail _ isRow => cases isRow with
    | head => exact Generator.noConfusion isAppHead
    | tail _ isRow => cases isRow with
      | head => exact Generator.noConfusion isAppHead
      | tail _ isRow => cases isRow with
        | head => exact Generator.noConfusion isAppHead
        | tail _ isRow => cases isRow with
          | head => exact Generator.noConfusion isAppHead
          | tail _ isRow => cases isRow with
            | head => exact Generator.noConfusion isAppHead
            | tail _ isRow => cases isRow with
              | head => exact Generator.noConfusion isAppHead
              | tail _ isRow => cases isRow with
                | head => exact Generator.noConfusion isAppHead
                | tail _ isRow => cases isRow with
                  | head => exact Generator.noConfusion isAppHead
                  | tail _ isRow => cases isRow with
                    | head => exact Generator.noConfusion isAppHead
                    | tail _ isRow => cases isRow with
                      | head => exact Generator.noConfusion isAppHead
                      | tail _ isRow => cases isRow with
                        | head => exact Generator.noConfusion isAppHead
                        | tail _ isRow => cases isRow with
                          | head => exact Generator.noConfusion isAppHead
                          | tail _ isRow => cases isRow with
                            | head => exact Generator.noConfusion isAppHead
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact Generator.noConfusion isAppHead
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact Generator.noConfusion isAppHead
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact Generator.noConfusion isAppHead
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        exact
                                          Generator.noConfusion isAppHead
                                    | tail _ isRow => cases isRow

/-- **The pathApp-head dispatch brick**: a table row eliminating
`gen_pathApp` IS the endpoint-β row. -/
theorem iotaRowAtPathAppIsPathBeta {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    (isPathAppHead : rule.elimGenerator = .gen_pathApp) :
    rule = pathBetaIotaRow := by
  cases isRow with
  | head => exact Generator.noConfusion isPathAppHead
  | tail _ isRow => cases isRow with
    | head => exact Generator.noConfusion isPathAppHead
    | tail _ isRow => cases isRow with
      | head => exact Generator.noConfusion isPathAppHead
      | tail _ isRow => cases isRow with
        | head => exact Generator.noConfusion isPathAppHead
        | tail _ isRow => cases isRow with
          | head => exact Generator.noConfusion isPathAppHead
          | tail _ isRow => cases isRow with
            | head => exact Generator.noConfusion isPathAppHead
            | tail _ isRow => cases isRow with
              | head => exact Generator.noConfusion isPathAppHead
              | tail _ isRow => cases isRow with
                | head => exact Generator.noConfusion isPathAppHead
                | tail _ isRow => cases isRow with
                  | head => exact Generator.noConfusion isPathAppHead
                  | tail _ isRow => cases isRow with
                    | head => exact Generator.noConfusion isPathAppHead
                    | tail _ isRow => cases isRow with
                      | head => exact Generator.noConfusion isPathAppHead
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact Generator.noConfusion isPathAppHead
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact Generator.noConfusion isPathAppHead
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact Generator.noConfusion isPathAppHead
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact
                                    Generator.noConfusion isPathAppHead
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact
                                      Generator.noConfusion isPathAppHead
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact
                                        Generator.noConfusion
                                          isPathAppHead
                                  | tail _ isRow => cases isRow with
                                    | head => rfl
                                    | tail _ isRow => cases isRow

/-! ## The decidable static↔operational coherence gates -/

/-- Does ONE ι row cohere with a typed-eliminator table?  If the row's
eliminator carries a typing row (per `hasElimTypingRow`), the row must
scrutinize a TYPED INTRODUCER (per `hasIntroTypingRow`) at slot 0 — the
eliminated child.  Rows at untyped eliminators are unconstrained. -/
def iotaRowCoheresWith (hasElimTypingRow hasIntroTypingRow :
    Generator → Bool) (rule : IotaRuleDesc) : Bool :=
  if hasElimTypingRow rule.elimGenerator then
    match rule.scrutinees with
    | [] => false
    | spec :: [] => Nat.beq spec.slot 0 && hasIntroTypingRow spec.head
    | _ :: _ :: _ => false
  else true

/-- ★ The GTL-17 coherence gate: every ι row at a `elimRuleDescOf`-typed
eliminator scrutinizes an `introRuleDescOf`-typed introducer at slot 0.
Decided by `rfl`; re-decides when either table grows. -/
theorem typedElimIotaRowsCohere :
    listForall
        (iotaRowCoheresWith
          (fun generator => (elimRuleDescOf generator).isSome)
          (fun generator => (introRuleDescOf generator).isSome))
        iotaRuleTable
      = true := rfl

/-- ★ The v2 coherence gate: every ι row at a `generalElimRuleOf`-typed
eliminator (`gen_app`, `gen_pathApp`) scrutinizes a
`gradedIntroRuleOf`-typed introducer (`gen_lam`, `gen_pathLam`) at
slot 0.  The two-row pairing β ↔ (app, lam) and endpoint-β ↔
(pathApp, pathLam), decided by `rfl`. -/
theorem gradedElimIotaRowsCohere :
    listForall
        (iotaRowCoheresWith
          (fun generator => (generalElimRuleOf generator).isSome)
          (fun generator => (gradedIntroRuleOf generator).isSome))
        iotaRuleTable
      = true := rfl

/-! ## ★ The generic typed table-redex subject reduction -/

/-- ★ **The ONE table arm** (IOTA-T7): a typed cell on which an ι-table
row fires has its reduct typed at the SAME classifier — quantified over
the ι row (`isRow`) and the elimination typing row (`isTypedElim`).
The static↔operational link: the typing side guarantees the eliminator
is `gen_app` (the current typed-eliminator table), the T5 key
discipline collapses the row to β (`iotaRowAtAppIsBeta`), the firing
inverts to the bespoke β step (`betaRowFiringToStep`), and the
unconditional master subject reduction carries the reduct — whose β arm
IS the substitution lemma.  A new typed eliminator extends the dispatch
brick by one case; the statement and every consumer stay fixed. -/
theorem HasTypeDescPi.tableRedexSubjectReduction {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable)
    {elimRule : ElimRuleDesc}
    (isTypedElim : elimRuleDescOf rule.elimGenerator = some elimRule)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (.mkGen rule.elimGenerator elimPayload spine) classifier)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct classifier := by
  have isAppHead : rule.elimGenerator = .gen_app :=
    elimRuleDescOf_isApp isTypedElim
  have ruleIsBeta : rule = betaIotaRow := iotaRowAtAppIsBeta isRow isAppHead
  subst ruleIsBeta
  exact HasTypeDescPi.subjectReduction typed wellFormed reduct
    (betaRowFiringToStep elimPayload fires)

/-! ## The legacy-table master subject reduction (the T9 migration seam) -/

/-- The master subject reduction over the LEGACY table relation — the
17-row `StepOverTable` coincides with the bespoke `Step` (IOTA-T1
adequacy), so the unconditional master transports verbatim. -/
theorem HasTypeDescPi.subjectReductionOverLegacyTable
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context)
    {reduct : RawTerm scope}
    (tableStep : StepOverTable legacyIotaRuleTable subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReduction typed wellFormed reduct
    (stepOverLegacyTable_iff_step.mp tableStep)

/-- The star closure of the legacy-table master subject reduction. -/
theorem HasTypeDescPi.subjectReductionStarOverLegacyTable
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    {reduct : RawTerm scope}
    (chain : ReflTransClosure
      (StepOverTable legacyIotaRuleTable (scope := scope)) subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  induction chain with
  | refl _ => exact typed
  | head firstStep _rest inductionHypothesis =>
      exact inductionHypothesis
        (HasTypeDescPi.subjectReductionOverLegacyTable typed wellFormed
          firstStep)

end FX1Poly.Typed
