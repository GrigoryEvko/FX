import FX1Poly.Core.StepTableRenameReflection

/-! # FX1Poly/Core/StepRenameReflectAssembly
    — the full arbitrary-renaming `Step` reflection-with-image, table-routed

  `Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u`

(the Kripke-arrow-CR3 ingredient the open-context logical relation
`GrownCtxConv-5` needs.)

## The table route

Renaming preserves the term skeleton, so every redex in `rename rho t` sits at
a position that is already a redex in `t` — reflection holds for an ARBITRARY
`rho` (no injectivity, no left inverse needed).  The historical proof ran the
`Step.rec` mutual recursion with 18 per-redex leaf arms (β + 16 ι, the retired
`StepRenameReflectEliminatorIota` dispatch); the table lane proves the SAME
skeleton-preservation argument ONCE over the row schema
(`StepOverTable.reflectRename`: a root firing reflects through the firing
dispatcher's rename equation `firesOn?_rename`, congruence recurses through
the spine), so the bespoke statement now harvests it across the IOTA-T1
adequacy `stepOverLegacyTable_iff_step` — two generic arms instead of eighteen
bespoke ones, and every future row is covered by its scope-uniformity
certificate alone.

## Zero-axiom verification

The table reflection and the adequacy transport are propext-free by their
shipped gates.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per-declaration in
`FX1PolyAudit/AuditCoreSubstrate.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **The full arbitrary-renaming `Step` reflection-with-image.**  If a
renamed term `rename rho sourceTerm` `Step`-reduces to `targetReduct`, then
`sourceTerm` itself `Step`-reduces to some `sourceReduct` whose renaming under
the SAME `rho` is exactly `targetReduct`.  Table-routed: the generic
`StepOverTable.reflectRename` at the 17-row legacy table, transported across
the IOTA-T1 adequacy.  The Kripke-arrow-CR3 ingredient for the open-context
logical relation (`GrownCtxConv-5`). -/
theorem Step.reflectRename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope}
    {targetReduct : RawTerm targetScope}
    (renamedStep : Step (RawTerm.rename rho sourceTerm) targetReduct) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step sourceTerm sourceReduct ∧
        RawTerm.rename rho sourceReduct = targetReduct := by
  obtain ⟨sourceReduct, tableStep, renameEq⟩ :=
    StepOverTable.reflectRename legacyIotaRuleTable_isScopeUniform rho
      (stepOverLegacyTable_iff_step.mpr renamedStep)
  exact ⟨sourceReduct, stepOverLegacyTable_iff_step.mp tableStep, renameEq⟩

/-- A reduct of a weakened source term strengthens to the same term obtained
by substituting a canonical source-scope unit for the fresh variable.

Table-routed: rename reflection pins the reduct as a weakened source-scope
term, for which the strengthen/substitute agreement is the structural
weaken-retraction (`weaken_subst_singleton`).  Replaces the historical
950-line per-constructor `Step.rec` freshness-preservation induction. -/
theorem Step.weaken_strengthenTarget {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetTerm : RawTerm (scope + 1)}
    (underBinderStep : Step (RawTerm.weaken sourceTerm) targetTerm) :
    RawTerm.strengthen targetTerm =
      some (RawTerm.subst
        (RawTermSubst.singleton
          (.mkGen .gen_unit () .childNil : RawTerm scope))
        targetTerm) := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have renamedStep :
      Step (RawTerm.rename RawRenaming.weaken sourceTerm) targetTerm := by
    rw [← RawTerm.weaken_eq_rename sourceTerm]
    exact underBinderStep
  obtain ⟨sourceReduct, _sourceStep, renameEq⟩ :=
    Step.reflectRename RawRenaming.weaken renamedStep
  have targetIsWeakened : RawTerm.weaken sourceReduct = targetTerm := by
    rw [RawTerm.weaken_eq_rename sourceReduct]
    exact renameEq
  have targetFresh :
      RawTerm.isFreshFor RawRenaming.weaken
        (RawTermSubst.singleton unitTerm) targetTerm := by
    rw [← targetIsWeakened]
    dsimp only [RawTerm.isFreshFor]
    rw [RawTerm.weaken_subst_singleton sourceReduct unitTerm]
    rw [RawTerm.weaken_eq_rename sourceReduct]
  exact RawTerm.strengthen_eq_subst_of_isFreshFor_singleton
    unitTerm targetTerm targetFresh

end FX1Poly.Core
