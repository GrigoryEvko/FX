import FX1Poly.Core.EtaContractionNaturality
import FX1Poly.Core.StructuralInductionPrimitives
import FX1Poly.Core.RawTermRenameAsSubst

/-! # StepEtaTableSubstitution — ETA-T2: the relation closure

The table eta relation is closed under substitution and renaming, for
ANY table whose rows are scope-safe: root contractions re-contract via
the firing naturality (`contractsOn?_subst`), congruences recurse with
the fold engine's own per-shift lift, and renaming is the one-line
corollary through `RawTermSubst.ofRenaming`.

The five canonical rows certify `IsScopeSafe` by closed-constructor
pins: every observer head and every intro head is a non-`gen_var`
generator (`Generator.noConfusion`), and every fresh block sits within
its binder depth (`[1]` within depth 1; empty blocks within depth 0).

This closes the ETA-T2 equivariance arc: strengthening squares
(`EtaStrengthenEquivariance`), firing naturality
(`EtaContractionNaturality`), and now the relation closure — the eta
twin of `StepOverTable.subst`/`StepOverTable.rename`
(`StepTableEquivariance`).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStepEtaTableSubstitution.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation (RawRenaming)

/-! ## The mutual closure -/

mutual

/-- ★ **The table eta relation is closed under substitution** — for
ANY table whose rows are scope-safe.  Root contractions re-contract via
`contractsOn?_subst`; congruences recurse with the fold engine's own
per-shift lift. -/
theorem StepEtaOverTable.subst {table : List EtaRuleDesc}
    (tableIsSafe : ∀ rule, rule ∈ table → rule.IsScopeSafe) :
    {scope targetScope : Nat} →
    (sigma : RawTermSubst scope targetScope) →
    {source target : RawTerm scope} →
    StepEtaOverTable table source target →
    StepEtaOverTable table (RawTerm.subst sigma source)
      (RawTerm.subst sigma target)
  | scope, targetScope, sigma, _, _,
      .etaRedex isRow isRawTier introPayload contracts => by
      rw [RawTerm.subst_nonVar_reduces sigma
        (tableIsSafe _ isRow).introIsNotVar introPayload _]
      exact .etaRedex isRow isRawTier _
        (EtaRuleDesc.contractsOn?_subst _ (tableIsSafe _ isRow) sigma
          contracts)
  | scope, targetScope, sigma, _, _, .cong gen payload childStep => by
      by_cases isVarGen : gen = .gen_var
      case pos =>
        subst isVarGen
        cases childStep
      case neg =>
        rw [RawTerm.subst_nonVar_reduces sigma isVarGen payload _,
          RawTerm.subst_nonVar_reduces sigma isVarGen payload _]
        exact .cong gen _
          (StepEtaOverTableChildren.subst tableIsSafe sigma childStep)

/-- Spine companion: each congruence position substitutes with the
fold engine's per-shift lift — the alignment is definitional. -/
theorem StepEtaOverTableChildren.subst {table : List EtaRuleDesc}
    (tableIsSafe : ∀ rule, rule ∈ table → rule.IsScopeSafe) :
    {parentScope parentTargetScope : Nat} →
    (sigma : RawTermSubst parentScope parentTargetScope) →
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    StepEtaOverTableChildren table children children' →
    StepEtaOverTableChildren table (RawTermChildren.subst sigma children)
      (RawTermChildren.subst sigma children')
  | parentScope, _, sigma, _, _, _,
      @StepEtaOverTableChildren.here _ _ headShift _ _ _ rest childStep =>
      .here (RawTermChildren.subst sigma rest)
        (StepEtaOverTable.subst tableIsSafe
          (iterateLiftRaw sigma headShift) childStep)
  | parentScope, _, sigma, _, _, _,
      @StepEtaOverTableChildren.there _ _ headShift _ head _ _ restStep =>
      .there (RawTerm.subst (iterateLiftRaw sigma headShift) head)
        (StepEtaOverTableChildren.subst tableIsSafe sigma restStep)

end

/-- ★ **The table eta relation is closed under renaming** — the
one-line corollary through `RawTermSubst.ofRenaming`. -/
theorem StepEtaOverTable.rename {table : List EtaRuleDesc}
    (tableIsSafe : ∀ rule, rule ∈ table → rule.IsScopeSafe)
    {scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    {source target : RawTerm scope}
    (etaStep : StepEtaOverTable table source target) :
    StepEtaOverTable table (RawTerm.rename someRenaming source)
      (RawTerm.rename someRenaming target) := by
  rw [RawTerm.rename_eq_subst_ofRenaming someRenaming source,
    RawTerm.rename_eq_subst_ofRenaming someRenaming target]
  exact StepEtaOverTable.subst tableIsSafe
    (RawTermSubst.ofRenaming someRenaming) etaStep

/-! ## The canonical rows are scope-safe -/

theorem etaLamRow_isScopeSafe : etaLamRow.IsScopeSafe where
  introIsNotVar := fun isVar => Generator.noConfusion isVar
  observationsAreScopeSafe := fun _spec isMember => by
    cases isMember with
    | head =>
        exact ⟨fun isVar => Generator.noConfusion isVar, Nat.le_refl 1⟩
    | tail _ isMember => cases isMember

theorem etaPairRow_isScopeSafe : etaPairRow.IsScopeSafe where
  introIsNotVar := fun isVar => Generator.noConfusion isVar
  observationsAreScopeSafe := fun _spec isMember => by
    cases isMember with
    | head =>
        exact ⟨fun isVar => Generator.noConfusion isVar, Nat.le_refl 0⟩
    | tail _ isMember =>
        cases isMember with
        | head =>
            exact ⟨fun isVar => Generator.noConfusion isVar, Nat.le_refl 0⟩
        | tail _ isMember => cases isMember

theorem etaPathLamRow_isScopeSafe : etaPathLamRow.IsScopeSafe where
  introIsNotVar := fun isVar => Generator.noConfusion isVar
  observationsAreScopeSafe := fun _spec isMember => by
    cases isMember with
    | head =>
        exact ⟨fun isVar => Generator.noConfusion isVar, Nat.le_refl 1⟩
    | tail _ isMember => cases isMember

theorem etaModIntroRow_isScopeSafe : etaModIntroRow.IsScopeSafe where
  introIsNotVar := fun isVar => Generator.noConfusion isVar
  observationsAreScopeSafe := fun _spec isMember => by
    cases isMember with
    | head =>
        exact ⟨fun isVar => Generator.noConfusion isVar, Nat.le_refl 0⟩
    | tail _ isMember => cases isMember

theorem etaGlueIntroRow_isScopeSafe : etaGlueIntroRow.IsScopeSafe where
  introIsNotVar := fun isVar => Generator.noConfusion isVar
  observationsAreScopeSafe := fun _spec isMember => by
    cases isMember with
    | head =>
        exact ⟨fun isVar => Generator.noConfusion isVar, Nat.le_refl 0⟩
    | tail _ isMember => cases isMember

theorem unitEtaRow_isScopeSafe : unitEtaRow.IsScopeSafe where
  introIsNotVar := fun isVar => Generator.noConfusion isVar
  observationsAreScopeSafe := fun _spec isMember => by cases isMember

/-- Every row of the canonical 6-row table carries its scope-safety
certificate. -/
theorem etaRuleTable_isScopeSafe :
    ∀ rule, rule ∈ etaRuleTable → rule.IsScopeSafe := by
  intro rule isRow
  cases isRow with
  | head => exact etaLamRow_isScopeSafe
  | tail _ isRow => cases isRow with
    | head => exact etaPairRow_isScopeSafe
    | tail _ isRow => cases isRow with
      | head => exact etaPathLamRow_isScopeSafe
      | tail _ isRow => cases isRow with
        | head => exact etaModIntroRow_isScopeSafe
        | tail _ isRow => cases isRow with
          | head => exact etaGlueIntroRow_isScopeSafe
          | tail _ isRow => cases isRow with
            | head => exact unitEtaRow_isScopeSafe
            | tail _ isRow => cases isRow

/-! ## Instantiation at the canonical table -/

/-- ★ **`StepEtaTable` is closed under substitution** — the canonical
5-row eta relation. -/
theorem StepEtaTable.subst {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope)
    {source target : RawTerm scope}
    (etaStep : StepEtaTable source target) :
    StepEtaTable (RawTerm.subst sigma source)
      (RawTerm.subst sigma target) :=
  StepEtaOverTable.subst etaRuleTable_isScopeSafe sigma etaStep

/-- ★ **`StepEtaTable` is closed under renaming** — the canonical
5-row eta relation. -/
theorem StepEtaTable.rename {scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    {source target : RawTerm scope}
    (etaStep : StepEtaTable source target) :
    StepEtaTable (RawTerm.rename someRenaming source)
      (RawTerm.rename someRenaming target) :=
  StepEtaOverTable.rename etaRuleTable_isScopeSafe someRenaming etaStep

end FX1Poly.Core
