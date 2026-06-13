import FX1Poly.Core.StepOverTable
import FX1Poly.Core.IotaTableEquivariance
import FX1Poly.Core.RawTermRenameAsSubst

/-! # FX1Poly/Core/StepTableEquivariance — substitution closure of the table relation

IOTA-T2's relation-level corollaries.  Two layers:

  * **Firing-dispatcher naturality** — the pattern test
    (`scrutineeSpecFires` / `scrutineesFire`) answers the same on a
    substituted spine, conditional on the scrutinee scope-uniformity
    certificates (non-var heads keep their heads under substitution;
    guards commute with the payload transport).  Therefore a fired row
    REFIRES after substitution, producing the substituted reduct
    (`firesOn?_subst`).
  * **Relation closure** — `StepOverTable.subst`: for ANY table whose
    rows are scope-uniform, the table-driven reduction relation is
    closed under substitution.  Instantiated at the canonical 21-row
    table as `StepTable.subst`.

This is the generic replacement for the bespoke per-constructor
substitution arms: ONE proof over the table schema covers every row
shipped today and every row added tomorrow — a new row only owes its
scope-uniformity certificate.

## Zero-axiom verification

Firing inversion via the shipped `scrutineeSpecFires_extractsHead`,
defeq-ascription through the matcher/dite reductions, the substrate's
view/projection naturality bricks, and structural recursion over the
derivation.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaTableEquivariance.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Firing-dispatcher naturality -/

/-- ONE scrutinee spec's pattern test survives substitution: the
matched cell's head is pinned to the declared (non-var) head, so the
substituted slot holds the SAME head with the transported payload, and
the guard (if any) answers the same by its scope-uniformity clause. -/
theorem IotaRuleDesc.scrutineeSpecFires_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    {spec : ScrutineeSpec} (specIsUniform : spec.IsScopeUniform)
    (specFires : rule.scrutineeSpecFires spine spec = true) :
    rule.scrutineeSpecFires (RawTermChildren.subst sigma spine) spec
      = true := by
  obtain ⟨isNotVarSpecHead, guardIsUniform⟩ := specIsUniform
  cases childLookup : (scopedChildAt? spine.toScopedChildren
      spec.slot).bind ScopedChild.atShiftZero? with
  | none =>
      exfalso
      dsimp only [IotaRuleDesc.scrutineeSpecFires] at specFires
      rw [childLookup] at specFires
      exact Bool.noConfusion specFires
  | some scrutineeCell =>
    cases scrutineeCell with
    | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      have isDeclaredHead : scrutineeGenerator = spec.head :=
        rule.scrutineeSpecFires_extractsHead specFires childLookup
      subst isDeclaredHead
      -- the ORIGINAL guard verdict, with the matcher/dite/Eq.rec
      -- reductions collapsed by defeq ascription
      have guardPasses :
          (match spec.payloadGuard? with
            | none => true
            | some payloadGuard => payloadGuard scope scrutineePayload)
          = true := by
        have specFiresDite :
            (if isHead : spec.head = spec.head then
              (match spec.payloadGuard? with
                | none => true
                | some payloadGuard =>
                    payloadGuard scope
                      (Eq.rec (motive := fun matchedHead _ =>
                          matchedHead.payload scope)
                        scrutineePayload isHead))
            else false) = true := by
          dsimp only [IotaRuleDesc.scrutineeSpecFires] at specFires
          rw [childLookup] at specFires
          exact specFires
        rw [dif_pos rfl] at specFiresDite
        exact specFiresDite
      -- the SUBSTITUTED slot holds the substituted cell — same head
      have substLookup :
          (scopedChildAt?
              (RawTermChildren.subst sigma spine).toScopedChildren
              spec.slot).bind ScopedChild.atShiftZero?
          = some (.mkGen spec.head
              (Generator.payload_scope_invariant_of_not_var
                  isNotVarSpecHead scope targetScope ▸ scrutineePayload)
              (foldChildren GenAlgebra.canonical sigma
                scrutineeChildren)) := by
        obtain ⟨scrutineeChild, slotEq, shiftEq⟩ :=
          optionBindEqSome childLookup
        dsimp only [scopedChildAt?] at slotEq ⊢
        rw [RawTermChildren.toScopedChildren_subst sigma spine,
          listEntryAt?_map, slotEq, optionSomeMap, optionSomeBindExplicit]
        rw [ScopedChild.atShiftZero?_substView, shiftEq, optionSomeMap]
        rw [RawTerm.subst_nonVar_reduces sigma isNotVarSpecHead
          scrutineePayload scrutineeChildren]
      -- refire on the substituted spine
      dsimp only [IotaRuleDesc.scrutineeSpecFires]
      rw [substLookup]
      show (if isHead : spec.head = spec.head then
          (match spec.payloadGuard? with
            | none => true
            | some payloadGuard =>
                payloadGuard targetScope
                  (Eq.rec (motive := fun matchedHead _ =>
                      matchedHead.payload targetScope)
                    (cast (Generator.payload_scope_invariant_of_not_var
                        isNotVarSpecHead scope targetScope)
                      scrutineePayload)
                    isHead))
        else false) = true
      rw [dif_pos rfl]
      cases guardShape : spec.payloadGuard? with
      | none => rfl
      | some payloadGuard =>
          have guardCommutes :
              ∀ (guardSourceScope guardTargetScope : Nat)
                (isNotVar : spec.head ≠ .gen_var)
                (matchedPayload : spec.head.payload guardSourceScope),
                payloadGuard guardTargetScope
                  (cast (Generator.payload_scope_invariant_of_not_var
                    isNotVar guardSourceScope guardTargetScope)
                    matchedPayload)
                = payloadGuard guardSourceScope matchedPayload := by
            rw [guardShape] at guardIsUniform
            exact guardIsUniform
          have guardPassedAtSource :
              payloadGuard scope scrutineePayload = true := by
            rw [guardShape] at guardPasses
            exact guardPasses
          exact (guardCommutes scope targetScope isNotVarSpecHead
            scrutineePayload).trans guardPassedAtSource

/-- The full pattern test survives substitution, spec by spec. -/
theorem IotaRuleDesc.scrutineesFire_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (specs : List ScrutineeSpec) →
    ScrutineeSpecsAreScopeUniform specs →
    rule.scrutineesFire spine specs = true →
    rule.scrutineesFire (RawTermChildren.subst sigma spine) specs = true
  | [], _, _ => rfl
  | spec :: restSpecs, specsAreUniform, allFire => by
      obtain ⟨specIsUniform, restAreUniform⟩ := specsAreUniform
      dsimp only [IotaRuleDesc.scrutineesFire] at allFire ⊢
      obtain ⟨specFires, restFire⟩ := andEqTrueSplit allFire
      rw [rule.scrutineeSpecFires_subst sigma spine specIsUniform specFires,
        rule.scrutineesFire_subst sigma spine restSpecs restAreUniform
          restFire]
      rfl

/-- ★ **Firing naturality**: a fired row refires on the substituted
spine, producing the substituted reduct — conditional on the row's
scope-uniformity certificate. -/
theorem IotaRuleDesc.firesOn?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (isUniform : rule.IsScopeUniform)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    rule.firesOn?
        (cast (Generator.payload_scope_invariant_of_not_var
          isUniform.isNotVarHead scope targetScope) elimPayload)
        (RawTermChildren.subst sigma spine)
      = some (RawTerm.subst sigma reduct) := by
  have allFire := rule.firesOn?_some_scrutineesFire fires
  have allFireAfterSubst := rule.scrutineesFire_subst sigma spine
    rule.scrutinees isUniform.scrutineesAreUniform allFire
  dsimp only [IotaRuleDesc.firesOn?] at fires ⊢
  rw [if_pos allFire] at fires
  rw [if_pos allFireAfterSubst]
  exact rule.interpretTarget?_subst sigma isUniform elimPayload spine fires

/-! ## Relation closure -/

mutual

/-- ★ **The table relation is closed under substitution** — for ANY
table whose rows are scope-uniform.  Root firings refire via
`firesOn?_subst`; congruences recurse with the fold engine's own
per-shift lift. -/
theorem StepOverTable.subst {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {scope targetScope : Nat} →
    (sigma : RawTermSubst scope targetScope) →
    {source target : RawTerm scope} →
    StepOverTable table source target →
    StepOverTable table (RawTerm.subst sigma source)
      (RawTerm.subst sigma target)
  | scope, targetScope, sigma, _, _,
      .tableRedex isRow elimPayload fires => by
      rw [RawTerm.subst_nonVar_reduces sigma
        (tableIsUniform _ isRow).isNotVarHead elimPayload _]
      exact .tableRedex isRow _
        (IotaRuleDesc.firesOn?_subst _ sigma (tableIsUniform _ isRow)
          elimPayload fires)
  | scope, targetScope, sigma, _, _, .cong gen payload childStep => by
      by_cases isVarGen : gen = .gen_var
      case pos =>
        subst isVarGen
        cases childStep
      case neg =>
        rw [RawTerm.subst_nonVar_reduces sigma isVarGen payload _,
          RawTerm.subst_nonVar_reduces sigma isVarGen payload _]
        exact .cong gen _
          (StepOverTableChildren.subst tableIsUniform sigma childStep)

/-- Spine companion: each congruence position substitutes with the
fold engine's per-shift lift — the alignment is definitional. -/
theorem StepOverTableChildren.subst {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {parentScope parentTargetScope : Nat} →
    (sigma : RawTermSubst parentScope parentTargetScope) →
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    StepOverTableChildren table children children' →
    StepOverTableChildren table (RawTermChildren.subst sigma children)
      (RawTermChildren.subst sigma children')
  | parentScope, _, sigma, _, _, _,
      @StepOverTableChildren.here _ _ headShift _ _ _ rest childStep =>
      .here (RawTermChildren.subst sigma rest)
        (StepOverTable.subst tableIsUniform
          (iterateLiftRaw sigma headShift) childStep)
  | parentScope, _, sigma, _, _, _,
      @StepOverTableChildren.there _ _ headShift _ head _ _ restStep =>
      .there (RawTerm.subst (iterateLiftRaw sigma headShift) head)
        (StepOverTableChildren.subst tableIsUniform sigma restStep)

end

/-! ## Instantiation at the canonical table -/

/-- Every row of the 21-row canonical table carries its
scope-uniformity certificate. -/
theorem iotaRuleTable_isScopeUniform :
    ∀ rule, rule ∈ iotaRuleTable → rule.IsScopeUniform := by
  intro rule isRow
  cases isRow with
  | head => exact betaIotaRow_isScopeUniform
  | tail _ isRow => cases isRow with
    | head => exact boolTrueIotaRow_isScopeUniform
    | tail _ isRow => cases isRow with
      | head => exact boolFalseIotaRow_isScopeUniform
      | tail _ isRow => cases isRow with
        | head => exact fstPairIotaRow_isScopeUniform
        | tail _ isRow => cases isRow with
          | head => exact sndPairIotaRow_isScopeUniform
          | tail _ isRow => cases isRow with
            | head => exact natElimZeroIotaRow_isScopeUniform
            | tail _ isRow => cases isRow with
              | head => exact natRecZeroIotaRow_isScopeUniform
              | tail _ isRow => cases isRow with
                | head => exact natElimSuccIotaRow_isScopeUniform
                | tail _ isRow => cases isRow with
                  | head => exact natRecSuccIotaRow_isScopeUniform
                  | tail _ isRow => cases isRow with
                    | head => exact listElimNilIotaRow_isScopeUniform
                    | tail _ isRow => cases isRow with
                      | head => exact listElimConsIotaRow_isScopeUniform
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact optionMatchNoneIotaRow_isScopeUniform
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact optionMatchSomeIotaRow_isScopeUniform
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact eitherMatchInlIotaRow_isScopeUniform
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact
                                    eitherMatchInrIotaRow_isScopeUniform
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact idJReflIotaRow_isScopeUniform
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact
                                        idStrictRecReflIotaRow_isScopeUniform
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        exact
                                          pathBetaIotaRow_isScopeUniform
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          exact
                                            quotRecMkIotaRow_isScopeUniform
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            exact
                                              quotElimMkIotaRow_isScopeUniform
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              exact
                                                truncRecIntroIotaRow_isScopeUniform
                                          | tail _ isRow => cases isRow

/-- Every legacy-fragment row is scope-uniform — the canonical table's
certificate restricted through the sublist embedding
`legacyRow_memFullTable`. -/
theorem legacyIotaRuleTable_isScopeUniform :
    ∀ rule, rule ∈ legacyIotaRuleTable → rule.IsScopeUniform :=
  fun rule isRow =>
    iotaRuleTable_isScopeUniform rule (legacyRow_memFullTable isRow)

/-- ★ **`StepTable` is closed under substitution** — the canonical
21-row relation, with every certificate discharged.  The table-generic
replacement for the bespoke per-constructor `Step.subst` arms. -/
theorem StepTable.subst {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope)
    {source target : RawTerm scope}
    (tableStep : StepTable source target) :
    StepTable (RawTerm.subst sigma source) (RawTerm.subst sigma target) :=
  StepOverTable.subst iotaRuleTable_isScopeUniform sigma tableStep

/-- Rename closure is the subst closure at the variable injection —
the rename-as-subst factoring makes it a corollary, not a second fold
induction. -/
theorem StepOverTable.rename {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    {source target : RawTerm scope}
    (tableStep : StepOverTable table source target) :
    StepOverTable table (RawTerm.rename someRenaming source)
      (RawTerm.rename someRenaming target) := by
  rw [RawTerm.rename_eq_subst_ofRenaming someRenaming source,
    RawTerm.rename_eq_subst_ofRenaming someRenaming target]
  exact StepOverTable.subst tableIsUniform
    (RawTermSubst.ofRenaming someRenaming) tableStep

/-- ★ **`StepTable` is closed under renaming** — the canonical 21-row
relation. -/
theorem StepTable.rename {scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    {source target : RawTerm scope}
    (tableStep : StepTable source target) :
    StepTable (RawTerm.rename someRenaming source)
      (RawTerm.rename someRenaming target) :=
  StepOverTable.rename iotaRuleTable_isScopeUniform someRenaming tableStep

end FX1Poly.Core
