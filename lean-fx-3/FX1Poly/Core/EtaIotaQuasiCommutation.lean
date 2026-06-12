import FX1Poly.Core.EtaIotaCongRootAssembly
import FX1Poly.Core.StrongNormalizationEtaTable

/-! # EtaIotaQuasiCommutation — ETA-T5 increment 4.5a: the full mutual
quasi-commutation of table eta over table iota

Assembles the four quadrants into ONE statement: an eta step followed
by an iota step reorders into a fronted iota step and a union star.
Root-eta-then-iota is the shipped copy-replacement argument
(`etaRedexQuasiCommutesOverIota`); cong-eta-then-root-iota is the
shipped dichotomy assembly (`congEtaQuasiCommutesOverRootIota`), with
its duality disjunct discharged by the `DualityReorders` oracle the
caller supplies (per intro/elim row pair — canonical pairs:
etaLam↔beta, etaPair↔fst/snd, etaPathLam↔pathBeta); the two deep-deep
quadrants are positional spine bookkeeping (different slots reorder
verbatim; the same slot recurses) — a term/children structural mutual
on the eta derivation.

The corollary `quasiCommutesRightOverLeft_ofTables` is exactly the
hypothesis the shipped abstract Geser engine
(`StrongNormalizationUnion.accUnion`) consumes: with eta SN proved
generically (ETA-T3) and any iota SN evidence, the UNION is SN.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaQuasiCommutation.lean`. -/

namespace FX1Poly.Core

/-! ## The duality oracle -/

/-- The per-pair reordering obligation for the eta/iota duality: when
a row fires on the post-eta spine and the pre-eta spine holds an eta
redex at a scrutinee slot, the caller must reorder by other means
(canonically: the row also fires on the redex — the eta intro head IS
the scrutinee head — and the observation structure makes the fronted
reduct literally the post-eta subject).  Discharged once per
intro/elim row pair; quantified here so the quasi-commutation stays
table-generic. -/
def DualityReorders (iotaTable : List IotaRuleDesc)
    (etaTable : List EtaRuleDesc) : Prop :=
  ∀ {scope : Nat} {rule : IotaRuleDesc}, rule ∈ iotaTable →
  ∀ (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope},
    StepEtaOverTableChildren etaTable spine spine' →
    ∀ {target : RawTerm scope},
    rule.firesOn? elimPayload spine' = some target →
    rule.HasEtaDualityAt etaTable spine spine' →
    ∃ commonReduct : RawTerm scope,
      StepOverTable iotaTable
        (.mkGen rule.elimGenerator elimPayload spine) commonReduct
      ∧ UnionStar (StepOverTable iotaTable (scope := scope))
          (StepEtaOverTable etaTable) commonReduct target

/-! ## Union-star congruence lifts -/

/-- A children-level union star lifts through a cell constructor. -/
theorem unionStarCongOfUnionChildrenStar {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc} {scope : Nat} (gen : Generator)
    (payload : gen.payload scope)
    {children children' : RawTermChildren gen.binderShifts scope}
    (childrenStar :
      UnionStar
        (StepOverTableChildren iotaTable (parentScope := scope)
          (binderShifts := gen.binderShifts))
        (StepEtaOverTableChildren etaTable) children children') :
    UnionStar (StepOverTable iotaTable (scope := scope))
      (StepEtaOverTable etaTable)
      (.mkGen gen payload children) (.mkGen gen payload children') := by
  induction childrenStar with
  | refl => exact .refl _
  | tailLeft _ stepToReduct ih =>
      exact .tailLeft ih (.cong gen payload stepToReduct)
  | tailRight _ stepToReduct ih =>
      exact .tailRight ih (.cong gen payload stepToReduct)

/-- A term-level union star at the head slot lifts through
`childCons` (the tail spine fixed). -/
theorem unionStarHereOfUnionStar {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc} {parentScope headShift : Nat}
    {restShifts : List Nat}
    {head head' : RawTerm (parentScope + headShift)}
    (rest : RawTermChildren restShifts parentScope)
    (headStar :
      UnionStar (StepOverTable iotaTable (scope := parentScope + headShift))
        (StepEtaOverTable etaTable) head head') :
    UnionStar
      (StepOverTableChildren iotaTable (parentScope := parentScope)
        (binderShifts := headShift :: restShifts))
      (StepEtaOverTableChildren etaTable)
      (.childCons head rest) (.childCons head' rest) := by
  induction headStar with
  | refl => exact .refl _
  | tailLeft _ stepToReduct ih =>
      exact .tailLeft ih (.here rest stepToReduct)
  | tailRight _ stepToReduct ih =>
      exact .tailRight ih (.here rest stepToReduct)

/-- A children-level union star on the tail spine lifts through
`childCons` (the head fixed). -/
theorem unionStarThereOfUnionStar {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc} {parentScope headShift : Nat}
    {restShifts : List Nat}
    (head : RawTerm (parentScope + headShift))
    {rest rest' : RawTermChildren restShifts parentScope}
    (restStar :
      UnionStar
        (StepOverTableChildren iotaTable (parentScope := parentScope)
          (binderShifts := restShifts))
        (StepEtaOverTableChildren etaTable) rest rest') :
    UnionStar
      (StepOverTableChildren iotaTable (parentScope := parentScope)
        (binderShifts := headShift :: restShifts))
      (StepEtaOverTableChildren etaTable)
      (.childCons head rest) (.childCons head rest') := by
  induction restStar with
  | refl => exact .refl _
  | tailLeft _ stepToReduct ih =>
      exact .tailLeft ih (.there head stepToReduct)
  | tailRight _ stepToReduct ih =>
      exact .tailRight ih (.there head stepToReduct)

/-! ## The mutual quasi-commutation -/

mutual

/-- ★ **Table eta quasi-commutes over table iota**: an eta step
followed by an iota step reorders into one fronted iota step and a
union star — by structural mutual induction on the eta derivation,
with the four quadrants dispatched to the shipped bricks and the
duality to the caller's oracle. -/
theorem etaIotaQuasiCommutes {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    (dualityReorders : DualityReorders iotaTable etaTable) :
    {scope : Nat} → {source middleTerm target : RawTerm scope} →
    StepEtaOverTable etaTable source middleTerm →
    StepOverTable iotaTable middleTerm target →
    ∃ commonReduct : RawTerm scope,
      StepOverTable iotaTable source commonReduct
      ∧ UnionStar (StepOverTable iotaTable (scope := scope))
          (StepEtaOverTable etaTable) commonReduct target
  | _, _, _, _,
      .etaRedex isRow isRawTier introPayload contracts, iotaStep =>
      etaRedexQuasiCommutesOverIota tableIsUniform etaTableIsWf
        rowsAreScopeSafe isRow isRawTier introPayload contracts iotaStep
  | _, _, _, _, .cong gen payload etaChildStep, iotaStep => by
      cases iotaStep with
      | tableRedex isRow elimPayload fires =>
          cases congEtaQuasiCommutesOverRootIota rowsAreScopeSafe isRow
              elimPayload etaChildStep fires with
          | inl reordered => exact reordered
          | inr duality =>
              exact dualityReorders isRow elimPayload etaChildStep
                fires duality
      | cong _gen _payload iotaChildStep =>
          obtain ⟨commonChildren, iotaChildren, childrenStar⟩ :=
            etaIotaQuasiCommutesChildren tableIsUniform etaTableIsWf
              rowsAreScopeSafe dualityReorders etaChildStep
              iotaChildStep
          exact ⟨.mkGen gen payload commonChildren,
            .cong gen payload iotaChildren,
            unionStarCongOfUnionChildrenStar gen payload childrenStar⟩

/-- Spine companion: positional reordering of an eta children-step
before an iota children-step. -/
theorem etaIotaQuasiCommutesChildren {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    (dualityReorders : DualityReorders iotaTable etaTable) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    {children middleChildren targetChildren :
      RawTermChildren binderShifts parentScope} →
    StepEtaOverTableChildren etaTable children middleChildren →
    StepOverTableChildren iotaTable middleChildren targetChildren →
    ∃ commonChildren : RawTermChildren binderShifts parentScope,
      StepOverTableChildren iotaTable children commonChildren
      ∧ UnionStar
          (StepOverTableChildren iotaTable (parentScope := parentScope)
            (binderShifts := binderShifts))
          (StepEtaOverTableChildren etaTable) commonChildren
          targetChildren
  | _, _, _, _, _, .here rest headEta, iotaChildStep => by
      cases iotaChildStep with
      | here _rest headIota =>
          obtain ⟨commonHead, iotaHead, headStar⟩ :=
            etaIotaQuasiCommutes tableIsUniform etaTableIsWf
              rowsAreScopeSafe dualityReorders headEta headIota
          exact ⟨.childCons commonHead rest, .here rest iotaHead,
            unionStarHereOfUnionStar rest headStar⟩
      | there _head restIota =>
          exact ⟨.childCons _ _, .there _ restIota,
            .tailRight (.refl _) (.here _ headEta)⟩
  | _, _, _, _, _, .there head restEta, iotaChildStep => by
      cases iotaChildStep with
      | here _rest headIota =>
          exact ⟨.childCons _ _, .here _ headIota,
            .tailRight (.refl _) (.there _ restEta)⟩
      | there _head restIota =>
          obtain ⟨commonRest, iotaRest, restStar⟩ :=
            etaIotaQuasiCommutesChildren tableIsUniform etaTableIsWf
              rowsAreScopeSafe dualityReorders restEta restIota
          exact ⟨.childCons head commonRest, .there head iotaRest,
            unionStarThereOfUnionStar head restStar⟩

end

/-! ## The Geser hypothesis and the union SN corollary -/

/-- ★★ **The Geser hypothesis, table-generic**: at every scope, table
eta quasi-commutes over table iota — exactly the shape
`StrongNormalizationUnion.accUnion` consumes. -/
theorem quasiCommutesRightOverLeft_ofTables
    {iotaTable : List IotaRuleDesc} {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    (dualityReorders : DualityReorders iotaTable etaTable)
    (scope : Nat) :
    QuasiCommutesRightOverLeft
      (StepOverTable iotaTable (scope := scope))
      (StepEtaOverTable etaTable) :=
  fun _source _middleTerm _target etaStep iotaStep =>
    etaIotaQuasiCommutes tableIsUniform etaTableIsWf rowsAreScopeSafe
      dualityReorders etaStep iotaStep

/-- ★★ **Union strong normalization, table-generic**: any term whose
iota reduction is accessible is accessible for the iota∪eta union —
eta SN is the ETA-T3 schema theorem, the reordering is the mutual
above, and the duality oracle is the only per-table input. -/
theorem accUnionOfTables {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    (dualityReorders : DualityReorders iotaTable etaTable)
    {scope : Nat} {subject : RawTerm scope}
    (iotaAccessible :
      Acc (fun later earlier =>
        StepOverTable iotaTable earlier later) subject) :
    Acc (UnionSuccessor
      (StepOverTable iotaTable (scope := scope))
      (StepEtaOverTable etaTable)) subject :=
  accUnion
    (fun term => StepEtaOverTable.isStronglyNormalizing etaTable term)
    (quasiCommutesRightOverLeft_ofTables tableIsUniform etaTableIsWf
      rowsAreScopeSafe dualityReorders scope)
    iotaAccessible

end FX1Poly.Core
