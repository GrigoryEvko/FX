import FX1Poly.Core.TableParallelStability
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.StepParallelConfluence

/-! # FX1Poly/Core/TableTakahashiTriangle — IOTA-T6: complete development, triangle, table confluence

The finale of the orthogonal-systems confluence theorem (Rosen/Nipkow)
mechanized over OUR rule table: a complete-development function, the
Takahashi triangle, the parallel diamond, and confluence of the
table-driven reduction — proven ONCE for every current and future row
of any well-formed scope-uniform table.

## The split-firing root walk

`completeDevelopOverTable` contracts, bottom-up, every redex VISIBLE in
the source: children develop first, then the root fires iff some row's
pattern matches the SOURCE children (`fireSplitAtRoot?` tests the
pattern on the source, interprets on the developed children — the
firing payload is the row's FULL `firesOn?` on the developed spine).
Testing on the source is what makes the triangle true: a root that
becomes a redex only AFTER development is NOT contracted, exactly
matching what a single parallel step out of the source can do.

## The triangle, by ONE derivation induction

`ParStepOverTable.triangle`: every parallel reduct further reduces, in
ONE parallel step, to the complete development of the source.

  * Root-vs-root: the step fired `rule` on its reduced spine; the
    children IH sends that reduced spine to the developed children;
    `firesOn?_parStable` refires there; the WALK returns exactly that
    firing because any co-firing row at the developed cell IS `rule`
    (IOTA-T5 `rootFiringDeterministic` — the orthogonality keystone
    consumed exactly where it was built to be).
  * Root-vs-cong: if the source fires, the congruence reduct is itself
    a redex (firing preservation — head rigidity), and it steps to the
    walk's firing via the children IH; if the source does not fire, the
    walk falls back to congruence.

The diamond and confluence then fall out of the shipped abstract
plumbing (`DiamondProperty.ofTriangle`, `confluentOfDiamondSimulation`)
with the IOTA-T6 sandwich bounds.

## Zero-axiom verification

Mutual structural recursion on terms and derivations, the `match h : e`
goal-generalization recipe on the walk, and the T5/T6 bricks.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTableTakahashiTriangle.lean`. -/

namespace FX1Poly.Core

/-! ## The split-firing root step -/

/-- Per-row split firing: the left-linear pattern is tested on the
SOURCE children, the reduct is the row's full firing on the DEVELOPED
children.  The complete development's root dispatcher. -/
def IotaRuleDesc.fireSplitAtRoot? (rule : IotaRuleDesc) {scope : Nat}
    (generator : Generator) (payload : generator.payload scope)
    (sourceChildren developedChildren :
      RawTermChildren generator.binderShifts scope) :
    Option (RawTerm scope) :=
  if isElimHead : generator = rule.elimGenerator then
    if rule.scrutineesFire (isElimHead ▸ sourceChildren) rule.scrutinees then
      rule.firesOn? (isElimHead ▸ payload) (isElimHead ▸ developedChildren)
    else none
  else none

/-- The split-firing table walk: first row whose pattern matches the
source AND whose firing succeeds on the developed children. -/
def fireSplitTableRedexOver {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (sourceChildren developedChildren :
      RawTermChildren generator.binderShifts scope) :
    List IotaRuleDesc → Option (RawTerm scope)
  | [] => none
  | rule :: restRows =>
      match rule.fireSplitAtRoot? generator payload sourceChildren
          developedChildren with
      | some reduct => some reduct
      | none =>
          fireSplitTableRedexOver generator payload sourceChildren
            developedChildren restRows

/-- A successful split firing decomposes into its three gates. -/
theorem IotaRuleDesc.fireSplitAtRoot?_someInversion {rule : IotaRuleDesc}
    {scope : Nat} {generator : Generator} {payload : generator.payload scope}
    {sourceChildren developedChildren :
      RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireSplit : rule.fireSplitAtRoot? generator payload sourceChildren
      developedChildren = some reduct) :
    ∃ isElimHead : generator = rule.elimGenerator,
      rule.scrutineesFire (isElimHead ▸ sourceChildren) rule.scrutinees
        = true
      ∧ rule.firesOn? (isElimHead ▸ payload)
          (isElimHead ▸ developedChildren)
        = some reduct := by
  dsimp only [IotaRuleDesc.fireSplitAtRoot?] at fireSplit
  by_cases isElimHead : generator = rule.elimGenerator
  · rw [dif_pos isElimHead] at fireSplit
    by_cases sourceFires :
        rule.scrutineesFire (isElimHead ▸ sourceChildren) rule.scrutinees
          = true
    · rw [if_pos sourceFires] at fireSplit
      exact ⟨isElimHead, sourceFires, fireSplit⟩
    · rw [if_neg sourceFires] at fireSplit
      injection fireSplit
  · rw [dif_neg isElimHead] at fireSplit
    injection fireSplit

/-- A successful split firing IS a full root firing at the developed
cell — the lift into the T5 determinism theorem. -/
theorem IotaRuleDesc.fireSplitAtRoot?_firesAtDevelopedRoot
    {rule : IotaRuleDesc} {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {sourceChildren developedChildren :
      RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireSplit : rule.fireSplitAtRoot? generator payload sourceChildren
      developedChildren = some reduct) :
    rule.fireAtRoot? generator payload developedChildren = some reduct := by
  obtain ⟨isElimHead, _sourceFires, firesEq⟩ :=
    rule.fireSplitAtRoot?_someInversion fireSplit
  subst isElimHead
  rw [rule.fireAtRoot?_atOwnElim]
  exact firesEq

/-- A successful walk names its firing row. -/
theorem fireSplitTableRedexOver_someInversion {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {sourceChildren developedChildren :
      RawTermChildren generator.binderShifts scope} :
    (rows : List IotaRuleDesc) → {reduct : RawTerm scope} →
    fireSplitTableRedexOver generator payload sourceChildren
        developedChildren rows
      = some reduct →
    ∃ rule, rule ∈ rows
      ∧ rule.fireSplitAtRoot? generator payload sourceChildren
          developedChildren
        = some reduct
  | [], _, walkEq => nomatch walkEq
  | headRule :: restRows, reduct, walkEq => by
      dsimp only [fireSplitTableRedexOver] at walkEq
      match headFireEq : headRule.fireSplitAtRoot? generator payload
          sourceChildren developedChildren with
      | some headReduct =>
          rw [headFireEq] at walkEq
          obtain rfl := Option.some.inj walkEq
          exact ⟨headRule, .head _, headFireEq⟩
      | none =>
          rw [headFireEq] at walkEq
          obtain ⟨rule, isInRest, ruleFires⟩ :=
            fireSplitTableRedexOver_someInversion restRows walkEq
          exact ⟨rule, .tail _ isInRest, ruleFires⟩

/-- **Walk determinism in a well-formed table**: when a member row split
fires, the walk returns exactly that firing — whichever row the walk
meets first co-fires at the developed cell, and T5 root determinism
makes the reducts agree. -/
theorem WfIotaTable.fireSplitTableRedexOver_eq_ofRowFires
    {table : List IotaRuleDesc} (tableIsWf : WfIotaTable table)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {sourceChildren developedChildren :
      RawTermChildren generator.binderShifts scope}
    {firingRule : IotaRuleDesc} (firingIsRow : firingRule ∈ table)
    {reduct : RawTerm scope}
    (rowFire : firingRule.fireSplitAtRoot? generator payload sourceChildren
      developedChildren = some reduct) :
    (rows : List IotaRuleDesc) →
    (rowsAreInTable : ∀ rule, rule ∈ rows → rule ∈ table) →
    firingRule ∈ rows →
    fireSplitTableRedexOver generator payload sourceChildren
        developedChildren rows
      = some reduct
  | [], _, isMember => by cases isMember
  | headRule :: restRows, rowsAreInTable, isMember => by
      dsimp only [fireSplitTableRedexOver]
      match headFireEq : headRule.fireSplitAtRoot? generator payload
          sourceChildren developedChildren with
      | some headReduct =>
          exact congrArg some
            (tableIsWf.rootFiringDeterministic
              (rowsAreInTable headRule (.head _)) firingIsRow
              (headRule.fireSplitAtRoot?_firesAtDevelopedRoot headFireEq)
              (firingRule.fireSplitAtRoot?_firesAtDevelopedRoot rowFire))
      | none =>
          cases isMember with
          | head => exact nomatch headFireEq.symm.trans rowFire
          | tail _ isInRest =>
              exact tableIsWf.fireSplitTableRedexOver_eq_ofRowFires
                firingIsRow rowFire restRows
                (fun rule inRest => rowsAreInTable rule (.tail _ inRest))
                isInRest

/-! ## Complete development -/

mutual

/-- **The complete development**: develop every child, then fire the
root iff some row's pattern matches the SOURCE children (interpreting
over the developed children).  Takahashi's maximal one-shot reduct over
the table. -/
def completeDevelopOverTable (table : List IotaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope
  | _, .mkGen generator payload children =>
      match fireSplitTableRedexOver generator payload children
          (completeDevelopChildrenOverTable table children) table with
      | some reduct => reduct
      | none =>
          .mkGen generator payload
            (completeDevelopChildrenOverTable table children)

/-- Pointwise complete development of a children spine. -/
def completeDevelopChildrenOverTable (table : List IotaRuleDesc) :
    {binderShifts : List Nat} → {scope : Nat} →
    RawTermChildren binderShifts scope → RawTermChildren binderShifts scope
  | _, _, .childNil => .childNil
  | _, _, .childCons childHead childTail =>
      .childCons (completeDevelopOverTable table childHead)
        (completeDevelopChildrenOverTable table childTail)

end

mutual

/-- **The complete development is a parallel step** — every term
parallel-reduces to its complete development (the walk's split firing
supplies the redex arm's three premises directly; the fallback is
congruence). -/
theorem ParStepOverTable.toCompleteDevelopment (table : List IotaRuleDesc) :
    {scope : Nat} → (term : RawTerm scope) →
    ParStepOverTable table term (completeDevelopOverTable table term)
  | _, .mkGen generator payload children => by
      have childrenDevelopment :=
        ParStepOverTableChildren.toCompleteDevelopment table children
      dsimp only [completeDevelopOverTable]
      match walkEq : fireSplitTableRedexOver generator payload children
          (completeDevelopChildrenOverTable table children) table with
      | some reduct =>
          obtain ⟨rule, isRow, ruleFireSplit⟩ :=
            fireSplitTableRedexOver_someInversion table walkEq
          obtain ⟨isElimHead, sourceFires, firesEq⟩ :=
            rule.fireSplitAtRoot?_someInversion ruleFireSplit
          subst isElimHead
          exact .tableRedex isRow payload childrenDevelopment sourceFires
            firesEq
      | none =>
          exact .cong generator payload childrenDevelopment

/-- Spine companion: every spine parallel-reduces pointwise to its
complete development. -/
theorem ParStepOverTableChildren.toCompleteDevelopment
    (table : List IotaRuleDesc) :
    {binderShifts : List Nat} → {scope : Nat} →
    (children : RawTermChildren binderShifts scope) →
    ParStepOverTableChildren table children
      (completeDevelopChildrenOverTable table children)
  | _, _, .childNil => .nil
  | _, _, .childCons childHead childTail =>
      .cons (ParStepOverTable.toCompleteDevelopment table childHead)
        (ParStepOverTableChildren.toCompleteDevelopment table childTail)

end

/-! ## THE Takahashi triangle -/

mutual

/-- ★ **The Takahashi triangle over the table**: every parallel reduct
further reduces, in ONE parallel step, to the complete development of
the source — for any well-formed (orthogonal) scope-uniform table.
Root-vs-root closes by parallel stability + T5 walk determinism;
root-vs-cong by firing preservation; cong-vs-cong by the children
induction. -/
theorem ParStepOverTable.triangle {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table)
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {scope : Nat} → {source target : RawTerm scope} →
    ParStepOverTable table source target →
    ParStepOverTable table target (completeDevelopOverTable table source)
  | scope, _, _,
      @ParStepOverTable.tableRedex _ _ rule isRow elimPayload spine
        reducedSpine reduct spinePar sourceFires fires => by
      have reducedToDeveloped :
          ParStepOverTableChildren table reducedSpine
            (completeDevelopChildrenOverTable table spine) :=
        ParStepOverTableChildren.triangleChildren tableIsWf tableIsUniform
          spinePar
      obtain ⟨developedReduct, firesOnDeveloped, reductPar⟩ :=
        rule.firesOn?_parStable tableIsUniform
          (tableIsWf.scrutineeHeadsAreRigid isRow) elimPayload
          reducedToDeveloped fires
      have ruleFireSplit :
          rule.fireSplitAtRoot? rule.elimGenerator elimPayload spine
              (completeDevelopChildrenOverTable table spine)
            = some developedReduct := by
        dsimp only [IotaRuleDesc.fireSplitAtRoot?]
        rw [dif_pos rfl, if_pos sourceFires]
        exact firesOnDeveloped
      dsimp only [completeDevelopOverTable]
      rw [tableIsWf.fireSplitTableRedexOver_eq_ofRowFires isRow
        ruleFireSplit table (fun _ isMember => isMember) isRow]
      exact reductPar
  | scope, _, _, .cong generator payload childrenPar => by
      have childrenTriangle :=
        ParStepOverTableChildren.triangleChildren tableIsWf tableIsUniform
          childrenPar
      dsimp only [completeDevelopOverTable]
      match walkEq : fireSplitTableRedexOver generator payload _
          (completeDevelopChildrenOverTable table _) table with
      | some reduct =>
          obtain ⟨rule, isRow, ruleFireSplit⟩ :=
            fireSplitTableRedexOver_someInversion table walkEq
          obtain ⟨isElimHead, sourceFires, firesEq⟩ :=
            rule.fireSplitAtRoot?_someInversion ruleFireSplit
          subst isElimHead
          exact .tableRedex isRow payload childrenTriangle
            (rule.scrutineesFire_parPreserved childrenPar rule.scrutinees
              (tableIsWf.scrutineeHeadsAreRigid isRow) sourceFires)
            firesEq
      | none =>
          exact .cong generator payload childrenTriangle

/-- Spine companion of the triangle. -/
theorem ParStepOverTableChildren.triangleChildren {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table)
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    ParStepOverTableChildren table children children' →
    ParStepOverTableChildren table children'
      (completeDevelopChildrenOverTable table children)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons headPar tailPar =>
      .cons (ParStepOverTable.triangle tableIsWf tableIsUniform headPar)
        (ParStepOverTableChildren.triangleChildren tableIsWf tableIsUniform
          tailPar)

end

/-! ## Diamond + confluence -/

/-- ★ **The parallel diamond** — Takahashi's triangle lemma applied to
the table's complete development. -/
theorem ParStepOverTable.diamond {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table)
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} :
    DiamondProperty
      (fun source target : RawTerm scope =>
        ParStepOverTable table source target) :=
  DiamondProperty.ofTriangle
    (fun parStep => ParStepOverTable.triangle tableIsWf tableIsUniform
      parStep)

/-- ★ **Table confluence**: the table-driven reduction of any
well-formed scope-uniform table is confluent — proven ONCE for every
current and future row.  The orthogonal-systems confluence theorem
(Rosen/Nipkow) over OUR table. -/
theorem StepOverTable.confluent {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table)
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} :
    Confluent
      (fun source target : RawTerm scope =>
        StepOverTable table source target) :=
  confluentOfDiamondSimulation
    (fun tableStep => tableStep.toParStepOverTable)
    (fun parStep => parStep.toStepClosure)
    (ParStepOverTable.diamond tableIsWf tableIsUniform)

/-- ★★ **The canonical 18-row relation is confluent** — both
certificates discharged by their `rfl`-decided table pins.  Adding a
row to `iotaRuleTable` re-decides the certificates and inherits
confluence with ZERO new proof. -/
theorem StepTable.confluent {scope : Nat} :
    Confluent
      (fun source target : RawTerm scope => StepTable source target) :=
  StepOverTable.confluent iotaRuleTable_isWf iotaRuleTable_isScopeUniform

end FX1Poly.Core
