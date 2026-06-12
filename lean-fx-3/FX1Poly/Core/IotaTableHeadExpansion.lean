import FX1Poly.Core.IotaTableOrientedSN
import FX1Poly.Core.TableTakahashiTriangle
import FX1Poly.Typed.TypedFragmentTableAdequacy

/-! # IotaTableHeadExpansion — IOTA-T8 Tier-3: the generic candidate
head-expansion arm over rows

The Tait-style head-expansion arm at the strong-normalization candidate,
genericized over `IotaRuleDesc`: **a fired table redex whose spine is SN
and whose reduct is SN is itself SN** — for ANY row of any well-formed
scope-uniform table, in ONE theorem.  This is the table analog of the
bespoke `betaSpineHeadExpansion` (the SN-candidate head expansion the
Tait fundamental theorem consumes at β-redexes), proved once for every
current and future row instead of per iota arm.

The proof is the orthogonality dividend.  Accessibility of the redex
needs every one-step successor accessible; the freed-subject inversion
(`StepOverTable.invertOrCong`, IOTA-T7) splits successors into

  * **a root firing by any member row** — T5 root determinism
    (`WfIotaTable.rootFiringDeterministic`) pins it to THE reduct,
    accessible by hypothesis;
  * **a child congruence** — the spine strictly descends (the outer
    accessibility induction), and the row REFIRES on the reduced spine
    with a parallel-related reduct (`firesOn?_parStable`, IOTA-T6);
    parallel steps flatten to step chains (`toStepClosure`), and
    accessibility transports along chains.

No row-specific reasoning anywhere: a new row that joins a well-formed
scope-uniform table inherits this head-expansion arm by re-deciding the
same two `rfl` certificates as confluence.

The import of `FX1Poly.Typed.TypedFragmentTableAdequacy` is for the
Core-named `StepOverTable.invertOrCong` it hosts; re-homing that lemma
into a Core module is IOTA-T11 restructuring fodder.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditIotaTableHeadExpansion.lean`. -/

namespace FX1Poly.Core

/-! ## Successor order on children spines -/

/-- Accessibility successor for the children companion: `laterChildren`
is below `earlierChildren` when `earlierChildren` table-contracts to it
at some position (mirrors `StepOverTable.successorOver`). -/
def StepOverTableChildren.successorOver (table : List IotaRuleDesc)
    {parentScope : Nat} {binderShifts : List Nat}
    (laterChildren earlierChildren :
      RawTermChildren binderShifts parentScope) : Prop :=
  StepOverTableChildren table earlierChildren laterChildren

/-! ## Accessibility transport along step chains -/

/-- Accessibility transports along a reflexive-transitive step chain:
every reduct of an SN term is SN. -/
theorem accOfTableStepClosure {table : List IotaRuleDesc} {scope : Nat} :
    {source target : RawTerm scope} →
    ReflTransClosure (StepOverTable table) source target →
    Acc (StepOverTable.successorOver table) source →
    Acc (StepOverTable.successorOver table) target
  | _, _, .refl _, sourceIsSN => sourceIsSN
  | _, _, .head firstStep restChain, sourceIsSN =>
      accOfTableStepClosure restChain (sourceIsSN.inv firstStep)

/-! ## Cell transport of a firing -/

/-- A row's firing transports across a raw-cell identification: when the
row's redex cell IS the cell `(generator, payload, children)`, the
firing is a `fireAtRoot?` success at those coordinates — the seam that
routes `invertOrCong`'s root disjunct into T5 root determinism. -/
theorem IotaRuleDesc.firesOn?_toFireAtRootAtCell {rule : IotaRuleDesc}
    {scope : Nat} {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (cellEq : RawTerm.mkGen rule.elimGenerator elimPayload spine
      = RawTerm.mkGen generator payload children)
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    rule.fireAtRoot? generator payload children = some reduct := by
  have headsAgree : rule.elimGenerator = generator := congrArg
    (fun cell => match cell with
      | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
    cellEq
  subst headsAgree
  injection cellEq with _scopeRefl _genRefl payloadEq childrenEq
  subst payloadEq
  subst childrenEq
  rw [rule.fireAtRoot?_atOwnElim]
  exact fires

/-! ## ★ The generic head-expansion arm at the SN candidate -/

/-- **★ Generic table head expansion at the strong-normalization
candidate**: a fired redex of ANY member row of a well-formed
scope-uniform table is SN as soon as its spine and its reduct are SN —
the Tait head-expansion arm over rows, replacing the per-iota-arm
expansion lemmas wholesale. -/
theorem WfIotaTable.tableRedexHeadExpansion {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table)
    (tableIsUniform : ∀ anyRule, anyRule ∈ table → anyRule.IsScopeUniform)
    {scope : Nat} {rule : IotaRuleDesc} (isRow : rule ∈ table)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineIsSN : Acc (StepOverTableChildren.successorOver table) spine)
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    (reductIsSN : Acc (StepOverTable.successorOver table) reduct) :
    Acc (StepOverTable.successorOver table)
      (.mkGen rule.elimGenerator elimPayload spine) := by
  revert reduct
  induction spineIsSN with
  | intro spine _spineAcc spineIH =>
    intro reduct fires reductIsSN
    refine Acc.intro _ (fun next stepToNext => ?_)
    cases StepOverTable.invertOrCong stepToNext rfl with
    | inl rootFiring =>
        obtain ⟨otherRule, otherIsRow, otherPayload, otherSpine, cellEq,
          otherFires⟩ := rootFiring
        have mineAtRoot :
            rule.fireAtRoot? rule.elimGenerator elimPayload spine
              = some reduct := by
          rw [rule.fireAtRoot?_atOwnElim]
          exact fires
        have theirsAtRoot :
            otherRule.fireAtRoot? rule.elimGenerator elimPayload spine
              = some next :=
          otherRule.firesOn?_toFireAtRootAtCell cellEq otherFires
        have nextIsTheReduct : next = reduct :=
          tableIsWf.rootFiringDeterministic otherIsRow isRow
            theirsAtRoot mineAtRoot
        exact nextIsTheReduct ▸ reductIsSN
    | inr congShape =>
        obtain ⟨laterSpine, nextShape, childrenStep⟩ := congShape
        subst nextShape
        obtain ⟨laterReduct, laterFires, reductPar⟩ :=
          rule.firesOn?_parStable tableIsUniform
            (tableIsWf.scrutineeHeadsAreRigid isRow) elimPayload
            childrenStep.toParStepOverTableChildren fires
        exact spineIH laterSpine childrenStep laterFires
          (accOfTableStepClosure reductPar.toStepClosure reductIsSN)

/-! ## Spine accessibility from per-child accessibility -/

/-- The empty spine is accessible — no children step leaves `childNil`. -/
theorem StepOverTableChildren.accNil {table : List IotaRuleDesc}
    {parentScope : Nat} :
    Acc (StepOverTableChildren.successorOver table)
      (RawTermChildren.childNil (scope := parentScope)) :=
  Acc.intro _ (fun _next noStep =>
    nomatch (noStep :
      StepOverTableChildren table RawTermChildren.childNil _next))

/-- Accessibility composes through `childCons`: an SN head and an SN
tail make an SN spine (a children step contracts exactly one position,
so the pair `(head, tail)` descends lexicographically). -/
theorem StepOverTableChildren.accCons {table : List IotaRuleDesc}
    {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
    {head : RawTerm (parentScope + headShift)}
    {rest : RawTermChildren restShifts parentScope}
    (headIsSN : Acc (StepOverTable.successorOver table) head)
    (restIsSN : Acc (StepOverTableChildren.successorOver table) rest) :
    Acc (StepOverTableChildren.successorOver table)
      (RawTermChildren.childCons head rest) := by
  revert rest
  induction headIsSN with
  | intro head _headAcc headIH =>
    intro rest restIsSN
    induction restIsSN with
    | intro rest restAcc restIH =>
      refine Acc.intro _ (fun nextChildren childrenStep => ?_)
      cases childrenStep with
      | here _rest headStep =>
          exact headIH _ headStep (Acc.intro rest restAcc)
      | there _head restStep =>
          exact restIH _ restStep

/-! ## ★★ The canonical 18-row instantiation -/

/-- **★★ Head expansion at the SN candidate over the canonical table** —
both certificates discharged by their `rfl`-decided pins.  Adding a row
to `iotaRuleTable` re-decides the certificates and inherits the
head-expansion arm with ZERO new proof. -/
theorem StepTable.tableRedexHeadExpansion {scope : Nat}
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineIsSN :
      Acc (StepOverTableChildren.successorOver iotaRuleTable) spine)
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    (reductIsSN : Acc (StepOverTable.successorOver iotaRuleTable) reduct) :
    Acc (StepOverTable.successorOver iotaRuleTable)
      (.mkGen rule.elimGenerator elimPayload spine) :=
  WfIotaTable.tableRedexHeadExpansion iotaRuleTable_isWf
    iotaRuleTable_isScopeUniform isRow elimPayload spineIsSN fires
    reductIsSN

end FX1Poly.Core
