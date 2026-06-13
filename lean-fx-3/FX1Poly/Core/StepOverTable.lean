import FX1Poly.Core.IotaRuleTable

/-! # FX1Poly/Core/StepOverTable — the table-driven reduction relation,
DEFINITION layer

`StepOverTable table` is single-step reduction whose ROOT redexes are
exactly the firings of the rows of `table` (`IotaRuleDesc.firesOn?`),
closed under uniform child congruence.  The relation is PARAMETERIZED
by the table — the RW-5 keystone shape — so the canonical instances are
just table choices:

  * `StepTable := StepOverTable iotaRuleTable` — the canonical full
    table (the canonicality-flip OFFICIAL relation, IOTA-T9);
  * `StepOverTable legacyIotaRuleTable` — the 17-row legacy fragment
    (the slice that coincides with the bespoke `Step`; the adequacy
    proof lives in `StepTable.lean`).

This file is the BESPOKE-FREE layer: it imports ONLY the rule table.
The Step <-> StepOverTable adequacy (which necessarily mentions the
bespoke `Step` constructors) stays in `StepTable.lean`, so pure-table
consumers can import this file without pulling the bespoke reduction
substrate — the IOTA-T11 retirement seam.

Contents: the legacy table + its membership pins, the
`StepOverTable`/`StepOverTableChildren` mutual inductives, the
`StepTable` abbrev, table monotonicity, the generic firing-inversion
trio (`firesOn?_some_scrutineesFire` / `scrutineeSpecFires_extractsHead`
/ `firesOn?_some_primaryHead`), and the table-native endpoint-beta
liveness witness `StepTable.pathBetaFires`.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditStepTable.lean`. -/

namespace FX1Poly.Core

/-! ## The legacy (17-row) table -/

/-- The 17 LEGACY rows — `iotaRuleTable` without the table-native
endpoint-β.  This is the fragment whose table relation coincides with
the bespoke `Step` (the adequacy below). -/
def legacyIotaRuleTable : List IotaRuleDesc :=
  [ betaIotaRow
  , boolTrueIotaRow, boolFalseIotaRow
  , fstPairIotaRow, sndPairIotaRow
  , natElimZeroIotaRow, natRecZeroIotaRow
  , natElimSuccIotaRow, natRecSuccIotaRow
  , listElimNilIotaRow, listElimConsIotaRow
  , optionMatchNoneIotaRow, optionMatchSomeIotaRow
  , eitherMatchInlIotaRow, eitherMatchInrIotaRow
  , idJReflIotaRow, idStrictRecReflIotaRow ]

/-- Stale-count guard: 17 legacy rows. -/
theorem legacyIotaRuleTable_length : legacyIotaRuleTable.length = 17 := rfl

/-- The full table IS the legacy table extended by the table-native
rows — endpoint-β plus the three IOTA-T10 demo rows —
definitionally. -/
theorem iotaRuleTable_eq_legacyAppendPathBeta :
    iotaRuleTable = legacyIotaRuleTable
      ++ [pathBetaIotaRow, quotRecMkIotaRow, quotElimMkIotaRow,
          truncRecIntroIotaRow] := rfl

/-! ## The table-driven reduction relation -/

mutual

/-- Single-step reduction OVER A RULE TABLE: a root redex is a firing
of some row of `table` (`firesOn?` — the left-linear pattern test plus
the template interpretation), and reduction is closed under the same
uniform child congruence as `Step`.  Adding an ι-rule to the kernel
becomes adding a ROW to the table parameter — no new constructors
anywhere. -/
inductive StepOverTable (table : List IotaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- **A table row fires at the root.**  The subject is the row's
      eliminator cell; the reduct is whatever the row's template
      interprets to. -/
  | tableRedex {scope : Nat} {rule : IotaRuleDesc} (isRow : rule ∈ table)
      (elimPayload : rule.elimGenerator.payload scope)
      {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
      {reduct : RawTerm scope}
      (fires : rule.firesOn? elimPayload spine = some reduct) :
      StepOverTable table (.mkGen rule.elimGenerator elimPayload spine) reduct
  /-- **Uniform congruence under any generator** — same shape as
      `Step.cong`. -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
      {children children' : RawTermChildren gen.binderShifts scope}
      (childStep : StepOverTableChildren table children children') :
      StepOverTable table (.mkGen gen payload children)
        (.mkGen gen payload children')

/-- A table step at some position in a children spine — the mutual
companion to `StepOverTable.cong`, mirroring `StepChildren`. -/
inductive StepOverTableChildren (table : List IotaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      {head head' : RawTerm (parentScope + headShift)}
      (rest : RawTermChildren restShifts parentScope)
      (childStep : StepOverTable table head head') :
      StepOverTableChildren table
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest)
  | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      (head : RawTerm (parentScope + headShift))
      {rest rest' : RawTermChildren restShifts parentScope}
      (restStep : StepOverTableChildren table rest rest') :
      StepOverTableChildren table
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head rest')

end

/-- THE table relation: `StepOverTable` at the full 18-row
`iotaRuleTable` — the IOTA-T9 canonicality-flip target. -/
abbrev StepTable {scope : Nat} (source target : RawTerm scope) : Prop :=
  StepOverTable iotaRuleTable source target

/-! ## Table monotonicity -/

/-- Hand-rolled left append membership (Init-only, axiom-free). -/
theorem listMemAppendLeft {entryType : Type} {entry : entryType}
    {frontEntries : List entryType} (backEntries : List entryType)
    (isMember : entry ∈ frontEntries) :
    entry ∈ frontEntries ++ backEntries := by
  induction isMember with
  | head _ => exact .head _
  | tail _ _ memberOfRest => exact .tail _ memberOfRest

/-- Membership in an append comes from one of the sides (hand-rolled by
list induction; the core lemma's axiom status is unaudited). -/
theorem listMemAppendInv {entryType : Type} {entry : entryType} :
    ∀ (firstList secondList : List entryType),
      entry ∈ firstList ++ secondList →
      entry ∈ firstList ∨ entry ∈ secondList
  | [], _, memSecond => Or.inr memSecond
  | listHead :: firstRest, secondList, memBoth => by
      cases memBoth with
      | head => exact Or.inl (List.Mem.head firstRest)
      | tail _ memRest =>
          rcases listMemAppendInv firstRest secondList memRest
            with inFirst | inSecond
          · exact Or.inl (List.Mem.tail listHead inFirst)
          · exact Or.inr inSecond

/-- Membership in a map comes from a source element (hand-rolled). -/
theorem listMemMapInv {sourceType targetType : Type}
    (mapped : sourceType → targetType) {entry : targetType} :
    ∀ (sourceList : List sourceType), entry ∈ sourceList.map mapped →
      ∃ source, source ∈ sourceList ∧ mapped source = entry
  | [], memEmpty => nomatch memEmpty
  | listHead :: rest, memMapped => by
      cases memMapped with
      | head => exact ⟨listHead, List.Mem.head rest, rfl⟩
      | tail _ memRest =>
          obtain ⟨source, memSource, mappedEq⟩ :=
            listMemMapInv mapped rest memRest
          exact ⟨source, List.Mem.tail listHead memSource, mappedEq⟩

/-- Every legacy row is a full-table row. -/
theorem legacyRow_memFullTable {rule : IotaRuleDesc}
    (isLegacy : rule ∈ legacyIotaRuleTable) : rule ∈ iotaRuleTable := by
  rw [iotaRuleTable_eq_legacyAppendPathBeta]
  exact listMemAppendLeft _ isLegacy

mutual

/-- A step over a table is a step over any WIDER table — rows only ever
ADD reduction behavior. -/
theorem StepOverTable.monotone {table widerTable : List IotaRuleDesc}
    (isWider : ∀ {rule : IotaRuleDesc}, rule ∈ table → rule ∈ widerTable)
    {scope : Nat} {source target : RawTerm scope}
    (tableStep : StepOverTable table source target) :
    StepOverTable widerTable source target :=
  match tableStep with
  | .tableRedex isRow elimPayload fires =>
      .tableRedex (isWider isRow) elimPayload fires
  | .cong gen payload childStep =>
      .cong gen payload (StepOverTableChildren.monotone isWider childStep)

/-- Spine companion of `StepOverTable.monotone`. -/
theorem StepOverTableChildren.monotone {table widerTable : List IotaRuleDesc}
    (isWider : ∀ {rule : IotaRuleDesc}, rule ∈ table → rule ∈ widerTable)
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep : StepOverTableChildren table children children') :
    StepOverTableChildren widerTable children children' :=
  match childStep with
  | .here rest headStep => .here rest (StepOverTable.monotone isWider headStep)
  | .there head restStep =>
      .there head (StepOverTableChildren.monotone isWider restStep)

end

/-! ## Legacy-row membership (17 explicit witnesses) -/

theorem betaIotaRow_memLegacy : betaIotaRow ∈ legacyIotaRuleTable := .head _
theorem boolTrueIotaRow_memLegacy : boolTrueIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.head _)
theorem boolFalseIotaRow_memLegacy : boolFalseIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.head _))
theorem fstPairIotaRow_memLegacy : fstPairIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.head _)))
theorem sndPairIotaRow_memLegacy : sndPairIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
theorem natElimZeroIotaRow_memLegacy :
    natElimZeroIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem natRecZeroIotaRow_memLegacy :
    natRecZeroIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem natElimSuccIotaRow_memLegacy :
    natElimSuccIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
theorem natRecSuccIotaRow_memLegacy :
    natRecSuccIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.head _))))))))
theorem listElimNilIotaRow_memLegacy :
    listElimNilIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.head _)))))))))
theorem listElimConsIotaRow_memLegacy :
    listElimConsIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.head _))))))))))
theorem optionMatchNoneIotaRow_memLegacy :
    optionMatchNoneIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.head _)))))))))))
theorem optionMatchSomeIotaRow_memLegacy :
    optionMatchSomeIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
theorem eitherMatchInlIotaRow_memLegacy :
    eitherMatchInlIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
theorem eitherMatchInrIotaRow_memLegacy :
    eitherMatchInrIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
theorem idJReflIotaRow_memLegacy : idJReflIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.head _)))))))))))))))
theorem idStrictRecReflIotaRow_memLegacy :
    idStrictRecReflIotaRow ∈ legacyIotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.head _))))))))))))))))

/-- The table-native endpoint-β row is a FULL-table row. -/
theorem pathBetaIotaRow_memTable : pathBetaIotaRow ∈ iotaRuleTable := by
  rw [iotaRuleTable_eq_legacyAppendPathBeta]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.tail _ (.head _)))))))))))))))))


/-! ## FULL-table membership pins (one per canonical row) -/

theorem betaIotaRow_memTable : betaIotaRow ∈ iotaRuleTable :=
  (.head _)

theorem boolTrueIotaRow_memTable : boolTrueIotaRow ∈ iotaRuleTable :=
  (.tail _ (.head _))

theorem boolFalseIotaRow_memTable : boolFalseIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.head _)))

theorem fstPairIotaRow_memTable : fstPairIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.head _))))

theorem sndPairIotaRow_memTable : sndPairIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem natElimZeroIotaRow_memTable : natElimZeroIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

theorem natRecZeroIotaRow_memTable : natRecZeroIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

theorem natElimSuccIotaRow_memTable : natElimSuccIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))

theorem natRecSuccIotaRow_memTable : natRecSuccIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))

theorem listElimNilIotaRow_memTable : listElimNilIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))

theorem listElimConsIotaRow_memTable : listElimConsIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))

theorem optionMatchNoneIotaRow_memTable : optionMatchNoneIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))

theorem optionMatchSomeIotaRow_memTable : optionMatchSomeIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))

theorem eitherMatchInlIotaRow_memTable : eitherMatchInlIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))

theorem eitherMatchInrIotaRow_memTable : eitherMatchInrIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))

theorem idJReflIotaRow_memTable : idJReflIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))

theorem idStrictRecReflIotaRow_memTable : idStrictRecReflIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))

theorem quotRecMkIotaRow_memTable : quotRecMkIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))

theorem quotElimMkIotaRow_memTable : quotElimMkIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))

theorem truncRecIntroIotaRow_memTable : truncRecIntroIotaRow ∈ iotaRuleTable :=
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))


/-! ## Generic firing inversion — the head extraction trio

The backward direction needs to learn, from `firesOn? = some reduct`,
that the declared scrutinee slot really holds the declared constructor
head.  Proved ONCE generically; the 17 per-row inversions then never
case on generators. -/

/-- Hand-rolled `&&`-split (full enumeration, axiom-free). -/
theorem andEqTrueSplit {leftFlag rightFlag : Bool}
    (bothHold : (leftFlag && rightFlag) = true) :
    leftFlag = true ∧ rightFlag = true :=
  match leftFlag, rightFlag, bothHold with
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, contra => Bool.noConfusion contra
  | false, true, contra => Bool.noConfusion contra
  | false, false, contra => Bool.noConfusion contra

/-- A successful firing implies the pattern test passed. -/
theorem IotaRuleDesc.firesOn?_some_scrutineesFire {rule : IotaRuleDesc}
    {scope : Nat} {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    rule.scrutineesFire spine rule.scrutinees = true := by
  by_cases allFire : rule.scrutineesFire spine rule.scrutinees = true
  · exact allFire
  · exfalso
    dsimp only [IotaRuleDesc.firesOn?] at fires
    rw [if_neg allFire] at fires
    injection fires

/-- A passing spec test pins the slot's head generator: whatever cell
the declared slot holds, its head IS the declared head (refutation via
the computed `false` branch otherwise). -/
theorem IotaRuleDesc.scrutineeSpecFires_extractsHead {rule : IotaRuleDesc}
    {scope : Nat}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {spec : ScrutineeSpec} {scrutineeGenerator : Generator}
    {scrutineePayload : scrutineeGenerator.payload scope}
    {scrutineeChildren :
      RawTermChildren scrutineeGenerator.binderShifts scope}
    (specFires : rule.scrutineeSpecFires spine spec = true)
    (slotHolds : (scopedChildAt? spine.toScopedChildren spec.slot).bind
        ScopedChild.atShiftZero?
      = some (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)) :
    scrutineeGenerator = spec.head := by
  by_cases isHead : scrutineeGenerator = spec.head
  · exact isHead
  · exfalso
    have specRefutes : rule.scrutineeSpecFires spine spec = false := by
      dsimp only [IotaRuleDesc.scrutineeSpecFires]
      rw [slotHolds]
      exact dif_neg isHead
    rw [specRefutes] at specFires
    exact Bool.noConfusion specFires

/-- The single-spec head extraction: for a singleton-pattern row, a
successful firing pins the primary slot's head. -/
theorem IotaRuleDesc.firesOn?_some_primaryHead {rule : IotaRuleDesc}
    {scope : Nat} {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {primarySpec : ScrutineeSpec}
    (specsShape : rule.scrutinees = [primarySpec])
    {scrutineeGenerator : Generator}
    {scrutineePayload : scrutineeGenerator.payload scope}
    {scrutineeChildren :
      RawTermChildren scrutineeGenerator.binderShifts scope}
    (slotHolds : (scopedChildAt? spine.toScopedChildren primarySpec.slot).bind
        ScopedChild.atShiftZero?
      = some (.mkGen scrutineeGenerator scrutineePayload scrutineeChildren)) :
    scrutineeGenerator = primarySpec.head := by
  have allFire := rule.firesOn?_some_scrutineesFire fires
  rw [specsShape] at allFire
  have specFires : rule.scrutineeSpecFires spine primarySpec = true :=
    (andEqTrueSplit allFire).1
  exact rule.scrutineeSpecFires_extractsHead specFires slotHolds


/-! ## Freed-subject inversion + the accessibility successor -/

/-- **Table-step inversion at a known cell**: a table step out of
`.mkGen gen payload children` is either a ROW FIRING (the row, its
membership, and the firing surfaced together with the cell
identification) or a CHILD CONGRUENCE.  Freed-subject form — the
derivation cases stay index-clean; consumers at a concrete head
discriminate the first disjunct by head extraction. -/
theorem StepOverTable.invertOrCong
    {table : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (tableStep : StepOverTable table source target)
    {gen : Generator} {payload : gen.payload scope}
    {children : RawTermChildren gen.binderShifts scope}
    (sourceShape : source = .mkGen gen payload children) :
    (∃ (rule : IotaRuleDesc) (_ : rule ∈ table)
        (elimPayload : rule.elimGenerator.payload scope)
        (spine : RawTermChildren rule.elimGenerator.binderShifts scope),
        RawTerm.mkGen rule.elimGenerator elimPayload spine
            = RawTerm.mkGen gen payload children
        ∧ rule.firesOn? elimPayload spine = some target)
    ∨ (∃ children', target = .mkGen gen payload children'
        ∧ StepOverTableChildren table children children') := by
  cases tableStep with
  | tableRedex isRow elimPayload fires =>
      exact Or.inl ⟨_, isRow, elimPayload, _, sourceShape, fires⟩
  | cong congGen congPayload childrenStep =>
      have headsAgree : congGen = gen := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        sourceShape
      subst headsAgree
      injection sourceShape with _scopeRefl _genRefl payloadEq childrenEq
      subst payloadEq
      subst childrenEq
      exact Or.inr ⟨_, rfl, childrenStep⟩

/-- Accessibility successor for a table relation: `laterTerm` is below
`earlierTerm` when `earlierTerm` table-contracts to it (mirrors
`IotaStep.successor`). -/
def StepOverTable.successorOver (table : List IotaRuleDesc) {scope : Nat}
    (laterTerm earlierTerm : RawTerm scope) : Prop :=
  StepOverTable table earlierTerm laterTerm

/-! ## The honesty ledger: the table-native row is LIVE -/

/-- Endpoint-β FIRES in the full-table relation — a root `StepTable`
step with NO bespoke `Step` constructor: the first table-native rule,
operationally live ahead of the IOTA-T9 canonicality flip. -/
theorem StepTable.pathBetaFires {scope : Nat}
    (body : RawTerm (scope + 1)) (arg : RawTerm scope) :
    StepTable
      (.mkGen .gen_pathApp ()
        (.childCons (.mkGen .gen_pathLam () (.childCons body .childNil))
          (.childCons arg .childNil)))
      (RawTerm.subst0 body arg) :=
  .tableRedex pathBetaIotaRow_memTable () rfl

end FX1Poly.Core
