import FX1Poly.Core.Step
import FX1Poly.Core.IotaRuleTable

/-! # FX1Poly/Core/StepTable — the TABLE-DRIVEN reduction relation (IOTA-T1)

`StepOverTable table` is single-step reduction whose ROOT redexes are
exactly the firings of the rows of `table` (`IotaRuleDesc.firesOn?`),
closed under the same uniform child congruence as `Step`.  The relation
is PARAMETERIZED by the table — the RW-5 keystone shape — so the
canonical instances are just table choices:

  * `StepTable := StepOverTable iotaRuleTable` — the 18-row relation
    (the canonicality-flip target, IOTA-T9);
  * `StepOverTable legacyIotaRuleTable` — the 17-row restriction
    (everything except the table-native endpoint-β).

## The adequacy (both directions)

`stepOverLegacyTable_iff_step`: the legacy-table relation IS `Step`.

  * FORWARD (`Step.toLegacyTableStep`): each bespoke `Step` root
    constructor maps to its row firing BY `rfl` — the IOTA-T0 adequacy
    equations compute the firing on every redex shape.
  * BACKWARD (`StepOverTable.legacyToStep`): a root firing of a legacy
    row yields the bespoke constructor.  The generic inversion trio
    (`firesOn?_some_scrutineesFire` / `scrutineesFire_singleton_split`
    / `scrutineeSpecFires_extractsHead`) extracts the constructor head
    POSITIVELY from the firing hypothesis, so the 17 per-row inversions
    are head-substitution + spine casing + `Option.some.inj` — no
    per-row case analysis on generators.

`Step.toStepTable` (forward into the FULL table) follows by table
monotonicity (`StepOverTable.monotone`).

## The honesty ledger: StepTable strictly extends Step

`StepTable.pathBetaFires`: endpoint-β
(`pathApp (pathLam body) arg ↝ subst0 body arg`) is a ROOT step of the
18-row relation, with NO bespoke `Step` constructor — the first
table-native rule, operationally live in `StepTable` ahead of the
IOTA-T9 canonicality flip.  (The strictness witness `¬ Step` on a
closed endpoint-β redex is the flip ledger's item at IOTA-T9, where the
relation swap makes it load-bearing.)

## Zero-axiom verification

Mutual `Prop` inductives, structural mutual recursion on derivations
(the `Step.toParStep` idiom), `dsimp only` + `dif_neg`/`if`-reduction
inversion (no `simp`, no eqn-lemma generation on the big matchers), and
hand-rolled list lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditStepTable.lean`.
-/

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

/-! ## FORWARD adequacy: every bespoke Step is a legacy-table step

Each root arm is the row firing BY `rfl` — the IOTA-T0 adequacy
equations compute `firesOn?` on every redex shape. -/

mutual

/-- `Step ⊆ StepOverTable legacyIotaRuleTable` — the forward half of
the IOTA-T1 adequacy.  Each bespoke root constructor maps to a
`tableRedex` whose firing equation closes definitionally. -/
theorem Step.toLegacyTableStep {scope : Nat} {source target : RawTerm scope} :
    Step source target → StepOverTable legacyIotaRuleTable source target
  | .beta => .tableRedex betaIotaRow_memLegacy () rfl
  | .cong gen payload childStep =>
      .cong gen payload (StepChildren.toLegacyTableStepChildren childStep)
  | .iotaBoolTrue => .tableRedex boolTrueIotaRow_memLegacy () rfl
  | .iotaBoolFalse => .tableRedex boolFalseIotaRow_memLegacy () rfl
  | .iotaFstPair => .tableRedex fstPairIotaRow_memLegacy () rfl
  | .iotaSndPair => .tableRedex sndPairIotaRow_memLegacy () rfl
  | .iotaNatElimZero => .tableRedex natElimZeroIotaRow_memLegacy () rfl
  | .iotaNatRecZero => .tableRedex natRecZeroIotaRow_memLegacy () rfl
  | .iotaListElimNil => .tableRedex listElimNilIotaRow_memLegacy () rfl
  | .iotaOptionMatchNone => .tableRedex optionMatchNoneIotaRow_memLegacy () rfl
  | .iotaOptionMatchSome => .tableRedex optionMatchSomeIotaRow_memLegacy () rfl
  | .iotaEitherMatchInl => .tableRedex eitherMatchInlIotaRow_memLegacy () rfl
  | .iotaEitherMatchInr => .tableRedex eitherMatchInrIotaRow_memLegacy () rfl
  | .iotaNatElimSucc => .tableRedex natElimSuccIotaRow_memLegacy () rfl
  | .iotaNatRecSucc => .tableRedex natRecSuccIotaRow_memLegacy () rfl
  | .iotaListElimCons => .tableRedex listElimConsIotaRow_memLegacy () rfl
  | .iotaIdJRefl => .tableRedex idJReflIotaRow_memLegacy () rfl
  | .iotaIdStrictRecRefl => .tableRedex idStrictRecReflIotaRow_memLegacy () rfl

/-- Spine companion of `Step.toLegacyTableStep`. -/
theorem StepChildren.toLegacyTableStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope} :
    StepChildren children children' →
    StepOverTableChildren legacyIotaRuleTable children children'
  | .here rest childStep => .here rest (Step.toLegacyTableStep childStep)
  | .there head restStep =>
      .there head (StepChildren.toLegacyTableStepChildren restStep)

end

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

/-! ## BACKWARD adequacy: each legacy row's firing is the bespoke Step

17 per-row root inversions: case the spine into its concrete children,
extract the constructor head POSITIVELY from the firing, substitute,
case the scrutinee's children — at which point the firing equation
computes and `Option.some.inj` delivers the reduct identification. -/

theorem betaRowFiringToStep {scope : Nat}
    (elimPayload : betaIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren betaIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : betaIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen betaIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons functionChild restSpine =>
    cases restSpine with
    | childCons argumentChild restNil =>
      cases restNil
      cases functionChild with
      | mkGen functionGenerator functionPayload functionChildren =>
        intro fires
        have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
        subst isHead
        cases functionChildren with
        | childCons domainAnn lamRest =>
          cases lamRest with
          | childCons lamBody lamNil =>
            cases lamNil
            exact Option.some.inj fires ▸ Step.beta

theorem boolTrueRowFiringToStep {scope : Nat}
    (elimPayload : boolTrueIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren boolTrueIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : boolTrueIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen boolTrueIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons thenBranch restTwo =>
      cases restTwo with
      | childCons elseBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ Step.iotaBoolTrue

theorem boolFalseRowFiringToStep {scope : Nat}
    (elimPayload : boolFalseIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren boolFalseIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : boolFalseIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen boolFalseIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons thenBranch restTwo =>
      cases restTwo with
      | childCons elseBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ Step.iotaBoolFalse

theorem fstPairRowFiringToStep {scope : Nat}
    (elimPayload : fstPairIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren fstPairIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : fstPairIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen fstPairIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons scrutineeChild restNil =>
    cases restNil
    cases scrutineeChild with
    | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      intro fires
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineeChildren with
      | childCons firstValue pairRest =>
        cases pairRest with
        | childCons secondValue pairNil =>
          cases pairNil
          exact Option.some.inj fires ▸ Step.iotaFstPair

theorem sndPairRowFiringToStep {scope : Nat}
    (elimPayload : sndPairIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren sndPairIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : sndPairIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen sndPairIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons scrutineeChild restNil =>
    cases restNil
    cases scrutineeChild with
    | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      intro fires
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineeChildren with
      | childCons firstValue pairRest =>
        cases pairRest with
        | childCons secondValue pairNil =>
          cases pairNil
          exact Option.some.inj fires ▸ Step.iotaSndPair

theorem natElimZeroRowFiringToStep {scope : Nat}
    (elimPayload : natElimZeroIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natElimZeroIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natElimZeroIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen natElimZeroIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ Step.iotaNatElimZero

theorem natRecZeroRowFiringToStep {scope : Nat}
    (elimPayload : natRecZeroIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natRecZeroIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natRecZeroIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen natRecZeroIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ Step.iotaNatRecZero

theorem natElimSuccRowFiringToStep {scope : Nat}
    (elimPayload : natElimSuccIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natElimSuccIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natElimSuccIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen natElimSuccIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons predecessor succNil =>
              cases succNil
              exact Option.some.inj fires ▸ Step.iotaNatElimSucc

theorem natRecSuccRowFiringToStep {scope : Nat}
    (elimPayload : natRecSuccIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natRecSuccIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natRecSuccIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen natRecSuccIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons predecessor succNil =>
              cases succNil
              exact Option.some.inj fires ▸ Step.iotaNatRecSucc

theorem listElimNilRowFiringToStep {scope : Nat}
    (elimPayload : listElimNilIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren listElimNilIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : listElimNilIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen listElimNilIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons nilBranch restTwo =>
      cases restTwo with
      | childCons consBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ Step.iotaListElimNil

theorem listElimConsRowFiringToStep {scope : Nat}
    (elimPayload : listElimConsIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren listElimConsIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : listElimConsIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen listElimConsIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons nilBranch restTwo =>
      cases restTwo with
      | childCons consBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons headValue consRest =>
              cases consRest with
              | childCons tailValue consNil =>
                cases consNil
                exact Option.some.inj fires ▸ Step.iotaListElimCons

theorem optionMatchNoneRowFiringToStep {scope : Nat}
    (elimPayload : optionMatchNoneIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren optionMatchNoneIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : optionMatchNoneIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen optionMatchNoneIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons noneBranch restTwo =>
      cases restTwo with
      | childCons someBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ Step.iotaOptionMatchNone

theorem optionMatchSomeRowFiringToStep {scope : Nat}
    (elimPayload : optionMatchSomeIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren optionMatchSomeIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : optionMatchSomeIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen optionMatchSomeIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons noneBranch restTwo =>
      cases restTwo with
      | childCons someBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value someNil =>
              cases someNil
              exact Option.some.inj fires ▸ Step.iotaOptionMatchSome

theorem eitherMatchInlRowFiringToStep {scope : Nat}
    (elimPayload : eitherMatchInlIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren eitherMatchInlIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : eitherMatchInlIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen eitherMatchInlIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons leftBranch restTwo =>
      cases restTwo with
      | childCons rightBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value inlNil =>
              cases inlNil
              exact Option.some.inj fires ▸ Step.iotaEitherMatchInl

theorem eitherMatchInrRowFiringToStep {scope : Nat}
    (elimPayload : eitherMatchInrIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren eitherMatchInrIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : eitherMatchInrIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen eitherMatchInrIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons leftBranch restTwo =>
      cases restTwo with
      | childCons rightBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value inrNil =>
              cases inrNil
              exact Option.some.inj fires ▸ Step.iotaEitherMatchInr

theorem idJReflRowFiringToStep {scope : Nat}
    (elimPayload : idJReflIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren idJReflIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : idJReflIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen idJReflIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons baseCase restTwo =>
      cases restTwo with
      | childCons scrutineeChild restNil =>
        cases restNil
        cases scrutineeChild with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
          intro fires
          have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
          subst isHead
          cases scrutineeChildren with
          | childCons rawWitness reflNil =>
            cases reflNil
            exact Option.some.inj fires ▸ Step.iotaIdJRefl

theorem idStrictRecReflRowFiringToStep {scope : Nat}
    (elimPayload : idStrictRecReflIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren idStrictRecReflIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires :
      idStrictRecReflIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen idStrictRecReflIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons baseCase restTwo =>
      cases restTwo with
      | childCons scrutineeChild restNil =>
        cases restNil
        cases scrutineeChild with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
          intro fires
          have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
          subst isHead
          cases scrutineeChildren with
          | childCons rawWitness reflNil =>
            cases reflNil
            exact Option.some.inj fires ▸ Step.iotaIdStrictRecRefl

/-- The root dispatcher: a firing of ANY legacy row is the bespoke
`Step` — 17-way membership dispatch into the per-row inversions. -/
theorem legacyRootFiringToStep {scope : Nat} {rule : IotaRuleDesc}
    (isRow : rule ∈ legacyIotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen rule.elimGenerator elimPayload spine) reduct := by
  cases isRow with
  | head => exact betaRowFiringToStep elimPayload fires
  | tail _ isRow => cases isRow with
    | head => exact boolTrueRowFiringToStep elimPayload fires
    | tail _ isRow => cases isRow with
      | head => exact boolFalseRowFiringToStep elimPayload fires
      | tail _ isRow => cases isRow with
        | head => exact fstPairRowFiringToStep elimPayload fires
        | tail _ isRow => cases isRow with
          | head => exact sndPairRowFiringToStep elimPayload fires
          | tail _ isRow => cases isRow with
            | head => exact natElimZeroRowFiringToStep elimPayload fires
            | tail _ isRow => cases isRow with
              | head => exact natRecZeroRowFiringToStep elimPayload fires
              | tail _ isRow => cases isRow with
                | head => exact natElimSuccRowFiringToStep elimPayload fires
                | tail _ isRow => cases isRow with
                  | head => exact natRecSuccRowFiringToStep elimPayload fires
                  | tail _ isRow => cases isRow with
                    | head =>
                        exact listElimNilRowFiringToStep elimPayload fires
                    | tail _ isRow => cases isRow with
                      | head =>
                          exact listElimConsRowFiringToStep elimPayload fires
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact optionMatchNoneRowFiringToStep
                              elimPayload fires
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact optionMatchSomeRowFiringToStep
                                elimPayload fires
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact eitherMatchInlRowFiringToStep
                                  elimPayload fires
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact eitherMatchInrRowFiringToStep
                                    elimPayload fires
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact idJReflRowFiringToStep
                                      elimPayload fires
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact idStrictRecReflRowFiringToStep
                                        elimPayload fires
                                  | tail _ isRow => cases isRow

mutual

/-- `StepOverTable legacyIotaRuleTable ⊆ Step` — the backward half of
the IOTA-T1 adequacy. -/
theorem StepOverTable.legacyToStep {scope : Nat}
    {source target : RawTerm scope}
    (tableStep : StepOverTable legacyIotaRuleTable source target) :
    Step source target :=
  match tableStep with
  | .tableRedex isRow elimPayload fires =>
      legacyRootFiringToStep isRow elimPayload fires
  | .cong gen payload childStep =>
      Step.cong gen payload
        (StepOverTableChildren.legacyToStepChildren childStep)

/-- Spine companion of `StepOverTable.legacyToStep`. -/
theorem StepOverTableChildren.legacyToStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep :
      StepOverTableChildren legacyIotaRuleTable children children') :
    StepChildren children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepOverTable.legacyToStep headStep)
  | .there head restStep =>
      .there head (StepOverTableChildren.legacyToStepChildren restStep)

end

/-! ## The headline adequacy + the canonical embedding -/

/-- ★ IOTA-T1 ADEQUACY (both directions): the legacy-table relation IS
the bespoke `Step`.  The reduction side of the kernel is faithfully
represented as DATA. -/
theorem stepOverLegacyTable_iff_step {scope : Nat}
    {source target : RawTerm scope} :
    StepOverTable legacyIotaRuleTable source target ↔ Step source target :=
  ⟨StepOverTable.legacyToStep, Step.toLegacyTableStep⟩

/-- Every bespoke `Step` is a full-table `StepTable` step (forward
through the legacy table, then table monotonicity). -/
theorem Step.toStepTable {scope : Nat} {source target : RawTerm scope}
    (sourceSteps : Step source target) : StepTable source target :=
  StepOverTable.monotone (fun isLegacy => legacyRow_memFullTable isLegacy)
    sourceSteps.toLegacyTableStep

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
