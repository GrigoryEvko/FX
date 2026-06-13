import FX1Poly.Core.StepOverTable
import FX1Poly.Core.RawIotaFullStepSN

/-! # IotaTableOrientedSN — IOTA-T8 Tier-2: the SN tier of the rule table

The tiered-guarantee ledger for `iotaRuleTable`.  Tier-1 (equivariance,
structural SR, deterministic firing, disjointness, orthogonal
confluence) is unconditional and shipped in IOTA-T2..T6.  THIS file is
Tier-2: **strong normalization for the decidably-classified oriented
sub-table** — and the honest refusal to promise SN for the rows that
fail the classifier.

Two independent decidable legs, both syntactic checks on the row's
reduct template:

  * `IotaRuleDesc.isStructurallyRecursive` (shipped at IOTA-T0): every
    recursive reassembly feeds scrutinee slots only with immediate
    scrutinee-CHILD projections;
  * `IotaRuleDesc.hasSubstitutionFreeReduct` (HERE): the reduct
    template contains NO substitution node — none of the four `subst…`
    shapes and neither motive instantiation.

Their conjunction `isRpoOrientable` carves out exactly the 14 rows
whose firings are `IotaOrientedHeadStep` arms, and the congruence
closure of those rows — `StepOverTable orientedIotaRuleTable` — embeds
into the shipped `IotaStep`, inheriting `iotaFullStep_wellFounded`'s
recursive-path-order SN **wholesale**: a future row that passes the
classifier joins the oriented table and inherits SN by re-deciding two
`rfl` certificates, no new termination proof.

The classifier honestly REJECTS:

  * `betaIotaRow` / `pathBetaIotaRow` — β-reducts are substitution
    instances; raw β is NOT SN (Omega), so the table must not promise
    it.  β-SN stays at the Tait-imported typed boundary.
  * `natElimSuccIotaRow` / `natRecSuccIotaRow` — the Phase-Z
    substituting succ-iotas (`substPair` of motive-shaped step cases);
    excluded from the bespoke oriented relation by the SAME split
    (`isNatRecursorSuccRedex`), so the table classifier and the bespoke
    guard agree row-for-row.
  * `nonStructuralReassemblyDemoRule` — substitution-FREE but
    non-structural (whole-scrutinee feedback, the fixpoint shape):
    demonstrates the legs are independent and BOTH are needed.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditIotaTableOrientedSN.lean`. -/

namespace FX1Poly.Core

/-! ## The substitution-freedom classifier (the second Tier-2 leg) -/

mutual

/-- The reduct builds NO substitution instance: none of the four
`subst…` template nodes and neither motive instantiation (motive
instantiation IS `subst0`/`substPair` into the motive spine child).
A substitution-free reduct erases to a rose tree assembled from spine
and scrutinee subterms plus fresh cells only — exactly the shape the
iota recursive path order orients. -/
def ReductTemplate.avoidsSubstitution : ReductTemplate → Bool
  | .boundVarAt _ => true
  | .spineChildAt _ => true
  | .scrutineeChildAt _ _ => true
  | .theScrutineeAt _ => true
  | .motiveInstantiatedWith _ => false
  | .motiveInstantiatedWithPair _ _ => false
  | .builtGen _ _ childTemplates => childTemplates.avoidsSubstitution
  | .reassembledReplacing replacements => replacements.avoidSubstitution
  | .substOneIntoSpineChild _ _ => false
  | .substOneIntoScrutineeChild _ _ _ => false
  | .substPairIntoSpineChild _ _ _ => false
  | .substPairIntoScrutineeChild _ _ _ _ => false

/-- Spine-wise conjunction of the substitution-freedom check. -/
def ReductTemplateSpine.avoidsSubstitution : ReductTemplateSpine → Bool
  | .spineNil => true
  | .spineCons childTemplate restTemplates =>
      childTemplate.avoidsSubstitution && restTemplates.avoidsSubstitution

/-- Replacement-wise conjunction of the substitution-freedom check. -/
def SpineReplacements.avoidSubstitution : SpineReplacements → Bool
  | .replaceNil => true
  | .replaceCons _ replacementTemplate restReplacements =>
      replacementTemplate.avoidsSubstitution
        && restReplacements.avoidSubstitution

end

/-- The row's reduct template is substitution-free. -/
def IotaRuleDesc.hasSubstitutionFreeReduct (rule : IotaRuleDesc) : Bool :=
  rule.target.avoidsSubstitution

/-- **The Tier-2 classifier**: the row is orientable by the iota
recursive path order — every recursive reassembly is structural
(immediate scrutinee-child projections at scrutinee slots) AND the
reduct is substitution-free.  Rows passing this check join
`orientedIotaRuleTable` and inherit SN generically. -/
def IotaRuleDesc.isRpoOrientable (rule : IotaRuleDesc) : Bool :=
  rule.isStructurallyRecursive && rule.hasSubstitutionFreeReduct

/-! ## Per-row verdict pins — the 18 shipped rows -/

/-- The 14 oriented rows, pinned one by one. -/
theorem boolTrueIotaRow_isRpoOrientable :
    boolTrueIotaRow.isRpoOrientable = true := rfl
theorem boolFalseIotaRow_isRpoOrientable :
    boolFalseIotaRow.isRpoOrientable = true := rfl
theorem fstPairIotaRow_isRpoOrientable :
    fstPairIotaRow.isRpoOrientable = true := rfl
theorem sndPairIotaRow_isRpoOrientable :
    sndPairIotaRow.isRpoOrientable = true := rfl
theorem natElimZeroIotaRow_isRpoOrientable :
    natElimZeroIotaRow.isRpoOrientable = true := rfl
theorem natRecZeroIotaRow_isRpoOrientable :
    natRecZeroIotaRow.isRpoOrientable = true := rfl
theorem listElimNilIotaRow_isRpoOrientable :
    listElimNilIotaRow.isRpoOrientable = true := rfl
theorem listElimConsIotaRow_isRpoOrientable :
    listElimConsIotaRow.isRpoOrientable = true := rfl
theorem optionMatchNoneIotaRow_isRpoOrientable :
    optionMatchNoneIotaRow.isRpoOrientable = true := rfl
theorem optionMatchSomeIotaRow_isRpoOrientable :
    optionMatchSomeIotaRow.isRpoOrientable = true := rfl
theorem eitherMatchInlIotaRow_isRpoOrientable :
    eitherMatchInlIotaRow.isRpoOrientable = true := rfl
theorem eitherMatchInrIotaRow_isRpoOrientable :
    eitherMatchInrIotaRow.isRpoOrientable = true := rfl
theorem idJReflIotaRow_isRpoOrientable :
    idJReflIotaRow.isRpoOrientable = true := rfl
theorem idStrictRecReflIotaRow_isRpoOrientable :
    idStrictRecReflIotaRow.isRpoOrientable = true := rfl

/-- β substitutes — the table does NOT promise SN for it (Omega
exists at the raw layer; β-SN is the Tait-imported typed boundary). -/
theorem betaIotaRow_isNotRpoOrientable :
    betaIotaRow.isRpoOrientable = false := rfl

/-- Endpoint-β substitutes — same honest refusal as β. -/
theorem pathBetaIotaRow_isNotRpoOrientable :
    pathBetaIotaRow.isRpoOrientable = false := rfl

/-- The substituting succ-iota: structurally recursive but NOT
substitution-free — the classifier split matches the bespoke
`isNatRecursorSuccRedex` source guard row-for-row. -/
theorem natElimSuccIotaRow_isNotRpoOrientable :
    natElimSuccIotaRow.isRpoOrientable = false := rfl
theorem natRecSuccIotaRow_isNotRpoOrientable :
    natRecSuccIotaRow.isRpoOrientable = false := rfl

/-- The succ-iota fails on the substitution leg specifically. -/
theorem natElimSuccIotaRow_substitutes :
    natElimSuccIotaRow.hasSubstitutionFreeReduct = false := rfl

/-- The fixpoint-shaped demo rule fails on the OTHER leg: its reduct is
substitution-free, yet the whole-scrutinee feedback loop flunks the
structural-recursion check — the two legs are independent and both are
needed before the table promises SN. -/
theorem nonStructuralReassemblyDemoRule_avoidsSubstitution :
    nonStructuralReassemblyDemoRule.hasSubstitutionFreeReduct = true := rfl
theorem nonStructuralReassemblyDemoRule_isNotRpoOrientable :
    nonStructuralReassemblyDemoRule.isRpoOrientable = false := rfl

/-! ## The tier ledger -/

/-- The per-row Tier-2 ledger over the FULL 21-row table, in table
order. -/
def iotaTableTierLedger : List Bool :=
  iotaRuleTable.map IotaRuleDesc.isRpoOrientable

/-- The pinned ledger: β, the two substituting succ-iotas, and
endpoint-β are the ONLY rows outside the SN tier — the three IOTA-T10
demo rows (substitution-free built applications) land IN the tier. -/
theorem iotaTableTierLedger_pinned :
    iotaTableTierLedger =
      [ false
      , true, true, true, true, true, true
      , false, false
      , true, true, true, true, true, true, true, true
      , false
      , true, true, true ] := rfl

/-! ## The oriented sub-table -/

/-- The 14 RPO-orientable LEGACY rows, in table order — the sub-table
whose congruence closure is strongly normalizing via the bespoke
`IotaHeadStep` RPO embedding.  Table-NATIVE orientable rows (the
IOTA-T10 demo rows pass `isRpoOrientable` too) are NOT here: the RPO
embedding routes through the bespoke head-step inductive, which has
no constructors for table-native rules by design — their oriented SN
awaits the table-generic RPO (no bespoke arms will be added for
them). -/
def orientedIotaRuleTable : List IotaRuleDesc :=
  [ boolTrueIotaRow, boolFalseIotaRow
  , fstPairIotaRow, sndPairIotaRow
  , natElimZeroIotaRow, natRecZeroIotaRow
  , listElimNilIotaRow, listElimConsIotaRow
  , optionMatchNoneIotaRow, optionMatchSomeIotaRow
  , eitherMatchInlIotaRow, eitherMatchInrIotaRow
  , idJReflIotaRow, idStrictRecReflIotaRow ]

/-- Stale-count guard: 14 oriented rows. -/
theorem orientedIotaRuleTable_length : orientedIotaRuleTable.length = 14 := rfl

/-- The oriented table IS the classifier's filter of the LEGACY table
— the membership criterion is the decidable check, definitionally
(the bespoke-RPO-embeddable fragment; table-native orientable rows
are tracked by the full-table tier ledger above). -/
theorem orientedIotaRuleTable_eq_filter :
    legacyIotaRuleTable.filter IotaRuleDesc.isRpoOrientable
      = orientedIotaRuleTable := rfl

/-- Every oriented row passes the classifier (the companion `rfl`
certificate). -/
theorem orientedRows_areRpoOrientable :
    orientedIotaRuleTable.all IotaRuleDesc.isRpoOrientable = true := rfl

/-- Every oriented row is a full-table row — 14-way membership
dispatch into the legacy witnesses. -/
theorem orientedRow_memFullTable {rule : IotaRuleDesc}
    (isOriented : rule ∈ orientedIotaRuleTable) : rule ∈ iotaRuleTable := by
  cases isOriented with
  | head => exact legacyRow_memFullTable boolTrueIotaRow_memLegacy
  | tail _ isOriented => cases isOriented with
    | head => exact legacyRow_memFullTable boolFalseIotaRow_memLegacy
    | tail _ isOriented => cases isOriented with
      | head => exact legacyRow_memFullTable fstPairIotaRow_memLegacy
      | tail _ isOriented => cases isOriented with
        | head => exact legacyRow_memFullTable sndPairIotaRow_memLegacy
        | tail _ isOriented => cases isOriented with
          | head => exact legacyRow_memFullTable natElimZeroIotaRow_memLegacy
          | tail _ isOriented => cases isOriented with
            | head => exact legacyRow_memFullTable natRecZeroIotaRow_memLegacy
            | tail _ isOriented => cases isOriented with
              | head =>
                  exact legacyRow_memFullTable listElimNilIotaRow_memLegacy
              | tail _ isOriented => cases isOriented with
                | head =>
                    exact legacyRow_memFullTable listElimConsIotaRow_memLegacy
                | tail _ isOriented => cases isOriented with
                  | head =>
                      exact legacyRow_memFullTable
                        optionMatchNoneIotaRow_memLegacy
                  | tail _ isOriented => cases isOriented with
                    | head =>
                        exact legacyRow_memFullTable
                          optionMatchSomeIotaRow_memLegacy
                    | tail _ isOriented => cases isOriented with
                      | head =>
                          exact legacyRow_memFullTable
                            eitherMatchInlIotaRow_memLegacy
                      | tail _ isOriented => cases isOriented with
                        | head =>
                            exact legacyRow_memFullTable
                              eitherMatchInrIotaRow_memLegacy
                        | tail _ isOriented => cases isOriented with
                          | head =>
                              exact legacyRow_memFullTable
                                idJReflIotaRow_memLegacy
                          | tail _ isOriented => cases isOriented with
                            | head =>
                                exact legacyRow_memFullTable
                                  idStrictRecReflIotaRow_memLegacy
                            | tail _ isOriented => cases isOriented

/-! ## Per-row firing inversions into the ORIENTED head step

Same skeletons as the `<row>FiringToStep` family (StepTable.lean), but
landing in `IotaOrientedHeadStep`: the bespoke head-iota arm PLUS the
`isNatRecursorSuccRedex = false` source guard, which computes to `rfl`
on every oriented row's redex shape (non-recursor heads refute both
guard branches; the `natZero` scrutinees refute the `natSucc` head
test). -/

theorem boolTrueRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : boolTrueIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren boolTrueIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : boolTrueIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen boolTrueIotaRow.elimGenerator elimPayload spine) reduct := by
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
            exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaBoolTrue, rfl⟩

theorem boolFalseRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : boolFalseIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren boolFalseIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : boolFalseIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen boolFalseIotaRow.elimGenerator elimPayload spine) reduct := by
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
            exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaBoolFalse, rfl⟩

theorem fstPairRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : fstPairIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren fstPairIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : fstPairIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen fstPairIotaRow.elimGenerator elimPayload spine) reduct := by
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
          exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaFstPair, rfl⟩

theorem sndPairRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : sndPairIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren sndPairIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : sndPairIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen sndPairIotaRow.elimGenerator elimPayload spine) reduct := by
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
          exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaSndPair, rfl⟩

theorem natElimZeroRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : natElimZeroIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natElimZeroIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natElimZeroIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen natElimZeroIotaRow.elimGenerator elimPayload spine) reduct := by
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
            exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaNatElimZero, rfl⟩

theorem natRecZeroRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : natRecZeroIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natRecZeroIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natRecZeroIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen natRecZeroIotaRow.elimGenerator elimPayload spine) reduct := by
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
            exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaNatRecZero, rfl⟩

theorem listElimNilRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : listElimNilIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren listElimNilIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : listElimNilIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen listElimNilIotaRow.elimGenerator elimPayload spine) reduct := by
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
            exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaListElimNil, rfl⟩

theorem listElimConsRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : listElimConsIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren listElimConsIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : listElimConsIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen listElimConsIotaRow.elimGenerator elimPayload spine) reduct := by
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
                exact
                  ⟨Option.some.inj fires ▸ IotaHeadStep.iotaListElimCons, rfl⟩

theorem optionMatchNoneRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : optionMatchNoneIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren optionMatchNoneIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : optionMatchNoneIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen optionMatchNoneIotaRow.elimGenerator elimPayload spine)
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
            exact
              ⟨Option.some.inj fires ▸ IotaHeadStep.iotaOptionMatchNone, rfl⟩

theorem optionMatchSomeRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : optionMatchSomeIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren optionMatchSomeIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : optionMatchSomeIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen optionMatchSomeIotaRow.elimGenerator elimPayload spine)
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
              exact
                ⟨Option.some.inj fires ▸ IotaHeadStep.iotaOptionMatchSome, rfl⟩

theorem eitherMatchInlRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : eitherMatchInlIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren eitherMatchInlIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : eitherMatchInlIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen eitherMatchInlIotaRow.elimGenerator elimPayload spine)
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
              exact
                ⟨Option.some.inj fires ▸ IotaHeadStep.iotaEitherMatchInl, rfl⟩

theorem eitherMatchInrRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : eitherMatchInrIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren eitherMatchInrIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : eitherMatchInrIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen eitherMatchInrIotaRow.elimGenerator elimPayload spine)
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
              exact
                ⟨Option.some.inj fires ▸ IotaHeadStep.iotaEitherMatchInr, rfl⟩

theorem idJReflRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : idJReflIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren idJReflIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : idJReflIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen idJReflIotaRow.elimGenerator elimPayload spine) reduct := by
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
            exact ⟨Option.some.inj fires ▸ IotaHeadStep.iotaIdJRefl, rfl⟩

theorem idStrictRecReflRowFiringToOrientedHeadStep {scope : Nat}
    (elimPayload : idStrictRecReflIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren idStrictRecReflIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires :
      idStrictRecReflIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen idStrictRecReflIotaRow.elimGenerator elimPayload spine)
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
            exact
              ⟨Option.some.inj fires ▸ IotaHeadStep.iotaIdStrictRecRefl, rfl⟩

/-- The oriented root dispatcher: a firing of ANY oriented row is an
`IotaOrientedHeadStep` — 14-way membership dispatch into the per-row
inversions. -/
theorem orientedRootFiringToOrientedHeadStep {scope : Nat}
    {rule : IotaRuleDesc} (isRow : rule ∈ orientedIotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    IotaOrientedHeadStep
      (.mkGen rule.elimGenerator elimPayload spine) reduct := by
  cases isRow with
  | head => exact boolTrueRowFiringToOrientedHeadStep elimPayload fires
  | tail _ isRow => cases isRow with
    | head => exact boolFalseRowFiringToOrientedHeadStep elimPayload fires
    | tail _ isRow => cases isRow with
      | head => exact fstPairRowFiringToOrientedHeadStep elimPayload fires
      | tail _ isRow => cases isRow with
        | head => exact sndPairRowFiringToOrientedHeadStep elimPayload fires
        | tail _ isRow => cases isRow with
          | head =>
              exact natElimZeroRowFiringToOrientedHeadStep elimPayload fires
          | tail _ isRow => cases isRow with
            | head =>
                exact natRecZeroRowFiringToOrientedHeadStep elimPayload fires
            | tail _ isRow => cases isRow with
              | head =>
                  exact listElimNilRowFiringToOrientedHeadStep
                    elimPayload fires
              | tail _ isRow => cases isRow with
                | head =>
                    exact listElimConsRowFiringToOrientedHeadStep
                      elimPayload fires
                | tail _ isRow => cases isRow with
                  | head =>
                      exact optionMatchNoneRowFiringToOrientedHeadStep
                        elimPayload fires
                  | tail _ isRow => cases isRow with
                    | head =>
                        exact optionMatchSomeRowFiringToOrientedHeadStep
                          elimPayload fires
                    | tail _ isRow => cases isRow with
                      | head =>
                          exact eitherMatchInlRowFiringToOrientedHeadStep
                            elimPayload fires
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact eitherMatchInrRowFiringToOrientedHeadStep
                              elimPayload fires
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact idJReflRowFiringToOrientedHeadStep
                                elimPayload fires
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact
                                  idStrictRecReflRowFiringToOrientedHeadStep
                                    elimPayload fires
                            | tail _ isRow => cases isRow

/-! ## The embedding into the shipped oriented-iota closure -/

mutual

/-- `StepOverTable orientedIotaRuleTable ⊆ IotaStep` — every oriented
table step is a step of the bespoke RPO-oriented closure: root firings
via the dispatcher, congruence arm-for-arm. -/
theorem orientedTableStepToIotaStep {scope : Nat}
    {source target : RawTerm scope}
    (tableStep : StepOverTable orientedIotaRuleTable source target) :
    IotaStep source target :=
  match tableStep with
  | .tableRedex isRow elimPayload fires =>
      .head (orientedRootFiringToOrientedHeadStep isRow elimPayload fires)
  | .cong gen payload childStep =>
      .cong gen payload (orientedTableChildrenToIotaStepChildren childStep)

/-- Spine companion of `orientedTableStepToIotaStep`. -/
theorem orientedTableChildrenToIotaStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep :
      StepOverTableChildren orientedIotaRuleTable children children') :
    IotaStepChildren children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (orientedTableStepToIotaStep headStep)
  | .there head restStep =>
      .there head (orientedTableChildrenToIotaStepChildren restStep)

end

/-- Every oriented-table step is a bespoke kernel `Step` — soundness
composed through `IotaStep.toStep`. -/
theorem orientedTableStepToStep {scope : Nat} {source target : RawTerm scope}
    (tableStep : StepOverTable orientedIotaRuleTable source target) :
    Step source target :=
  (orientedTableStepToIotaStep tableStep).toStep

/-! ## ★ Strong normalization of the oriented table -/

/-- **★ The oriented 14-row table relation is strongly normalizing** —
inherited WHOLESALE from `iotaFullStep_wellFounded` through the
embedding: one recursive path order orients every row that passes the
Tier-2 classifier, including all congruence positions.  A future
classifier-passing row extends `orientedIotaRuleTable` and lands under
this same theorem with NO new termination argument. -/
theorem stepOverOrientedTable_wellFounded {scope : Nat} :
    WellFounded
      (StepOverTable.successorOver orientedIotaRuleTable (scope := scope)) :=
  Subrelation.wf
    (r := IotaStep.successor)
    (fun tableStep => orientedTableStepToIotaStep tableStep)
    iotaFullStep_wellFounded

/-- Every raw term is strongly normalizing for the oriented table
relation (per-term accessibility). -/
theorem orientedTableStep_isStronglyNormalizing {scope : Nat}
    (sourceTerm : RawTerm scope) :
    Acc (StepOverTable.successorOver orientedIotaRuleTable) sourceTerm :=
  stepOverOrientedTable_wellFounded.apply sourceTerm

/-! ## Non-vacuity smoke -/

/-- The oriented table relation genuinely fires:
`boolElim motive unit unit boolTrue ↝ unit` as a root `tableRedex` of
the FIRST oriented row, firing by `rfl`. -/
theorem orientedTableStep_smoke :
    StepOverTable orientedIotaRuleTable (scope := 0)
      (.mkGen .gen_boolElim ()
        (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil)
              (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))))
      (.mkGen .gen_unit () .childNil) :=
  StepOverTable.tableRedex (rule := boolTrueIotaRow) (.head _) () rfl

end FX1Poly.Core
