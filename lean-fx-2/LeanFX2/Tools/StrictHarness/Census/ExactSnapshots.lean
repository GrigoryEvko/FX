import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census.ModeDiscipline
import LeanFX2.Tools.StrictHarness.Census.SemanticSignature
import LeanFX2.Tools.StrictHarness.Census.RichSchemaLinkage

/-! # LeanFX2.Tools.StrictHarness.Census.ExactSnapshots

Exact constructor-name snapshots for the small, high-risk semantic
debt classes.  Count-only budgets miss the substitution pattern where
one bad constructor is repaired while a new bad constructor appears in
the same class.  These snapshots pin the names so any replacement debt
requires an explicit harness update.

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Exact semantic-debt snapshots

The budget gates above prevent debt counts from growing.  Count-only
budgets still miss a dangerous substitution pattern: one known bad
constructor can be repaired while a new bad constructor appears in the
same class, keeping the total count unchanged.  These snapshot gates pin
the exact constructor names for the small, high-risk semantic debt
classes so any replacement debt requires an explicit harness update.
-/

/-- Extract constructor names from signature-debt records. -/
def signatureDebtConstructorNames
    (records : Array SignatureDebtRecord) :
    Array Name :=
  records.map (fun record => record.constructorName)

/-- Render a constructor-name array compactly for error messages. -/
def formatNameArray (names : Array Name) : String :=
  "[" ++ String.intercalate ", " (names.toList.map toString) ++ "]"

/-- Order-sensitive equality for constructor-name arrays.  Constructor
collectors walk the inductive in declaration order, so an ordering change is
also useful signal during review. -/
def nameArraysEqual (leftNames rightNames : Array Name) : Bool :=
  leftNames.size == rightNames.size &&
    (leftNames.toList.zip rightNames.toList).all
      (fun (namePair : Name × Name) => namePair.1 == namePair.2)

/-- Build-failing exact snapshot for a small semantic-debt class. -/
def assertExactDebtSnapshot
    (snapshotName : String) (auditCountName : Name)
    (actualNames expectedNames : Array Name) :
    CommandElabM Unit := do
  recordAuditCount auditCountName actualNames.size
  if nameArraysEqual actualNames expectedNames then
    logInfo
      (s!"{snapshotName} exact snapshot ok " ++
      s!"({actualNames.size} constructors)")
  else
    throwError
      (s!"{snapshotName} exact snapshot FAILED\n" ++
      s!"  actual:   {formatNameArray actualNames}\n" ++
      s!"  expected: {formatNameArray expectedNames}")

/-- Expected current Term constructors with missing mode premises. -/
def expectedTermModeDebtNames : Array Name := #[]

/-- Expected current fixed-motive eliminator constructors.  `Term.boolElim`
was refactored to a dependent motive family `Ty level (scope + 1)` in commit
db1b88d ("Restore LeanFX2 build and strict audit"); the heuristic in
`hasFixedMotiveTypeBinder` recognises the extended-scope motive shape and
excludes it from this debt list. -/
def expectedTermDependentMotiveDebtNames : Array Name := #[
  `LeanFX2.Term.natElim,
  `LeanFX2.Term.natRec,
  `LeanFX2.Term.listElim,
  `LeanFX2.Term.optionMatch,
  `LeanFX2.Term.eitherMatch,
  `LeanFX2.Term.idJ,
  `LeanFX2.Term.oeqJ,
  `LeanFX2.Term.idStrictRec
]

/-- Expected current constructors with unit-typed proof/tag placeholders. -/
def expectedTermUnitPlaceholderDebtNames : Array Name := #[
  `LeanFX2.Term.refineIntro
]

/-- Expected current modal constructors whose type signatures are no-ops. -/
def expectedTermModalNoopDebtNames : Array Name := #[
  `LeanFX2.Term.modIntro,
  `LeanFX2.Term.modElim,
  `LeanFX2.Term.subsume
]

/-- Expected current session constructors without protocol advancement. -/
def expectedTermSessionNoAdvanceDebtNames : Array Name := #[
  `LeanFX2.Term.sessionSend,
  `LeanFX2.Term.sessionRecv
]

/-- Expected current equivalence constructors without coherence witnesses. -/
def expectedTermEquivCoherenceDebtNames : Array Name := #[]

/-- Expected current transport constructor with unlinked universe endpoints. -/
def expectedTermTransportLinkageDebtNames : Array Name := #[
  `LeanFX2.Term.transp
]

/-- Expected current Glue constructors without rich boundary/equiv schema. -/
def expectedTermGlueSchemaDebtNames : Array Name := #[
  `LeanFX2.Term.glueIntro,
  `LeanFX2.Term.glueElim
]

/-- Expected current effect constructor without row-membership schema. -/
def expectedTermEffectSchemaDebtNames : Array Name := #[
]

/-- Expected current session constructors without protocol schema. -/
def expectedTermSessionSchemaDebtNames : Array Name := #[
  `LeanFX2.Term.sessionSend,
  `LeanFX2.Term.sessionRecv
]

/-- Expected current hcomp constructor without Kan-boundary evidence. -/
def expectedTermHcompKanDebtNames : Array Name := #[
  `LeanFX2.Term.hcomp
]

/-- Exact snapshots for the small high-risk Term semantic-debt classes. -/
elab "#assert_term_semantic_debt_snapshots " inductiveSyntax:ident :
    command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  assertExactDebtSnapshot "Term mode-discipline debt"
    `term_mode_discipline_snapshot
    (modeDisciplineDebtRecordsForInductive environment inductiveName |>.map
      (fun record => record.constructorName))
    expectedTermModeDebtNames
  assertExactDebtSnapshot "Term dependent-motive debt"
    `term_dependent_motive_snapshot
    (dependentEliminatorDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermDependentMotiveDebtNames
  assertExactDebtSnapshot "Term unit-placeholder debt"
    `term_unit_placeholder_snapshot
    (unitPlaceholderDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermUnitPlaceholderDebtNames
  assertExactDebtSnapshot "Term modal-noop debt"
    `term_modal_noop_snapshot
    (modalNoopDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermModalNoopDebtNames
  assertExactDebtSnapshot "Term session no-advance debt"
    `term_session_no_advance_snapshot
    (sessionNoAdvanceDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermSessionNoAdvanceDebtNames
  assertExactDebtSnapshot "Term equiv-coherence debt"
    `term_equiv_coherence_snapshot
    (equivCoherenceDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermEquivCoherenceDebtNames
  assertExactDebtSnapshot "Term transport-linkage debt"
    `term_transport_linkage_snapshot
    (transportLinkageDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermTransportLinkageDebtNames
  assertExactDebtSnapshot "Term Glue-schema debt"
    `term_glue_schema_snapshot
    (glueSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermGlueSchemaDebtNames
  assertExactDebtSnapshot "Term effect-schema debt"
    `term_effect_schema_snapshot
    (effectSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermEffectSchemaDebtNames
  assertExactDebtSnapshot "Term session-schema debt"
    `term_session_schema_snapshot
    (sessionSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermSessionSchemaDebtNames
  assertExactDebtSnapshot "Term hcomp-Kan debt"
    `term_hcomp_kan_snapshot
    (hcompKanDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermHcompKanDebtNames

/-- Expected current Ty constructors whose endpoints remain raw. -/
def expectedTyRawEndpointDebtNames : Array Name := #[
  `LeanFX2.Ty.id,
  `LeanFX2.Ty.path,
  `LeanFX2.Ty.oeq,
  `LeanFX2.Ty.idStrict
]

/-- Expected current Ty constructors with unstructured schema payloads. -/
def expectedTyUnstructuredSchemaDebtNames : Array Name := #[
  `LeanFX2.Ty.glue,
  `LeanFX2.Ty.refine,
  `LeanFX2.Ty.session,
  `LeanFX2.Ty.effect,
  `LeanFX2.Ty.modal
]

/-- Exact snapshots for the small high-risk Ty schema-debt classes. -/
elab "#assert_ty_schema_debt_snapshots " inductiveSyntax:ident :
    command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  assertExactDebtSnapshot "Ty raw-endpoint debt"
    `ty_raw_endpoint_snapshot
    (tyRawEndpointDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTyRawEndpointDebtNames
  assertExactDebtSnapshot "Ty unstructured-schema debt"
    `ty_unstructured_schema_snapshot
    (tyUnstructuredSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTyUnstructuredSchemaDebtNames

end LeanFX2.Tools
