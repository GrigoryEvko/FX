import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility
import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionFormationHeadInversion
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionUnionSubstituent
import FX1Poly.Typed.Metatheory.SubjectReduction.BridgeEndpointStep
import FX1Poly.Typed.Metatheory.Validity.TypedAtUniverseFibrantlyUsable

/-! # FX1Poly/Typed/Metatheory/Validity/HasTypeUnionValidity — UNION CLASSIFIER VALIDITY

The foundational regularity lemma for the unified judgment `HasTypeUnion`: a union-typed subject's
CLASSIFIER is itself a well-formed type — it inhabits SOME universe code.  This is the union analogue of
the grown `HasTypeDescPi.classifierIsTypeDescPi` (WFG-3) and the type-correctness leg unconditional
subject reduction rests on.

## The conclusion shape

`UnionClassifierIsType profile context classifier` is the single existential
`∃ levelExpr flag, HasTypeUnion profile context classifier (universeCodeCell levelExpr flag)`.  A
universe code is folded in by self-typing: `universeCodeCell L f : universeCodeCell L.lsucc f` via the
host `universeFormation` rule (embedded by `ofGrown`), so the "is a universe code" disjunct is subsumed —
one existential carries every case.

## What closes UNCONDITIONALLY (the foundational win)

  * **conv** — `reclassifierTyped` IS the witness: `classifier` (the reclassifier) is union-typed at a
    universe code by construction.  Direct, no IH.
  * **ofGrown** — the shipped HOST validity `HasTypeDescPi.classifierIsTypeDescPi` (WFG-3, unconditional
    over `WfContextDescPi`) yields `IsTypeDescPi context classifier`; its universe witness re-embeds via
    `ofGrown`.  Uses the host well-formedness `wellFormed : WfContextDescPi context`.
  * **formationRule** (all three families) — the output classifier is ALWAYS a universe code
    (`baseRule.outputUniverse` / `flatRule.outputType = universeFormerOutput` /
    `termIndexedRule.outputType = termIndexedCarrierOutput`, all `universeCodeCell …`).  A universe code
    self-types via `universeFormation`/`ofGrown`.  No IH, no well-formedness.
  * **intro — the 7 nullary-base rows** (boolTrue / boolFalse / unit / interval0 / interval1 / natZero /
    natSucc): the output is a NULLARY base type code (`boolTypeCell` / `unitTypeCell` / `intervalTypeCell`
    / `natTypeCell`), itself formed by the `baseType` formation row at `Type@0(standard)`.  Re-formed in
    the union via `formationRule .gen_…Code`.  No IH.
  * **elim — the 6 branch-selecting rows** (natElim / natRec / boolElim / optionMatch / idJ / listElim):
    the output is `resultType`, read off `params`, and a BRANCH obligation is typed at `resultType` in the
    ORIGINAL context (natElim/natRec baseBranch, boolElim thenBranch, optionMatch noneBranch, idJ baseCase,
    listElim nilBranch).  The IH on that branch gives `resultType` inhabits a universe.

## The honest residual (clearly-named hypotheses, NOT faked)

Two row-families genuinely cannot close from the union IH alone — exactly the walls the union dissolves
elsewhere but validity cannot cross:

  * `dataIntroResidual` — the 10 COMPOSITE-data-intro rows (lam / pathLam / listCons / optionSome /
    optionNone / listNil / eitherInl / eitherInr / pair / refl).  Output is a composite data type code
    (`piTyCodeCell` / `optionTypeCell` / `listTypeCell` / `eitherTypeCell` / `productTypeCell` /
    `bridgeTypeCell` / `idTypeCell`).  Re-forming it needs a GROWN (`HasTypeDescPi`) typing of the type
    PARAMETERS — but the IH supplies only a UNION typing, and there is no union→grown reflection at
    universe codes (the fundamental wall).  Residual.
  * `substElimResidual` — the 5 SUBSTITUTING / PROJECTING / handler-typed elim rows (app / pathApp / fst /
    snd / eitherMatch).  app's output `subst0 codomainCode argument` needs a substitution-preserves-
    formation lemma; pathApp's `carrierCode`, fst/snd's component, and eitherMatch's `resultType` (whose
    branches are at handler types `A → C`, not `resultType` directly) need formation-code inversion.
    Residual.

Each residual is supplied as a hypothesis precisely typed to the row's `memberCell`/`outputType`, exactly
as `HasTypeDescPi.piElimUpToClassifierConv` pins its `classifierRespectsConv` residual — everything else
is shipped and unconditional.

## Zero-axiom

`induction` over the 5 union arms + host validity + `universeFormation`/`ofGrown` + the base-type
formation row + IH list-membership dispatch.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditHasTypeUnionValidity.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **The union classifier-validity conclusion.**  A classifier is a well-formed union type iff it
inhabits SOME universe code in the union judgment.  A universe code satisfies this by self-typing
(`universeCodeCell L f : universeCodeCell L.lsucc f`), so this one existential carries the "is a universe
code" case too. -/
def UnionClassifierIsType (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeUnion profile context classifier (universeCodeCell levelExpr flag)

/-- **A non-fibrant DIMENSION classifier** (#1886 / FIBRANCY-AXIS-0).  The named hook for the classifiers that
are pretypes-but-NOT-fibrant-types: the affine interval now (`Conv classifier intervalTypeCell`), the clock /
cohesion dimensions later (each a new disjunct, never another invariant sweep — its eventual `DimUniverse`).  A
`lockCons`-bound dimension variable is classified HERE, never at a universe code — that is the content of the
interval becoming genuinely non-fibrant. -/
def UnionClassifierIsDimension (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  Conv classifier intervalTypeCell

/-- **A well-formed PRETYPE classifier** — a fibrant type OR a non-fibrant dimension.  The honest conclusion of
the (weakened) validity invariant `HasTypeUnion.classifierIsType`: every well-typed subject's classifier is a
fibrant type (`UnionClassifierIsType`) or the interval dimension (`UnionClassifierIsDimension`).  Sites that
genuinely need FIBRANCY (Π/Σ formation re-typing, the SR closure's reclassification, a fibrant binder's
well-formedness) discharge the dimension disjunct via the `IntervalNotConvRigidHeads` family — you cannot Π/Σ
over the interval, which IS the subject-reduction fix.  The strong `UnionClassifierIsType` is kept INTACT (this
is purely additive); only the invariant's conclusion weakens to this disjunction. -/
def UnionClassifierIsPretype (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  UnionClassifierIsType profile context classifier ∨ UnionClassifierIsDimension profile context classifier

/-- The interval IS a dimension classifier (reflexivity). -/
theorem UnionClassifierIsDimension.interval {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    UnionClassifierIsDimension profile context (intervalTypeCell : RawTerm scope) :=
  Conv.refl intervalTypeCell

/-- A fibrant type is a pretype (the `Or.inl` lift). -/
theorem UnionClassifierIsType.toPretype {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : UnionClassifierIsType profile context classifier) :
    UnionClassifierIsPretype profile context classifier := Or.inl isType

/-- A dimension is a pretype (the `Or.inr` lift). -/
theorem UnionClassifierIsDimension.toPretype {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isDimension : UnionClassifierIsDimension profile context classifier) :
    UnionClassifierIsPretype profile context classifier := Or.inr isDimension

/-- The interval IS a pretype (the dimension branch). -/
theorem UnionClassifierIsPretype.interval {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    UnionClassifierIsPretype profile context (intervalTypeCell : RawTerm scope) :=
  Or.inr (UnionClassifierIsDimension.interval context)

/-- **★ Discharge the dimension disjunct.**  A pretype classifier that is NOT a dimension (not convertible to
the interval) is a FIBRANT type.  The combinator every fibrancy-needing consumer routes through: it supplies the
concrete `¬ UnionClassifierIsDimension` (= `¬ Conv classifier intervalTypeCell`, from the
`IntervalNotConvRigidHeads` family for its former's head) and recovers the strong `UnionClassifierIsType`.
Propext-free `Or` elimination. -/
theorem UnionClassifierIsPretype.resolveType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isPretype : UnionClassifierIsPretype profile context classifier)
    (notDimension : ¬ UnionClassifierIsDimension profile context classifier) :
    UnionClassifierIsType profile context classifier :=
  match isPretype with
  | Or.inl isType => isType
  | Or.inr isDimension => absurd isDimension notDimension

/-- **A universe code is a well-formed union type.**  `universeCodeCell L f` is union-typed at
`universeCodeCell L.lsucc f` by the NATIVE `universeFormation` arm (no host engine). -/
theorem UnionClassifierIsType.ofUniverseCode {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    UnionClassifierIsType profile context (universeCodeCell levelExpr flag) :=
  ⟨levelExpr.lsucc, flag, HasTypeUnion.universeFormation context levelExpr flag⟩

/-- **A nullary base type code is a well-formed union type.**  Given the base-type formation row hit, the
code `.mkGen generator () .childNil` is union-typed at the row's pinned universe `Type@0(standard)` via the
`formationRule` arm (base-type family).  The output universe is the constant `Type@0(standard)`
(`baseTypeRuleTableOutputIsType0`), so the classifier is a universe code on the nose. -/
theorem UnionClassifierIsType.ofBaseTypeRow {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (baseRule : BaseTypeRuleDesc)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (isBaseRow : formationRuleOf generator = some (FormationRule.baseType baseRule)) :
    UnionClassifierIsType profile context (.mkGen generator payload children) := by
  have isBaseType : baseTypeRuleDescOf generator = some baseRule :=
    formationRuleOf_baseType_inv isBaseRow
  refine ⟨LevelExpr.lzero, UniverseFlag.standard, ?_⟩
  have formed :
      HasTypeUnion profile context (.mkGen generator payload children)
        ((FormationRule.baseType baseRule).outputType scope [] LevelExpr.lzero
          UniverseFlag.standard) :=
    HasTypeUnion.formationRuleOfObligations context generator payload children (.baseType baseRule)
      [] (.mkGen generator payload children) LevelExpr.lzero UniverseFlag.standard isBaseRow
      (fun _obligation hmem => by cases hmem)
      (fun _obligation hmem => by cases hmem)
  have outputIsType0 :
      (FormationRule.baseType baseRule).outputType scope [] LevelExpr.lzero UniverseFlag.standard
        = universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
    show baseRule.outputUniverse scope = universeCodeCell LevelExpr.lzero UniverseFlag.standard
    rw [baseTypeRuleTableOutputIsType0 isBaseType]
  rwa [outputIsType0] at formed

/-- **Any TABLED formation-rule output is a universe code — hence a well-formed union type.**  All three
formation families emit a `universeCodeCell` once the table hit pins the rule's `outputType`: base
(`outputUniverse` pinned to `Type@0(standard)` via `baseTypeRuleTableOutputIsType0`), flat
(`outputType = universeFormerOutput = universeCodeCell (lmaxAll levels) flag` via
`flatTypingRuleDescOf_outputIsUniverseFormer`), term-indexed
(`outputType = termIndexedCarrierOutput = universeCodeCell level flag` via
`termIndexedFormerDescOf_outputIsUniverse`).  The `formationRule` arm's classifier is thus always a
universe code, discharged by `ofUniverseCode`. -/
theorem UnionClassifierIsType.ofFormationOutput {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (rule : FormationRule)
    (levels : List LevelExpr) (level : LevelExpr) (flag : UniverseFlag)
    (isFormationRule : formationRuleOf generator = some rule) :
    UnionClassifierIsType profile context (rule.outputType scope levels level flag) := by
  cases rule with
  | baseType baseRule =>
      have isBaseType : baseTypeRuleDescOf generator = some baseRule :=
        formationRuleOf_baseType_inv isFormationRule
      show UnionClassifierIsType profile context (baseRule.outputUniverse scope)
      rw [baseTypeRuleTableOutputIsType0 isBaseType]
      exact UnionClassifierIsType.ofUniverseCode context LevelExpr.lzero UniverseFlag.standard
  | flat flatRule =>
      have isFlat : flatTypingRuleDescOf generator = some flatRule :=
        formationRuleOf_flat_inv isFormationRule
      show UnionClassifierIsType profile context (flatRule.outputType scope levels flag)
      rw [flatTypingRuleDescOf_outputIsUniverseFormer isFlat]
      show UnionClassifierIsType profile context (universeCodeCell (lmaxAll levels) flag)
      exact UnionClassifierIsType.ofUniverseCode context (lmaxAll levels) flag
  | cumulative cumulativeRule =>
      -- TYTAB-2 wave U2: the cumulative output is a universe code for EVERY row shape — the universe-former
      -- Π/Σ/list/option rows (`universeFormerOutput`) and the flag-pinned nullary unit row alike.  Read off
      -- the row-shape-agnostic `typingRuleDescOf_output_isUniverseCode`, then a universe code is a type by
      -- self-typing.
      have isCumulative : typingRuleDescOf generator = some cumulativeRule :=
        formationRuleOf_cumulative_inv isFormationRule
      dsimp only [FormationRule.outputType]
      obtain ⟨outputLevel, outputFlag, outputEq⟩ :=
        typingRuleDescOf_output_isUniverseCode isCumulative _ levels flag
      rw [outputEq]
      exact UnionClassifierIsType.ofUniverseCode context outputLevel outputFlag
  | termIndexed termRule =>
      have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
        formationRuleOf_termIndexed_inv isFormationRule
      rw [termIndexedFormerDescOf_outputIsUniverse isTermIndexed]
      show UnionClassifierIsType profile context (universeCodeCell level flag)
      exact UnionClassifierIsType.ofUniverseCode context level flag

/-! ## ★ TYTAB-2 wave U3: the single-child cumulative data-former validity, DISCHARGED

After wave U2 the `gen_listCode` / `gen_optionCode` formers are `.cumulative` `formationRuleOf` rows, so a
ONE-child data type code (`List A` / `Option A`) re-forms DIRECTLY in the union from its element's validity
via `formationRuleOfObligations` — the single cumulative obligation IS the element-at-its-universe typing the
validity supplies, at the element's own flag (no flag-coherence obstruction, the former is single-child).
The two-child flat formers (`either` / `product`) and the missing-codomain `pi` / missing-endpoint `id` /
interval-strengthening `bridge` rows genuinely cannot close this way — flag coherence across two independent
child validities, or a child validity the row's IH does not supply (the residual fields below). -/

/-- **`Option A` is a union type given `A` is.**  The single cumulative obligation (`A` at its universe code)
IS the element validity; re-form `optionTypeCell A` at the `.cumulative gen_optionCode` formation row.  The
output `universeFormerOutput scope [elementLevel] flag = universeCodeCell (lmaxAll [elementLevel]) flag` is a
universe code.  Discharges the `optionFormed` field of `UnionDataFormerValidity` UNCONDITIONALLY. -/
theorem UnionClassifierIsType.optionFormed_ofValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (elementType : RawTerm scope)
    (locksInterval : context.AllLocksAreInterval)
    (elementIsType : UnionClassifierIsType profile context elementType) :
    UnionClassifierIsType profile context (optionTypeCell elementType) := by
  obtain ⟨elementLevel, flag, elementTyped⟩ := elementIsType
  refine ⟨lmaxAll [elementLevel], flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_optionCode ()
    (.childCons elementType .childNil) (.cumulative { outputType := universeFormerOutput })
    [elementLevel] (optionTypeCell elementType) elementLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact elementTyped
      | tail _ tailMember => cases tailMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval elementTyped
      | tail _ tailMember => cases tailMember)

/-- **`List A` is a union type given `A` is.**  The `optionFormed` twin at the `.cumulative gen_listCode`
formation row.  Discharges the `listFormed` field of `UnionDataFormerValidity` UNCONDITIONALLY. -/
theorem UnionClassifierIsType.listFormed_ofValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (elementType : RawTerm scope)
    (locksInterval : context.AllLocksAreInterval)
    (elementIsType : UnionClassifierIsType profile context elementType) :
    UnionClassifierIsType profile context (listTypeCell elementType) := by
  obtain ⟨elementLevel, flag, elementTyped⟩ := elementIsType
  refine ⟨lmaxAll [elementLevel], flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_listCode ()
    (.childCons elementType .childNil) (.cumulative { outputType := universeFormerOutput })
    [elementLevel] (listTypeCell elementType) elementLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact elementTyped
      | tail _ tailMember => cases tailMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval elementTyped
      | tail _ tailMember => cases tailMember)

/-! ## ★ TYTAB-2 wave W3: the two-child SAME-FLAG cumulative / term-indexed data-former validity, DISCHARGED

`piFormed` and `idFormed` are NOT the flag-coherence wall (`eitherFormed` / `productFormed`): in the `lam`
and `refl` intro rows the type-parameter premises already share ONE flag (`lamIntroRule` types both domain
and codomain at the row's single `flag`; `reflIntroRule` carries a single carrier the endpoints classify
at).  So given the two pieces AT a common flag the row delivers — domain-at-`flag` plus codomain-at-`flag`
under the binder for Π, carrier-at-`flag` plus the two endpoints-at-carrier for Id — the type code re-forms
DIRECTLY in the union via `formationRuleOfObligations` at the `.cumulative gen_piTyCode` /
`.termIndexed gen_idCode` row.  These two are now THEOREMS, dropped from the residual. -/

/-- **`Π(domain).codomain` is a union type given the domain and (binder-crossing) codomain are union types
AT A COMMON FLAG.**  The two cumulative obligations of the `.cumulative gen_piTyCode` row at the Π spine
`[0, 1]` are exactly domain-at-`flag` (ambient) and codomain-at-`flag` (the binder-extended context); the
output `universeFormerOutput scope [domainLevel, codomainLevel] flag = universeCodeCell (lmaxAll …) flag`
is a universe code.  Discharges the `lam` row of validity UNCONDITIONALLY — the lam intro premises supply
both typings at the row's single `flag`, no flag-coherence obstruction (unlike `eitherFormed` /
`productFormed`, whose two component validities carry INDEPENDENT flags). -/
theorem UnionClassifierIsType.piFormed_atCommonFlag {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) (domainLevel codomainLevel : LevelExpr)
    (flag : UniverseFlag)
    (locksInterval : context.AllLocksAreInterval)
    (domainTyped : HasTypeUnion profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasTypeUnion profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    :
    UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode) := by
  refine ⟨lmaxAll [domainLevel, codomainLevel], flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_piTyCode ()
    (.childCons domainCode (.childCons codomainCode .childNil))
    (.cumulative { outputType := universeFormerOutput })
    [domainLevel, codomainLevel] (piTyCodeCell domainCode codomainCode) domainLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact domainTyped
      | tail _ tailMember => cases tailMember with
        | head => exact codomainTyped
        | tail _ deeperMember => cases deeperMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval domainTyped
      | tail _ tailMember => cases tailMember with
        | head =>
          exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval
            (TypingContext.AllLocksAreInterval.cons locksInterval) codomainTyped
        | tail _ deeperMember => cases deeperMember)

/-- **`Id(carrier, witness, witness)` is a union type given the carrier is a union type and the witness is
typed at the carrier.**  The three term-indexed obligations of the `.termIndexed gen_idCode` row at the
spine `[0, 0, 0]` are the carrier-at-its-universe obligation followed by the two endpoint-at-carrier
obligations; the output `termIndexedCarrierOutput scope carrierLevel flag = universeCodeCell carrierLevel
flag` is a universe code.  Discharges the `refl` row of validity UNCONDITIONALLY — the refl intro premise
supplies the endpoint typing (`witness : carrier`) and the IH on it the carrier validity, ONE flag (the
carrier's), no obstruction. -/
theorem UnionClassifierIsType.idFormed_ofCarrier {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrierCode witness : RawTerm scope)
    (locksInterval : context.AllLocksAreInterval)
    (witnessUsable : context.isSubjectUsableAtModality witness .fibrant = true)
    (carrierIsType : UnionClassifierIsType profile context carrierCode)
    (witnessTyped : HasTypeUnion profile context witness carrierCode) :
    UnionClassifierIsType profile context (idTypeCell carrierCode witness witness) := by
  obtain ⟨carrierLevel, flag, carrierTyped⟩ := carrierIsType
  refine ⟨carrierLevel, flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_idCode ()
    (.childCons carrierCode (.childCons witness (.childCons witness .childNil)))
    (.termIndexed { outputType := termIndexedCarrierOutput })
    [] carrierCode carrierLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact carrierTyped
      | tail _ tailMember => cases tailMember with
        | head => exact witnessTyped
        | tail _ deeperMember => cases deeperMember with
          | head => exact witnessTyped
          | tail _ deepestMember => cases deepestMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval carrierTyped
      | tail _ tailMember => cases tailMember with
        | head => exact witnessUsable
        | tail _ deeperMember => cases deeperMember with
          | head => exact witnessUsable
          | tail _ deepestMember => cases deepestMember)

/-! ## ★ TYTAB-2 wave W5: the two-child FLAT data-former validity AT A COMMON FLAG, DISCHARGED

After the construction-side flag-coherence refinement of the `pair` / `eitherInl` / `eitherInr` intro rules
(each now carries a formedness premise typing BOTH type params at the SAME row `flag`, matching the flat
`productCode` / `eitherCode` formation row), the two flat data formers re-form DIRECTLY in the union — exactly
like `piFormed_atCommonFlag` does for the cumulative Π row.  The flag-coherence "frontier" dissolves: it was
never a metatheory wall, only an intro rule that under-specified its type params relative to the formation
rule it must reconstruct.  A flag-INCOHERENT `product(A@f1, B@f2)` is now unconstructible at intro, so the
fragment validity must reconstruct is exactly the flag-coherent one the formation row accepts. -/

/-- **`product(first, second)` is a union type given both components are union types AT A COMMON FLAG.**  The
two flat obligations of the `.flat gen_productCode` row at the spine `[0, 0]` are exactly first-at-`flag` and
second-at-`flag`; the output `universeFormerOutput scope [firstLevel, secondLevel] flag = universeCodeCell
(lmaxAll …) flag` is a universe code.  Discharges the `pair` row of validity UNCONDITIONALLY — the refined
pair intro premises supply both type-param typings at the row's single `flag`. -/
theorem UnionClassifierIsType.productFormed_atCommonFlag {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (firstType secondType : RawTerm scope)
    (firstLevel secondLevel : LevelExpr) (flag : UniverseFlag)
    (locksInterval : context.AllLocksAreInterval)
    (firstTyped : HasTypeUnion profile context firstType (universeCodeCell firstLevel flag))
    (secondTyped : HasTypeUnion profile context secondType (universeCodeCell secondLevel flag)) :
    UnionClassifierIsType profile context (productTypeCell firstType secondType) := by
  refine ⟨lmaxAll [firstLevel, secondLevel], flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_productCode ()
    (.childCons firstType (.childCons secondType .childNil))
    (.flat { outputType := universeFormerOutput })
    [firstLevel, secondLevel] (productTypeCell firstType secondType) firstLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact firstTyped
      | tail _ tailMember => cases tailMember with
        | head => exact secondTyped
        | tail _ deeperMember => cases deeperMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval firstTyped
      | tail _ tailMember => cases tailMember with
        | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval secondTyped
        | tail _ deeperMember => cases deeperMember)

/-- **`either(left, right)` is a union type given both components are union types AT A COMMON FLAG.**  The
`productFormed_atCommonFlag` twin at the `.flat gen_eitherCode` row.  Discharges the `eitherInl` / `eitherInr`
rows of validity UNCONDITIONALLY — the refined either intro premises supply both type-param typings at the
row's single `flag`. -/
theorem UnionClassifierIsType.eitherFormed_atCommonFlag {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (leftType rightType : RawTerm scope)
    (leftLevel rightLevel : LevelExpr) (flag : UniverseFlag)
    (locksInterval : context.AllLocksAreInterval)
    (leftTyped : HasTypeUnion profile context leftType (universeCodeCell leftLevel flag))
    (rightTyped : HasTypeUnion profile context rightType (universeCodeCell rightLevel flag)) :
    UnionClassifierIsType profile context (eitherTypeCell leftType rightType) := by
  refine ⟨lmaxAll [leftLevel, rightLevel], flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_eitherCode ()
    (.childCons leftType (.childCons rightType .childNil))
    (.flat { outputType := universeFormerOutput })
    [leftLevel, rightLevel] (eitherTypeCell leftType rightType) leftLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact leftTyped
      | tail _ tailMember => cases tailMember with
        | head => exact rightTyped
        | tail _ deeperMember => cases deeperMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval leftTyped
      | tail _ tailMember => cases tailMember with
        | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval rightTyped
        | tail _ deeperMember => cases deeperMember)

/-! ## ★ TYTAB-2 wave W3: the bridge-carrier elim-output validity, DISCHARGED

`pathApp`'s output type is the bridge carrier.  Inverting the bridge code's union typing at the carrier leg
(`HasTypeUnion.invertAtBridgeCodeHeadCarrier`) recovers the carrier validity UNCONDITIONALLY — the bridge is a
`.termIndexed` formation row whose obligation list ALWAYS opens with the carrier-at-universe obligation (read
from the `level` parameter, NOT the `levels` list), so there is no degenerate escape (unlike the flat product
/ either rows, whose obligations are read positionally from a FREE `levels` list and so admit an empty-`levels`
typing carrying no component validity). -/

/-- **`bridgeTypeCell carrier left right` validity yields the carrier validity.**  Inverts the bridge code's
union typing at the carrier leg.  Discharges the `pathApp` elim-output row UNCONDITIONALLY (the term-indexed
carrier obligation has no `levels`-degeneracy escape). -/
theorem UnionClassifierIsType.pathAppOutputFormed_ofValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrierCode leftEndpoint rightEndpoint : RawTerm scope)
    (bridgeIsType :
      UnionClassifierIsType profile context (bridgeTypeCell carrierCode leftEndpoint rightEndpoint)) :
    UnionClassifierIsType profile context carrierCode := by
  obtain ⟨_bridgeLevel, _bridgeFlag, bridgeTyped⟩ := bridgeIsType
  exact HasTypeUnion.invertAtBridgeCodeHeadCarrier bridgeTyped rfl

/-- **★ `product(first, second)` validity yields the FIRST component validity.**  Inverts the product code's
union typing at the flat-former obligation list (now total — the free-`levels` fix forces both component
obligations).  Discharges `fstOutputFormed` UNCONDITIONALLY. -/
theorem UnionClassifierIsType.fstOutputFormed_ofValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (firstType secondType : RawTerm scope)
    (productIsType : UnionClassifierIsType profile context (productTypeCell firstType secondType)) :
    UnionClassifierIsType profile context firstType := by
  obtain ⟨_productLevel, _productFlag, productTyped⟩ := productIsType
  exact (HasTypeUnion.invertAtProductCodeHeadComponents productTyped rfl).1

/-- **★ `product(first, second)` validity yields the SECOND component validity.**  The `fst` twin at the
second flat obligation.  Discharges `sndOutputFormed` UNCONDITIONALLY. -/
theorem UnionClassifierIsType.sndOutputFormed_ofValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (firstType secondType : RawTerm scope)
    (productIsType : UnionClassifierIsType profile context (productTypeCell firstType secondType)) :
    UnionClassifierIsType profile context secondType := by
  obtain ⟨_productLevel, _productFlag, productTyped⟩ := productIsType
  exact (HasTypeUnion.invertAtProductCodeHeadComponents productTyped rfl).2

/-- **The two `either` component validities, recovered.**  Inverts the either code's union typing at the
flat-former obligation list (now total).  The inversion direction (the `eitherInl` / `eitherInr` intro rows
build the code, which is the obstructed flag-coherence DIRECTION — see `eitherFormed`). -/
theorem UnionClassifierIsType.eitherComponents_ofValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (leftType rightType : RawTerm scope)
    (eitherIsType : UnionClassifierIsType profile context (eitherTypeCell leftType rightType)) :
    UnionClassifierIsType profile context leftType ∧
    UnionClassifierIsType profile context rightType := by
  obtain ⟨_eitherLevel, _eitherFlag, eitherTyped⟩ := eitherIsType
  exact HasTypeUnion.invertAtEitherCodeHeadComponents eitherTyped rfl

/-- **★ `subst0 codomainCode argument` validity from the Π-code validity AND the argument typing.**  Inverts
the Π-code's union typing at the codomain leg (now total — the free-`levels` fix forces the cumulative
codomain obligation), giving codomain-under-binder validity; then the W4 single substitution
(`subst0WithUnionImage`) transports the argument, landing `subst0 codomainCode argument` at
`subst0 (universeCodeCell …) argument = universeCodeCell …` (closed).  Discharges the `app` elim output
UNCONDITIONALLY when the argument typing is available (it is, in the `app` elim case's premise). -/
theorem UnionClassifierIsType.appOutputFormed_ofValidityAndArg {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) (argument : RawTerm scope)
    (piIsType : UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeUnion profile context argument domainCode)
    (argumentUsable : context.isSubjectUsableAtModality argument .fibrant = true) :
    UnionClassifierIsType profile context (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := piIsType
  obtain ⟨codomainLevel, flag, codomainTyped⟩ :=
    HasTypeUnion.invertAtPiCodeHeadCodomain piTyped rfl
  refine ⟨codomainLevel, flag, ?_⟩
  have substituted := HasTypeUnion.subst0WithUnionImage argument codomainTyped argumentTyped
    argumentUsable
  -- The codomain classifier `universeCodeCell codomainLevel flag` is closed; `subst0` leaves it unchanged.
  rwa [show RawTerm.subst0 (universeCodeCell codomainLevel flag) argument
        = universeCodeCell codomainLevel flag by
      rw [show (universeCodeCell codomainLevel flag : RawTerm (scope + 1))
            = RawTerm.weaken (universeCodeCell codomainLevel flag) by
          rw [RawTerm.weaken_eq_rename, rename_universeCodeCell], RawTerm.subst0_weaken]] at substituted

/-- **★ The dependent-eliminator output `subst0 motive argument` is a type — from the motive's universe
typing and the argument's data typing.**  The branch-selecting recursors (boolElim / natElim / natRec /
optionMatch / listElim) all produce the dependent output `subst0 motive argument` where the MOTIVE is
typed at a universe code `universeCodeCell levelExpr flag` over the data-extended context
`context.cons dataCode`, and the eliminated argument (scrutinee) is typed at `dataCode`.  The W4 single
substitution (`subst0WithUnionImage`) transports the motive's universe typing along the argument, landing
`subst0 motive argument` at `subst0 (universeCodeCell …) argument = universeCodeCell …` (the universe code
is closed, hence subst-invariant).  This is the dependent twin of `appOutputFormed_ofValidityAndArg` —
SIMPLER, because the motive is universe-typed DIRECTLY (no Π-code inversion step).  The shared validity
leg of every dependent branch-selecting eliminator: once the motive is a table obligation, the dependent
output's formedness is derivable, so the row needs no separate result-formedness obligation (exactly the
`app`-unhardened discipline). -/
theorem UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument {profile : PolyProfile}
    {scope : Nat} (context : TypingContext profile scope) (dataCode : RawTerm scope)
    (motive : RawTerm (scope + 1)) (argument : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons dataCode) motive (universeCodeCell levelExpr flag))
    (argumentTyped : HasTypeUnion profile context argument dataCode)
    (argumentUsable : context.isSubjectUsableAtModality argument .fibrant = true) :
    UnionClassifierIsType profile context (RawTerm.subst0 motive argument) := by
  refine ⟨levelExpr, flag, ?_⟩
  have substituted := HasTypeUnion.subst0WithUnionImage argument motiveTyped argumentTyped
    argumentUsable
  -- The universe-code classifier `universeCodeCell levelExpr flag` is closed; `subst0` leaves it unchanged.
  rwa [show RawTerm.subst0 (universeCodeCell levelExpr flag) argument
        = universeCodeCell levelExpr flag by
      rw [show (universeCodeCell levelExpr flag : RawTerm (scope + 1))
            = RawTerm.weaken (universeCodeCell levelExpr flag) by
          rw [RawTerm.weaken_eq_rename, rename_universeCodeCell], RawTerm.subst0_weaken]] at substituted

/-- **★ JMAX-3: the genuine Paulin-Mohring `idJ` output `idJMotiveAt motive right witness` is a type — from the
motive's universe typing under TWO binders, the right endpoint's data typing, and the witness's identity
typing.**  Genuine path induction's output `C[b := right, p := witness] = idJMotiveAt motive right witness =
substPair motive witness right` is a TWO-variable instantiation of the motive, which is typed at a universe code
over `(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode left)`.  The two-binder transport
`substPairUnderTwoBindingsUnionImages` fills the inner path binder (`var 0`) with `witness` and the outer
endpoint binder (`var 1`) with `rightEndpoint`; the inner-binder type collapses to the based identity code
`idTypeCell typeCode left right` (`subst_singleton_idJMotiveSecondBinderType`), which is exactly what `witness`
inhabits, and the universe-code classifier is closed (subst-stable).  The genuine-J twin of
`dependentMotiveOutputFormed_ofMotiveAndArgument` — the UNIQUE eliminator whose output is a two-variable
substitution, so it needs the two-binder transport rather than a single `subst0`. -/
theorem UnionClassifierIsType.idJOutputFormed_ofMotiveEndpointWitness {profile : PolyProfile}
    {scope : Nat} (context : TypingContext profile scope)
    (typeCode leftEndpoint rightEndpoint : RawTerm scope)
    (motive : RawTerm (scope + 2)) (witness : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile
      ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint))
      motive (universeCodeCell levelExpr flag))
    (rightEndpointTyped : HasTypeUnion profile context rightEndpoint typeCode)
    (witnessTyped : HasTypeUnion profile context witness
      (idTypeCell typeCode leftEndpoint rightEndpoint))
    (witnessUsable : context.isSubjectUsableAtModality witness .fibrant = true)
    (rightEndpointUsable : context.isSubjectUsableAtModality rightEndpoint .fibrant = true) :
    UnionClassifierIsType profile context (idJMotiveAt motive rightEndpoint witness) := by
  refine ⟨levelExpr, flag, ?_⟩
  -- The inner path binder's type `idJMotiveSecondBinderType typeCode left` collapses, under `var 0 := right`, to
  -- the based identity code `witness` inhabits — feeding the two-binder transport at the right instantiated type.
  have innerArgAtSubstituted : HasTypeUnion profile context witness
      (RawTerm.subst (RawTermSubst.singleton rightEndpoint)
        (idJMotiveSecondBinderType typeCode leftEndpoint)) := by
    rw [subst_singleton_idJMotiveSecondBinderType]
    exact witnessTyped
  have substituted :=
    HasTypeUnion.substPairUnderTwoBindingsUnionImages witness rightEndpoint motiveTyped
      innerArgAtSubstituted rightEndpointTyped witnessUsable rightEndpointUsable
  -- `idJMotiveAt motive right witness = substPair motive witness right
  --   = subst (cons witness (singleton right)) motive` (defeq); the universe classifier is closed (subst-stable).
  rw [subst_universeCodeCell] at substituted
  exact substituted

/-! ## ★ TYTAB-2 wave W4: the bridge carrier validity, DISCHARGED via interval-endpoint substitution
(NOT interval strengthening)

The `pathLam` row's body obligation classifies the body at `RawTerm.weaken carrierCode` under
`context.cons intervalTypeCell` — so recursive validity makes `weaken carrierCode` a TYPE under the interval
binder (`HasTypeUnion (context.cons intervalTypeCell) (weaken carrierCode) (universeCodeCell L f)`).  The
"interval strengthening" framing was a RED HERRING: there is no need to strengthen a typing across the
interval binder at all.  Substituting the interval-`0` endpoint into the body validity via the W4 single
substitution (`subst0WithUnionImage`) lands `subst0 (weaken carrierCode) intervalZeroCell` at
`subst0 (universeCodeCell L f) intervalZeroCell`, and BOTH collapse by `subst0_weaken`
(`subst0 (weaken t) a = t`; the universe code is closed, hence its own weaken-image):
`carrierCode : universeCodeCell L f` in the BASE context — the carrier validity, on the nose.  No
strengthening campaign, no flag-coherence triples — the closed substitution IS the descent. -/

/-- **The interval-`0` endpoint is union-typed at the interval type.**  `intervalZeroCell : intervalTypeCell`
via the nullary `interval0` intro row (no premises). -/
theorem HasTypeUnion.intervalZeroTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeUnion profile context intervalZeroCell intervalTypeCell := by
  refine HasTypeUnion.intro context .gen_interval0 interval0IntroRule .childNil .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    (by dischargeUsability interval0IntroRule)
  intro obligation hmem; cases hmem

/-- The interval-`0` endpoint former is a non-variable dimension former, hence usable at the DIMENSIONAL
modality in any context — the discharge the lock substitution (`subst0WithUnionLockImage`) demands for the
interval endpoint it substitutes for the locked dimension. -/
theorem intervalZeroCellUsableDimensionally {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    context.isSubjectUsableAtModality intervalZeroCell .dimensional = true :=
  isSubjectUsableAtModality_dimensional_ofNonVarHead context Generator.gen_interval0 () .childNil
    (by decide)

/-- The interval-`1` endpoint former is dimensionally usable — the `intervalZeroCellUsableDimensionally`
twin. -/
theorem intervalOneCellUsableDimensionally {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    context.isSubjectUsableAtModality intervalOneCell .dimensional = true :=
  isSubjectUsableAtModality_dimensional_ofNonVarHead context Generator.gen_interval1 () .childNil
    (by decide)

/-- **★ `Bridge carrier left right` validity from the body validity — via interval substitution.**  Given
the body validity `weaken carrierCode` is a type under the interval binder (what the `pathLam` row's IH
delivers), substitute the interval-`0` endpoint: `subst0WithUnionImage` lands the substituted body at the
substituted classifier, and `subst0_weaken` collapses BOTH closed weaken-images to `carrierCode` and the
universe code respectively.  Discharges the `bridgeFormed` field UNCONDITIONALLY — the interval-strengthening
"frontier" dissolves into a closed substitution. -/
theorem UnionClassifierIsType.bridgeFormed_ofBodyValidity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrierCode : RawTerm scope)
    (bodyCarrierIsType : UnionClassifierIsType profile (context.lockCons intervalTypeCell)
      (RawTerm.weaken carrierCode)) :
    UnionClassifierIsType profile context carrierCode := by
  obtain ⟨carrierLevel, flag, weakCarrierTyped⟩ := bodyCarrierIsType
  -- The universe-code classifier is closed, hence its own weaken-image.
  have universeIsWeakenImage :
      RawTerm.weaken (universeCodeCell carrierLevel flag : RawTerm scope)
        = (universeCodeCell carrierLevel flag : RawTerm (scope + 1)) := by
    rw [RawTerm.weaken_eq_rename, rename_universeCodeCell]
  have weakCarrierTypedAtWeakUniverse :
      HasTypeUnion profile (context.lockCons intervalTypeCell) (RawTerm.weaken carrierCode)
        (RawTerm.weaken (universeCodeCell carrierLevel flag)) := by
    rw [universeIsWeakenImage]
    exact weakCarrierTyped
  -- Substitute the interval-`0` endpoint THROUGH THE LOCK: both weaken-images collapse by `subst0_weaken`.
  have substituted :=
    HasTypeUnion.subst0WithUnionLockImage (intervalZeroCell : RawTerm scope)
      weakCarrierTypedAtWeakUniverse (HasTypeUnion.intervalZeroTyped context)
      (intervalZeroCellUsableDimensionally context)
  rw [RawTerm.subst0_weaken, RawTerm.subst0_weaken] at substituted
  exact ⟨carrierLevel, flag, substituted⟩

/-- **The interval-`1` endpoint is union-typed at the interval type.**  The `interval0` twin. -/
theorem HasTypeUnion.intervalOneTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeUnion profile context intervalOneCell intervalTypeCell := by
  refine HasTypeUnion.intro context .gen_interval1 interval1IntroRule .childNil .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
    (by dischargeUsability interval1IntroRule)
  intro obligation hmem; cases hmem

/-- **★ `Bridge carrier (subst0 body i0) (subst0 body i1)` is a union type — the full `pathLam`-output bridge
code, DISCHARGED.**  Given the body premise `body : weaken carrierCode` under the interval binder: the carrier
validity descends by `bridgeFormed_ofBodyValidity`; each endpoint `subst0 body iN` is typed AT `carrierCode`
by the W4 substitution of the body premise (the body classifier `weaken carrierCode` collapses to
`carrierCode` under `subst0_weaken`); the bridge code re-forms at the `.termIndexed gen_bridgeCode` row
(carrier-at-universe + the two endpoint-at-carrier obligations).  Discharges the `pathLam` row of validity
UNCONDITIONALLY — the interval-strengthening "frontier" fully dissolved. -/
theorem UnionClassifierIsType.bridgeFormed_ofBodyPremise {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrierCode : RawTerm scope)
    (body : RawTerm (scope + 1))
    (locksInterval : context.AllLocksAreInterval)
    (bodyUsable : (context.lockCons intervalTypeCell).isSubjectUsableAtModality body .fibrant = true)
    (carrierUnderIntervalIsType : UnionClassifierIsType profile (context.lockCons intervalTypeCell)
      (RawTerm.weaken carrierCode))
    (bodyTyped : HasTypeUnion profile (context.lockCons intervalTypeCell) body
      (RawTerm.weaken carrierCode)) :
    UnionClassifierIsType profile context
      (bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
        (RawTerm.subst0 body intervalOneCell)) := by
  -- Carrier validity (interval-0 substitution THROUGH THE LOCK of the body's CLASSIFIER validity = the IH upstream).
  obtain ⟨carrierLevel, flag, carrierTyped⟩ :=
    UnionClassifierIsType.bridgeFormed_ofBodyValidity context carrierCode carrierUnderIntervalIsType
  -- Each endpoint `subst0 body iN : subst0 (weaken carrierCode) iN = carrierCode` by W4 lock-subst + subst0_weaken.
  have endpointZeroTyped : HasTypeUnion profile context (RawTerm.subst0 body intervalZeroCell) carrierCode := by
    have substituted := HasTypeUnion.subst0WithUnionLockImage (intervalZeroCell : RawTerm scope)
      bodyTyped (HasTypeUnion.intervalZeroTyped context)
      (intervalZeroCellUsableDimensionally context)
    rwa [RawTerm.subst0_weaken] at substituted
  have endpointOneTyped : HasTypeUnion profile context (RawTerm.subst0 body intervalOneCell) carrierCode := by
    have substituted := HasTypeUnion.subst0WithUnionLockImage (intervalOneCell : RawTerm scope)
      bodyTyped (HasTypeUnion.intervalOneTyped context)
      (intervalOneCellUsableDimensionally context)
    rwa [RawTerm.subst0_weaken] at substituted
  -- The endpoints `subst0 body iN` are fibrantly usable: the body is fibrantly usable under the lock (the
  -- pathLam intro's own use-site conjunct), and the interval-endpoint singleton substitution (a dimensionally
  -- usable interval former) preserves that usability into the base context — `subjectUsabilityPreservedUnderSubst`
  -- composed with `substLockSingletonAccessibilityPreserved`.  A body that USED the locked dimension fibrantly
  -- (the SR-breaker shape) makes `bodyUsable` false, so no endpoint reconstruction is ever demanded of it.
  have endpointZeroUsable :
      context.isSubjectUsableAtModality (RawTerm.subst0 body intervalZeroCell) .fibrant = true :=
    subjectUsabilityPreservedUnderSubst (RawTermSubst.singleton intervalZeroCell) .fibrant
      (substLockSingletonAccessibilityPreserved context intervalTypeCell intervalZeroCell
        (intervalZeroCellUsableDimensionally context) .fibrant)
      body bodyUsable
  have endpointOneUsable :
      context.isSubjectUsableAtModality (RawTerm.subst0 body intervalOneCell) .fibrant = true :=
    subjectUsabilityPreservedUnderSubst (RawTermSubst.singleton intervalOneCell) .fibrant
      (substLockSingletonAccessibilityPreserved context intervalTypeCell intervalOneCell
        (intervalOneCellUsableDimensionally context) .fibrant)
      body bodyUsable
  -- Re-form the bridge code at the term-indexed `gen_bridgeCode` row (carrier + two endpoints-at-carrier).
  refine ⟨carrierLevel, flag, ?_⟩
  refine HasTypeUnion.formationRuleOfObligations context Generator.gen_bridgeCode ()
    (.childCons carrierCode (.childCons (RawTerm.subst0 body intervalZeroCell)
      (.childCons (RawTerm.subst0 body intervalOneCell) .childNil)))
    (.termIndexed { outputType := termIndexedCarrierOutput })
    [] carrierCode carrierLevel flag rfl
    (fun obligation hmem => by cases hmem with
      | head => exact carrierTyped
      | tail _ tailMember => cases tailMember with
        | head => exact endpointZeroTyped
        | tail _ deeperMember => cases deeperMember with
          | head => exact endpointOneTyped
          | tail _ deepestMember => cases deepestMember)
    (fun obligation hmem => by cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval carrierTyped
      | tail _ tailMember => cases tailMember with
        | head => exact endpointZeroUsable
        | tail _ deeperMember => cases deeperMember with
          | head => exact endpointOneUsable
          | tail _ deepestMember => cases deepestMember)

/-! ## ★ TYTAB-2 wave W4: the UNION well-formedness `WfContextUnion` (admits NATIVE bindings)

The host well-formedness `WfContextDescPi` gates each binding by `IsTypeDescPi` (a HOST formation typing), so
it CANNOT admit a native-only type code like `intervalTypeCell` (`typingRuleDescOf .gen_intervalCode = none`;
the host formation engine has no base-type arm).  That is the sole reason `classifierIsType`'s IH could not be
invoked on the `pathLam` body premise (which lives under `context.cons intervalTypeCell`).  `WfContextUnion`
gates each binding by `UnionClassifierIsType` instead — the UNION notion of "is a type", which DOES type
`intervalTypeCell` (via `ofBaseTypeRow`).  So the interval binder is admissible, and the `pathLam` IH fires. -/

/-- **Union well-formedness.**  Each binding is a UNION type (`UnionClassifierIsType`), the union analogue of
`WfContextDesc` / `WfContextDescPi`.  Admits native bindings (bridge codes) the host wf rejects.

★ **Interval non-fibrancy (#1805).**  The `.cons` arm additionally forbids the interval (`¬ Conv bindingType
intervalTypeCell`): an ordinary (fibrant) binder may NOT bind the interval, so the dimension can only ever enter
the context under the affine `lockCons` LOCK.  This is the exact DUAL of the `.lockCons` arm's `dimensionType =
intervalTypeCell` (only the interval may be LOCKED).  Together they pin the interval as genuinely non-fibrant:
`WfContextUnion (context.cons intervalTypeCell)` is uninhabitable (its `.2.2` conjunct is `¬ Conv intervalTypeCell
intervalTypeCell`, refuted by `Conv.refl`), and every interval-typed variable in a well-formed context is
necessarily a LOCKED dimension — the use-site statement of non-fibrancy that the dimensional usability bridge
(`NoConsBindingIsInterval`) rests on, now PINNED into well-formedness rather than threaded as a free hypothesis. -/
def WfContextUnion {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContextUnion restContext ∧ UnionClassifierIsType profile restContext bindingType
        ∧ ¬ Conv bindingType intervalTypeCell
  | _, .lockCons restContext dimensionType =>
      WfContextUnion restContext ∧ dimensionType = intervalTypeCell

/-- The empty context is union-well-formed. -/
theorem WfContextUnion.empty {profile : PolyProfile} :
    WfContextUnion (profile := profile) .empty := trivial

/-- Extend a union-well-formed context by a binding that is a union type AND is not the affine interval
(`¬ Conv bindingType intervalTypeCell`, the #1805 non-fibrancy discipline — an ordinary binder never binds the
dimension; the dimension enters only under `lockCons`). -/
theorem WfContextUnion.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextUnion restContext)
    (bindingIsType : UnionClassifierIsType profile restContext bindingType)
    (notInterval : ¬ Conv bindingType intervalTypeCell) :
    WfContextUnion (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsType, notInterval⟩

/-- Extend a union-well-formed context by the affine dimension LOCK (`lockCons`).  The `lockCons` twin of
`WfContextUnion.cons`, with ONE extra discipline beyond the `.cons` arm: the locked dimension must be the
affine interval `intervalTypeCell` (the FitchTT / fib-3a affine-multiplier pinning).  That field is what keeps
the variable-rule accessibility discipline coherent — a variable at a `lockCons`-0 position is typed at the
locked dimension, and only `intervalTypeCell` (not a universe code) can sit there, so a universe-typed binding
is never under a lock and stays fibrantly accessible to `HasTypeUnionOver.var`'s `isAccessible` premise.  The
`pathLam` body premise binds exactly `intervalTypeCell`, so the field is `rfl` at every construction site.

★ FIBRANCY-AXIS-0 (#1886): the lock arm NO LONGER demands the dimension be a fibrant type — the interval is a
non-fibrant DIMENSION, so requiring `UnionClassifierIsType … intervalTypeCell` would make the arm uninhabitable
once the interval loses its universe classifier.  The dimension's identity is pinned by `dimensionType =
intervalTypeCell` alone (the honest FitchTT statement: the lock binds a dimension, not a fibrant type). -/
theorem WfContextUnion.lockCons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {dimensionType : RawTerm scope}
    (restWellFormed : WfContextUnion restContext)
    (dimensionIsInterval : dimensionType = intervalTypeCell) :
    WfContextUnion (restContext.lockCons dimensionType) :=
  ⟨restWellFormed, dimensionIsInterval⟩

/-- **★ Union well-formedness pins the interval-lock discipline.**  A `WfContextUnion` context satisfies
`AllLocksAreInterval` — every `lockCons` arm of `WfContextUnion` carries `dimensionType = intervalTypeCell`
(its `.2.2` conjunct), and ordinary `cons` arms are transparent.  This is the structural bridge that lets the
typed-implies-fibrantly-usable engine (`typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval`) fire over any
well-formed context: a subject typed at a universe code under `WfContextUnion` is fibrantly usable. -/
theorem WfContextUnion.allLocksAreInterval {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) →
      WfContextUnion context → context.AllLocksAreInterval
  | _, .empty, _wellFormed => TypingContext.AllLocksAreInterval.empty
  | _, .cons restContext _bindingType, wellFormed =>
      TypingContext.AllLocksAreInterval.cons
        (WfContextUnion.allLocksAreInterval restContext wellFormed.1)
  | _, .lockCons restContext _dimensionType, wellFormed =>
      ⟨WfContextUnion.allLocksAreInterval restContext wellFormed.1, wellFormed.2⟩

/-- **★ The `WfContextUnion`-signed typed-implies-fibrantly-usable bridge (#1829 deliverable).**  A subject
union-typed at a universe code, under a well-formed context, is fibrantly usable — the three-line bridge
`WfContextUnion → AllLocksAreInterval → (the engine)`.  This is the fact the composite-data-former validity
rows discharge their `usabilityHolds` against: a type parameter typed at a universe code is never the locked
dimension (the lock carries the interval, which is not convertible to a universe code), so it stays fibrantly
accessible. -/
theorem typedAtUniverseImpliesFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context subject (universeCodeCell levelExpr flag)) :
    context.isSubjectUsableAtModality subject ObligationModality.fibrant = true :=
  typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval
    (WfContextUnion.allLocksAreInterval context wellFormed) typed

/-- The tail of a union-well-formed `cons` context is union-well-formed. -/
theorem WfContextUnion.tailWellFormed {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextUnion (restContext.cons bindingType)) :
    WfContextUnion restContext := wellFormed.1

/-- The head binding of a union-well-formed `cons` context is a union type. -/
theorem WfContextUnion.headIsType {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextUnion (restContext.cons bindingType)) :
    UnionClassifierIsType profile restContext bindingType := wellFormed.2.1

/-- The head binding of a union-well-formed `cons` context is NOT the affine interval (the #1805 non-fibrancy
conjunct).  The `cons`-arm dual of the `lockCons`-arm's `dimensionType = intervalTypeCell`. -/
theorem WfContextUnion.headNotInterval {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextUnion (restContext.cons bindingType)) :
    ¬ Conv bindingType intervalTypeCell := wellFormed.2.2

/-- **Union validity weakens under a binder.**  If a classifier is a union type, its weakening is a union
type under one extra binder — the universe-code classifier is rename-stable, so the SAME (level, flag)
serves.  The union analogue of `IsTypeDescPi.weakenUnderBinding`, built on the forward union weakening. -/
theorem UnionClassifierIsType.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (newBinding : RawTerm scope)
    (isType : UnionClassifierIsType profile context classifier) :
    UnionClassifierIsType profile (context.cons newBinding)
      (RawTerm.weaken classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  refine ⟨levelExpr, flag, ?_⟩
  have weakened := typed.weakenUnderBinding newBinding
  rwa [rename_universeCodeCell] at weakened

/-- **Union validity weakens under the affine dimension LOCK (`lockCons`)** — the `lockCons` twin of
`UnionClassifierIsType.weakenUnderBinding`, built on the native-union `HasTypeUnion.weakenUnderLockBinding`. -/
theorem UnionClassifierIsType.weakenUnderLockBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (dimensionType : RawTerm scope)
    (isType : UnionClassifierIsType profile context classifier) :
    UnionClassifierIsType profile (context.lockCons dimensionType)
      (RawTerm.weaken classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  refine ⟨levelExpr, flag, ?_⟩
  have weakened := typed.weakenUnderLockBinding dimensionType
  rwa [rename_universeCodeCell] at weakened

/-- The dimension hook weakens under a binder: the interval is rename-fixed, so `Conv classifier interval`
implies `Conv (weaken classifier) interval`.  (`Conv.weaken` + `rename_intervalTypeCell`.) -/
theorem UnionClassifierIsDimension.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (newBinding : RawTerm scope)
    (isDimension : UnionClassifierIsDimension profile context classifier) :
    UnionClassifierIsDimension profile (context.cons newBinding) (RawTerm.weaken classifier) := by
  show Conv (RawTerm.weaken classifier) intervalTypeCell
  have weakened : Conv (RawTerm.weaken classifier) (RawTerm.weaken (intervalTypeCell : RawTerm scope)) :=
    Conv.weaken isDimension
  rwa [show RawTerm.weaken (intervalTypeCell : RawTerm scope) = intervalTypeCell from
    rename_intervalTypeCell RawRenaming.weaken] at weakened

/-- The dimension hook weakens under the affine lock — the `lockCons` twin of the above. -/
theorem UnionClassifierIsDimension.weakenUnderLockBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (dimensionType : RawTerm scope)
    (isDimension : UnionClassifierIsDimension profile context classifier) :
    UnionClassifierIsDimension profile (context.lockCons dimensionType) (RawTerm.weaken classifier) := by
  show Conv (RawTerm.weaken classifier) intervalTypeCell
  have weakened : Conv (RawTerm.weaken classifier) (RawTerm.weaken (intervalTypeCell : RawTerm scope)) :=
    Conv.weaken isDimension
  rwa [show RawTerm.weaken (intervalTypeCell : RawTerm scope) = intervalTypeCell from
    rename_intervalTypeCell RawRenaming.weaken] at weakened

/-- A pretype weakens under a binder (dispatch on the disjunction). -/
theorem UnionClassifierIsPretype.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (newBinding : RawTerm scope)
    (isPretype : UnionClassifierIsPretype profile context classifier) :
    UnionClassifierIsPretype profile (context.cons newBinding) (RawTerm.weaken classifier) :=
  match isPretype with
  | Or.inl isType => Or.inl (isType.weakenUnderBinding newBinding)
  | Or.inr isDimension => Or.inr (isDimension.weakenUnderBinding newBinding)

/-- A pretype weakens under the affine lock (dispatch on the disjunction). -/
theorem UnionClassifierIsPretype.weakenUnderLockBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (dimensionType : RawTerm scope)
    (isPretype : UnionClassifierIsPretype profile context classifier) :
    UnionClassifierIsPretype profile (context.lockCons dimensionType) (RawTerm.weaken classifier) :=
  match isPretype with
  | Or.inl isType => Or.inl (isType.weakenUnderLockBinding dimensionType)
  | Or.inr isDimension => Or.inr (isDimension.weakenUnderLockBinding dimensionType)

/-- **Every binding of a union-well-formed context is a union type.**  The union analogue of
`WfContextDescPi.lookupIsType` — the per-variable validity the `ofGrown`/`var` arm of `classifierIsType`
reads to validate a variable's looked-up classifier (with NO host typing — the lookup is a union type). -/
theorem WfContextUnion.lookupIsType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextUnion context →
      ∀ index : Fin scope, UnionClassifierIsType profile context (context.lookup index) := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          rw [TypingContext.lookup_cons_zero]
          exact (WfContextUnion.headIsType wellFormed).weakenUnderBinding bindingType
      | succ priorValue =>
          rw [TypingContext.lookup_cons_succ]
          exact (ih (WfContextUnion.tailWellFormed wellFormed)
            ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding bindingType
  | lockCons restContext dimensionType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          rw [TypingContext.lookup_lockCons_zero, wellFormed.2]
          exact (UnionClassifierIsType.ofBaseTypeRow restContext .gen_intervalCode _ () .childNil
            rfl).weakenUnderLockBinding intervalTypeCell
      | succ priorValue =>
          rw [TypingContext.lookup_lockCons_succ]
          exact (ih wellFormed.1
            ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderLockBinding dimensionType

/-- **★ Every binding of a union-well-formed context is a PRETYPE** (#1886 / FIBRANCY-AXIS-0).  The
durable form of `lookupIsType`: a fibrant (`cons`) binding is a fibrant type; a locked (`lockCons`) dimension
binding is the interval dimension.  While the interval is still fibrant this lifts the strong `lookupIsType`
through `.toPretype`; once the interval becomes non-fibrant this is reproved by direct induction (the locked
lookup lands in the dimension disjunct `Or.inr`, not a universe code).  This is the var-arm tool of
`classifierIsPretype`. -/
theorem WfContextUnion.lookupIsPretype {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextUnion context →
      ∀ index : Fin scope, UnionClassifierIsPretype profile context (context.lookup index) := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          rw [TypingContext.lookup_cons_zero]
          exact ((WfContextUnion.headIsType wellFormed).weakenUnderBinding bindingType).toPretype
      | succ priorValue =>
          rw [TypingContext.lookup_cons_succ]
          exact (ih (WfContextUnion.tailWellFormed wellFormed)
            ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding bindingType
  | lockCons restContext dimensionType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          rw [TypingContext.lookup_lockCons_zero, wellFormed.2]
          exact Or.inr ((UnionClassifierIsDimension.interval restContext).weakenUnderLockBinding
            intervalTypeCell)
      | succ priorValue =>
          rw [TypingContext.lookup_lockCons_succ]
          exact (ih wellFormed.1
            ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderLockBinding dimensionType


/-! ## The honest residuals — the data-intro former and the substituting / projecting / handler elim
output types

These two oracles bundle the rows validity cannot close from the union IH alone.  Each is supplied as a
hypothesis to `HasTypeUnion.classifierIsType`, exactly as `HasTypeDescPi.piElimUpToClassifierConv` pins
its `classifierRespectsConv` — everything else in the lemma is shipped and unconditional. -/

/-- **The composite-data former residual (FULL, retained for back-compat).**  For each of the seven
composite data type-code former families, the output type is a well-formed union type.  After TYTAB-2
wave U3 the `optionFormed` / `listFormed` fields are THEOREMS
(`UnionClassifierIsType.optionFormed_ofValidity` / `listFormed_ofValidity`), so `HasTypeUnion.classifierIsType`
no longer takes this full structure — it takes the SHRUNK `UnionDataFormerResidual` (the five
genuinely-obstructed fields).  This full structure is retained because `UnionDataFormerResidual.ofFull`
projects it onto the residual, so any pre-U3 witness of the full structure still feeds the lemma; each field
is the precise output-type validity the matching intro row would deliver. -/
structure UnionDataFormerValidity (profile : PolyProfile) : Prop where
  /-- `lam`: `Π(domain).codomain` is a type given the domain is.  (The grown formation also needs the
  codomain under the domain-extended context; the union flat-formation arm demands GROWN child typings,
  which the union IH cannot supply — hence the residual.) -/
  piFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
    UnionClassifierIsType profile context domainCode →
    UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode)
  /-- `pathLam`: `Bridge carrier left right` is a type.  UNCONDITIONAL because the carrier validity lives
  in the interval-EXTENDED context (the pathLam body obligation classifies at `weaken carrierCode` under
  `context.cons intervalTypeCell`); strengthening it back across the interval binder to the base context is
  the genuine residual ingredient, so this one row's formation is supplied directly. -/
  bridgeFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope),
    UnionClassifierIsType profile context (bridgeTypeCell carrierCode leftEndpoint rightEndpoint)
  /-- `optionSome` / `optionNone`: `option(element)` is a type given the element is. -/
  optionFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (elementType : RawTerm scope),
    UnionClassifierIsType profile context elementType →
    UnionClassifierIsType profile context (optionTypeCell elementType)
  /-- `listCons` / `listNil`: `List(element)` is a type given the element is. -/
  listFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (elementType : RawTerm scope),
    UnionClassifierIsType profile context elementType →
    UnionClassifierIsType profile context (listTypeCell elementType)
  /-- `eitherInl` / `eitherInr`: `either(left, right)` is a type given both components are. -/
  eitherFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope),
    UnionClassifierIsType profile context leftType →
    UnionClassifierIsType profile context rightType →
    UnionClassifierIsType profile context (eitherTypeCell leftType rightType)
  /-- `pair`: `product(first, second)` is a type given both components are. -/
  productFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (firstType secondType : RawTerm scope),
    UnionClassifierIsType profile context firstType →
    UnionClassifierIsType profile context secondType →
    UnionClassifierIsType profile context (productTypeCell firstType secondType)
  /-- `refl`: `Id(type, left, right)` is a type given the carrier type is. -/
  idFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (typeCode left right : RawTerm scope),
    UnionClassifierIsType profile context typeCode →
    UnionClassifierIsType profile context (idTypeCell typeCode left right)

/-- **★ The composite-data former residual — now EMPTY (TYTAB-2 waves U3 + W3 + W4 + W5).**  Every one of the
original seven data-former fields is now a THEOREM:

  * `optionFormed` / `listFormed` (wave U3) — single-child cumulative formers re-form from the element validity
    (`optionFormed_ofValidity` / `listFormed_ofValidity`).
  * `piFormed` / `idFormed` (wave W3) — the `lam` / `refl` intro rows supply both type-parameter premises at a
    COMMON flag, so the Π / Id code re-forms via `piFormed_atCommonFlag` / `idFormed_ofCarrier`.
  * `bridgeFormed` (wave W4) — the `pathLam` case threads `WfContextUnion` (which admits the native interval
    binder) to invoke the body-premise IH, then `bridgeFormed_ofBodyValidity` re-forms the bridge code by
    interval-endpoint substitution (the "interval-strengthening frontier" was a closed substitution).
  * **`eitherFormed` / `productFormed` (wave W5)** — the former "FLAG-COHERENCE FRONTIER", now DISSOLVED by a
    construction-side rule refinement.  The wall was that the `pair` / `eitherInl` / `eitherInr` intro rows
    typed only the VALUE at its component type, leaving the two type params at INDEPENDENT flags while the flat
    `gen_productCode` / `gen_eitherCode` formation row demands ONE common flag (flag cumulativity being absent:
    `universeCodeCell_inj_of_conv` forces flag EQUALITY, `UniverseFlag.le_total` is inert in the judgment).
    The FIX (necessary AND sufficient, byte-matching the flat row, matching the Σ-formation
    `cumulativeBinderObligations` precedent): each intro rule now carries a formedness premise typing the
    value-side type param at the SAME row `flag`.  A flag-INCOHERENT `product(A@f1, B@f2)` is now
    unconstructible at intro, so the fragment validity must reconstruct is exactly the flag-coherent one the
    formation row accepts.  The rows then close directly via `productFormed_atCommonFlag` /
    `eitherFormed_atCommonFlag`.  It was never a metatheory wall — only an intro rule that under-specified its
    type params relative to the formation rule it must reconstruct.

`HasTypeUnion.classifierIsType` no longer takes ANY residual parameter — every data-former row is a theorem,
so the lemma is parameter-free (only the derivation and `WfContextUnion`).  `UnionDataFormerResidual` is kept
(empty) solely so `UnionDataFormerValidity.ofFull` and any historical witness still typecheck. -/
structure UnionDataFormerResidual (profile : PolyProfile) : Prop where
  -- ★ EMPTY (wave W5): every data-former row of validity is now a THEOREM.  The last two fields —
  -- `eitherFormed` / `productFormed`, once the "flag-coherence frontier" — discharged via
  -- `eitherFormed_atCommonFlag` / `productFormed_atCommonFlag` after the construction-side flag-coherence
  -- refinement of the `pair` / `eitherInl` / `eitherInr` intro rules (each now types both type params at the
  -- SAME row `flag`, matching the flat formation row it must reconstruct).  The frontier was never a
  -- metatheory wall — only an intro rule that under-specified its type params.  The structure is retained
  -- (empty) so `classifierIsType`'s arity and `ofFull` are stable for any existing call site.

/-- **The full data-former oracle projects onto the (now EMPTY) residual.**  Every data-former field
(`optionFormed` / `listFormed` / `piFormed` / `idFormed` / `bridgeFormed` / `eitherFormed` / `productFormed`)
is now a THEOREM, so the residual carries no obligation — any `UnionDataFormerValidity` witness (or none)
yields it.  Lets any holder of a full `UnionDataFormerValidity` witness feed `classifierIsType` unchanged. -/
def UnionDataFormerResidual.ofFull {profile : PolyProfile}
    (_dataFormers : UnionDataFormerValidity profile) : UnionDataFormerResidual profile := {}

/-- **The data-former residual holds UNCONDITIONALLY** (it is empty — every former row is a theorem). -/
theorem UnionDataFormerResidual.trivial {profile : PolyProfile} :
    UnionDataFormerResidual profile := {}

/-! ## ★ TYTAB-3: the eliminator-output residual is DELETED — the elim table is SELF-CERTIFYING

The former `UnionElimOutputValidity` oracle (its last field `eitherMatchOutputFormed`) is GONE.  Every
`ElimRule` row now premises its RESULT type's formedness at `universeCodeCell level0 flag` as the LAST entry
of its `rule.obligations` list — perfectly symmetric to the `IntroRule` table.  So `classifierIsType`'s elim
arm reads the result-type validity DIRECTLY off `premisesHold` (a uniform table read, like the
`formationRule` arm), and `eitherMatch`'s handler-inhabitant gap dissolves: the result type is premised
outright, no descent through a handler code needed.  `classifierIsType` is now FULLY UNCONDITIONAL — it takes
only the (empty) `UnionDataFormerResidual`, no elim-output oracle.  Soundness: a well-typed elimination's
result type IS always a valid type (that is what this very lemma proves), so premising result-formedness
rejects no genuinely-typeable program — it makes the elim table self-certifying, matching the intro table.

The bespoke per-row output helpers (`appOutputFormed_ofValidityAndArg`, `pathAppOutputFormed_ofValidity`,
`fstOutputFormed_ofValidity`, `sndOutputFormed_ofValidity`, the `invertAt…` validity uses) remain in this
file as standalone lemmas. -/

/-! ## ★ UNION CLASSIFIER VALIDITY — the main theorem -/

/-- **★ Union classifier validity — FULLY UNCONDITIONAL (TYTAB-3).**  Every union-typed subject's classifier
inhabits a universe code (`UnionClassifierIsType`), under the UNION well-formedness `WfContextUnion` (which
admits the native interval binder the host wf rejects — the key to the `pathLam` row).  There are NO residual
oracles AND NO residual parameter: every data-former row is a theorem (after wave W5's flag-coherence rule
refinement of the `pair` / `eitherInl` / `eitherInr` intro rows), and the elim-output oracle
`UnionElimOutputValidity` is DELETED — the `elim` table is now SELF-CERTIFYING (each row premises its result
type's formedness, read uniformly off `premisesHold`).  The lemma takes only the derivation and
`WfContextUnion`.

By `induction` on `derivation.toNativeOnly` (the SIX native-only arms — the host embedding is provably
redundant via `HasTypeUnion.iff_nativeOnly`, so the `ofGrown` host case never arises; each native arm's
`premisesHold` is re-embedded into `HasTypeUnion` via `.toUnion`):

  * **var** — `WfContextUnion.lookupIsType`: the context lookup is a union type.
  * **universeFormation** — `ofUniverseCode`: the universe code self-types.
  * **conv** — `reclassifierTyped.toUnion` IS the witness (the reclassifier is union-typed at a universe code).
  * **formationRule** — `ofFormationOutput`: the output is always a universe code.
  * **intro** — the 7 nullary-base rows close via `ofBaseTypeRow`; option / list (wave U3) via
    `optionFormed_ofValidity` / `listFormed_ofValidity`; Π / Id (wave W3) via `piFormed_atCommonFlag` /
    `idFormed_ofCarrier`; bridge (wave W4) via `bridgeFormed_ofBodyValidity` threading `WfContextUnion`; either
    / product (wave W5) via `eitherFormed_atCommonFlag` / `productFormed_atCommonFlag` (the refined intro
    premises supply both type params at one flag).  EVERY intro row is unconditional.
  * **elim** — ★ now a UNIFORM TABLE READ (TYTAB-3): every one of the 11 rows premises its result type's
    formedness at `universeCodeCell level0 flag` as the LAST `rule.obligations` entry, so the classifier
    validity is `⟨level0, flag, premisesHold _ <last-index>⟩` — symmetric to the `formationRule` arm.  No
    per-row helper, no IH-on-branch, no `eitherMatch` oracle. -/
theorem HasTypeUnion.classifierIsType {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier) :
    WfContextUnion context → UnionClassifierIsType profile context classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var context index =>
      intro wellFormed
      exact WfContextUnion.lookupIsType context wellFormed index
  | universeFormation context levelExpr flag =>
      intro _wellFormed
      exact UnionClassifierIsType.ofUniverseCode context levelExpr.lsucc flag
  | conv levelExpr flag typed converts reclassifierTyped _typedIH _reclassifierIH =>
      intro _wellFormed
      exact ⟨levelExpr, flag, reclassifierTyped.toUnion⟩
  | formationRule context generator payload children rule levels carrier level flag
      isFormationRule _premisesHold =>
      intro _wellFormed
      exact UnionClassifierIsType.ofFormationOutput context generator rule levels level flag
        isFormationRule
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      usabilityHolds ihPremises =>
      intro wellFormed
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- 1 boolTrue → boolTypeCell (nullary base)
      · exact UnionClassifierIsType.ofBaseTypeRow context .gen_boolCode _ () .childNil rfl
      -- 2 boolFalse → boolTypeCell
      · exact UnionClassifierIsType.ofBaseTypeRow context .gen_boolCode _ () .childNil rfl
      -- 3 unit → unitTypeCell
      · exact UnionClassifierIsType.ofBaseTypeRow context .gen_unitCode _ () .childNil rfl
      -- 4 interval0 → intervalTypeCell
      · exact UnionClassifierIsType.ofBaseTypeRow context .gen_intervalCode _ () .childNil rfl
      -- 5 interval1 → intervalTypeCell
      · exact UnionClassifierIsType.ofBaseTypeRow context .gen_intervalCode _ () .childNil rfl
      -- 6 natZero → natTypeCell
      · exact UnionClassifierIsType.ofBaseTypeRow context .gen_natCode _ () .childNil rfl
      -- 7 lam → piTyCodeCell domainCode codomainCode.  UNCONDITIONAL (wave W3): the lam intro premises
      -- type the domain (index 0) AND the binder-crossing codomain (index 1) at the SAME row `flag`, so the
      -- Π code re-forms directly via `piFormed_atCommonFlag` — no residual, no flag-coherence obstruction.
      · match args, params with
        | .childCons domainCode (.childCons _body .childNil), .childCons codomainCode .childNil =>
          have domainTyped : HasTypeUnion profile context domainCode
              (universeCodeCell level0 flag) := (premisesHold _ (List.Mem.head _)).toUnion
          have codomainTyped : HasTypeUnion profile (context.cons domainCode) codomainCode
              (universeCodeCell level1 flag) := (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion
          exact UnionClassifierIsType.piFormed_atCommonFlag context domainCode codomainCode
            level0 level1 flag wellFormed.allLocksAreInterval domainTyped codomainTyped
      -- 8 pathLam → bridgeTypeCell carrierCode (subst0 body i0) (subst0 body i1).  UNCONDITIONAL (wave W4):
      -- the body premise classifies `body : weaken carrierCode` UNDER `context.cons intervalTypeCell`.  Since
      -- `WfContextUnion` ADMITS the native interval binder (`ofBaseTypeRow` makes `intervalTypeCell` a union
      -- type), the IH on the body premise gives the carrier-under-interval validity, which
      -- `bridgeFormed_ofBodyValidity` descends to the base context by interval-`0` substitution (NOT
      -- strengthening — a closed `subst0_weaken` collapse).
      · match args, params with
        | .childCons body .childNil, .childCons carrierCode .childNil =>
          have intervalWellFormed : WfContextUnion (context.lockCons intervalTypeCell) :=
            WfContextUnion.lockCons wellFormed rfl
          have carrierUnderIntervalIsType := ihPremises _ (List.Mem.head _) intervalWellFormed
          have bodyTyped : HasTypeUnion profile (context.lockCons intervalTypeCell) body
              (RawTerm.weaken carrierCode) := (premisesHold _ (List.Mem.head _)).toUnion
          exact UnionClassifierIsType.bridgeFormed_ofBodyPremise context carrierCode body
            wellFormed.allLocksAreInterval (usabilityHolds _ (List.Mem.head _))
            carrierUnderIntervalIsType bodyTyped
      -- 9 natSucc → natTypeCell (nullary base output)
      · match args with
        | .childCons _child .childNil =>
          exact UnionClassifierIsType.ofBaseTypeRow context .gen_natCode _ () .childNil rfl
      -- 10 listCons → listTypeCell elementType.  The single-child cumulative former re-forms from the element
      -- validity (index-0 IH): `elementType` is union-typed at a universe code (the IH witness), and
      -- `listFormed_ofValidity` re-forms the list code from that validity.  No use-site usability obligation is
      -- involved — the lock-accessibility discipline lives solely at the variable rule (`HasTypeUnionOver.var`'s
      -- `isAccessible` premise), not on this formation arm.
      · match args, params with
        | .childCons _head (.childCons _tail .childNil), .childCons elementType .childNil =>
          obtain ⟨elementLevel, elementFlag, elementTyped⟩ := ihPremises _ (List.Mem.head _) wellFormed
          exact UnionClassifierIsType.listFormed_ofValidity context elementType
            wellFormed.allLocksAreInterval ⟨elementLevel, elementFlag, elementTyped⟩
      -- 11 optionSome → optionTypeCell typeParam0.  `typeParam0`'s FIBRANT usability is NOT an intro subject
      -- (the optionSome obligation is value@typeParam0), so it is discharged by the typed-implies-fibrantly-usable
      -- bridge: `typeParam0` is union-typed at a universe code (the IH witness), hence fibrantly usable.
      · match args, params with
        | .childCons _value .childNil, .childCons typeParam0 .childNil =>
          obtain ⟨elementLevel, elementFlag, elementTyped⟩ := ihPremises _ (List.Mem.head _) wellFormed
          exact UnionClassifierIsType.optionFormed_ofValidity context typeParam0
            wellFormed.allLocksAreInterval ⟨elementLevel, elementFlag, elementTyped⟩
      -- 12 optionNone → optionTypeCell typeParam0.  UNCONDITIONAL (wave U3): the index-0 obligation
      -- (`typeParam0 : universeCode level0 flag`) is the PREMISE.
      · match params with
        | .childCons typeParam0 .childNil =>
          have elementIsType : UnionClassifierIsType profile context typeParam0 :=
            ⟨level0, flag, (premisesHold _ (List.Mem.head _)).toUnion⟩
          exact UnionClassifierIsType.optionFormed_ofValidity context typeParam0
            wellFormed.allLocksAreInterval elementIsType
      -- 13 listNil → listTypeCell typeParam0 (same shape as optionNone).  UNCONDITIONAL (wave U3).
      · match params with
        | .childCons typeParam0 .childNil =>
          have elementIsType : UnionClassifierIsType profile context typeParam0 :=
            ⟨level0, flag, (premisesHold _ (List.Mem.head _)).toUnion⟩
          exact UnionClassifierIsType.listFormed_ofValidity context typeParam0
            wellFormed.allLocksAreInterval elementIsType
      -- 14 eitherInl → eitherTypeCell typeParam0 typeParam1.  UNCONDITIONAL (wave W5): the refined eitherInl
      -- intro premises type the RIGHT type param (index 1) AND the LEFT type param (index 2) at the SAME row
      -- `flag` (level0 and level1 respectively), so the either code re-forms directly via
      -- `eitherFormed_atCommonFlag` — no residual, the flag-coherence obstruction dissolved by the rule
      -- refinement.
      · match args, params with
        | .childCons _value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have leftTyped : HasTypeUnion profile context typeParam0 (universeCodeCell level1 flag) :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion
          have rightTyped : HasTypeUnion profile context typeParam1 (universeCodeCell level0 flag) :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion
          exact UnionClassifierIsType.eitherFormed_atCommonFlag context typeParam0 typeParam1
            level1 level0 flag wellFormed.allLocksAreInterval leftTyped rightTyped
      -- 15 eitherInr → eitherTypeCell typeParam1 typeParam0 (output swaps the two type params).
      -- UNCONDITIONAL (wave W5): same refined premises, output puts the free side first.
      · match args, params with
        | .childCons _value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have rightTyped : HasTypeUnion profile context typeParam0 (universeCodeCell level1 flag) :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion
          have leftTyped : HasTypeUnion profile context typeParam1 (universeCodeCell level0 flag) :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion
          exact UnionClassifierIsType.eitherFormed_atCommonFlag context typeParam1 typeParam0
            level0 level1 flag wellFormed.allLocksAreInterval leftTyped rightTyped
      -- 16 pair → productTypeCell typeParam0 typeParam1.  UNCONDITIONAL (wave W5): the refined pair intro
      -- premises type BOTH type params at the SAME row `flag` (index 2 = typeParam0 at level0, index 3 =
      -- typeParam1 at level1), so the product code re-forms directly via `productFormed_atCommonFlag`.
      · match args, params with
        | .childCons _child0 (.childCons _child1 .childNil),
          .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have firstTyped : HasTypeUnion profile context typeParam0 (universeCodeCell level0 flag) :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion
          have secondTyped : HasTypeUnion profile context typeParam1 (universeCodeCell level1 flag) :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion
          exact UnionClassifierIsType.productFormed_atCommonFlag context typeParam0 typeParam1
            level0 level1 flag wellFormed.allLocksAreInterval firstTyped secondTyped
      -- 17 refl → idTypeCell typeParam0 witness witness.  UNCONDITIONAL (wave W3): index-0 premise is
      -- `witness : typeParam0` (the endpoint-at-carrier), the IH on it gives the carrier validity, and the
      -- two endpoints ARE the witness typed at the carrier — `idFormed_ofCarrier` re-forms the Id code at the
      -- carrier's single flag.  No use-site usability obligation is involved: the lock-accessibility discipline
      -- lives solely at the variable rule (`HasTypeUnionOver.var`'s `isAccessible` premise), not on this
      -- formation arm.
      · match args, params with
        | .childCons witness .childNil, .childCons typeParam0 .childNil =>
          have witnessTyped : HasTypeUnion profile context witness typeParam0 :=
            (premisesHold _ (List.Mem.head _)).toUnion
          obtain ⟨carrierLevel, carrierFlag, carrierTyped⟩ := ihPremises _ (List.Mem.head _) wellFormed
          exact UnionClassifierIsType.idFormed_ofCarrier context typeParam0 witness
            wellFormed.allLocksAreInterval (usabilityHolds _ (List.Mem.head _))
            ⟨carrierLevel, carrierFlag, carrierTyped⟩ witnessTyped
  | elim context generator rule args params level0 level1 flag isElim premisesHold
      usabilityHolds ihPremises =>
      -- ★ THE (ALMOST-FULLY) SELF-CERTIFYING ELIM ARM (TYTAB-3): TEN of the eleven rows now premise their
      -- RESULT type's formedness at `universeCodeCell level0 flag` as the LAST obligation of their
      -- `rule.obligations` list, EXACTLY as the `intro` table does — so their classifier validity is a
      -- UNIFORM TABLE READ `⟨level0, flag, premisesHold _ <last-index>⟩`, no bespoke helper, no IH-on-branch,
      -- no `eitherMatch` oracle.  The SOLE exception is `app` (the grown engine's eliminator), whose output
      -- formedness lives HERE where `WfContextUnion` is available (the host-substitution path cannot supply
      -- it table-locally — the var-leaf wall): its case uses `appOutputFormed_ofValidityAndArg` exactly as
      -- before.  `rcases` the table hit to fix each row's obligation-list length, then read its last entry.
      intro wellFormed
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- 1 app — NON-self-certifying (see `appElimRule`): IH on the function (index 0) gives the Π code is a
      -- type; `appOutputFormed_ofValidityAndArg` inverts the codomain and substitutes the argument (index 1).
      · match args, params with
        | .childCons _function (.childCons argument .childNil),
          .childCons domainCode (.childCons codomainCode .childNil) =>
          have functionTypeIsType := ihPremises _ (List.Mem.head _) wellFormed
          have argumentTyped : HasTypeUnion profile context argument domainCode :=
            (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion
          exact UnionClassifierIsType.appOutputFormed_ofValidityAndArg context domainCode codomainCode
            argument functionTypeIsType argumentTyped
            (usabilityHolds _ (List.Mem.tail _ (List.Mem.head _)))
      -- 2 pathApp: self-certifying, 3 obligations, result-formedness (carrierCode) at index 2.
      · match args, params with
        | .childCons _path (.childCons _argument .childNil),
          .childCons _carrierCode (.childCons _leftEndpoint (.childCons _rightEndpoint .childNil)) =>
          exact ⟨level0, flag, (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion⟩
      -- 3 natElim: DEPENDENT — output `subst0 motive scrutinee` (app-unhardened regime, paramShifts []).
      -- Result-formedness is reconstructed from the motive obligation (index 3, universe-typed under
      -- `natTypeCell`) and the scrutinee obligation (index 0) via `dependentMotiveOutputFormed_ofMotiveAndArgument`.
      · match args with
        | .childCons motive (.childCons _baseBranch (.childCons _stepBranch
            (.childCons scrutinee .childNil))) =>
          exact UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context _ motive
            scrutinee level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))
      -- 4 natRec: DEPENDENT — identical to natElim (shared substrate; only the cell former differs).
      · match args with
        | .childCons motive (.childCons _baseBranch (.childCons _stepBranch
            (.childCons scrutinee .childNil))) =>
          exact UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context _ motive
            scrutinee level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))
      -- 5 boolElim: DEPENDENT — output `subst0 motive scrutinee`.  App-unhardened regime (paramShifts []):
      -- formedness is NOT a result-type param read but reconstructed from the motive obligation (index 3,
      -- universe-typed under `boolTypeCell`) and the scrutinee obligation (index 0) via brick-1
      -- `dependentMotiveOutputFormed_ofMotiveAndArgument` — exactly the `app` discipline.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons _thenBranch
            (.childCons _elseBranch .childNil))), .childNil =>
          exact UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context _ motive
            scrutinee level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))
      -- 6 optionMatch: DEPENDENT — output `subst0 motive scrutinee`; its formedness is reconstructed (app-style,
      -- unhardened) from the motive obligation (index 3, motive@universe under `option(A)`) and the scrutinee
      -- typing (index 0) via `dependentMotiveOutputFormed_ofMotiveAndArgument` — mirrors the boolElim/eitherMatch arm.
      · match args, params with
        | .childCons motive (.childCons _noneBranch (.childCons _someBranch
            (.childCons scrutinee .childNil))),
          .childCons _typeParamA (.childCons _typeParamB .childNil) =>
          exact UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context _ motive
            scrutinee level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))
      -- 7 eitherMatch: DEPENDENT — output `subst0 motive scrutinee`; its formedness is reconstructed (app-style,
      -- unhardened) from the motive obligation (index 3, motive@universe under `either(A, B)`) and the scrutinee
      -- typing (index 0) via `dependentMotiveOutputFormed_ofMotiveAndArgument` — mirrors the boolElim arm.
      · match args, params with
        | .childCons motive (.childCons _leftBranch (.childCons _rightBranch
            (.childCons scrutinee .childNil))),
          .childCons _typeParamA (.childCons _typeParamB .childNil) =>
          exact UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context _ motive
            scrutinee level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))
      -- 8 idJ: DEPENDENT (genuine Paulin-Mohring) — output `idJMotiveAt motive right witness`; its formedness is
      -- the two-binder transport of the motive obligation (index 3, motive@universe under TWO binders) along the
      -- right-endpoint typing (index 1) and the witness identity typing (index 0), via
      -- `idJOutputFormed_ofMotiveEndpointWitness`.  The UNIQUE eliminator whose output is a two-variable subst.
      · match args, params with
        | .childCons motive (.childCons _baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
          exact UnionClassifierIsType.idJOutputFormed_ofMotiveEndpointWitness context
            typeCode leftEndpoint rightEndpoint motive witness level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))
            (usabilityHolds _ (List.Mem.tail _ (List.Mem.head _)))
      -- 9 fst: self-certifying, 2 obligations, result-formedness (firstType) at index 1.
      · match args, params with
        | .childCons _pairTerm .childNil,
          .childCons _firstType (.childCons _secondType .childNil) =>
          exact ⟨level0, flag, (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion⟩
      -- 10 snd: self-certifying, 2 obligations, result-formedness (secondType) at index 1.
      · match args, params with
        | .childCons _pairTerm .childNil,
          .childCons _firstType (.childCons _secondType .childNil) =>
          exact ⟨level0, flag, (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion⟩
      -- 11 listElim: DEPENDENT — output `subst0 motive scrutinee`; its formedness is reconstructed (app-style,
      -- unhardened) from the motive obligation (index 3, motive@universe under `List(A)`) and the scrutinee
      -- typing (index 0) via `dependentMotiveOutputFormed_ofMotiveAndArgument` — mirrors the natElim/optionMatch arm.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons _nilBranch
            (.childCons _consBranch .childNil))),
          .childCons _elementType (.childCons _resultType .childNil) =>
          exact UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument context _ motive
            scrutinee level0 flag
            ((premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).toUnion)
            ((premisesHold _ (List.Mem.head _)).toUnion)
            (usabilityHolds _ (List.Mem.head _))

/-- **★ The PRETYPE validity invariant** (#1886 / FIBRANCY-AXIS-0) — the honest, DURABLE conclusion of union
classifier validity: every well-typed subject's classifier is a fibrant type OR the interval dimension
(`UnionClassifierIsPretype`).  This is the form the SR drift / gate machinery and the SR closure consume; a
fibrancy-needing site recovers the strong `UnionClassifierIsType` via `.resolveType` (discharging the dimension
disjunct with the `IntervalNotConvRigidHeads` family — you cannot Π/Σ over the interval).

While the interval is still fibrant this lifts the strong `classifierIsType` through `.toPretype`; once the
interval becomes non-fibrant `classifierIsType` retires and this is reproved by direct induction (the only arm
that changes is `var` at a `lockCons`-0 position, which lands in the dimension disjunct). -/
theorem HasTypeUnion.classifierIsPretype {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context) :
    UnionClassifierIsPretype profile context classifier :=
  (HasTypeUnion.classifierIsType derivation wellFormed).toPretype

end FX1Poly.Typed
