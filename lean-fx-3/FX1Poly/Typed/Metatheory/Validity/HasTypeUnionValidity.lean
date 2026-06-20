import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiClassifierValidity

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

open FX1Poly.Core FX1Poly.Universe

/-- **The union classifier-validity conclusion.**  A classifier is a well-formed union type iff it
inhabits SOME universe code in the union judgment.  A universe code satisfies this by self-typing
(`universeCodeCell L f : universeCodeCell L.lsucc f`), so this one existential carries the "is a universe
code" case too. -/
def UnionClassifierIsType (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeUnion profile context classifier (universeCodeCell levelExpr flag)

/-- **A universe code is a well-formed union type.**  `universeCodeCell L f` is union-typed at
`universeCodeCell L.lsucc f` by the host `universeFormation` rule, embedded via `ofGrown`. -/
theorem UnionClassifierIsType.ofUniverseCode {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    UnionClassifierIsType profile context (universeCodeCell levelExpr flag) :=
  ⟨levelExpr.lsucc, flag,
    HasTypeUnion.ofGrown
      (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context levelExpr flag))⟩

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
    HasTypeUnion.formationRule context generator payload children (.baseType baseRule)
      [] (.mkGen generator payload children) LevelExpr.lzero UniverseFlag.standard isBaseRow trivial
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
  | termIndexed termRule =>
      have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
        formationRuleOf_termIndexed_inv isFormationRule
      rw [termIndexedFormerDescOf_outputIsUniverse isTermIndexed]
      show UnionClassifierIsType profile context (universeCodeCell level flag)
      exact UnionClassifierIsType.ofUniverseCode context level flag

/-! ## The honest residuals — the data-intro former and the substituting / projecting / handler elim
output types

These two oracles bundle the rows validity cannot close from the union IH alone.  Each is supplied as a
hypothesis to `HasTypeUnion.classifierIsType`, exactly as `HasTypeDescPi.piElimUpToClassifierConv` pins
its `classifierRespectsConv` — everything else in the lemma is shipped and unconditional. -/

/-- **The composite-data former residual.**  For each of the ten composite data type-code formers, the
output type is a well-formed union type.  Re-forming the code (`piTyCodeCell`, `optionTypeCell`, …) needs
a GROWN (`HasTypeDescPi`) typing of the type PARAMETERS, but the intro arm's IH yields only a UNION
typing — and there is no union→grown reflection at universe codes (the fundamental wall the union
dissolves for TERMS but not for the formation premise).  Each field is the precise output-type validity
the matching intro row would deliver. -/
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

/-- **The substituting / projecting / handler-typed eliminator residual.**  For the five elim rows whose
output type is NOT directly a branch classifier, the output type's validity follows from a genuine
further ingredient, supplied here CONDITIONED on the data the elim arm's IH already delivers (so each
field is the honest inversion / substitution obligation, never "any term is a type"):

  * `app` — `subst0 codomainCode argument` is a type given the function classifier
    `piTyCodeCell domainCode codomainCode` is a type (substitution-preserves-formation).
  * `pathApp` — `carrierCode` is a type given `bridgeTypeCell carrierCode left right` is a type
    (bridge-code inversion).
  * `fst` / `snd` — the projected component is a type given `productTypeCell first second` is a type
    (product-code inversion).
  * `eitherMatch` — `resultType` is a type given the handler code `piTyCodeCell typeParam (weaken
    resultType)` is a type (Pi-code inversion + strengthening). -/
structure UnionElimOutputValidity (profile : PolyProfile) : Prop where
  /-- `app`: substitution preserves formation — `subst0 codomainCode argument` is a type when the Π-code
  classifying the function is. -/
  appOutputFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) (argument : RawTerm scope),
    UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode) →
    UnionClassifierIsType profile context (RawTerm.subst0 codomainCode argument)
  /-- `pathApp`: bridge-code inversion — the carrier is a type when the bridge code is. -/
  pathAppOutputFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope),
    UnionClassifierIsType profile context (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) →
    UnionClassifierIsType profile context carrierCode
  /-- `fst`: product-code inversion — the first component is a type when the product code is. -/
  fstOutputFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (firstType secondType : RawTerm scope),
    UnionClassifierIsType profile context (productTypeCell firstType secondType) →
    UnionClassifierIsType profile context firstType
  /-- `snd`: product-code inversion — the second component is a type when the product code is. -/
  sndOutputFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (firstType secondType : RawTerm scope),
    UnionClassifierIsType profile context (productTypeCell firstType secondType) →
    UnionClassifierIsType profile context secondType
  /-- `eitherMatch`: Π-code inversion + strengthening — the result is a type when the handler code
  `Π(typeParam).(weaken resultType)` is. -/
  eitherMatchOutputFormed : ∀ {scope : Nat} (context : TypingContext profile scope)
    (typeParam resultType : RawTerm scope),
    UnionClassifierIsType profile context
      (piTyCodeCell typeParam (RawTerm.weaken resultType)) →
    UnionClassifierIsType profile context resultType

/-! ## ★ UNION CLASSIFIER VALIDITY — the main theorem -/

/-- **★ Union classifier validity.**  Every union-typed subject's classifier inhabits a universe code
(`UnionClassifierIsType`), under the grown well-formedness `WfContextDescPi` (the same notion the host
validity uses) and the two honest residual oracles.

By `induction` on the union derivation (5 arms):

  * **conv** — `reclassifierTyped` IS the witness (the reclassifier is union-typed at a universe code).
  * **ofGrown** — host validity `HasTypeDescPi.classifierIsTypeDescPi` re-embedded via `ofGrown`.
  * **formationRule** — `ofFormationOutput`: the output is always a universe code.
  * **intro** — the 7 nullary-base rows close via `ofBaseTypeRow`; the 10 composite-data rows close via
    `dataFormers` fed the component validity sourced from the IH / param premise.
  * **elim** — the 6 branch-selecting rows close via the IH on the branch typed at the output `resultType`;
    the 5 substituting / projecting / handler rows close via `elimOutputs` fed the scrutinee/function
    classifier validity sourced from the IH. -/
theorem HasTypeUnion.classifierIsType {profile : PolyProfile}
    (dataFormers : UnionDataFormerValidity profile)
    (elimOutputs : UnionElimOutputValidity profile)
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier) :
    WfContextDescPi context → UnionClassifierIsType profile context classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped _typedIH _reclassifierIH =>
      intro _wellFormed
      exact ⟨levelExpr, flag, reclassifierTyped⟩
  | ofGrown hostTyped =>
      intro wellFormed
      obtain ⟨levelExpr, flag, classifierTyped⟩ :=
        HasTypeDescPi.classifierIsTypeDescPi wellFormed hostTyped
      exact ⟨levelExpr, flag, HasTypeUnion.ofGrown classifierTyped⟩
  | formationRule context generator payload children rule levels carrier level flag
      isFormationRule premise =>
      intro _wellFormed
      exact UnionClassifierIsType.ofFormationOutput context generator rule levels level flag
        isFormationRule
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
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
      -- 7 lam → piTyCodeCell domainCode codomainCode.
      -- index-0 obligation = `domainCode : universeCode level0 flag`, so the PREMISE itself witnesses
      -- `domainCode` is a type.
      · match args, params with
        | .childCons domainCode (.childCons _body .childNil), .childCons codomainCode .childNil =>
          have domainIsType : UnionClassifierIsType profile context domainCode :=
            ⟨level0, flag, premisesHold _ (List.Mem.head _)⟩
          exact dataFormers.piFormed context domainCode codomainCode domainIsType
      -- 8 pathLam → bridgeTypeCell carrierCode (subst0 body i0) (subst0 body i1).
      -- The carrier validity lives in the interval-extended context (the body obligation's classifier is
      -- `weaken carrierCode` at `scope + 1`); strengthening it to the base context is the genuine gap, so
      -- the bridge formation is supplied UNCONDITIONALLY by the residual oracle for this one row.
      · match args, params with
        | .childCons _body .childNil, .childCons carrierCode .childNil =>
          exact dataFormers.bridgeFormed context carrierCode
            (RawTerm.subst0 _body intervalZeroCell) (RawTerm.subst0 _body intervalOneCell)
      -- 9 natSucc → natTypeCell (nullary base output)
      · match args with
        | .childCons _child .childNil =>
          exact UnionClassifierIsType.ofBaseTypeRow context .gen_natCode _ () .childNil rfl
      -- 10 listCons → listTypeCell elementType.
      -- index-0 obligation = `head : elementType`, so the IH on it gives `elementType` is a type.
      · match args, params with
        | .childCons _head (.childCons _tail .childNil), .childCons elementType .childNil =>
          have elementIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact dataFormers.listFormed context elementType elementIsType
      -- 11 optionSome → optionTypeCell typeParam0.  index-0 = `value : typeParam0`; IH → typeParam0 type.
      · match args, params with
        | .childCons _value .childNil, .childCons typeParam0 .childNil =>
          have elementIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact dataFormers.optionFormed context typeParam0 elementIsType
      -- 12 optionNone → optionTypeCell typeParam0.
      -- index-0 obligation = `typeParam0 : universeCode level0 flag`, so the PREMISE witnesses it.
      · match params with
        | .childCons typeParam0 .childNil =>
          have elementIsType : UnionClassifierIsType profile context typeParam0 :=
            ⟨level0, flag, premisesHold _ (List.Mem.head _)⟩
          exact dataFormers.optionFormed context typeParam0 elementIsType
      -- 13 listNil → listTypeCell typeParam0 (same shape as optionNone)
      · match params with
        | .childCons typeParam0 .childNil =>
          have elementIsType : UnionClassifierIsType profile context typeParam0 :=
            ⟨level0, flag, premisesHold _ (List.Mem.head _)⟩
          exact dataFormers.listFormed context typeParam0 elementIsType
      -- 14 eitherInl → eitherTypeCell typeParam0 typeParam1.
      -- index-0 = `value : typeParam0` (IH → typeParam0 type); index-1 = `typeParam1 : universe`
      -- (premise → typeParam1 type).
      · match args, params with
        | .childCons _value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have leftIsType := ihPremises _ (List.Mem.head _) wellFormed
          have rightIsType : UnionClassifierIsType profile context typeParam1 :=
            ⟨level0, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
          exact dataFormers.eitherFormed context typeParam0 typeParam1 leftIsType rightIsType
      -- 15 eitherInr → eitherTypeCell typeParam1 typeParam0 (output swaps the two type params)
      · match args, params with
        | .childCons _value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have firstIsType := ihPremises _ (List.Mem.head _) wellFormed
          have secondIsType : UnionClassifierIsType profile context typeParam1 :=
            ⟨level0, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
          exact dataFormers.eitherFormed context typeParam1 typeParam0 secondIsType firstIsType
      -- 16 pair → productTypeCell typeParam0 typeParam1.
      -- index-0 = `child0 : typeParam0`; index-1 = `child1 : typeParam1`; IH on both.
      · match args, params with
        | .childCons _child0 (.childCons _child1 .childNil),
          .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have firstIsType := ihPremises _ (List.Mem.head _) wellFormed
          have secondIsType := ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
          exact dataFormers.productFormed context typeParam0 typeParam1 firstIsType secondIsType
      -- 17 refl → idTypeCell typeParam0 witness witness.
      -- index-0 = `witness : typeParam0`; IH → typeParam0 type.
      · match args, params with
        | .childCons _witness .childNil, .childCons typeParam0 .childNil =>
          have typeIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact dataFormers.idFormed context typeParam0 _witness _witness typeIsType
  | elim context generator rule args params isElim premisesHold ihPremises =>
      intro wellFormed
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- 1 app → subst0 codomainCode argument.  IH on the function (index 0) gives the Π-code is a type;
      -- the residual transports through the substitution.
      · match args, params with
        | .childCons _function (.childCons argument .childNil),
          .childCons domainCode (.childCons codomainCode .childNil) =>
          have functionTypeIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact elimOutputs.appOutputFormed context domainCode codomainCode argument functionTypeIsType
      -- 2 pathApp → carrierCode.  IH on the path (index 0) gives the bridge code is a type; the residual
      -- inverts it to the carrier.
      · match args, params with
        | .childCons _path (.childCons _argument .childNil),
          .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
          have bridgeIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact elimOutputs.pathAppOutputFormed context carrierCode leftEndpoint rightEndpoint
            bridgeIsType
      -- 3 natElim → resultType.  IH on the base branch (index 1, typed AT resultType, original context).
      · match args, params with
        | .childCons _motive (.childCons _baseBranch (.childCons _stepBranch
            (.childCons _scrutinee .childNil))), .childCons _resultType .childNil =>
          exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
      -- 4 natRec → resultType (same shape as natElim)
      · match args, params with
        | .childCons _motive (.childCons _baseBranch (.childCons _stepBranch
            (.childCons _scrutinee .childNil))), .childCons _resultType .childNil =>
          exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
      -- 5 boolElim → resultType.  IH on the THEN branch (index 1, typed AT resultType).
      · match args, params with
        | .childCons _motive (.childCons _scrutinee (.childCons _thenBranch
            (.childCons _elseBranch .childNil))),
          .childCons _typeParamA (.childCons _typeParamB (.childCons _resultType .childNil)) =>
          exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
      -- 6 optionMatch → resultType.  IH on the NONE branch (index 1, typed AT resultType).
      · match args, params with
        | .childCons _motive (.childCons _noneBranch (.childCons _someBranch
            (.childCons _scrutinee .childNil))),
          .childCons _typeParamA (.childCons _typeParamB (.childCons _resultType .childNil)) =>
          exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
      -- 7 eitherMatch → resultType.  No branch is typed AT resultType (both at handler codes
      -- `Π(typeParam).(weaken resultType)`); IH on the LEFT branch (index 1) gives the handler code is a
      -- type, and the residual inverts + strengthens to resultType.
      · match args, params with
        | .childCons _motive (.childCons _leftBranch (.childCons _rightBranch
            (.childCons _scrutinee .childNil))),
          .childCons typeParamA (.childCons _typeParamB (.childCons resultType .childNil)) =>
          have handlerIsType := ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
          exact elimOutputs.eitherMatchOutputFormed context typeParamA resultType handlerIsType
      -- 8 idJ → resultType.  IH on the base case (index 1, typed AT resultType).
      · match args, params with
        | .childCons _motive (.childCons _baseCase (.childCons _witness .childNil)),
          .childCons _typeCode (.childCons _endpoint (.childCons _resultType .childNil)) =>
          exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed
      -- 9 fst → firstType.  IH on the pair term (index 0) gives the product code is a type; the residual
      -- inverts it to the first component.
      · match args, params with
        | .childCons _pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have productIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact elimOutputs.fstOutputFormed context firstType secondType productIsType
      -- 10 snd → secondType (same shape as fst, second component)
      · match args, params with
        | .childCons _pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have productIsType := ihPremises _ (List.Mem.head _) wellFormed
          exact elimOutputs.sndOutputFormed context firstType secondType productIsType
      -- 11 listElim → resultType.  IH on the NIL branch (index 1, typed AT resultType).
      · match args, params with
        | .childCons _motive (.childCons _scrutinee (.childCons _nilBranch
            (.childCons _consBranch .childNil))),
          .childCons _elementType (.childCons _resultType .childNil) =>
          exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) wellFormed

end FX1Poly.Typed
