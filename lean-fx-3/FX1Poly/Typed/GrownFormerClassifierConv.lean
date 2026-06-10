import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion
import FX1Poly.Typed.PiTypeFunctionInversion
import FX1Poly.Typed.EmptyTypeValueInversion
import FX1Poly.Typed.ListCodeShape

/-! # FX1Poly/Typed/GrownFormerClassifierConv
    — the GROWN head-agnostic former-classifier inversion + the `listCode` piElim/empty refutations (GTL-11)

The formation engine ships `HasTypeDesc.inversionFormerWithConvGeneric` (`HasTypeDescFormerTelescopeInversion`):
for ANY generator carrying a `typingRuleDescOf` rule, a formation derivation of a cell with that head has its
classifier `Conv` a universe code.  This file is the GROWN-engine twin — the cascade-free former inversion the
grown canonical-forms `piElim` crux needs once a data type code (`listCode`, GTL-11) joins the table.

## The grown generic inversion

`HasTypeDescPi.formerClassifierConvUniverseGeneric` mirrors the formation version over `HasTypeDescPi`'s five
arms: `ofFormation` delegates to the formation generic inversion; `conv` recurses and threads the classifier
`Conv` through (`Conv.trans`); `piIntro` / `piElim` are refuted (their `gen_lam` / `gen_app` heads are not in
`typingRuleDescOf`, the `if_neg` non-former branch — now three-way over Π / Σ / list); `genFormationPi` reads
the classifier off the row-shape-agnostic `typingRuleDescOf_output_isUniverseCode` (output is SOME universe
code) + `Conv.refl`.  Head-agnostic: a future data type code — including a flag-pinned nullary row — is
absorbed with no new arm — exactly the FRAME-2 extensibility property at the grown layer.

## The two `listCode` refutations

`listFormerNotTypedAtPiType` / `listFormerNotTypedAtEmptyType` specialize the generic inversion to the
`gen_listCode` former: its classifier `Conv` a universe code refutes against a Π-type / empty-type classifier
(`Conv.piTyCode_not_universeCode` / `Conv.universeCode_not_emptyTypeCode`), exactly as the shipped Π / Σ /
universe `*NotTypedAt{Pi,Empty}Type` lemmas do.  These are the head→shape reconstructions
(`eq_listCodeCell_of_headGenerator`) plus the generic inversion that the `gen_listCode` branch of the grown
closed canonical-forms (`GrownCanonicalForms.lean`: `closedNormalSubjectHead`'s `piElim` arm, and the grown
consistency theorem's empty-type arm) reads.

## Zero-axiom verification

Term-mode dependent `match` on the five grown arms + `congrArg RawTerm.headGenerator` head-equalities +
`unfold typingRuleDescOf` / `if_neg` non-former discharge + `typingRuleDescOf_output_isUniverseCode` +
`Conv.refl` / `Conv.trans`; the specializations add `eq_listCodeCell_of_headGenerator` + a single Conv
refutation.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Grown head-agnostic former-classifier inversion.**  For any generator carrying a `typingRuleDescOf` rule,
a grown derivation whose subject is a cell with that head has its classifier `Conv` a universe code.  The grown
twin of `HasTypeDesc.inversionFormerWithConvGeneric`: `ofFormation` delegates to the formation generic
inversion, `conv` threads the `Conv`, `piIntro` / `piElim` hit the non-former `if_neg` branch, `genFormationPi`
reads the classifier off `universeFormerOutput`.  Head-agnostic — a future data type code is absorbed with no
new arm. -/
theorem HasTypeDescPi.formerClassifierConvUniverseGeneric {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    ∀ {payload : generator.payload generalScope}
      {children : RawTermChildren generator.binderShifts generalScope},
      subject = RawTerm.mkGen generator payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
  fun {_payloadImplicit} {_childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, _telescope, convToCode⟩ :=
          HasTypeDesc.inversionFormerWithConvGeneric formationTyped isFormation subjectEq
        exact ⟨levels, flag, convToCode⟩
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨levels, flag, convToCode⟩ :=
          HasTypeDescPi.formerClassifierConvUniverseGeneric typedPremise isFormation subjectEq
        exact ⟨levels, flag, Conv.trans converts.sym convToCode⟩
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq => by
        have rootEq : Generator.gen_lam = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma),
          if_neg (fun isList => Generator.noConfusion isList)] at isFormation
        cases isFormation
    | .piElim _functionTyped _argumentTyped => fun subjectEq => by
        have rootEq : Generator.gen_app = generator :=
          congrArg RawTerm.headGenerator subjectEq
        rw [← rootEq] at isFormation
        unfold typingRuleDescOf at isFormation
        rw [if_neg (fun isPi => Generator.noConfusion isPi),
          if_neg (fun isSigma => Generator.noConfusion isSigma),
          if_neg (fun isList => Generator.noConfusion isList)] at isFormation
        cases isFormation
    | .genFormationPi _armContext armGenerator _armPayload _armChildren armLevels armFlag
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = generator :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        -- ROW-SHAPE-AGNOSTIC: read the output through `typingRuleDescOf_output_isUniverseCode`
        -- (it is SOME universe code) rather than the strong `= universeFormerOutput` equation.
        -- The existential's `lmaxAll levels` is filled with the singleton `[outputLevel]`
        -- (`lmaxAll [outputLevel] = outputLevel` definitionally), so a future flag-pinned nullary
        -- row absorbs here verbatim.
        obtain ⟨outputLevel, outputFlag, hOutput⟩ :=
          typingRuleDescOf_output_isUniverseCode armIsFormation _ armLevels armFlag
        refine ⟨[outputLevel], outputFlag, ?_⟩
        rw [hOutput]
        exact Conv.refl _

/-- **A `listCode` data former is not a member of a Π-type.**  The `gen_listCode` specialization of the grown
generic inversion: a closed `List element` is a TYPE (classifier `Conv` a universe code), and a Π-code is not
`Conv` a universe code.  The data-former analogue of `piFormerNotTypedAtPiType`, via the head-agnostic
`formerClassifierConvUniverseGeneric` (no bespoke `invertListCode`). -/
theorem HasTypeDescPi.listFormerNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {element : RawTerm scope}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (.mkGen .gen_listCode () (.childCons element .childNil))
        (piTyCodeCell outerDomain outerCodomain)) :
    False := by
  obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
    HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_listCode rfl
  exact Conv.piTyCode_not_universeCode convToUniverseCode

/-- **A `listCode` data former is not a member of the empty type.**  The empty-type twin of
`listFormerNotTypedAtPiType`: a `List element` classifier `Conv` a universe code refutes against the empty-type
classifier (`Conv.universeCode_not_emptyTypeCode`).  The data-former analogue of `piFormerNotTypedAtEmptyType`,
the `gen_listCode` arm of the grown closed-consistency canonical forms. -/
theorem HasTypeDescPi.listFormerNotTypedAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {element : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (.mkGen .gen_listCode () (.childCons element .childNil))
        (emptyTypeCell (scope := scope))) :
    False := by
  obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
    HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_listCode rfl
  exact Conv.universeCode_not_emptyTypeCode convToUniverseCode.sym

/-- **An `optionCode` data former is not a member of a Π-type.**  The `gen_optionCode` specialization of the
grown generic inversion (GTL-13): a closed `Option element` is a TYPE (classifier `Conv` a universe code), and a
Π-code is not `Conv` a universe code.  The one-child option twin of `listFormerNotTypedAtPiType`, via the
head-agnostic `formerClassifierConvUniverseGeneric` (no bespoke `invertOptionCode`). -/
theorem HasTypeDescPi.optionFormerNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {element : RawTerm scope}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (.mkGen .gen_optionCode () (.childCons element .childNil))
        (piTyCodeCell outerDomain outerCodomain)) :
    False := by
  obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
    HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_optionCode rfl
  exact Conv.piTyCode_not_universeCode convToUniverseCode

/-- **An `optionCode` data former is not a member of the empty type.**  The empty-type twin of
`optionFormerNotTypedAtPiType`: an `Option element` classifier `Conv` a universe code refutes against the
empty-type classifier (`Conv.universeCode_not_emptyTypeCode`).  The one-child option arm (GTL-13) of the grown
closed-consistency canonical forms. -/
theorem HasTypeDescPi.optionFormerNotTypedAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {element : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (.mkGen .gen_optionCode () (.childCons element .childNil))
        (emptyTypeCell (scope := scope))) :
    False := by
  obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
    HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_optionCode rfl
  exact Conv.universeCode_not_emptyTypeCode convToUniverseCode.sym

end FX1Poly.Typed
