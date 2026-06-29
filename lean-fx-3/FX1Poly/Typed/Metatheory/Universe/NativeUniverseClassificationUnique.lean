import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericVariableInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionAppInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathProjInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathAppInversion
import FX1Poly.Typed.Metatheory.Universe.UniverseClassificationUnique
import FX1Poly.Typed.Metatheory.Universe.UniverseCodeConversion
import FX1Poly.Typed.Metatheory.Universe.ConvCodeInjectivity
import FX1Poly.Typed.Engine.Formation.ConvFlatCodeInjectivity
import FX1Poly.Typed.Engine.Formation.ConvDataCodeInjectivity
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair
import FX1Poly.Core.Substrate.Neutral.NeutralTerm

/-! # FX1Poly/Typed/Metatheory/Universe/NativeUniverseClassificationUnique
    — native universe-flag-uniqueness, the leaves + the neutral spine (consistency-leg keystone #1697/#1740)

The native `HasTypeUnion` port of `HasTypeDescPi.variableUniverseClassificationUnique`: two universe-code
classifiers of ONE variable agree on BOTH level and flag.  Built directly on the variable-head inversion
(`invertAtVarHeadGeneric`): each universe-code typing of `variableCell index` makes the context lookup
`context.lookup index` convert to that universe code, so the two universe codes are mutually `Conv` (through the
shared lookup), and `Conv.universeCode_injective` reads off the level/flag agreement.

These are the structural leaves of native universe-flag-uniqueness for type-subjects — the keystone the
option/either/nat/list motive-step congruence subject-reduction arms (gate-2 residual of the consistency leg)
reduce to via drifted-branch-type reformedness at a common flag.

This file ships, beyond the variable and universe-code leaves: the `lam` dispatch arm
(`lamNotTypedAtUniverseCode` — a λ never inhabits a universe code), the `idStrictRec` untypability lemma (the
one substrate eliminator with no ι-rule), and the NEUTRAL spine `neutralClassifierUnique` — any two union
classifiers of a neutral subject are `Conv`, via `IsNeutral` induction: the recursive heads (app / pathApp /
fst / snd / idJ) recurse on the principal child and split with the matching code-injectivity, the six
dependent branch eliminators read their subject-pinned output (params ignored), and `idStrictRec` is vacuous.
Its universe specialization `neutralUniverseClassificationUnique` reads off (level, flag) agreement.

Unlike the grown engine — where every eliminator but Π-application is untyped, so the grown neutral spine is
nearly vacuous — the native table types every eliminator, so each neutral arm is genuine work.

The remaining structural assembly (the budget-recursive root dispatch `normalUniverseClassificationUnique`
over var / universe / lam / former / neutral, mirroring `normalUniverseClassificationUniqueAtBudget`) consumes
these leaves plus a native former-telescope universe determinism; it is the follow-up.

## Zero-axiom verification

`invertAtVarHeadGeneric` / `invertAtAppHead` / `invertAtPathAppHead` / `invertAtFstHead` / `invertAtSndHead` /
`invertAtLamHead` / `invertAtElimHeadGeneric`, the code-injectivity lemmas (`piTyCode_inj` /
`bridgeTypeCode_inj` / `productCode_inj` / `idCode_inj` / `piTyCode_not_universeCode`), `Conv.subst0` /
`Conv.substPair`, `variableCell_inj_of_conv`, `Conv.universeCode_injective`, and `Conv.refl` / `Conv.sym` /
`Conv.trans`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Native variable universe-classification uniqueness.**  A variable typed at two universe codes agrees on
level and flag — the native variable leaf of universe-flag-uniqueness.  Both inversions route the lookup through
`Conv` to the respective universe code; the codes are then mutually convertible and `universeCode_injective`
closes it. -/
theorem HasTypeUnion.variableUniverseClassificationUnique {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {index : Fin scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (firstClassified : HasTypeUnion profile context (variableCell index)
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeUnion profile context (variableCell index)
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  obtain ⟨firstIndex, firstShape, firstLookupConv⟩ :=
    HasTypeUnion.invertAtVarHeadGeneric firstClassified rfl
  obtain ⟨secondIndex, secondShape, secondLookupConv⟩ :=
    HasTypeUnion.invertAtVarHeadGeneric secondClassified rfl
  have firstConvVar : Conv (variableCell index : RawTerm scope) (variableCell firstIndex) :=
    firstShape ▸ Conv.refl (variableCell index)
  have secondConvVar : Conv (variableCell index : RawTerm scope) (variableCell secondIndex) :=
    secondShape ▸ Conv.refl (variableCell index)
  have firstEq : index = firstIndex := variableCell_inj_of_conv firstConvVar
  have secondEq : index = secondIndex := variableCell_inj_of_conv secondConvVar
  rw [← firstEq] at firstLookupConv
  rw [← secondEq] at secondLookupConv
  exact Conv.universeCode_injective (firstLookupConv.sym.trans secondLookupConv)

/-- **The generic native universe-code-head inversion.**  When `RawTerm.rootGenerator subject = gen_universeCode`,
the subject is a `universeCodeCell level flag` whose successor-universe classifier `universeCodeCell level.lsucc
flag` converts to the actual classifier.  The `universeFormation`-surviving twin of `invertAtVarHeadGeneric`:
non-universe arms refute by root-generator distinctness + the `*RuleOf gen_universeCode = none` reductions; `conv`
recurses; only `universeFormation` survives, contributing `Conv.refl` at the successor universe. -/
theorem HasTypeUnion.invertAtUniverseCodeHeadGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (headIsUniverse : RawTerm.rootGenerator subject = Generator.gen_universeCode) :
    ∃ (level : LevelExpr) (flag : UniverseFlag),
      subject = universeCodeCell level flag ∧
      Conv (universeCodeCell level.lsucc flag) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _ctx _index =>
      have headEq : Generator.gen_var = Generator.gen_universeCode := headIsUniverse
      exact Generator.noConfusion headEq
  | universeFormation _ctx levelExpr flag => exact ⟨levelExpr, flag, rfl, Conv.refl _⟩
  | formationRule _ctx formGen _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _ihPremises =>
      have headEq : formGen = Generator.gen_universeCode := headIsUniverse
      subst headEq
      rw [show formationRuleOf Generator.gen_universeCode = none from rfl] at isFormationRule
      cases isFormationRule
  | intro _ctx introGen _introRule introArgs _params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _ihPremises =>
      have headEq : introGen = Generator.gen_universeCode :=
        (introMemberCellRootGenerator isIntro introArgs).symm.trans headIsUniverse
      subst headEq
      rw [show introRuleOf Generator.gen_universeCode = none from rfl] at isIntro
      cases isIntro
  | elim _ctx elimGen _elimRule elimArgs _elimParams _elimLevel0 _elimLevel1 _elimFlag isElim
      _premisesHold _ihPremises =>
      have headEq : elimGen = Generator.gen_universeCode :=
        (elimMemberCellRootGenerator isElim elimArgs).symm.trans headIsUniverse
      subst headEq
      rw [show elimRuleOf Generator.gen_universeCode = none from rfl] at isElim
      cases isElim
  | conv _levelExpr _flag _typed converts _reclassifierTyped typedIH _reclassifierIH =>
      obtain ⟨level, flag, subjectShape, convToClassifier⟩ := typedIH headIsUniverse
      exact ⟨level, flag, subjectShape, convToClassifier.trans converts⟩

/-- **★ Native universe-code universe-classification uniqueness.**  A universe code typed at two universe codes
agrees on level and flag — the native universe-code leaf of universe-flag-uniqueness.  Both inversions pin the
subject's own (level, flag) via universe-code injectivity, then the successor-universe classifiers are mutually
`Conv` and `universeCode_injective` reads off the agreement. -/
theorem HasTypeUnion.universeCodeUniverseClassificationUnique {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {level : LevelExpr} {flag : UniverseFlag}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (firstClassified : HasTypeUnion profile context (universeCodeCell level flag)
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeUnion profile context (universeCodeCell level flag)
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  obtain ⟨firstSubLevel, firstSubFlag, firstShape, firstConv⟩ :=
    HasTypeUnion.invertAtUniverseCodeHeadGeneric firstClassified rfl
  obtain ⟨secondSubLevel, secondSubFlag, secondShape, secondConv⟩ :=
    HasTypeUnion.invertAtUniverseCodeHeadGeneric secondClassified rfl
  have firstConvCells : Conv (universeCodeCell level flag : RawTerm scope)
      (universeCodeCell firstSubLevel firstSubFlag) := firstShape ▸ Conv.refl (universeCodeCell level flag)
  have secondConvCells : Conv (universeCodeCell level flag : RawTerm scope)
      (universeCodeCell secondSubLevel secondSubFlag) := secondShape ▸ Conv.refl (universeCodeCell level flag)
  obtain ⟨firstLevelEq, firstFlagEq⟩ := Conv.universeCode_injective firstConvCells
  obtain ⟨secondLevelEq, secondFlagEq⟩ := Conv.universeCode_injective secondConvCells
  rw [← firstLevelEq, ← firstFlagEq] at firstConv
  rw [← secondLevelEq, ← secondFlagEq] at secondConv
  obtain ⟨firstSuccEq, firstFlagEq2⟩ := Conv.universeCode_injective firstConv
  obtain ⟨secondSuccEq, secondFlagEq2⟩ := Conv.universeCode_injective secondConv
  exact ⟨firstSuccEq.symm.trans secondSuccEq, firstFlagEq2.symm.trans secondFlagEq2⟩

/-- **★ A λ is never union-classified at a universe code.**  The lam dispatch arm of native
universe-flag-uniqueness: a `lamCell`-headed subject's classifier is a Π code
(`invertAtLamHead`), and a Π code is never `Conv` a universe code
(`Conv.piTyCode_not_universeCode`) — so no λ inhabits a universe code, refuting the lam arm of the
budget root dispatch outright (the native twin of the grown `lam_notTypedAtUniverseCode`). -/
theorem HasTypeUnion.lamNotTypedAtUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {domainAnn : RawTerm scope}
    {body : RawTerm (scope + 1)} {level : LevelExpr} {flag : UniverseFlag}
    (derivation : HasTypeUnion profile context (lamCell domainAnn body)
      (universeCodeCell level flag)) : False := by
  obtain ⟨_codomainCode, _domainLevel, _codomainLevel, _flag, classifierConv, _domainFormed,
      _codomainFormed, _bodyTyped⟩ := HasTypeUnion.invertAtLamHead derivation rfl
  exact Conv.piTyCode_not_universeCode classifierConv

/-- **The `idStrictRec` head is union-untypable.**  `gen_idStrictRec` carries no formation, intro,
OR elim rule (`elimRuleOf gen_idStrictRec = none`), so reflecting a host embedding away with
`toNativeOnly` leaves every native arm refuted by head clash or a `*RuleOf … = none` reduction.
The native counterpart of the grown `untypedAtNonGrownRoot` at the one substrate eliminator with no
ι-rule — it makes the `idStrictRec` neutral arm of classifier uniqueness vacuous. -/
theorem HasTypeUnion.idStrictRecHeadUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idStrictRecCell motive baseCase witness) : False := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _ctx _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _ctx _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv _levelExpr _flag _typed _converts _reclassifierTyped typedIH _reclassifierIH =>
      exact typedIH subjectShape
  | formationRule _ctx formGen _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _usabilityHolds _ihPremises =>
      have headEq : formGen = Generator.gen_idStrictRec :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      rw [show formationRuleOf Generator.gen_idStrictRec = none from rfl] at isFormationRule
      cases isFormationRule
  | intro _ctx introGen _introRule introArgs _params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _usabilityHolds _ihPremises =>
      have headEq : introGen = Generator.gen_idStrictRec :=
        (introMemberCellRootGenerator isIntro introArgs).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      subst headEq
      rw [show introRuleOf Generator.gen_idStrictRec = none from rfl] at isIntro
      cases isIntro
  | elim _ctx elimGen _elimRule elimArgs _elimParams _elimLevel0 _elimLevel1 _elimFlag isElim
      _premisesHold _usabilityHolds _ihPremises =>
      have headEq : elimGen = Generator.gen_idStrictRec :=
        (elimMemberCellRootGenerator isElim elimArgs).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      subst headEq
      rw [show elimRuleOf Generator.gen_idStrictRec = none from rfl] at isElim
      cases isElim

/-- **★ Native neutral classifier-class uniqueness.**  Any two union classifiers of one NEUTRAL
subject are `Conv`.  Spine induction on `IsNeutral`:

  * `var` — both classifiers `Conv` the fixed context lookup (`invertAtVarHeadGeneric`).
  * `app` / `pathApp` / `fst` / `snd` — invert at the elim head, apply the IH to the neutral
    principal child (the two head codes `Conv`), split with the matching code-injectivity
    (`piTyCode_inj` / `bridgeTypeCode_inj` / `productCode_inj`), and transport the output.
  * the six dependent branch eliminators (`boolElim` / `natElim` / `natRec` / `listElim` /
    `optionMatch` / `eitherMatch`) — their `outputType` ignores the inferred params, so the output is
    pinned by the subject's own children; both classifiers `Conv` the one output, no IH needed.
  * `idJ` — invert, recurse on the witness (its identity type `Conv`s), read the right endpoint off
    `idCode_inj`, and lift it through the output's two-binder substitution with `Conv.substPair`.
  * `idStrictRec` — vacuous: the head is union-untypable (`idStrictRecHeadUntyped`).

Unlike the grown engine (where every eliminator but `app` is untyped), the native table types every
eliminator, so each arm is genuine work; only `idStrictRec` (no ι-rule) refutes. -/
theorem HasTypeUnion.neutralClassifierUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (neutral : IsNeutral subject) :
    ∀ {firstClassifier secondClassifier : RawTerm scope},
      HasTypeUnion profile context subject firstClassifier →
      HasTypeUnion profile context subject secondClassifier →
      Conv firstClassifier secondClassifier := by
  induction neutral with
  | var index =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstIndex, firstShape, firstConv⟩ :=
        HasTypeUnion.invertAtVarHeadGeneric firstTyped rfl
      obtain ⟨secondIndex, secondShape, secondConv⟩ :=
        HasTypeUnion.invertAtVarHeadGeneric secondTyped rfl
      have shapesEq : variableCell firstIndex = (variableCell secondIndex : RawTerm scope) :=
        firstShape.symm.trans secondShape
      have indicesConv : Conv (variableCell firstIndex : RawTerm scope) (variableCell secondIndex) :=
        shapesEq ▸ Conv.refl (variableCell firstIndex)
      have indicesEq : firstIndex = secondIndex := variableCell_inj_of_conv indicesConv
      rw [indicesEq] at firstConv
      exact firstConv.sym.trans secondConv
  | app headIsNeutral headIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨_firstDomain, firstCodomain, firstFunctionTyped, _firstArgTyped, firstConv⟩ :=
        HasTypeUnion.invertAtAppHead firstTyped rfl
      obtain ⟨_secondDomain, secondCodomain, secondFunctionTyped, _secondArgTyped, secondConv⟩ :=
        HasTypeUnion.invertAtAppHead secondTyped rfl
      obtain ⟨_domainsConv, codomainsConv⟩ :=
        Conv.piTyCode_inj (headIH firstFunctionTyped secondFunctionTyped)
      exact firstConv.trans
        ((Conv.subst0 codomainsConv (Conv.refl _)).trans secondConv.sym)
  | pathApp functionIsNeutral functionIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨_firstCarrier, _firstLeft, _firstRight, firstPathTyped, _firstArgTyped, firstConv⟩ :=
        HasTypeUnion.invertAtPathAppHead firstTyped rfl
      obtain ⟨_secondCarrier, _secondLeft, _secondRight, secondPathTyped, _secondArgTyped,
          secondConv⟩ := HasTypeUnion.invertAtPathAppHead secondTyped rfl
      obtain ⟨carriersConv, _leftsConv, _rightsConv⟩ :=
        Conv.bridgeTypeCode_inj (functionIH firstPathTyped secondPathTyped)
      exact firstConv.trans (carriersConv.trans secondConv.sym)
  | fst argumentIsNeutral argumentIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨_firstSecondType, _firstPinned, firstPairTyped, firstConv⟩ :=
        HasTypeUnion.invertAtFstHead firstTyped rfl
      obtain ⟨_secondSecondType, _secondPinned, secondPairTyped, secondConv⟩ :=
        HasTypeUnion.invertAtFstHead secondTyped rfl
      obtain ⟨pinnedConv, _secondTypesConv⟩ :=
        Conv.productCode_inj (argumentIH firstPairTyped secondPairTyped)
      exact firstConv.sym.trans (pinnedConv.trans secondConv)
  | snd argumentIsNeutral argumentIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨_firstFirstType, _firstPinned, firstPairTyped, firstConv⟩ :=
        HasTypeUnion.invertAtSndHead firstTyped rfl
      obtain ⟨_secondFirstType, _secondPinned, secondPairTyped, secondConv⟩ :=
        HasTypeUnion.invertAtSndHead secondTyped rfl
      obtain ⟨_firstTypesConv, pinnedConv⟩ :=
        Conv.productCode_inj (argumentIH firstPairTyped secondPairTyped)
      exact firstConv.sym.trans (pinnedConv.trans secondConv)
  | boolElim _scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, _firstParams, _, _, _, firstMember, _, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := boolElimRule)
          (show elimRuleOf Generator.gen_boolElim = some boolElimRule from rfl) rfl
      obtain ⟨secondArgs, _secondParams, _, _, _, secondMember, _, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := boolElimRule)
          (show elimRuleOf Generator.gen_boolElim = some boolElimRule from rfl) rfl
      match firstArgs, firstMember, firstConv with
      | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), firstMember, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondMember, secondConv with
        | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), secondMember,
          secondConv =>
          rcases secondMember with ⟨⟩
          exact firstConv.sym.trans secondConv
  | natElim _scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, _firstParams, _, _, _, firstMember, _, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := natElimRule)
          (show elimRuleOf Generator.gen_natElim = some natElimRule from rfl) rfl
      obtain ⟨secondArgs, _secondParams, _, _, _, secondMember, _, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := natElimRule)
          (show elimRuleOf Generator.gen_natElim = some natElimRule from rfl) rfl
      match firstArgs, firstMember, firstConv with
      | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), firstMember, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondMember, secondConv with
        | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), secondMember,
          secondConv =>
          rcases secondMember with ⟨⟩
          exact firstConv.sym.trans secondConv
  | natRec _scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, _firstParams, _, _, _, firstMember, _, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := natRecElimRule)
          (show elimRuleOf Generator.gen_natRec = some natRecElimRule from rfl) rfl
      obtain ⟨secondArgs, _secondParams, _, _, _, secondMember, _, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := natRecElimRule)
          (show elimRuleOf Generator.gen_natRec = some natRecElimRule from rfl) rfl
      match firstArgs, firstMember, firstConv with
      | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), firstMember, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondMember, secondConv with
        | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), secondMember,
          secondConv =>
          rcases secondMember with ⟨⟩
          exact firstConv.sym.trans secondConv
  | listElim _scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, _firstParams, _, _, _, firstMember, _, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := listElimRule)
          (show elimRuleOf Generator.gen_listElim = some listElimRule from rfl) rfl
      obtain ⟨secondArgs, _secondParams, _, _, _, secondMember, _, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := listElimRule)
          (show elimRuleOf Generator.gen_listElim = some listElimRule from rfl) rfl
      match firstArgs, firstMember, firstConv with
      | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), firstMember, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondMember, secondConv with
        | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), secondMember,
          secondConv =>
          rcases secondMember with ⟨⟩
          exact firstConv.sym.trans secondConv
  | optionMatch _scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, _firstParams, _, _, _, firstMember, _, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := optionMatchElimRule)
          (show elimRuleOf Generator.gen_optionMatch = some optionMatchElimRule from rfl) rfl
      obtain ⟨secondArgs, _secondParams, _, _, _, secondMember, _, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := optionMatchElimRule)
          (show elimRuleOf Generator.gen_optionMatch = some optionMatchElimRule from rfl) rfl
      match firstArgs, firstMember, firstConv with
      | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), firstMember, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondMember, secondConv with
        | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), secondMember,
          secondConv =>
          rcases secondMember with ⟨⟩
          exact firstConv.sym.trans secondConv
  | eitherMatch _scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, _firstParams, _, _, _, firstMember, _, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := eitherMatchElimRule)
          (show elimRuleOf Generator.gen_eitherMatch = some eitherMatchElimRule from rfl) rfl
      obtain ⟨secondArgs, _secondParams, _, _, _, secondMember, _, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := eitherMatchElimRule)
          (show elimRuleOf Generator.gen_eitherMatch = some eitherMatchElimRule from rfl) rfl
      match firstArgs, firstMember, firstConv with
      | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), firstMember, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondMember, secondConv with
        | .childCons _ (.childCons _ (.childCons _ (.childCons _ .childNil))), secondMember,
          secondConv =>
          rcases secondMember with ⟨⟩
          exact firstConv.sym.trans secondConv
  | idJ witnessIsNeutral witnessIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstArgs, firstParams, _, _, _, firstMember, firstObl, _, firstConv⟩ :=
        firstTyped.invertAtElimHeadGeneric (rule := idJElimRule)
          (show elimRuleOf Generator.gen_idJ = some idJElimRule from rfl) rfl
      obtain ⟨secondArgs, secondParams, _, _, _, secondMember, secondObl, _, secondConv⟩ :=
        secondTyped.invertAtElimHeadGeneric (rule := idJElimRule)
          (show elimRuleOf Generator.gen_idJ = some idJElimRule from rfl) rfl
      match firstArgs, firstParams, firstMember, firstObl, firstConv with
      | .childCons _ (.childCons _ (.childCons _ .childNil)),
        .childCons _ (.childCons _ (.childCons _ .childNil)), firstMember, firstObl, firstConv =>
        rcases firstMember with ⟨⟩
        match secondArgs, secondParams, secondMember, secondObl, secondConv with
        | .childCons _ (.childCons _ (.childCons _ .childNil)),
          .childCons _ (.childCons _ (.childCons _ .childNil)), secondMember, secondObl,
          secondConv =>
          rcases secondMember with ⟨⟩
          obtain ⟨_typeCodesConv, _leftsConv, rightsConv⟩ :=
            Conv.idCode_inj
              (witnessIH (firstObl _ (List.Mem.head _)) (secondObl _ (List.Mem.head _)))
          exact firstConv.sym.trans
            ((Conv.substPair (Conv.refl _) (Conv.refl _) rightsConv).trans secondConv)
  | idStrictRec _witnessIsNeutral _witnessIH =>
      intro firstClassifier _secondClassifier firstTyped _secondTyped
      exact (HasTypeUnion.idStrictRecHeadUntyped firstTyped rfl).elim

/-- **★ Native universe classification is unique at every NEUTRAL** — a neutral's two union universe
classifications agree on (level, flag), via `Conv.universeCode_injective` over
`neutralClassifierUnique`.  The native port of `HasTypeDescPi.neutralUniverseClassificationUnique`
and the application/eliminator arm the budget root dispatch consumes. -/
theorem HasTypeUnion.neutralUniverseClassificationUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (neutral : IsNeutral subject)
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (firstClassified : HasTypeUnion profile context subject
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeUnion profile context subject
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag :=
  Conv.universeCode_injective
    (HasTypeUnion.neutralClassifierUnique neutral firstClassified secondClassified)

end FX1Poly.Typed
