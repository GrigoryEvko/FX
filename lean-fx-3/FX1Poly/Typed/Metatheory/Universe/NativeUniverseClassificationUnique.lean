import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericVariableInversion
import FX1Poly.Typed.Metatheory.Universe.UniverseClassificationUnique
import FX1Poly.Typed.Metatheory.Universe.UniverseCodeConversion

/-! # FX1Poly/Typed/Metatheory/Universe/NativeUniverseClassificationUnique
    — native universe-flag-uniqueness, the variable leaf (consistency-leg keystone #1697/#1740)

The native `HasTypeUnion` port of `HasTypeDescPi.variableUniverseClassificationUnique`: two universe-code
classifiers of ONE variable agree on BOTH level and flag.  Built directly on the variable-head inversion
(`invertAtVarHeadGeneric`): each universe-code typing of `variableCell index` makes the context lookup
`context.lookup index` convert to that universe code, so the two universe codes are mutually `Conv` (through the
shared lookup), and `Conv.universeCode_injective` reads off the level/flag agreement.

This is the first of the structural leaves of native universe-flag-uniqueness for type-subjects — the keystone
the option/either/nat/list/idJ motive-step congruence subject-reduction arms (gate-2 residual of the consistency
leg) reduce to via drifted-branch-type reformedness at a common flag.  The neutral (application-spine) leaf and
the structural assembly follow, mirroring `neutralUniverseClassificationUnique` /
`normalUniverseClassificationUniqueAtBudget`.

## Zero-axiom verification

`invertAtVarHeadGeneric`, `variableCell_inj_of_conv`, `Conv.universeCode_injective`, `Conv.refl` / `Conv.sym` /
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

end FX1Poly.Typed
