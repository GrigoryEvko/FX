import FX1Poly.Typed.GenericFormerTelescopeInversion
import FX1Poly.Typed.TelescopeUniverseDeterminism
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion

/-! # Normal-subject universe-classification uniqueness

THE flag-negotiation master of the grown-strengthening enrichment campaign: two grown universe
classifications of one NORMAL subject agree on (level, flag).  Budget-recursive over subject
size with a 5-way root dispatch — var (`variableUniverseClassificationUnique`), universe-code
(`inversionUniverseCode` + `Conv.universeCode_injective`), lam (refuted: a λ's classifier is a
Π-code, never a universe code), app (`normalAppIsNeutral` + `neutralUniverseClassificationUnique`),
former (`invertFormerTelescopeWithConvGeneric` ×2 + `DescTelescopePi.universeDeterminismOfChildIH`
at the recursive child IH).

The flag agreement at formers is UNCONDITIONAL because every formation row binds at least one
child (`typingRuleDescOf_binderShiftsNonempty`, a table-wide fact re-verified on each new row) —
a nonempty telescope anchors the flag at its head child.  No well-formedness premise anywhere;
the former arm is table-generic.

Consumers: the Conv-lift under wf (normalize both classifier pins via SR-star, negotiate at the
join) and onward the flag-coherent pair extraction feeding the pinned-reflection λ-reduct arm. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Every NON-NULLARY formation row binds at least one child.**  A generator carrying a
`typingRuleDescOf` rule, other than the nullary `gen_unitCode`, has nonempty `binderShifts` —
the fact that anchors the universe FLAG of a former classification at its head child.  The
nullary row is typed at every flag through its empty telescope, so its flag agreement is by
output CONSTANCY instead (`HasTypeDescPi.invertFormerClassifierPinned`); the build re-verifies
this lemma on each new row. -/
theorem typingRuleDescOf_binderShiftsNonempty {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode) :
    generator.binderShifts ≠ [] := by
  by_cases isPi : generator = .gen_piTyCode
  · subst isPi
    exact fun emptyShifts => nomatch emptyShifts
  · by_cases isSigma : generator = .gen_sigmaTyCode
    · subst isSigma
      exact fun emptyShifts => nomatch emptyShifts
    · by_cases isList : generator = .gen_listCode
      · subst isList
        exact fun emptyShifts => nomatch emptyShifts
      · by_cases isOption : generator = .gen_optionCode
        · subst isOption
          exact fun emptyShifts => nomatch emptyShifts
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg isPi, if_neg isSigma, if_neg isList, if_neg isOption,
            if_neg isNotNullary] at isFormation
          contradiction

/-- A telescope over children with nonempty binder shifts has a nonempty level list (the `nil`
telescope only fits `childNil`, whose shift index is `[]`). -/
theorem DescTelescopePi.levelsNonemptyOfShiftsNonempty {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children)
    (shiftsNonempty : binderShifts ≠ []) : levels ≠ [] := by
  cases telescope with
  | nil _context _flag => exact absurd rfl shiftsNonempty
  | cons _context head headLevel restLevels _flag rest headTyped restTyped =>
      exact fun levelsEmpty => nomatch levelsEmpty

/-- **E2.7 master (budget form)**: two grown universe classifications of one NORMAL subject
agree on (level, flag), by strong induction on a size budget. -/
theorem HasTypeDescPi.normalUniverseClassificationUniqueAtBudget {profile : PolyProfile} :
    (budget : Nat) → ∀ {scope : Nat} {context : TypingContext profile scope}
      (subject : RawTerm scope) {firstLevel secondLevel : LevelExpr}
      {firstFlag secondFlag : UniverseFlag},
      subject.size ≤ budget → RawTerm.isStepNormalForm subject →
      HasTypeDescPi profile context subject (universeCodeCell firstLevel firstFlag) →
      HasTypeDescPi profile context subject (universeCodeCell secondLevel secondFlag) →
      firstLevel = secondLevel ∧ firstFlag = secondFlag
  | 0 => by
      intro subject firstLevel secondLevel firstFlag secondFlag
        sizeBound _normal _firstTyped _secondTyped
      cases subject with
      | mkGen generator payload children =>
          exact absurd sizeBound (Nat.not_succ_le_zero _)
  | budget + 1 => by
      intro subject firstLevel secondLevel firstFlag secondFlag
        sizeBound normal firstTyped secondTyped
      cases subject with
      | mkGen generator payload children =>
          rcases firstTyped.subjectRootGeneratorGeneric with
            isVar | isUniverse | isLam | isApp | ⟨rule, isFormer⟩
          · have generatorEq : generator = Generator.gen_var := isVar
            subst generatorEq
            cases children
            exact HasTypeDescPi.variableUniverseClassificationUnique firstTyped secondTyped
          · have generatorEq : generator = Generator.gen_universeCode := isUniverse
            subst generatorEq
            cases children
            obtain ⟨subjectLevel, subjectFlag⟩ := payload
            obtain ⟨firstLevelEq, firstFlagEq⟩ :=
              Conv.universeCode_injective firstTyped.inversionUniverseCode
            obtain ⟨secondLevelEq, secondFlagEq⟩ :=
              Conv.universeCode_injective secondTyped.inversionUniverseCode
            exact ⟨firstLevelEq.trans secondLevelEq.symm,
              firstFlagEq.trans secondFlagEq.symm⟩
          · have generatorEq : generator = Generator.gen_lam := isLam
            subst generatorEq
            cases children with
            | childCons domainAnn rest =>
                cases rest with
                | childCons body restRest =>
                    cases restRest
                    obtain ⟨_codomainCode, _domainLevel, _codomainLevel, _pinFlag,
                      classifierConv, _domainTyped, _codomainTyped, _bodyTyped⟩ :=
                      HasTypeDescPi.invertLam firstTyped
                    exact (Conv.piTyCode_not_universeCode classifierConv.sym).elim
          · have generatorEq : generator = Generator.gen_app := isApp
            subst generatorEq
            cases children with
            | childCons functionTerm rest =>
                cases rest with
                | childCons argument restRest =>
                    cases restRest
                    exact HasTypeDescPi.neutralUniverseClassificationUnique
                      (HasTypeDescPi.normalAppIsNeutral firstTyped normal)
                      firstTyped secondTyped
          · have isFormation : typingRuleDescOf generator = some rule := isFormer
            by_cases isNullary : generator = Generator.gen_unitCode
            · -- the nullary row: both classifications reach the ONE pinned output, by output
              -- constancy — the empty telescope anchors no flag, so no negotiation is needed
              subst isNullary
              obtain ⟨firstLevelEq, firstFlagEq⟩ := Conv.universeCode_injective
                (HasTypeDescPi.invertFormerClassifierPinned firstTyped isFormation
                  (typingRuleDescOf_unitCode_outputConstant isFormation _) rfl)
              obtain ⟨secondLevelEq, secondFlagEq⟩ := Conv.universeCode_injective
                (HasTypeDescPi.invertFormerClassifierPinned secondTyped isFormation
                  (typingRuleDescOf_unitCode_outputConstant isFormation _) rfl)
              exact ⟨firstLevelEq.trans secondLevelEq.symm,
                firstFlagEq.trans secondFlagEq.symm⟩
            · obtain ⟨firstLevels, firstPinFlag, firstTelescope, firstConv⟩ :=
                firstTyped.invertFormerTelescopeWithConvGeneric isFormation rfl
              obtain ⟨secondLevels, secondPinFlag, secondTelescope, secondConv⟩ :=
                secondTyped.invertFormerTelescopeWithConvGeneric isFormation rfl
              obtain ⟨firstLevelEq, firstFlagEq⟩ := Conv.universeCode_injective firstConv
              obtain ⟨secondLevelEq, secondFlagEq⟩ := Conv.universeCode_injective secondConv
              have childrenNormal := RawTerm.isStepNormalForm_childrenNormal normal
              have childrenSize : RawTermChildren.size children ≤ budget :=
                Nat.le_of_succ_le_succ sizeBound
              obtain ⟨levelsAgree, flagsConditional⟩ :=
                DescTelescopePi.universeDeterminismOfChildIH
                  (fun {_childScope} childContext child {_childFirstLevel} {_childSecondLevel}
                      {_childFirstFlag} {_childSecondFlag} childSize childNormal
                      childFirst childSecond =>
                    HasTypeDescPi.normalUniverseClassificationUniqueAtBudget budget
                      child childSize childNormal childFirst childSecond)
                  firstTelescope secondTelescope childrenSize childrenNormal
              have flagsAgree := flagsConditional
                (firstTelescope.levelsNonemptyOfShiftsNonempty
                  (typingRuleDescOf_binderShiftsNonempty isFormation isNullary))
              refine ⟨?_, ?_⟩
              · rw [firstLevelEq, secondLevelEq, levelsAgree]
              · rw [firstFlagEq, secondFlagEq, flagsAgree]

/-- **E2.7 master**: two grown universe classifications of one NORMAL subject agree on
(level, flag) — the negotiation lemma at the heart of the flag-coherent pair extraction.
Unconditional (no wf premise); table-generic (the former arm survives table growth). -/
theorem HasTypeDescPi.normalUniverseClassificationUnique {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {subject : RawTerm scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (normal : RawTerm.isStepNormalForm subject)
    (firstClassified : HasTypeDescPi profile context subject
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeDescPi profile context subject
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag :=
  HasTypeDescPi.normalUniverseClassificationUniqueAtBudget subject.size subject
    (Nat.le_refl _) normal firstClassified secondClassified

end FX1Poly.Typed
