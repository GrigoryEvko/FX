import FX1Poly.Typed.FormationEngineFundamental
import FX1Poly.Typed.HasTypeDescPiFundamentalVectorFromFormation
import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.FormerChildrenReducible

/-! # FX1Poly/Typed/FormationEngineFundamentalAssembly
    — the COMPLETE formation-engine fundamental theorem (vector shape), modulo the single #672 hypothesis.

`FormationEngineFundamental.lean` proved the three non-former arms of the formation engine as standalone
theorems (`universeFormation` unconditional, `conv` over the two sub-IHs, `var` isolated to the all-positive
member residual #672).  This file performs the FOUR-arm assembly — adding the `genFormation` former arm and the
two telescope arms inline — so that the entire formation-engine fundamental theorem

```
HasTypeDesc profile context subject classifier → IsFundamentalConclusionAtVector context subject classifier
```

stands as ONE theorem whose ONLY non-proven input is the universe-domain-Π all-positive member extension (#672),
supplied here as the explicit hypothesis `variablesAllPositive`.  Combined with
`HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental`
(`FormationEngineFundamentalReduction.lean`), this collapses the entire SN-027 dependent metatheory — and hence
SN-043 SN-for-well-typed and its ~35 downstream tasks — to the single statement #672.

## The port

The formation telescope `DescTelescope` and the grown telescope `DescTelescopePi` have STRUCTURALLY IDENTICAL
`nil` / `cons` constructors (`DescTelescope`'s `cons` carries a `HasTypeDesc` head premise where `DescTelescopePi`
carries a `HasTypeDescPi`; otherwise identical).  So the grown engine's already-proven recursor assembly
(`HasTypeDescPi.fundamentalVectorFromFormation`, `HasTypeDescPiFundamentalVectorFromFormation.lean`) ports
near-verbatim to `HasTypeDesc.rec` — MINUS the grown engine's `piIntro` / `piElim` arms (the formation engine has
no application or λ).  The genFormation former arm dispatches on `gen_piTyCode` / `gen_sigmaTyCode` and reads the
former-children reducibility bundle off the telescope logical relation via
`FormerChildrenReducible.ofTelescopeReducible … |>.toPiMember / .toSigmaMember`, the SAME construction the grown
genFormationPi arm uses; the only swap is `DescTelescope.twoChildLevels` for `DescTelescopePi.twoChildLevels`.

Because the former arm CONSTRUCTS a fresh member at whatever conclusion level is requested (consing the domain at
that single level, exactly as the grown engine does), it does NOT hit the #672 obstruction.  The sole arm that
does is `var`: the env supplies a variable at its single stored level, but the vector conclusion demands an
arbitrary positive level — the universe-domain-Π fixpoint.  So every arm here is proven outright except `var`,
which is discharged from the explicit `variablesAllPositive` hypothesis via
`formationFundamentalVarArmOfAllPositiveMember`.

## Zero-axiom verification

`IsTelescopeReducibleAtVectorFormation` is the formation-telescope counterpart of the grown
`IsTelescopeReducibleAtVector` motive (same body, indexed by `DescTelescope`).  The assembly is one
`HasTypeDesc.rec` whose arms reuse the shipped `formationFundamentalUniverseFormationArm` /
`formationFundamentalConvArm` / `formationFundamentalVarArmOfAllPositiveMember`
(SN-037 / SN-034 / #672-residual) and port the proven grown former + telescope arms
(`FormerChildrenReducible.ofTelescopeReducible`, `subst_universeCodeCell`, `ReducibleEnvVec.cons`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The formation-telescope vector-reducibility motive.**  The formation-engine counterpart of the grown
`IsTelescopeReducibleAtVector`: indexed by a `DescTelescope` (rather than a `DescTelescopePi`), with the SAME
body — under any closing substitution and reducible env, the children form the `TelescopeReducible` logical
relation at the telescope's level list.  This is `motive_2` for the `HasTypeDesc.rec` assembly below. -/
abbrev IsTelescopeReducibleAtVectorFormation {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescope profile context levelsList flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    {envLevels : Fin (baseScope + currentDepth) → Nat} (_predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length),
    TelescopeReducible flag currentDepth levelsList.length substitution levelsList (shapeEq ▸ children)

/-- **The complete formation-engine fundamental theorem (vector shape), modulo #672.**  Every `HasTypeDesc`
derivation yields the vector fundamental conclusion, given the single explicit hypothesis `variablesAllPositive`
— the universe-domain-Π all-positive member extension (#672), the sole unconditional gate.  `universeFormation`,
`conv`, the `genFormation` former arm, and both telescope arms are proven outright; only `var` consumes the
hypothesis.  Wiring this through `HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental` discharges the
entire dependent SN metatheory from #672 alone. -/
theorem formationFundamentalVectorOfAllVariablesPositive {profile : PolyProfile}
    (variablesAllPositive :
      ∀ {varScope : Nat} (varContext : TypingContext profile varScope) (index : Fin varScope)
        {targetScope : Nat} (substitution : RawTermSubst varScope (targetScope + 1))
        {envLevels : Fin varScope → Nat} (_env : ReducibleEnvVec envLevels varContext substitution),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (varContext.lookup index))
          (RawTerm.subst substitution (variableCell index)))
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    IsFundamentalConclusionAtVector context subject classifier := by
  refine HasTypeDesc.rec
    (motive_1 := fun context subject classifier _typed =>
      IsFundamentalConclusionAtVector context subject classifier)
    (motive_2 := IsTelescopeReducibleAtVectorFormation)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope typed
  · -- var: the sole #672 residual, discharged from the explicit all-positive hypothesis
    intro _scope context index
    refine formationFundamentalVarArmOfAllPositiveMember context index ?_
    intro _targetScope substitution _envLevels env
    exact variablesAllPositive context index substitution env
  · -- conv: reuse the shipped level-preserving conv arm over the two sub-IHs
    intro _scope _context _subject _classifier _reclassifier _levelExpr _flag _typed converts
      _reclassifierTyped subjectIH reclassifierIH
    exact formationFundamentalConvArm subjectIH reclassifierIH converts
  · -- universeFormation: reuse the shipped unconditional arm
    intro _scope context levelExpr flag
    exact formationFundamentalUniverseFormationArm context levelExpr flag
  · -- genFormation: the former arm, ported from the proven grown genFormationPi arm
    intro _scope context generator payload children levels flag rule isFormation premises
      premisesFundamental
    intro _targetScope substitution _envLevels predLevel env
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons _domainCode (.childCons _codomainCode .childNil) =>
          obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ :=
            DescTelescope.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          rw [subst_universeCodeCell]
          exact (FormerChildrenReducible.ofTelescopeReducible predLevel
            (premisesFundamental substitution predLevel env
              Generator.gen_piTyCode_binderShifts_eq)).toPiMember
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        match children with
        | .childCons _domainCode (.childCons _codomainCode .childNil) =>
            obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ :=
              DescTelescope.twoChildLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            rw [subst_universeCodeCell]
            exact (FormerChildrenReducible.ofTelescopeReducible predLevel
              (premisesFundamental substitution predLevel env
                Generator.gen_sigmaTyCode_binderShifts_eq)).toSigmaMember
      · by_cases isListFormer : generator = .gen_listCode
        · subst isListFormer
          obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
          match children with
          | .childCons _element .childNil =>
              obtain ⟨_elementLevel, levelsShape⟩ := DescTelescope.oneChildLevel premises
              subst levelsShape
              dsimp only [universeFormerOutput]
              exact IsReducibleMemberAt.listFormerFromTelescope predLevel
                (premisesFundamental substitution predLevel env
                  Generator.gen_listCode_binderShifts_eq)
        · by_cases isOptionFormer : generator = .gen_optionCode
          · subst isOptionFormer
            obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
            match children with
            | .childCons _element .childNil =>
                obtain ⟨_elementLevel, levelsShape⟩ := DescTelescope.oneChildLevel premises
                subst levelsShape
                dsimp only [universeFormerOutput]
                exact IsReducibleMemberAt.optionFormerFromTelescope predLevel
                  (premisesFundamental substitution predLevel env
                    Generator.gen_optionCode_binderShifts_eq)
          · by_cases isUnitFormer : generator = .gen_unitCode
            · subst isUnitFormer
              obtain rfl : rule = { outputType := nullaryFormerOutput } :=
                Option.some.inj (isFormation.symm.trans typingRuleDescOf_unitCode)
              match children with
              | .childNil =>
                  dsimp only [nullaryFormerOutput]
                  rw [subst_universeCodeCell]
                  exact IsReducibleMemberAt.unitFormerInUniverse LevelExpr.lzero
                    UniverseFlag.standard
            · exfalso
              unfold typingRuleDescOf at isFormation
              rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer,
                if_neg isUnitFormer] at isFormation
              contradiction
  · -- nilTelescope: the empty telescope is trivially reducible
    intro _baseScope _currentDepth _context _flag
    intro _targetScope _substitution _envLevels _predLevel _env _shapeEq
    exact True.intro
  · -- consTelescope: thread the head member and the rest telescope under the consed env
    intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped headFundamental restFundamental
    intro _targetScope substitution _envLevels predLevel env shapeEq
    simp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    refine ⟨fun level => ?_, fun {_memberLevel} argument argumentMember => ?_⟩
    · have headMember := headFundamental substitution level env
      rwa [subst_universeCodeCell] at headMember
    · exact restFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons env argumentMember) rfl

end FX1Poly.Typed
