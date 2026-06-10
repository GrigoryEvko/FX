import FX1Poly.Typed.FundamentalAtAllVectorPremises
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.ListFormerMemberLevelIndexed
import FX1Poly.Typed.OptionFormerMemberLevelIndexed
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.StrongNormalizationRename

/-! # FX1Poly/Typed/HasTypeDescPiFundamentalVectorFromFormation
    — assemble the grown-engine vector fundamental theorem from the formation-engine one

The grown description engine `HasTypeDescPi` embeds the formation engine (`ofFormation`) and adds the
dependent lambda/application rules.  This file proves a conditional vector-premise assembly by the kernel's
mutual recursor:

* `conv`, `piIntro`, `piElim`, and `genFormationPi` are discharged directly from already-gated semantic
  rules and telescope reducibility; and
* `ofFormation` is factored as an explicit hypothesis: a formation-engine vector premise.

No placeholder proof is hidden here; the formation premise is an argument of the theorem.  The premise is
intentionally strong and should not be confused with the final formation fundamental theorem: an arbitrary
vector conclusion is not derivable for `HasTypeDesc.var`, whose level is fixed by the environment entry.
The final all-level theorem must use this vector shape only for binder-local recursive premises whose fresh
head level is supplied by the binder rule, not as a global replacement for the formation fragment.

## Zero-axiom verification

The proof is one `HasTypeDescPi.rec` application.  The binder arm uses
`RawTerm.subst_cons_eq_subst0_lift` and `ReducibleEnvVec.cons`; the telescope arm uses the recursor-provided
head and tail induction hypotheses plus `FormerChildrenReducible.ofTelescopeReducible`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Vector reducibility for a grown premise telescope.**  Under a per-variable-level reducible
environment, every telescope head is a member of its universe at every positive level, and the tail remains
reducible after consing any reducible head argument.  The `shapeEq` parameter aligns the recursor's generic
child-spine index with the consecutive-shift index consumed by `TelescopeReducible`. -/
abbrev IsTelescopeReducibleAtVector {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescopePi profile context levelsList flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    {envLevels : Fin (baseScope + currentDepth) → Nat} (_predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length),
    TelescopeReducible flag currentDepth levelsList.length substitution levelsList (shapeEq ▸ children)

/-- **Grown-engine vector premise assembly, assuming a formation-engine vector premise.**  This is the
complete `HasTypeDescPi` recursor assembly under a deliberately strong hypothesis for the embedded
`HasTypeDesc` arm.  It is useful for binder-local premises, but the hypothesis is not the final formation
fundamental theorem because unrestricted `var` cannot satisfy arbitrary vector levels. -/
theorem HasTypeDescPi.fundamentalVectorFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
      HasTypeDescPi profile context subject classifier →
        IsFundamentalConclusionAtVector context subject classifier := by
  intro scope context subject classifier typed
  refine HasTypeDescPi.rec
    (motive_1 := fun context subject classifier _typed =>
      IsFundamentalConclusionAtVector context subject classifier)
    (motive_2 := IsTelescopeReducibleAtVector)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope typed
  · intro _scope _context _subject _classifier formationTyped
    exact formationFundamental formationTyped
  · intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped subjectFundamental reclassifierFundamental
    intro _targetScope substitution _envLevels predLevel env
    have reclassifierMember := reclassifierFundamental substitution (predLevel + 1) env
    rw [subst_universeCodeCell] at reclassifierMember
    obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
    exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
      (subjectFundamental substitution predLevel env) reclassifierReducible converts
  · intro _scope _context _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped domainFundamental codomainFundamental bodyFundamental
    intro _targetScope substitution _envLevels predLevel env
    have domainMember := domainFundamental substitution (predLevel + 1) env
    rw [subst_universeCodeCell] at domainMember
    have domainAnnSN := domainMember.stronglyNormalizing
    obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
    refine IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution domainReducible domainAnnSN
      (fun _argument argumentInDomain =>
        domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
      (fun argument argumentInDomain => ?_) (fun argument argumentInDomain => ?_)
    · rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
      have codomainMember := codomainFundamental (RawTermSubst.cons argument substitution)
        (predLevel + 1)
        (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩)
      rw [subst_universeCodeCell] at codomainMember
      exact codomainMember.tarskiDecode
    · rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
        ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
      exact bodyFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩)
  · intro _scope _context _functionTerm _argument _domainCode _codomainCode _functionTyped
      _argumentTyped functionFundamental argumentFundamental
    intro _targetScope substitution _envLevels predLevel env
    exact IsReducibleMemberAt.applicationUnderSubst substitution
      (functionFundamental substitution predLevel env) (argumentFundamental substitution predLevel env)
  · intro _scope _context generator _payload children levelsList flag rule isFormation premises
      premisesFundamental
    intro _targetScope substitution _envLevels predLevel env
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons _domainCode (.childCons _codomainCode .childNil) =>
          obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ :=
            DescTelescopePi.twoChildLevels premises
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
              DescTelescopePi.twoChildLevels premises
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
              obtain ⟨_elementLevel, levelsShape⟩ := DescTelescopePi.oneChildLevel premises
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
                obtain ⟨_elementLevel, levelsShape⟩ := DescTelescopePi.oneChildLevel premises
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
              dsimp only [typingRuleDescOf] at isFormation
              rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer,
                if_neg isUnitFormer] at isFormation
              contradiction
  · intro _baseScope _currentDepth _context _flag
    intro _targetScope _substitution _envLevels _predLevel _env _shapeEq
    exact True.intro
  · intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped headFundamental restFundamental
    intro _targetScope substitution _envLevels predLevel env shapeEq
    dsimp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    refine ⟨fun level => ?_, fun {_memberLevel} argument argumentMember => ?_⟩
    · have headMember := headFundamental substitution level env
      rwa [subst_universeCodeCell] at headMember
    · exact restFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons env argumentMember) rfl

/-- **All-level grown-engine fundamental theorem, conditional on the formation-engine vector premise.**
`fundamentalVectorFromFormation` is the recursor assembly shape used under binders; this theorem exports the
same result in the public all-level closing-environment shape.  The remaining hypothesis is explicit and
unchanged: a formation-engine vector premise strong enough for `ofFormation`. -/
theorem HasTypeDescPi.fundamentalAtAllFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    FundamentalConclusionAtAll context subject classifier :=
  fundamentalConclusionAtAllOfVector
    ((HasTypeDescPi.fundamentalVectorFromFormation formationFundamental) typed)

/-- **Strong normalization from the conditional grown-engine fundamental theorem.**  Under a closing
all-level reducible substitution, a `HasTypeDescPi` subject is strongly normalizing once the explicit
formation-engine vector premise is supplied.  This is the downstream SN handoff in exactly the substituted
shape produced by the fundamental theorem; no closed-term or checker equivalence claim is hidden here. -/
theorem HasTypeDescPi.subjectStronglyNormalizingFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  ((HasTypeDescPi.fundamentalAtAllFromFormation formationFundamental typed)
    substitution env predLevel).stronglyNormalizing

/-- **Classifier strong normalization from the conditional grown-engine fundamental theorem.**  Validity
turns the classifier into a grown type, then the conditional all-level theorem applies to that
classifier-as-subject.  The formation-engine vector premise remains explicit; no unconditional FT claim is
hidden here. -/
theorem HasTypeDescPi.classifierStronglyNormalizingFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDescPi contextWellFormed
  exact HasTypeDescPi.subjectStronglyNormalizingFromFormation
    formationFundamental classifierTyped substitution env predLevel

/-- **Closed reducibility under a closing substitution, conditional on the formation-engine premise.**  In the
empty context the all-level environment is vacuous, so the conditional grown-engine fundamental theorem
immediately specializes to a closed term under any target closing substitution.  This is the reducible-member
handoff the downstream semantic spine consumes; the only remaining assumption is still explicit, namely the
formation-engine vector premise. -/
theorem HasTypeDescPi.closedSubjectReducibleUnderSubstFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  (HasTypeDescPi.fundamentalAtAllFromFormation formationFundamental typed)
    substitution (ReducibleEnvAtAllLevels.empty substitution) predLevel

/-- **Closed strong normalization under a closing substitution, conditional on the formation-engine premise.**
This is the CR1 projection of `closedSubjectReducibleUnderSubstFromFormation`: after closing an empty-context
`HasTypeDescPi` derivation by any target substitution, the substituted subject is strongly normalizing. -/
theorem HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (HasTypeDescPi.closedSubjectReducibleUnderSubstFromFormation
    formationFundamental substitution predLevel typed).stronglyNormalizing

/-- **Closed classifier strong normalization under a closing substitution, conditional on the
formation-engine premise.** -/
theorem HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) :=
  HasTypeDescPi.classifierStronglyNormalizingFromFormation
    formationFundamental (WfContextDescPi.emptyIsWellFormed (profile := profile)) typed
    substitution (ReducibleEnvAtAllLevels.empty substitution) predLevel

/-- **Closed strong normalization from the conditional grown-engine fundamental theorem.**  In the empty
context, instantiate the closing substitution with the unique empty substitution into scope `1`, use the
vacuous all-level environment, then reflect strong normalization back along the unique empty renaming.  The
formation-engine premise remains explicit; this is the closed-term SN handoff that becomes unconditional
exactly when the formation premise is discharged. -/
theorem HasTypeDescPi.closedSubjectStronglyNormalizingFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing subject := by
  let emptyRenaming : RawRenaming 0 1 := fun emptyIndex => emptyIndex.elim0
  let emptySubstitution : RawTermSubst 0 1 :=
    RawRenaming.thenSubst emptyRenaming (RawTermSubst.identity : RawTermSubst 1 1)
  have subjectNormalizing :
      IsStronglyNormalizing (RawTerm.subst emptySubstitution subject) :=
    HasTypeDescPi.subjectStronglyNormalizingFromFormation
      formationFundamental typed emptySubstitution
      (ReducibleEnvAtAllLevels.empty emptySubstitution) 0
  have renamedSubjectNormalizing :
      IsStronglyNormalizing (RawTerm.rename emptyRenaming subject) := by
    rw [← RawTerm.subst_identity_apply (RawTerm.rename emptyRenaming subject)]
    rwa [RawTerm.rename_subst_commute emptyRenaming
      (RawTermSubst.identity : RawTermSubst 1 1) subject]
  exact StepStar.isStronglyNormalizing_of_rename emptyRenaming renamedSubjectNormalizing

/-- **Closed classifier strong normalization from the conditional grown-engine fundamental theorem.**
Validity turns the closed classifier into a closed grown type, and the conditional closed-subject theorem
normalizes that type.  The formation-engine premise remains explicit. -/
theorem HasTypeDescPi.closedClassifierStronglyNormalizingFromFormation {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing classifier := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDescPi (WfContextDescPi.emptyIsWellFormed (profile := profile))
  exact HasTypeDescPi.closedSubjectStronglyNormalizingFromFormation
    formationFundamental classifierTyped

end FX1Poly.Typed
