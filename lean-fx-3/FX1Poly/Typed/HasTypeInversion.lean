import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeStronglyNormalizing
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.HasTypeDecidableConv

/-! # FX1Poly/Typed/HasTypeInversion — per-shape typing inversion (#454)

Inversion characterizes the classifier of a well-typed cell *up to
conversion*: whatever type a variable cell is given, that type is convertible
to the variable's principal type (its context lookup); likewise a universe-code
cell's type is convertible to the next universe.  These are the lemmas
uniqueness-of-typing (#469) consumes — they let two derivations of the same
subject be compared through a shared principal type.

## Proof shape (equation-motive, not `cases`)

A variable subject `variableCell idx = mkGen gen_var idx childNil` is a
*compound constructor index* of `HasType`; inverting it with `cases`/`induction`
directly would leak `propext` through the match compiler's equation lemmas.  So
each inversion generalizes the subject to a free variable and threads an
explicit `subject = variableCell idx` equation, moving all constructor
discrimination onto a plain `Eq`: `injection` extracts the payload in the
matching arm, and `congrArg RawTerm.headGenerator` refutes the impossible arm
by generator mismatch.

The `conv` arm is the load-bearing one: it rewrites the classifier, so the
induction hypothesis is collapsed through the premise's classifier, which is a
type by validity (`HasType.classifierIsType`, needing `WfContext`) and hence a
legal Newman middle for `Conv.trans_of_typedMiddle`.

## Zero-axiom verification

Equation-motive induction + `injection` (propext-free) + the head-generator
refutation + the proven typed `Conv.trans`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Inversion for a variable cell.**  Any classifier a variable cell receives
is convertible to the variable's principal type (its context lookup).  Needs
`WfContext` so the `conv` arm's intermediate classifier is a type (validity)
and therefore strongly normalizing — a legal middle for the typed Newman
bridge. -/
theorem HasType.inversionVariable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasType profile context (variableCell index) classifier) :
    Conv classifier (context.lookup index) := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reachedClassifier : RawTerm generalScope},
        HasType profile generalContext subject reachedClassifier →
          WfContext generalContext →
            ∀ {targetIndex : Fin generalScope},
              subject = variableCell targetIndex →
                Conv reachedClassifier (generalContext.lookup targetIndex) from
    general typed wellFormed rfl
  intro generalScope generalContext subject reachedClassifier derivation
  induction derivation with
  | var armContext armIndex =>
      intro wellFormedArm targetIndex subjectEq
      have indicesAgree : armIndex = targetIndex := by
        injection subjectEq
      subst indicesAgree
      exact Conv.refl _
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro wellFormedArm targetIndex subjectEq
      exact Conv.trans_of_typedMiddle
        (HasType.classifierIsType wellFormedArm typedPremise)
        converts.sym
        (ihPremise wellFormedArm subjectEq)
  | universeFormation armContext armLevel armFlag =>
      intro wellFormedArm targetIndex subjectEq
      have headGeneratorsAgree :
          Generator.gen_universeCode = Generator.gen_var :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree
  | piFormation armContext domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetIndex subjectEq
      have headGeneratorsAgree :
          Generator.gen_piTyCode = Generator.gen_var :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree
  | sigmaFormation armContext domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetIndex subjectEq
      have headGeneratorsAgree :
          Generator.gen_sigmaTyCode = Generator.gen_var :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree

/-- **Inversion for a universe-code cell.**  Any classifier a universe-code
cell `Type@(e, flag)` receives is convertible to the next universe
`Type@(e+1, flag)`.  Mirror of `inversionVariable`: the `var` arm is the
impossible one (refuted by generator mismatch), and `universeFormation` lands
the principal type by reflexivity. -/
theorem HasType.inversionUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {classifier : RawTerm scope}
    (typed :
      HasType profile context (universeCodeCell levelExpr flag) classifier) :
    Conv classifier (universeCodeCell levelExpr.lsucc flag) := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reachedClassifier : RawTerm generalScope},
        HasType profile generalContext subject reachedClassifier →
          WfContext generalContext →
            ∀ {targetLevel : LevelExpr} {targetFlag : UniverseFlag},
              subject = universeCodeCell targetLevel targetFlag →
                Conv reachedClassifier
                  (universeCodeCell targetLevel.lsucc targetFlag) from
    general typed wellFormed rfl
  intro generalScope generalContext subject reachedClassifier derivation
  induction derivation with
  | var armContext armIndex =>
      intro wellFormedArm targetLevel targetFlag subjectEq
      have headGeneratorsAgree :
          Generator.gen_var = Generator.gen_universeCode :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree
  | conv levelExprArm flagArm typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro wellFormedArm targetLevel targetFlag subjectEq
      exact Conv.trans_of_typedMiddle
        (HasType.classifierIsType wellFormedArm typedPremise)
        converts.sym
        (ihPremise wellFormedArm subjectEq)
  | universeFormation armContext armLevel armFlag =>
      intro wellFormedArm targetLevel targetFlag subjectEq
      have payloadEq : (armLevel, armFlag) = (targetLevel, targetFlag) := by
        injection subjectEq
      injection payloadEq with levelAgree flagAgree
      subst levelAgree
      subst flagAgree
      exact Conv.refl _
  | piFormation armContext domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetLevel targetFlag subjectEq
      have headGeneratorsAgree :
          Generator.gen_piTyCode = Generator.gen_universeCode :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree
  | sigmaFormation armContext domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetLevel targetFlag subjectEq
      have headGeneratorsAgree :
          Generator.gen_sigmaTyCode = Generator.gen_universeCode :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree

/-- **Inversion for a Π-type code cell.**  A `piTyCodeCell domainCode
codomainCode` is typed only by `piFormation` (up to `conv`): its classifier is
convertible to `Type@(lmax domainLevel codomainLevel, flag)`, where the domain is
a type at `domainLevel`, the codomain a type at `codomainLevel` under the
extended context, both at one SHARED universe flag.  The Π analog of
`inversionVariable` / `inversionUniverseCode`, and simultaneously the
Π-well-formedness inversion (the Π is a type iff its parts are).  Consumed by
recursive `uniqueness` and the `Decidable IsType` Π branch.

Same equation-motive shape as the leaf inversions: generalize the subject + thread
`WfContext` (the `conv` arm needs `classifierIsType` at the case's context); the
`var` / `universeFormation` arms are impossible (generator mismatch), and the
`piFormation` arm hands back its own premises after `injection` aligns the
arm's children with the targeted `domainCode` / `codomainCode`. -/
theorem HasType.inversionPiCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasType profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasType profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasType profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        Conv classifier
          (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reachedClassifier : RawTerm generalScope},
        HasType profile generalContext subject reachedClassifier →
          WfContext generalContext →
            ∀ {targetDomain : RawTerm generalScope}
              {targetCodomain : RawTerm (generalScope + 1)},
              subject = piTyCodeCell targetDomain targetCodomain →
                ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
                  HasType profile generalContext targetDomain
                    (universeCodeCell domainLevel flag) ∧
                  HasType profile (generalContext.cons targetDomain) targetCodomain
                    (universeCodeCell codomainLevel flag) ∧
                  Conv reachedClassifier
                    (universeCodeCell
                      (LevelExpr.lmax domainLevel codomainLevel) flag) from
    general typed wellFormed rfl
  intro generalScope generalContext subject reachedClassifier derivation
  induction derivation with
  | var armContext armIndex =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator subjectEq :
          Generator.gen_var = Generator.gen_piTyCode)
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      obtain ⟨domainLevel, codomainLevel, sharedFlag,
        domainTyped, codomainTyped, convToCode⟩ :=
        ihPremise wellFormedArm subjectEq
      exact ⟨domainLevel, codomainLevel, sharedFlag, domainTyped, codomainTyped,
        Conv.trans_of_typedMiddle
          (HasType.classifierIsType wellFormedArm typedPremise)
          converts.sym convToCode⟩
  | universeFormation armContext armLevel armFlag =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator subjectEq :
          Generator.gen_universeCode = Generator.gen_piTyCode)
  | piFormation armContext armDomain armCodomain armDomainLevel armCodomainLevel
      armFlag domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      obtain ⟨domainEq, codomainEq⟩ := piTyCodeCell_inj subjectEq
      subst domainEq
      subst codomainEq
      exact ⟨armDomainLevel, armCodomainLevel, armFlag,
        domainTyped, codomainTyped, Conv.refl _⟩
  | sigmaFormation armContext armDomain armCodomain armDomainLevel armCodomainLevel
      armFlag domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      have headGeneratorsAgree :
          Generator.gen_sigmaTyCode = Generator.gen_piTyCode :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree

/-- **Inversion for a Σ-type code cell.**  The dual of `inversionPiCode`: a
`sigmaTyCodeCell domainCode codomainCode` is typed only by `sigmaFormation` (up
to `conv`); its classifier is convertible to
`Type@(lmax domainLevel codomainLevel, flag)`, the domain a type at
`domainLevel`, the codomain a type at `codomainLevel` under the extended context,
both at one shared flag.  Same equation-motive shape as `inversionPiCode`, with
the roles swapped: the `var` / `universeFormation` / `piFormation` arms are
impossible (generator mismatch), and the `sigmaFormation` arm hands back its own
premises after `sigmaTyCodeCell_inj` aligns the children. -/
theorem HasType.inversionSigmaCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasType profile context (sigmaTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasType profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasType profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        Conv classifier
          (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reachedClassifier : RawTerm generalScope},
        HasType profile generalContext subject reachedClassifier →
          WfContext generalContext →
            ∀ {targetDomain : RawTerm generalScope}
              {targetCodomain : RawTerm (generalScope + 1)},
              subject = sigmaTyCodeCell targetDomain targetCodomain →
                ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
                  HasType profile generalContext targetDomain
                    (universeCodeCell domainLevel flag) ∧
                  HasType profile (generalContext.cons targetDomain) targetCodomain
                    (universeCodeCell codomainLevel flag) ∧
                  Conv reachedClassifier
                    (universeCodeCell
                      (LevelExpr.lmax domainLevel codomainLevel) flag) from
    general typed wellFormed rfl
  intro generalScope generalContext subject reachedClassifier derivation
  induction derivation with
  | var armContext armIndex =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator subjectEq :
          Generator.gen_var = Generator.gen_sigmaTyCode)
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      obtain ⟨domainLevel, codomainLevel, sharedFlag,
        domainTyped, codomainTyped, convToCode⟩ :=
        ihPremise wellFormedArm subjectEq
      exact ⟨domainLevel, codomainLevel, sharedFlag, domainTyped, codomainTyped,
        Conv.trans_of_typedMiddle
          (HasType.classifierIsType wellFormedArm typedPremise)
          converts.sym convToCode⟩
  | universeFormation armContext armLevel armFlag =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator subjectEq :
          Generator.gen_universeCode = Generator.gen_sigmaTyCode)
  | piFormation armContext armDomain armCodomain armDomainLevel armCodomainLevel
      armFlag domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator subjectEq :
          Generator.gen_piTyCode = Generator.gen_sigmaTyCode)
  | sigmaFormation armContext armDomain armCodomain armDomainLevel armCodomainLevel
      armFlag domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm targetDomain targetCodomain subjectEq
      obtain ⟨domainEq, codomainEq⟩ := sigmaTyCodeCell_inj subjectEq
      subst domainEq
      subst codomainEq
      exact ⟨armDomainLevel, armCodomainLevel, armFlag,
        domainTyped, codomainTyped, Conv.refl _⟩

/-- **Uniqueness of typing (#469)** for the current fragment: any two classifiers
of the same subject are convertible.  Proved by **induction on the first
derivation**: the `var` and
`universeFormation` subjects have a derivation-INDEPENDENT principal type, so
their cases just `.sym` the matching inversion of the second derivation; the
`conv` case forwards its premise's IH through the converted classifier (a type by
validity).  The `piFormation` case is the genuinely recursive one — a Π's
principal type `Type@(lmax l₁ l₂, f)` depends on the derivation's premises, so it
inverts the second derivation (`inversionPiCode`), uses the domain/codomain IHs to
force the two derivations' levels and flag to agree
(`levelFlag_eq_of_conv_universeCodeCell`), and concludes the two principal
universe codes are literally equal.  `WfContext.cons` supplies the codomain IH's
context (the domain is a type by its own premise). -/
theorem HasType.uniqueness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {subject firstClassifier secondClassifier : RawTerm scope}
    (firstTyped : HasType profile context subject firstClassifier)
    (secondTyped : HasType profile context subject secondClassifier) :
    Conv firstClassifier secondClassifier := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject firstReached : RawTerm generalScope},
        HasType profile generalContext subject firstReached →
          WfContext generalContext →
            ∀ {secondReached : RawTerm generalScope},
              HasType profile generalContext subject secondReached →
                Conv firstReached secondReached from
    general firstTyped wellFormed secondTyped
  intro generalScope generalContext subject firstReached derivation
  induction derivation with
  | var armContext armIndex =>
      intro wellFormedArm secondReached secondDerivation
      exact (HasType.inversionVariable wellFormedArm secondDerivation).sym
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro wellFormedArm secondReached secondDerivation
      exact Conv.trans_of_typedMiddle
        (HasType.classifierIsType wellFormedArm typedPremise)
        converts.sym
        (ihPremise wellFormedArm secondDerivation)
  | universeFormation armContext armLevel armFlag =>
      intro wellFormedArm secondReached secondDerivation
      exact (HasType.inversionUniverseCode wellFormedArm secondDerivation).sym
  | piFormation armContext armDomain armCodomain armDomainLevel armCodomainLevel
      armFlag domainTyped codomainTyped ihDomain ihCodomain =>
      intro wellFormedArm secondReached secondDerivation
      obtain ⟨secondDomainLevel, secondCodomainLevel, secondFlag,
        secondDomainTyped, secondCodomainTyped, secondConvToCode⟩ :=
        HasType.inversionPiCode wellFormedArm secondDerivation
      obtain ⟨domainLevelAgree, domainFlagAgree⟩ :=
        levelFlag_eq_of_conv_universeCodeCell (context := armContext)
          (ihDomain wellFormedArm secondDomainTyped)
      have codomainWellFormed : WfContext (armContext.cons armDomain) :=
        WfContext.cons wellFormedArm ⟨armDomainLevel, armFlag, domainTyped⟩
      obtain ⟨codomainLevelAgree, _codomainFlagAgree⟩ :=
        levelFlag_eq_of_conv_universeCodeCell
          (context := armContext.cons armDomain)
          (ihCodomain codomainWellFormed secondCodomainTyped)
      subst domainLevelAgree
      subst codomainLevelAgree
      subst domainFlagAgree
      exact secondConvToCode.sym
  | sigmaFormation armContext armDomain armCodomain armDomainLevel armCodomainLevel
      armFlag domainTyped codomainTyped ihDomain ihCodomain =>
      -- exact mirror of the `piFormation` case: invert the second derivation with
      -- `inversionSigmaCode`, force the levels / flag to agree via the
      -- domain/codomain IHs, then the two principal universe codes coincide
      intro wellFormedArm secondReached secondDerivation
      obtain ⟨secondDomainLevel, secondCodomainLevel, secondFlag,
        secondDomainTyped, secondCodomainTyped, secondConvToCode⟩ :=
        HasType.inversionSigmaCode wellFormedArm secondDerivation
      obtain ⟨domainLevelAgree, domainFlagAgree⟩ :=
        levelFlag_eq_of_conv_universeCodeCell (context := armContext)
          (ihDomain wellFormedArm secondDomainTyped)
      have codomainWellFormed : WfContext (armContext.cons armDomain) :=
        WfContext.cons wellFormedArm ⟨armDomainLevel, armFlag, domainTyped⟩
      obtain ⟨codomainLevelAgree, _codomainFlagAgree⟩ :=
        levelFlag_eq_of_conv_universeCodeCell
          (context := armContext.cons armDomain)
          (ihCodomain codomainWellFormed secondCodomainTyped)
      subst domainLevelAgree
      subst codomainLevelAgree
      subst domainFlagAgree
      exact secondConvToCode.sym

end FX1Poly.Typed
