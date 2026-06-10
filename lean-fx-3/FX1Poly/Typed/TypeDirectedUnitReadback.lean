import FX1Poly.Typed.UnitSpineDetectionBoundary
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/TypeDirectedUnitReadback
   — the type-directed readback skeleton, unit-instantiated (#481 brick 1)

The unit campaign's five refutations proved that no bottom-up syntactic procedure decides the
congruent unit-η relation — the classifier must flow TOP-DOWN.  This module ships that flow:
`readbackAtClassifier` receives the classifier at every position and

  * at classifier `unitTypeCell`: returns `unitCell` — the η-long readback at unit is CONSTANT,
    so every unit-classified subterm (variable, compound neutral, λ-application, value)
    collapses without any detection;
  * at a literal Π classifier over a matching λ: descends into the body with the CODOMAIN
    classifier under the extended context — the binder crossing, now type-directed;
  * everywhere else (and at fuel 0): falls back to the shipped UNCONDITIONALLY sound
    binder-crossing collapse — fuel exhaustion and uncovered classifiers DEGRADE, never break.

`readbackAtClassifier_congruent` is the typed soundness: on a subject typed at the classifier
(with the classifier itself universe-typed — the standard NbE presupposition), the readback is
congruently unit-η-equal to the input.  The unit arm is one `unitEta` leaf justified by the
typing hypothesis itself; the Π arm re-types the body at the GIVEN codomain via `invertLam` +
`Conv.piTyCode_inj` + the grown `conv` rule (its reclassifier obligation discharged by
`invertPiTyCode` on the classifier's universe typing) and recurses.

## The payoff — every refutation boundary pair, decided by ONE procedure

  * β-surfacing pair and compound-neutral pair: both sides read back to `unitCell` at classifier
    `unitTypeCell` — decided by `ofReadbackEqual` with `rfl`.
  * λ-argument pair (the 5th refutation, undetectable bottom-up): `app(g, λx.x)` reads back to
    `unitCell` instantly — the classifier arrived top-down; no spine synthesis, no checking.
  * binder-fence normal forms: at the Π classifier the readback crosses the binder
    type-directedly and identifies them by `rfl` (the η-long-at-unit codomain).

## Honest boundaries

(1) Soundness requires the subject GROWN-typed at the classifier — data-intro-typed subjects
(e.g. `unitCell` itself) are not yet inputs; deciding a pair against a data value uses the
direct form (readback of the typed side computes to the value).  (2) Classifier recovery at
APPLICATION positions (function/argument of an app at a known classifier) is not yet wired —
the spine detector is the tool; those positions currently fall back.  (3) The Π arm COLLAPSES
under the binder but does not yet η-EXPAND non-λ functions — η-long readback at Π (#360) is the
next brick.  Each widening strengthens the same soundness statement.

## Zero-axiom verification

`asLamCell?` follows the `fireRootEtaRedex?` dispatch recipe; the readback is fuel-structural
(rfl-computing, no `WellFounded.fix`); soundness mirrors the function with goal-side `split`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Destructure a λ cell into its domain annotation and body (syntactic). -/
def asLamCell? {scope : Nat} : RawTerm scope → Option (RawTerm scope × RawTerm (scope + 1))
  | .mkGen generator _payload children =>
      if isLam : generator = Generator.gen_lam then
        match (isLam ▸ children :
            RawTermChildren (Generator.gen_lam.binderShifts) scope) with
        | .childCons domainAnn (.childCons body .childNil) => some (domainAnn, body)
      else none

/-- `asLamCell?` is honest: a positive answer reconstructs the λ cell. -/
theorem asLamCell?_sound {scope : Nat} {term : RawTerm scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (isLam : asLamCell? term = some (domainAnn, body)) :
    term = lamCell domainAnn body := by
  match term, isLam with
  | .mkGen generator payload children, isLam =>
    dsimp only [asLamCell?] at isLam
    split at isLam
    · next isLamGen =>
        subst isLamGen
        split at isLam
        next headDomain headBody childrenEq =>
        have childrenShape :
            children = .childCons headDomain (.childCons headBody .childNil) := childrenEq
        subst childrenShape
        cases Option.some.inj isLam
        rfl
    · cases isLam

/-- **The type-directed readback, unit fragment**: classifier-directed unit collapse with
Π-descent; everywhere else (and at fuel 0) the unconditionally sound deep collapse. -/
def readbackAtClassifier {profile : PolyProfile} :
    Nat → {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → RawTerm scope
  | 0, _, context, _, term => collapseUnitVariablesDeep context term
  | fuel + 1, _, context, classifier, term =>
      if classifier = unitTypeCell then unitCell
      else
        match asPiCode? classifier with
        | none => collapseUnitVariablesDeep context term
        | some (domainCode, codomainCode) =>
            match asLamCell? term with
            | none => collapseUnitVariablesDeep context term
            | some (domainAnn, body) =>
                if domainAnn = domainCode then
                  lamCell domainAnn
                    (readbackAtClassifier fuel (context.cons domainAnn) codomainCode body)
                else collapseUnitVariablesDeep context term

/-- **★ Typed soundness of the type-directed readback**: a subject grown-typed at the classifier
(itself universe-typed) is congruently unit-η-equal to its readback, at every fuel.  The unit arm
is one `unitEta` leaf justified by the typing hypothesis; the Π arm re-types the body at the
given codomain (`invertLam` + Π-injectivity + `conv`, the reclassifier obligation from
`invertPiTyCode`) and recurses; all other arms are the shipped unconditional deep-collapse
soundness. -/
theorem readbackAtClassifier_congruent {profile : PolyProfile} :
    (fuel : Nat) → {scope : Nat} → (context : TypingContext profile scope) →
      (classifier term : RawTerm scope) →
      {classifierLevel : LevelExpr} → {classifierFlag : UniverseFlag} →
      (subjectTyped : HasTypeDescPi profile context term classifier) →
      (classifierTyped : HasTypeDescPi profile context classifier
        (universeCodeCell classifierLevel classifierFlag)) →
      DefEqUnitEtaCong profile context term
        (readbackAtClassifier fuel context classifier term)
  | 0, _, context, _, term, _, _, _subjectTyped, _classifierTyped =>
      collapseUnitVariablesDeep_congruent context term
  | fuel + 1, _, context, classifier, term, _, _, subjectTyped, classifierTyped => by
      dsimp only [readbackAtClassifier]
      split
      · next isUnit =>
          exact .ofDefEq (.unitEta (Or.inr (isUnit ▸ subjectTyped))
            (Or.inl (HasTypeDescDataIntro.unitValueTyped context)))
      · next _notUnit =>
          split
          · exact collapseUnitVariablesDeep_congruent context term
          · next domainCode codomainCode hPiCode =>
              split
              · exact collapseUnitVariablesDeep_congruent context term
              · next domainAnn body hLam =>
                  split
                  · next domainsMatch =>
                      have termIsLam := asLamCell?_sound hLam
                      have classifierIsPi := asPiCode?_sound hPiCode
                      subst termIsLam
                      subst classifierIsPi
                      subst domainsMatch
                      obtain ⟨innerCodomain, _innerDomainLevel, _innerCodomainLevel, _innerFlag,
                        convToInner, _domainUniverseTypedInner, _innerCodomainUniverseTyped,
                        bodyTypedInner⟩ := HasTypeDescPi.invertLam subjectTyped
                      have codomainsConv : Conv codomainCode innerCodomain :=
                        (Conv.piTyCode_inj convToInner).2
                      obtain ⟨_piDomainLevel, piCodomainLevel, piFlag,
                        _domainUniverseTyped, codomainUniverseTyped,
                        _classifierConvUniverse⟩ :=
                        HasTypeDescPi.invertPiTyCode classifierTyped
                      have bodyTyped :
                          HasTypeDescPi profile (context.cons domainAnn) body codomainCode :=
                        HasTypeDescPi.conv piCodomainLevel piFlag bodyTypedInner
                          (Conv.sym codomainsConv) codomainUniverseTyped
                      exact DefEqUnitEtaCong.congGen (generator := Generator.gen_lam) ()
                        (.consEqualZero (.consBinder
                          (readbackAtClassifier_congruent fuel (context.cons domainAnn)
                            codomainCode body bodyTyped codomainUniverseTyped)
                          .nil))
                  · next _domainsDiffer =>
                      exact collapseUnitVariablesDeep_congruent context term

/-- **Sound semi-decision, type-directed mode**: two subjects grown-typed at the same
universe-typed classifier with EQUAL readbacks are congruently unit-η-equal. -/
theorem DefEqUnitEtaCong.ofReadbackEqual {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier leftTerm rightTerm : RawTerm scope}
    {leftFuel rightFuel : Nat}
    {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
    (leftTyped : HasTypeDescPi profile context leftTerm classifier)
    (rightTyped : HasTypeDescPi profile context rightTerm classifier)
    (classifierTyped : HasTypeDescPi profile context classifier
      (universeCodeCell classifierLevel classifierFlag))
    (readbacksEqual : readbackAtClassifier leftFuel context classifier leftTerm
      = readbackAtClassifier rightFuel context classifier rightTerm) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .trans (readbackAtClassifier_congruent leftFuel context classifier leftTerm
      leftTyped classifierTyped)
    (readbacksEqual ▸ (readbackAtClassifier_congruent rightFuel context classifier rightTerm
      rightTyped classifierTyped).sym)

/-- **The β-surfacing pair, decided by the type-directed readback**: both sides read back to
`unitCell` at classifier `unitTypeCell` — the pair that refuted one-pass collapse-then-compare
is now a `rfl` for the uniform procedure. -/
theorem betaSurfacingPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      betaSurfacingRedex (variableCell ⟨0, Nat.zero_lt_one⟩) :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 1) (rightFuel := 1)
    (betaSurfacingRedexTyped profile) (unitVariableTyped profile)
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped (unitVariableContext profile)))
    rfl

/-- **The compound-neutral pair, decided by the type-directed readback**: the classifier arrives
top-down, so the neutral needs NO spine synthesis — both sides read back to `unitCell`. -/
theorem compoundNeutralPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      (variableCell ⟨0, Nat.le.step Nat.le.refl⟩) compoundUnitNeutral :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 1) (rightFuel := 1)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨0, Nat.le.step Nat.le.refl⟩))
    (compoundUnitNeutralTyped profile)
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped (unitFunctionContext profile)))
    rfl

/-- **★ The λ-argument pair (the 5th refutation), decided by the type-directed readback**: the
pair NO bottom-up procedure could decide is resolved instantly — `app(g, λx.x)` reads back to
`unitCell` because the classifier flowed top-down.  Direct form: the readback of the typed side
computes to the data value itself. -/
theorem lambdaArgumentPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (higherOrderUnitContext profile)
      lambdaArgumentNeutral unitCell :=
  readbackAtClassifier_congruent 1 (higherOrderUnitContext profile) unitTypeCell
    lambdaArgumentNeutral (lambdaArgumentNeutralTyped profile)
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped (higherOrderUnitContext profile)))

/-- **The binder-fence normal forms are identified at the Π classifier** — the readback crosses
the binder TYPE-DIRECTEDLY (the codomain classifier travels under the λ) and both βη-normal
forms compute to the η-long-at-unit form `λ(x:Unit).unitCell`, by `rfl`. -/
theorem readback_identifiesKonstNormalFormsAtPi (profile : PolyProfile) :
    readbackAtClassifier 1 (unitVariableContext profile)
        (piTyCodeCell unitTypeCell unitTypeCell) konstAppliedToVariableNormalForm
      = readbackAtClassifier 1 (unitVariableContext profile)
          (piTyCodeCell unitTypeCell unitTypeCell) konstAppliedToUnitNormalForm := rfl

end FX1Poly.Typed
