import FX1Poly.Typed.UnitSpineDetectionBoundary
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiEtaExpansionGrown
import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/TypeDirectedUnitReadback
   — the type-directed η-long readback, unit + Π fragment (#481 bricks 1–2, #360 core)

The unit campaign's five refutations proved that no bottom-up syntactic procedure decides the
congruent unit-η relation — the classifier must flow TOP-DOWN.  This module ships that flow:
`readbackAtClassifier` receives the classifier at every position and

  * at classifier `unitTypeCell`: returns `unitCell` — the η-long readback at unit is CONSTANT,
    so every unit-classified subterm (variable, compound neutral, λ-application, value)
    collapses without any detection;
  * at a literal Π classifier over a matching λ: descends into the body with the CODOMAIN
    classifier under the extended context — the binder crossing, type-directed;
  * at a literal Π classifier over a NON-λ subject: η-EXPANDS — emits
    `λ(D, readback(app(weaken t, var₀)) at C)`, the η-LONG readback at Π (#360); the inner
    position then sees the codomain classifier, so η and unit-η COMPOSE (a neutral
    `f : Π(_:Unit).Unit` reads back to the full η-long form `λ(_:Unit).unitCell`);
  * everywhere else (and at fuel 0): falls back to the shipped UNCONDITIONALLY sound
    binder-crossing collapse — fuel exhaustion and uncovered classifiers DEGRADE, never break.

`readbackAtClassifier_congruent` is the typed soundness under the standard NbE presuppositions —
formation-well-formed context, subject grown-typed at the classifier, classifier
FORMATION-typed at a universe (so its Π-inversion both extends the wf down binders and feeds
every grown obligation via `ofFormation`).  The η-expansion leg lifts the one-step η-contraction
through `DefEqUnitEta.ofBetaEtaConv` (whose wf + both-typed presuppositions are discharged by
the hypotheses + `etaExpansionPreservesTypingGrown`), then recurses into the expansion body via
the inlined `weakenUnderBinding`/`piElim`/η-identity derivation.

## The payoff — η and unit-η decided by ONE procedure

  * β-surfacing pair and compound-neutral pair: both sides read back to `unitCell` at classifier
    `unitTypeCell` — decided by `ofReadbackEqual` with `rfl`.
  * λ-argument pair (the 5th refutation): `app(g, λx.x)` reads back to `unitCell` instantly.
  * binder-fence normal forms: identified at the Π classifier by `rfl`.
  * THE η PAIR (`f` vs `λx.(weaken f)x`): both read back to the η-long form — decided by
    `ofReadbackEqual` with `rfl` (`etaPair_decidedByReadback`).
  * the MIXED η+unit pair (`f` vs `λ(_:Unit).unitCell`): undecidable by every prior procedure
    (deep collapse fixes both; both are βη-normal) — decided directly
    (`etaUnitPair_decidedByReadback`): the readback of `f` IS the η-long form, by `rfl`.

## Honest boundaries

(1) Soundness presupposes the classifier FORMATION-typed (static type codes — no β-redex
classifiers) and the subject grown-typed; data-intro-typed subjects (e.g. `unitCell` itself)
enter only as direct-form right-hand sides.  (2) η-expansion fires only at LITERAL Π codes;
classifiers that merely reduce to Π codes fall back.  (3) Σ (surjective pairing, #361) and the
modal/cubical η classifiers (#363) are not yet arms.  Each widening strengthens the same
soundness statement.

## Zero-axiom verification

`asLamCell?` follows the `fireRootEtaRedex?` dispatch recipe; the readback is fuel-structural
(rfl-computing, no `WellFounded.fix`); soundness mirrors the function with goal-side `split`;
the η leg threads only shipped zero-axiom pieces (`etaExpansionPreservesTypingGrown`,
`weakenUnderBinding`, `rename_piTyCodeCell`, `subst0_iterateLiftWeaken_newestVar`,
`inversionPiCodeComponents`, `Step.eta.etaLam`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

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

/-- Destructure an application cell into its function and argument (syntactic). -/
def asAppCell? {scope : Nat} : RawTerm scope → Option (RawTerm scope × RawTerm scope)
  | .mkGen generator _payload children =>
      if isApp : generator = Generator.gen_app then
        match (isApp ▸ children :
            RawTermChildren (Generator.gen_app.binderShifts) scope) with
        | .childCons functionTerm (.childCons argument .childNil) =>
            some (functionTerm, argument)
      else none

/-- `asAppCell?` is honest: a positive answer reconstructs the application cell. -/
theorem asAppCell?_sound {scope : Nat} {term : RawTerm scope}
    {functionTerm argument : RawTerm scope}
    (isApp : asAppCell? term = some (functionTerm, argument)) :
    term = appCell functionTerm argument := by
  match term, isApp with
  | .mkGen generator payload children, isApp =>
    dsimp only [asAppCell?] at isApp
    split at isApp
    · next isAppGen =>
        subst isAppGen
        split at isApp
        next headFunction headArgument childrenEq =>
        have childrenShape :
            children = .childCons headFunction (.childCons headArgument .childNil) :=
          childrenEq
        subst childrenShape
        cases Option.some.inj isApp
        rfl
    · cases isApp

/-- Destructure a variable cell into its de Bruijn index (syntactic). -/
def asVarCell? {scope : Nat} : RawTerm scope → Option (Fin scope)
  | .mkGen generator payload _children =>
      if isVar : generator = Generator.gen_var then
        some (isVar ▸ payload : Generator.gen_var.payload scope)
      else none

/-- `asVarCell?` is honest: a positive answer reconstructs the variable cell. -/
theorem asVarCell?_sound {scope : Nat} {term : RawTerm scope} {index : Fin scope}
    (isVar : asVarCell? term = some index) :
    term = variableCell index := by
  match term, isVar with
  | .mkGen generator payload children, isVar =>
    dsimp only [asVarCell?] at isVar
    split at isVar
    · next isVarGen =>
        subst isVarGen
        cases Option.some.inj isVar
        rw [RawTermChildren.eq_childNil children]
        rfl
    · cases isVar

/-- **The type-directed η-long readback, unit + Π + spine fragment**: classifier-directed unit
collapse, Π-descent on matching λs, η-EXPANSION on non-λ subjects at Π, and — at classifiers
that are neither — the NEUTRAL-SPINE arm: a variable-headed application's argument is read back
at the DOMAIN of the head's looked-up Π code (the classifier the 6th boundary proved
unreachable bottom-up); everywhere else (and at fuel 0) the unconditionally sound deep
collapse. -/
def readbackAtClassifier {profile : PolyProfile} :
    Nat → {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → RawTerm scope
  | 0, _, context, _, term => collapseUnitVariablesDeep context term
  | fuel + 1, _, context, classifier, term =>
      if classifier = unitTypeCell then unitCell
      else
        match asPiCode? classifier with
        | none =>
            match asAppCell? term with
            | none => collapseUnitVariablesDeep context term
            | some (functionTerm, argument) =>
                match asVarCell? functionTerm with
                | none => collapseUnitVariablesDeep context term
                | some index =>
                    match asPiCode? (context.lookup index) with
                    | none => collapseUnitVariablesDeep context term
                    | some (domainCode, _codomainCode) =>
                        appCell functionTerm
                          (readbackAtClassifier fuel context domainCode argument)
        | some (domainCode, codomainCode) =>
            match asLamCell? term with
            | none =>
                lamCell domainCode
                  (readbackAtClassifier fuel (context.cons domainCode) codomainCode
                    (appCell (RawTerm.weaken term) RawTerm.newestVar))
            | some (domainAnn, body) =>
                if domainAnn = domainCode then
                  lamCell domainAnn
                    (readbackAtClassifier fuel (context.cons domainAnn) codomainCode body)
                else collapseUnitVariablesDeep context term

/-- **★ Typed soundness of the type-directed η-long readback**: under the NbE presuppositions
(formation-wf context, subject grown-typed at the classifier, classifier FORMATION-typed at a
universe), the readback is congruently unit-η-equal to the input, at every fuel.  The unit arm
is one `unitEta` leaf; the η-expansion arm lifts the η-contraction through `ofBetaEtaConv`
(`etaExpansionPreservesTypingGrown` supplies the expansion typing) and recurses into the body
(the inlined weaken/`piElim`/η-identity derivation); the λ arm re-types the body at the given
codomain (`invertLam` + Π-injectivity + `conv`, the reclassifier obligation from the
classifier's formation inversion — which also extends the wf under the binder); all other arms
are the shipped unconditional deep-collapse soundness. -/
theorem readbackAtClassifier_congruent {profile : PolyProfile} :
    (fuel : Nat) → {scope : Nat} → (context : TypingContext profile scope) →
      (classifier term : RawTerm scope) →
      (contextWellFormed : WfContextDesc context) →
      (subjectTyped : HasTypeDescPi profile context term classifier) →
      {classifierLevel : LevelExpr} → {classifierFlag : UniverseFlag} →
      (classifierTyped : HasTypeDesc profile context classifier
        (universeCodeCell classifierLevel classifierFlag)) →
      DefEqUnitEtaCong profile context term
        (readbackAtClassifier fuel context classifier term)
  | 0, _, context, _, term, _, _, _, _, _ =>
      collapseUnitVariablesDeep_congruent context term
  | fuel + 1, _, context, classifier, term, contextWellFormed, subjectTyped, _, _,
      classifierTyped => by
      dsimp only [readbackAtClassifier]
      split
      · next isUnit =>
          exact .ofDefEq (.unitEta (Or.inr (isUnit ▸ subjectTyped))
            (Or.inl (HasTypeDescDataIntro.unitValueTyped context)))
      · next _notUnit =>
          split
          · -- the NEUTRAL-SPINE arm: classifier is not a Π code
            split
            · exact collapseUnitVariablesDeep_congruent context term
            · next functionTerm argument hApp =>
                split
                · exact collapseUnitVariablesDeep_congruent context term
                · next index hVar =>
                    split
                    · exact collapseUnitVariablesDeep_congruent context term
                    · next domainCode _codomainCode hLookupPi =>
                        have termIsApp := asAppCell?_sound hApp
                        have functionIsVar := asVarCell?_sound hVar
                        subst termIsApp
                        subst functionIsVar
                        have lookupIsPi := asPiCode?_sound hLookupPi
                        obtain ⟨innerDomain, innerCodomain, functionTyped,
                          argumentTypedInner, _classifierConv⟩ :=
                          HasTypeDescPi.invertApp subjectTyped
                        have functionClassifierConv :=
                          HasTypeDescPi.invertVar functionTyped
                        rw [lookupIsPi] at functionClassifierConv
                        have domainsConv : Conv innerDomain domainCode :=
                          (Conv.piTyCode_inj functionClassifierConv).1
                        obtain ⟨_lookupLevel, _lookupFlag, lookupFormationTyped⟩ :=
                          WfContextDesc.lookupIsTypeDesc context contextWellFormed index
                        rw [lookupIsPi] at lookupFormationTyped
                        obtain ⟨formDomainLevel, _formCodomainLevel, formFlag,
                          domainFormationTyped, _codomainFormationTyped, _convClass⟩ :=
                          HasTypeDesc.inversionPiCodeComponents lookupFormationTyped
                        have argumentTyped :
                            HasTypeDescPi profile context argument domainCode :=
                          HasTypeDescPi.conv formDomainLevel formFlag argumentTypedInner
                            domainsConv
                            (HasTypeDescPi.ofFormation domainFormationTyped)
                        exact DefEqUnitEtaCong.congGen (generator := Generator.gen_app) ()
                          (.consEqualZero (.consZero
                            (readbackAtClassifier_congruent fuel context domainCode
                              argument contextWellFormed argumentTyped
                              domainFormationTyped)
                            .nil))
          · next domainCode codomainCode hPiCode =>
              have classifierIsPi := asPiCode?_sound hPiCode
              subst classifierIsPi
              obtain ⟨formDomainLevel, formCodomainLevel, formFlag,
                domainFormationTyped, codomainFormationTyped, _convClassifier⟩ :=
                HasTypeDesc.inversionPiCodeComponents classifierTyped
              have wellFormedExtended : WfContextDesc (context.cons domainCode) :=
                WfContextDesc.cons contextWellFormed
                  ⟨formDomainLevel, formFlag, domainFormationTyped⟩
              split
              · -- η-EXPANSION: the subject is not a λ
                have etaExpansionTyped :=
                  HasTypeDescPi.etaExpansionPreservesTypingGrown
                    (WfContextDescPi.ofWfContextDesc contextWellFormed) subjectTyped
                have functionWeakened :
                    HasTypeDescPi profile (context.cons domainCode)
                      (RawTerm.weaken term)
                      (piTyCodeCell (RawTerm.rename RawRenaming.weaken domainCode)
                        (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1)
                          codomainCode)) := by
                  have weakened := HasTypeDescPi.weakenUnderBinding domainCode subjectTyped
                  rw [rename_piTyCodeCell] at weakened
                  exact weakened
                have newestVarTyped :
                    HasTypeDescPi profile (context.cons domainCode) RawTerm.newestVar
                      (RawTerm.rename RawRenaming.weaken domainCode) :=
                  HasTypeDescPi.ofFormation
                    (HasTypeDesc.var (context.cons domainCode) ⟨0, Nat.zero_lt_succ _⟩)
                have bodyTyped :
                    HasTypeDescPi profile (context.cons domainCode)
                      (appCell (RawTerm.weaken term) RawTerm.newestVar) codomainCode := by
                  have applied := HasTypeDescPi.piElim functionWeakened newestVarTyped
                  rw [RawTerm.subst0_iterateLiftWeaken_newestVar] at applied
                  exact applied
                have expansionConv :
                    BetaEtaConv term (RawTerm.etaLamSource domainCode term) :=
                  ⟨term, Step.betaEtaStar.refl term,
                    Step.betaEtaStar.trans (Or.inr (Step.eta.etaLam domainCode term))
                      (Step.betaEtaStar.refl term)⟩
                exact DefEqUnitEtaCong.trans
                  (.ofDefEq (.ofBetaEtaConv contextWellFormed subjectTyped
                    etaExpansionTyped expansionConv))
                  (DefEqUnitEtaCong.congGen (generator := Generator.gen_lam) ()
                    (.consEqualZero (.consBinder
                      (readbackAtClassifier_congruent fuel (context.cons domainCode)
                        codomainCode (appCell (RawTerm.weaken term) RawTerm.newestVar)
                        wellFormedExtended bodyTyped codomainFormationTyped)
                      .nil)))
              · next domainAnn body hLam =>
                  split
                  · next domainsMatch =>
                      have termIsLam := asLamCell?_sound hLam
                      subst termIsLam
                      subst domainsMatch
                      obtain ⟨innerCodomain, _innerDomainLevel, _innerCodomainLevel,
                        _innerFlag, convToInner, _domainUniverseTypedInner,
                        _innerCodomainUniverseTyped, bodyTypedInner⟩ :=
                        HasTypeDescPi.invertLam subjectTyped
                      have codomainsConv : Conv codomainCode innerCodomain :=
                        (Conv.piTyCode_inj convToInner).2
                      have bodyTyped :
                          HasTypeDescPi profile (context.cons domainAnn) body
                            codomainCode :=
                        HasTypeDescPi.conv formCodomainLevel formFlag bodyTypedInner
                          (Conv.sym codomainsConv)
                          (HasTypeDescPi.ofFormation codomainFormationTyped)
                      exact DefEqUnitEtaCong.congGen (generator := Generator.gen_lam) ()
                        (.consEqualZero (.consBinder
                          (readbackAtClassifier_congruent fuel (context.cons domainAnn)
                            codomainCode body wellFormedExtended bodyTyped
                            codomainFormationTyped)
                          .nil))
                  · next _domainsDiffer =>
                      exact collapseUnitVariablesDeep_congruent context term

/-- **Sound semi-decision, type-directed mode**: two subjects grown-typed at the same
formation-typed classifier in a wf context, with EQUAL readbacks, are congruently
unit-η-equal. -/
theorem DefEqUnitEtaCong.ofReadbackEqual {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier leftTerm rightTerm : RawTerm scope}
    {leftFuel rightFuel : Nat}
    {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm classifier)
    (rightTyped : HasTypeDescPi profile context rightTerm classifier)
    (classifierTyped : HasTypeDesc profile context classifier
      (universeCodeCell classifierLevel classifierFlag))
    (readbacksEqual : readbackAtClassifier leftFuel context classifier leftTerm
      = readbackAtClassifier rightFuel context classifier rightTerm) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .trans (readbackAtClassifier_congruent leftFuel context classifier leftTerm
      contextWellFormed leftTyped classifierTyped)
    (readbacksEqual ▸ (readbackAtClassifier_congruent rightFuel context classifier rightTerm
      contextWellFormed rightTyped classifierTyped).sym)

/-- The context `(f : Π(_:Unit).Unit, x : Unit)` is formation-well-formed — the Π entry through
the generic formation arm over the unit rows. -/
theorem unitFunctionContextWellFormed (profile : PolyProfile) :
    WfContextDesc (unitFunctionContext profile) :=
  WfContextDesc.cons
    (WfContextDesc.cons WfContextDesc.emptyIsWellFormed
      ⟨_, _, hasTypeDesc_piFormation_viaGenArm TypingContext.empty
        unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
        (unitTypeCellFormationTyped TypingContext.empty)
        (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell))⟩)
    (unitTypeCellIsTypeDesc
      ((TypingContext.empty : TypingContext profile 0).cons
        (piTyCodeCell unitTypeCell unitTypeCell)))

/-- The context `(g : Π(_:Π(_:Unit).Unit).Unit)` is formation-well-formed — nested Π formation
through the generic arm. -/
theorem higherOrderUnitContextWellFormed (profile : PolyProfile) :
    WfContextDesc (higherOrderUnitContext profile) :=
  WfContextDesc.cons WfContextDesc.emptyIsWellFormed
    ⟨_, _, hasTypeDesc_piFormation_viaGenArm TypingContext.empty
      (piTyCodeCell unitTypeCell unitTypeCell) unitTypeCell
      (LevelExpr.lmax LevelExpr.lzero LevelExpr.lzero) LevelExpr.lzero UniverseFlag.standard
      (hasTypeDesc_piFormation_viaGenArm TypingContext.empty
        unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
        (unitTypeCellFormationTyped TypingContext.empty)
        (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell)))
      (unitTypeCellFormationTyped
        (TypingContext.empty.cons (piTyCodeCell unitTypeCell unitTypeCell)))⟩

/-- **The β-surfacing pair, decided by the type-directed readback**: both sides read back to
`unitCell` at classifier `unitTypeCell`. -/
theorem betaSurfacingPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      betaSurfacingRedex (variableCell ⟨0, Nat.zero_lt_one⟩) :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 1) (rightFuel := 1)
    (unitVariableContextWellFormed profile)
    (betaSurfacingRedexTyped profile) (unitVariableTyped profile)
    (unitTypeCellFormationTyped (unitVariableContext profile))
    rfl

/-- **The compound-neutral pair, decided by the type-directed readback**: the classifier arrives
top-down, so the neutral needs NO spine synthesis — both sides read back to `unitCell`. -/
theorem compoundNeutralPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      (variableCell ⟨0, Nat.le.step Nat.le.refl⟩) compoundUnitNeutral :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 1) (rightFuel := 1)
    (unitFunctionContextWellFormed profile)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨0, Nat.le.step Nat.le.refl⟩))
    (compoundUnitNeutralTyped profile)
    (unitTypeCellFormationTyped (unitFunctionContext profile))
    rfl

/-- **★ The λ-argument pair (the 5th refutation), decided by the type-directed readback**:
direct form — the readback of the typed side computes to the data value itself. -/
theorem lambdaArgumentPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (higherOrderUnitContext profile)
      lambdaArgumentNeutral unitCell :=
  readbackAtClassifier_congruent 1 (higherOrderUnitContext profile) unitTypeCell
    lambdaArgumentNeutral (higherOrderUnitContextWellFormed profile)
    (lambdaArgumentNeutralTyped profile)
    (unitTypeCellFormationTyped (higherOrderUnitContext profile))

/-- **The binder-fence normal forms are identified at the Π classifier** — the readback crosses
the binder TYPE-DIRECTEDLY and both βη-normal forms compute to the η-long-at-unit form
`λ(x:Unit).unitCell`, by `rfl`. -/
theorem readback_identifiesKonstNormalFormsAtPi (profile : PolyProfile) :
    readbackAtClassifier 1 (unitVariableContext profile)
        (piTyCodeCell unitTypeCell unitTypeCell) konstAppliedToVariableNormalForm
      = readbackAtClassifier 1 (unitVariableContext profile)
          (piTyCodeCell unitTypeCell unitTypeCell) konstAppliedToUnitNormalForm := rfl

/-- **★ η-expansion computes (#360)**: the neutral `f : Π(_:Unit).Unit` reads back to the FULL
η-long form `λ(x:Unit).unitCell` — η-expansion at Π composes with the unit collapse at the
codomain, by `rfl`. -/
theorem readback_etaExpandsNeutralAtPi (profile : PolyProfile) :
    readbackAtClassifier 2 (unitFunctionContext profile)
        (piTyCodeCell unitTypeCell unitTypeCell) (variableCell ⟨1, Nat.le.refl⟩)
      = lamCell unitTypeCell unitCell := rfl

/-- **★ THE η PAIR, decided by the type-directed readback**: `f` and its η-expansion
`λx.((weaken f) x)` both read back to the η-long form — `ofReadbackEqual` at `rfl`, with the
expansion typing from `etaExpansionPreservesTypingGrown`. -/
theorem etaPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      (variableCell ⟨1, Nat.le.refl⟩)
      (RawTerm.etaLamSource unitTypeCell (variableCell ⟨1, Nat.le.refl⟩)) :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 2) (rightFuel := 2)
    (unitFunctionContextWellFormed profile)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨1, Nat.le.refl⟩))
    (HasTypeDescPi.etaExpansionPreservesTypingGrown
      (WfContextDescPi.ofWfContextDesc (unitFunctionContextWellFormed profile))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.var (unitFunctionContext profile) ⟨1, Nat.le.refl⟩)))
    (hasTypeDesc_piFormation_viaGenArm (unitFunctionContext profile)
      unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
      (unitTypeCellFormationTyped (unitFunctionContext profile))
      (unitTypeCellFormationTyped ((unitFunctionContext profile).cons unitTypeCell)))
    rfl

/-- **★ The MIXED η+unit pair, decided by the type-directed readback** — the brick-2 boundary
witness: the neutral `f` and the η-long value `λ(x:Unit).unitCell` are both βη-NORMAL and fixed
by the deep collapse (no prior procedure decides this pair), yet the readback of `f` IS the
η-long form — direct soundness, RHS by computation. -/
theorem etaUnitPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      (variableCell ⟨1, Nat.le.refl⟩) (lamCell unitTypeCell unitCell) :=
  readbackAtClassifier_congruent 2 (unitFunctionContext profile)
    (piTyCodeCell unitTypeCell unitTypeCell) (variableCell ⟨1, Nat.le.refl⟩)
    (unitFunctionContextWellFormed profile)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨1, Nat.le.refl⟩))
    (hasTypeDesc_piFormation_viaGenArm (unitFunctionContext profile)
      unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
      (unitTypeCellFormationTyped (unitFunctionContext profile))
      (unitTypeCellFormationTyped ((unitFunctionContext profile).cons unitTypeCell)))

end FX1Poly.Typed
