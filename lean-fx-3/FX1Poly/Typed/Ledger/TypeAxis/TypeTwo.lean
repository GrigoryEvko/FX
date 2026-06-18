import FX1Poly.Typed.Engine.HasTypeDescPi.Formation.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiBetaSR
import FX1Poly.Typed.Metatheory.Canonicity.Forms.GrownCanonicalFormsByClassifier
import FX1Poly.Typed.Engine.HasTypeDescPi.Eta.HasTypeDescPiEtaExpansionGrown
import FX1Poly.Typed.Metatheory.Universe.TypedUniverseNoTop
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleUniverseDecode

/-! # type-2 — the MIDDLE rung: display + Π classifier, the basic right adjoint, the Tarski roundtrip

The middle content rung of the type axis: the RIGHT-adjoint dual to `type-1`'s LEFT/Σ — the dependent
FUNCTION (Π) type former — together with the UNIVERSE CLASSIFIER (`Type@e` classifies the types at level e)
and the TARSKI ROUNDTRIP (decode / encode of codes against types).  Like `type-1`, this is a NON-DUPLICATIVE
cross-layer ledger ABOVE Typed (a `Tier0/Type` file cannot cite the Typed/Core substrate — import cycle):
marker + `_isBacked` referencing named shipped theorems.

## What this rung backs (each `= true`, conjoined with named shipped theorems)

  * **`fxType_hasDependentFunctionFormation`** — Π FORMATION: `Π domain. codomain : Type@(u ⊔ v)` from a
    domain `: Type@u` and codomain `: Type@v` under the domain binder (`HasTypeDescPi.piFormationViaGenArm`,
    the exact dual of `type-1`'s `sigmaFormationViaGenArm`).
  * **`fxType_hasFunctionDynamics`** — the dependent function COMPUTES and is CANONICAL: β SUBJECT REDUCTION
    (`HasTypeDescPi.betaSubjectReduction` — `(λ.body) arg` and `body[arg]` type at the same classifier), Π
    CANONICITY (`HasTypeDescPi.closedNormalFunctionIsLambda` — a closed normal term at a Π code IS a λ), and
    η EXPANSION preserving typing (`HasTypeDescPi.etaExpansionPreservesTypingGrown`).
  * **`fxType_hasUniverseClassifier`** — the universe is a genuine CLASSIFIER: a universe code's classifier is
    rigidly its successor (`universeCodeClassifierIsSuccessor`), unique up to conversion
    (`universeCodeClassifierUnique`), and the tower has NO TOP (`universeHierarchyHasNoTop` — predicative, the
    antithesis of `Type : Type`).
  * **`fxType_hasTarskiRoundtrip`** — the Tarski code/type roundtrip: DECODE (a member of `Type@(e+1)` is a
    reducible type at `e`, `tarskiDecode`), ENCODE (an SN reducible type at `e` inhabits `Type@(e+1)`,
    `tarskiEncode`), and their packaged CHARACTERIZATION (`universeMembership_iff` — `Type@(e+1)` is PRECISELY
    the SN reducible types at `e`).

## What is deferred

  * `fxType_hasFibredFunctionRightAdjoint` — Π as the fibred RIGHT ADJOINT to reindexing (the categorical
    universal property).  `fxComprehensionCategory_hasFibredPiRightAdjoint = false` / LCC local exponentials
    `= false` — needs `context-16` (democracy + LCC), cross-axis `×type` / `fib-1`.  `= false`.
  * `fxType_hasDisplayMapClassifier` — the display-map-as-classifier UNIVERSAL PROPERTY at the type level.
    The shipped split display fibration with its cartesian-lift universal property is CONTEXT-side
    (`fxDisplaySplitFibration` / `FxComprehensionCategory`); gluing it to the type display is `fib-1`.
    `= false`.
  * `fxType_hasTarskiRoundtripInverse` — a genuine decode/encode MUTUAL-INVERSE `Equiv`.  Only the membership
    biconditional ships (the relation is `Prop`-valued, so the iff is the complete statement); a propositional
    inverse pair is the `type-20` Tarski↔Russell-coherence frontier.  `= false`.

## Zero-axiom verification

Four `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + named shipped theorems) and
three `:= false` deferral markers.  Gating this file's `_isBacked` theorems transitively certifies the cited
Core Tarski theorems (`tarskiDecode` / `tarskiEncode` / `universeMembership_iff`) zero-axiom even though they
carry no individual gate of their own.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TypeTwo.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core
open FX1Poly.Core.StepStar
open FX1Poly.Typed
open FX1Poly.Universe

/-! ## Dependent function (Π) formation -/

/-- **Honesty marker** — `type-2` (dependent Π formation).  The dependent function type former
`Π domain. codomain` FORMS at the join level `u ⊔ v` — the RIGHT-adjoint dual to `type-1`'s Σ.  Backed in
`fxType_dependentFunctionFormation_isBacked`.  `= true`. -/
def fxType_hasDependentFunctionFormation : Bool := true

/-- ★ **Backed flip (Π formation).**  The marker is `true` AND `Π domain. codomain` types at `Type@(u ⊔ v)`
whenever the domain types at `Type@u` and the codomain types at `Type@v` under the domain binder
(`HasTypeDescPi.piFormationViaGenArm`). -/
theorem fxType_dependentFunctionFormation_isBacked :
    fxType_hasDependentFunctionFormation = true
      ∧ (∀ {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
          (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
          (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
          HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) →
          HasTypeDescPi profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) →
          HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
            (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)) := by
  refine ⟨rfl, ?_⟩
  intro profile scope context domainCode codomainCode domainLevel codomainLevel flag
    domainTyped codomainTyped
  exact HasTypeDescPi.piFormationViaGenArm context domainCode codomainCode
    domainLevel codomainLevel flag domainTyped codomainTyped

/-! ## Function dynamics — β subject reduction, canonicity, η -/

/-- **Honesty marker** — `type-2` (function dynamics).  The dependent function COMPUTES and is CANONICAL: β
subject reduction, Π canonicity (closed normal = λ), and η expansion preserve/produce typing.  Backed in
`fxType_functionDynamics_isBacked`.  `= true`. -/
def fxType_hasFunctionDynamics : Bool := true

/-- ★ **Backed flip (function dynamics).**  The marker is `true` AND (i) β SUBJECT REDUCTION
(`HasTypeDescPi.betaSubjectReduction`); (ii) Π CANONICITY — a closed normal term at a Π code is a λ
(`HasTypeDescPi.closedNormalFunctionIsLambda`); (iii) η EXPANSION preserves typing
(`HasTypeDescPi.etaExpansionPreservesTypingGrown`). -/
theorem fxType_functionDynamics_isBacked :
    fxType_hasFunctionDynamics = true
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {argument classifier : RawTerm scope},
          HasTypeDescPi profile context (appCell (lamCell domainAnn body) argument) classifier →
          WfContextDescPi context →
          HasTypeDescPi profile context (RawTerm.subst0 body argument) classifier)
      ∧ (∀ {profile : PolyProfile} {subject : RawTerm 0}
          {outerDomain : RawTerm 0} {outerCodomain : RawTerm 1},
          HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
            (piTyCodeCell outerDomain outerCodomain) →
          RawTerm.isStepNormalForm subject →
          ∃ (domainAnn : RawTerm 0) (body : RawTerm 1), subject = lamCell domainAnn body)
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
          WfContextDescPi context →
          HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode) →
          HasTypeDescPi profile context (RawTerm.etaLamSource domainCode functionTerm)
            (piTyCodeCell domainCode codomainCode)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro profile scope context domainAnn body argument classifier redexTyped wellFormed
    exact HasTypeDescPi.betaSubjectReduction redexTyped wellFormed
  · intro profile subject outerDomain outerCodomain typed normal
    exact HasTypeDescPi.closedNormalFunctionIsLambda typed normal
  · intro profile scope context functionTerm domainCode codomainCode wellFormed functionTyped
    exact HasTypeDescPi.etaExpansionPreservesTypingGrown wellFormed functionTyped

/-! ## The universe classifier -/

/-- **Honesty marker** — `type-2` (universe classifier).  The universe code is a genuine classifier: its
classifier is rigidly its successor, unique up to conversion, and the tower has no top (predicative).  Backed
in `fxType_universeClassifier_isBacked`.  `= true`. -/
def fxType_hasUniverseClassifier : Bool := true

/-- ★ **Backed flip (universe classifier).**  The marker is `true` AND (i) a universe code's classifier is its
successor (`universeCodeClassifierIsSuccessor`); (ii) classifiers are unique up to `Conv`
(`universeCodeClassifierUnique`); (iii) the hierarchy has no top (`universeHierarchyHasNoTop`). -/
theorem fxType_universeClassifier_isBacked :
    fxType_hasUniverseClassifier = true
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag},
          HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag)
            (universeCodeCell classifierLevel classifierFlag) →
          classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag)
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag}
          {classifierLeft classifierRight : RawTerm scope},
          HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag) classifierLeft →
          HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag) classifierRight →
          Conv classifierLeft classifierRight)
      ∧ (∀ {profile : PolyProfile} (flag : UniverseFlag),
          ¬ ∃ topClassifier : RawTerm 0,
            ∀ n : Nat, HasTypeDescPi profile TypingContext.empty (universeLevelTower flag n) topClassifier) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro profile scope context subjectLevel classifierLevel subjectFlag classifierFlag typed
    exact universeCodeClassifierIsSuccessor typed
  · intro profile scope context subjectLevel subjectFlag classifierLeft classifierRight typedLeft typedRight
    exact universeCodeClassifierUnique typedLeft typedRight
  · intro profile flag
    exact universeHierarchyHasNoTop flag

/-! ## The Tarski roundtrip (decode / encode) -/

/-- **Honesty marker** — `type-2` (Tarski roundtrip).  Codes decode to types and SN reducible types encode to
universe members, packaged as the universe-membership characterization.  Backed in
`fxType_tarskiRoundtrip_isBacked`.  `= true`.  The full decode/encode mutual-inverse `Equiv` is deferred
(`fxType_hasTarskiRoundtripInverse`). -/
def fxType_hasTarskiRoundtrip : Bool := true

/-- ★ **Backed flip (Tarski roundtrip).**  The marker is `true` AND (i) DECODE (`tarskiDecode` — a member of
`Type@(e+1)` is a reducible type at `e`); (ii) ENCODE (`tarskiEncode` — an SN reducible type at `e` inhabits
`Type@(e+1)`); (iii) the membership CHARACTERIZATION (`universeMembership_iff`). -/
theorem fxType_tarskiRoundtrip_isBacked :
    fxType_hasTarskiRoundtrip = true
      ∧ (∀ {scope : Nat} {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
          {typeCode : RawTerm scope},
          IsReducibleMemberAt (predLevel + 1)
            (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode →
          IsReducibleTypeAt predLevel typeCode)
      ∧ (∀ {scope : Nat} {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
          {typeCode : RawTerm scope},
          IsStronglyNormalizing typeCode → IsReducibleTypeAt predLevel typeCode →
          IsReducibleMemberAt (predLevel + 1)
            (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode)
      ∧ (∀ {scope : Nat} {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
          {typeCode : RawTerm scope},
          IsReducibleMemberAt (predLevel + 1)
              (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode ↔
            IsStronglyNormalizing typeCode ∧ IsReducibleTypeAt predLevel typeCode) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro scope predLevel levelExpr flag typeCode member
    exact IsReducibleMemberAt.tarskiDecode member
  · intro scope predLevel levelExpr flag typeCode stronglyNormalizing typeReducible
    exact IsReducibleMemberAt.tarskiEncode stronglyNormalizing typeReducible
  · intro scope predLevel levelExpr flag typeCode
    exact IsReducibleMemberAt.universeMembership_iff

/-! ## Honesty markers (the deferred MIDDLE frontier) -/

/-- **Honesty marker.**  Π as the fibred RIGHT ADJOINT to reindexing (the categorical universal property) —
`fxComprehensionCategory_hasFibredPiRightAdjoint = false` / LCC local exponentials `= false`, needs
`context-16` (democracy + LCC), cross-axis `×type` / `fib-1`, deferred.  `= false`. -/
def fxType_hasFibredFunctionRightAdjoint : Bool := false

/-- **Honesty marker.**  The display-map-as-classifier UNIVERSAL PROPERTY at the type level — the shipped
split display fibration + cartesian-lift universal property is CONTEXT-side (`fxDisplaySplitFibration`);
gluing it to the type display is `fib-1`, deferred.  `= false`. -/
def fxType_hasDisplayMapClassifier : Bool := false

/-- **Honesty marker.**  A genuine decode/encode MUTUAL-INVERSE `Equiv` — only the membership biconditional
ships (the relation is `Prop`-valued); the propositional inverse pair is the `type-20`
Tarski↔Russell-coherence frontier, deferred.  `= false`. -/
def fxType_hasTarskiRoundtripInverse : Bool := false

end FX1Poly.Tier0
