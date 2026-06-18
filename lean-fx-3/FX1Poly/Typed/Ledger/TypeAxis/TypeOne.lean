import FX1Poly.Typed.Engine.HasTypeDescPi.Formation.HasTypeDescPiFormerCongruence
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleUniverseDecode
import FX1Poly.Tier0.Term.Action.InitialAlgebra

/-! # type-1 — the LEFT / initial structure of the type axis: Σ + inductive types as initial algebras

The first content rung of the type axis (the LEFT / initial side, dual to `type-3`'s RIGHT / terminal
coalgebra).  Where `type-0` (`Tier0/Type/TypeAxis.lean`) is the pure-SYNTAX design-lock (codes / levels /
flags), the type-axis METATHEORY genuinely lives across `Tier0/Term` (the initial-algebra universal
property), `Core/` (the reducibility membership of data formers) and `Typed/` (the dependent-Σ formation
typing).  Since `Typed/` and `Core/` import `Tier0/Type`, a Tier0/Type file cannot cite them (import cycle) —
so this ledger sits ABOVE Typed and certifies the already-shipped LEFT/initial substrate as a
NON-DUPLICATIVE ledger (marker + `_isBacked` referencing named shipped theorems), per the type-axis
double-check discipline.

## What this rung backs (each `= true`, conjoined with a named shipped theorem)

  * **`fxType_hasDependentSumFormation`** — dependent Σ FORMATION: from a domain code `: Type@u` and a
    codomain code `: Type@v` UNDER the domain binder, `Σ domain. codomain : Type@(u ⊔ v)`
    (`HasTypeDescPi.sigmaFormationViaGenArm`, via the generic `genFormationPi` arm + `typingRuleDescOf`
    sigma row).  The genuine dependent (binder-shape) Σ type-former, distinct from the non-dependent product.
  * **`fxType_hasInitialAlgebra`** — the INITIAL-ALGEBRA universal property: any homomorphism out of the
    signature algebra agrees with the catamorphism — INITIALITY (`IsCarrierHomomorphism.unique`, shipped at
    the signature level as `term-1`).  "Constructors = initial algebra"; the LEFT / free-functor universal
    property, re-exposed as the type axis's initial structure.
  * **`fxType_hasDataFormerReducibility`** — data type formers inhabit a universe in the Tarski reducibility
    model (`IsReducibleMemberAt.unitFormerInUniverse`, the nullary instance of the generic
    `dataFormerInUniverse` route): `Unit : Type@(succ ·)` semantically.

## What is deferred (the genuine type-level LEFT frontier)

  * `fxType_hasDependentSumElimination` — dependent Σ INTRODUCTION + ELIMINATION TYPING.  The grown engine
    PROVES `pairCellHasNoTyping` / `fstCellHasNoTyping` / `sndCellHasNoTyping`; the only typed pair/projection
    judgments (`HasTypeUnion.nonDependentBinaryIntro` / `projectionElim`) are at the NON-dependent
    `productTypeCell` (second component cannot depend on the first).  The dependent eliminator ships at the
    display-map fibration — `Core/`, glued `×type` / `fib-1`.  `= false`.
  * `fxType_hasInductiveTypeObjectInitiality` — an individual OBJECT inductive type (Nat) as an initial
    F-algebra / colimit AT THE TYPE LEVEL.  The shipped initiality is signature-level (`term-1`); the
    per-object-type universal property is the new `type-1` frontier.  `= false`.
  * `fxType_hasWTypes` — W-types (`type-4` / EXT-1) are demo iota rows only (`wStyleRecursiveBinderDemoRule`),
    no typed W-former.  `= false`.

## Zero-axiom verification

Three `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + a named shipped theorem:
`HasTypeDescPi.sigmaFormationViaGenArm`, `IsCarrierHomomorphism.unique`,
`IsReducibleMemberAt.unitFormerInUniverse`) and three `:= false` deferral markers.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTier0TypeOne.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core
open FX1Poly.Typed
open FX1Poly.Universe

/-! ## Dependent Σ formation -/

/-- **Honesty marker** — `type-1` (dependent Σ formation).  The dependent sum type former `Σ domain.
codomain` (binder-shape `sigmaTyCodeCell`) FORMS at the join level `u ⊔ v`.  Backed in
`fxType_dependentSumFormation_isBacked`.  `= true`. -/
def fxType_hasDependentSumFormation : Bool := true

/-- ★ **Backed flip (dependent Σ formation).**  The marker is `true` AND `Σ domain. codomain` types at
`Type@(u ⊔ v)` whenever the domain types at `Type@u` and the codomain types at `Type@v` under the domain
binder (`HasTypeDescPi.sigmaFormationViaGenArm`). -/
theorem fxType_dependentSumFormation_isBacked :
    fxType_hasDependentSumFormation = true
      ∧ (∀ {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
          (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
          (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
          HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) →
          HasTypeDescPi profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) →
          HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
            (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)) := by
  refine ⟨rfl, ?_⟩
  intro profile scope context domainCode codomainCode domainLevel codomainLevel flag
    domainTyped codomainTyped
  exact HasTypeDescPi.sigmaFormationViaGenArm context domainCode codomainCode
    domainLevel codomainLevel flag domainTyped codomainTyped

/-! ## The initial-algebra universal property -/

/-- **Honesty marker** — `type-1` (inductive types = initial algebra).  The INITIAL-ALGEBRA universal
property: the catamorphism is the unique homomorphism out of the signature algebra (`term-1`'s
`IsCarrierHomomorphism.unique`).  Backed in `fxType_initialAlgebra_isBacked`.  `= true`. -/
def fxType_hasInitialAlgebra : Bool := true

/-- ★ **Backed flip (initial algebra).**  The marker is `true` AND any carrier homomorphism agrees with the
catamorphism — INITIALITY (`IsCarrierHomomorphism.unique`). -/
theorem fxType_initialAlgebra_isBacked :
    fxType_hasInitialAlgebra = true
      ∧ (∀ {C : Nat → Type} {algebra : CarrierAlgebra C}
          (homomorphism : IsCarrierHomomorphism algebra) {scope : Nat} (term : RawTerm scope),
          homomorphism.map term = cata algebra term) := by
  refine ⟨rfl, ?_⟩
  intro C algebra homomorphism scope term
  exact homomorphism.unique term

/-! ## Data-former reducibility (the Tarski membership) -/

/-- **Honesty marker** — `type-1` (data-former reducibility).  A data type former inhabits a universe in the
Tarski reducibility model (`Unit : Type@(succ ·)` semantically; the nullary instance of the generic
`dataFormerInUniverse` route).  Backed in `fxType_dataFormerReducibility_isBacked`.  `= true`. -/
def fxType_hasDataFormerReducibility : Bool := true

/-- ★ **Backed flip (data-former reducibility).**  The marker is `true` AND the unit type former is a
reducible member of any universe code (`IsReducibleMemberAt.unitFormerInUniverse`). -/
theorem fxType_dataFormerReducibility_isBacked :
    fxType_hasDataFormerReducibility = true
      ∧ (∀ {scope : Nat} {predLevel : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag),
          IsReducibleMemberAt (predLevel + 1)
            (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
            (.mkGen .gen_unitCode () .childNil : RawTerm scope)) := by
  refine ⟨rfl, ?_⟩
  intro scope predLevel levelExpr flag
  exact IsReducibleMemberAt.unitFormerInUniverse levelExpr flag

/-! ## Honesty markers (the deferred type-level LEFT frontier) -/

/-- **Honesty marker.**  Dependent Σ INTRODUCTION + ELIMINATION TYPING — the grown engine proves
`pairCellHasNoTyping` / `fstCellHasNoTyping` / `sndCellHasNoTyping`; the only typed pair/projection judgments
are the NON-dependent product (`HasTypeUnion.nonDependentBinaryIntro` / `projectionElim`).  The dependent
eliminator ships at the display fibration (`Core/`, `×type` / `fib-1`), deferred.  `= false`. -/
def fxType_hasDependentSumElimination : Bool := false

/-- **Honesty marker.**  An individual OBJECT inductive type (e.g. Nat) as an initial F-algebra / colimit AT
THE TYPE LEVEL — the shipped initiality is signature-level (`term-1`); the per-object universal property is
the new frontier, deferred.  `= false`. -/
def fxType_hasInductiveTypeObjectInitiality : Bool := false

/-- **Honesty marker.**  W-TYPES (`type-4` / EXT-1) — demo iota rows only (`wStyleRecursiveBinderDemoRule`),
no typed W-former, deferred.  `= false`. -/
def fxType_hasWTypes : Bool := false

end FX1Poly.Tier0
