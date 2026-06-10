import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.IsTypeDesc
import FX1Poly.Typed.HasTypeDescContextConversion

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionValidityReduction
    — the SECOND piElim-arm reduction: to `TypeCodeValidityRespectsReduction` (GrownCtxConv-5-VALRED, toward #842)

`#1092` (GrownCtxConv-5-REASSEMBLY) reduced GrownCtxConv-5's piElim arm to `ConvContextPreservesPiValidity` via the EXACT route
(re-type the function at the *original* `Π domainCode codomainCode`).  This file gives a SECOND, independent
reduction via the FLEXIBLE route, isolating a DIFFERENT — and more standard — residual.

## The flexible-vs-exact tension (the fine-grained GrownCtxConv-5 obstruction)

A grown context-conversion bundle must, at the piElim arm, re-type the applied function under the target context
at SOME `Π`-code.  Two motives:

  * **exact** — re-type at the original `Π domainCode codomainCode`.  Closes piElim (`#1092`'s reassembly) but the
    `var` arm needs `IsType` to respect `Conv` (re-type the *source* binding `Γ[i]` under the target), which is
    FALSE (`#1058`).
  * **flexible** — re-type at any `Conv`-equal `Π`-code.  The `var` arm closes (`WfContextDescPi.lookupIsType`
    gives the *target* binding's validity directly), but the piElim arm needs the function's flexibly-transferred
    `Π`-classifier `PC'` (`Conv (Π D C) PC'`, `PC'` valid) to yield a *syntactic* `Π`-code validity — i.e.
    `PC' ⤳* Π reductD reductC` (`Conv.reducesToPiTyCode`) and then **type validity must survive that reduction**.

Both bridges (`IsType`-respects-`Conv`; validity-survives-reduction) are the SAME subject-reduction-grade fact,
which routes through the logical relation (the extrinsic `lnAtBounded` model carries no typing, so reflection is
unavailable; master SR is gated on the same `piElim` arm).  This file ships the flexible route's machinery and its
residual.

## What this ships

  * **`TypeCodeValidityRespectsReduction`** — the flexible-route residual, a single-context statement:
    `IsTypeDescPi Γ S → StepStar S T → IsTypeDescPi Γ T` (type validity survives reduction).  Strictly more
    standard than the context-conversion residual `ConvContextPreservesPiValidity` — it is "subject reduction for
    type codes" with NO context change.
  * **`HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity`** — generalizes `#1092`'s reassembly to accept a
    `Conv`-equal `Π reductDomain reductCodomain` validity (with `Conv domainCode reductDomain`,
    `Conv codomainCode reductCodomain`): re-type the function via `Conv.piTyCode_cong` + transitivity, the argument
    via the inversion domain conjunct, then `piElim`; the output classifier is `subst0 reductCodomain argument`,
    `Conv`-equal to `subst0 codomainCode argument` via `Conv.subst0`.
  * **`HasTypeDescPi.piElimArmFromValidityRespectsReduction`** — the flexible-route piElim discharge: from the
    function's FLEXIBLE classifier-transfer IH (`∃ PC', Conv (Π D C) PC' ∧ IsTypeDescPi tgt PC'`),
    `Conv.reducesToPiTyCode` exposes `PC' ⤳* Π reductD reductC`, the residual `validityRespectsReduction` yields
    `IsTypeDescPi tgt (Π reductD reductC)`, and the generalized reassembly finishes.

Together with `#1092`/`#1093` this TRIANGULATES the GrownCtxConv-5 residual: the same obstruction (re-typing a dependent
former's components across a binder change) appears as `ConvContextPreservesPiValidity` (exact),
`TypeCodeValidityRespectsReduction` (flexible), and the master-SR `genFormationPi` arm — all inter-derivable, all
discharged by the logical relation.

## Zero-axiom verification

`obtain`-destructuring + `Conv.piTyCode_cong` + `HasTypeDescPi.conv` + `inversionPiCodeComponentsUnconditional` +
`piElim` + `Conv.subst0`/`.trans`/`.sym`/`.refl` + `Conv.reducesToPiTyCode`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The flexible-route GrownCtxConv-5 residual: type validity survives reduction.**  If `subjectType` is a grown type
(`IsTypeDescPi`) and it reduces to `reductType`, then `reductType` is a grown type.  A single-context statement
("subject reduction for type codes") — more standard than the context-conversion residual
`ConvContextPreservesPiValidity` (`#1092`), and the obligation the flexible context-conversion bundle's piElim arm
needs.  Genuinely open (gated on the same master-SR `genFormationPi` arm / logical relation as the other GrownCtxConv-5
residuals — see the file header). -/
def TypeCodeValidityRespectsReduction (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subjectType reductType : RawTerm scope},
    IsTypeDescPi profile context subjectType →
    StepStar subjectType reductType →
    IsTypeDescPi profile context reductType

/-- **Generalized reassembly: a `Conv`-equal `Π`-validity suffices.**  Like
`reassembleApplicationUnderContextConversion` (`#1092`) but the target `Π`-validity may be at a `Conv`-equal
`Π reductDomain reductCodomain` (`Conv domainCode reductDomain`, `Conv codomainCode reductCodomain`).  The function
re-types at `Π reductDomain reductCodomain` (`Conv.piTyCode_cong` + transitivity through its IH conversion); the
argument re-types at `reductDomain` (the inversion domain conjunct); `piElim` produces `subst0 reductCodomain
argument`, `Conv`-equal to `subst0 codomainCode argument` by `Conv.subst0 convCodomain rfl`. -/
theorem HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity {profile : PolyProfile} {scope : Nat}
    {targetContext : TypingContext profile scope}
    {functionTerm argument domainCode reductDomain : RawTerm scope}
    {codomainCode reductCodomain : RawTerm (scope + 1)}
    (functionConverted : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        HasTypeDescPi profile targetContext functionTerm functionClassifier)
    (argumentConverted : ∃ argumentClassifier,
      Conv domainCode argumentClassifier ∧
        HasTypeDescPi profile targetContext argument argumentClassifier)
    (convDomain : Conv domainCode reductDomain)
    (convCodomain : Conv codomainCode reductCodomain)
    (piValidityTarget : IsTypeDescPi profile targetContext (piTyCodeCell reductDomain reductCodomain)) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode argument) classifier' ∧
      HasTypeDescPi profile targetContext (appCell functionTerm argument) classifier' := by
  obtain ⟨functionClassifier, convPiToFunctionClassifier, functionAtClassifier⟩ := functionConverted
  obtain ⟨argumentClassifier, convDomainToArgClassifier, argumentAtClassifier⟩ := argumentConverted
  obtain ⟨piLevel, piFlag, piTyped⟩ := piValidityTarget
  have convPiReduct : Conv (piTyCodeCell domainCode codomainCode)
      (piTyCodeCell reductDomain reductCodomain) := Conv.piTyCode_cong convDomain convCodomain
  have functionAtReduct : HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell reductDomain reductCodomain) :=
    HasTypeDescPi.conv piLevel piFlag functionAtClassifier
      (Conv.trans convPiToFunctionClassifier.sym convPiReduct) piTyped
  obtain ⟨domainLevel, _codomainLevel, flag, domainTyped, _codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  have argumentAtReduct : HasTypeDescPi profile targetContext argument reductDomain :=
    HasTypeDescPi.conv domainLevel flag argumentAtClassifier
      (Conv.trans convDomainToArgClassifier.sym convDomain) domainTyped
  exact ⟨RawTerm.subst0 reductCodomain argument,
    Conv.subst0 convCodomain (Conv.refl argument),
    HasTypeDescPi.piElim functionAtReduct argumentAtReduct⟩

/-- **The flexible-route piElim discharge.**  Under the residual `TypeCodeValidityRespectsReduction`, the grown
context-conversion piElim arm follows from the function's FLEXIBLE classifier-transfer IH (`∃ PC',
Conv (Π domainCode codomainCode) PC' ∧ IsTypeDescPi targetContext PC'`) together with the convContext term IHs:
`Conv.reducesToPiTyCode` exposes `PC' ⤳* Π reductDomain reductCodomain`, the residual yields `IsTypeDescPi
targetContext (Π reductDomain reductCodomain)`, and `reassembleApplicationFromConvEqualPiValidity` rebuilds the
application.  The flexible twin of `piElimArmFromPiValidityTransfer` (`#1092`). -/
theorem HasTypeDescPi.piElimArmFromValidityRespectsReduction {profile : PolyProfile}
    (validityRespectsReduction : TypeCodeValidityRespectsReduction profile)
    {scope : Nat} {targetContext : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionFlexible : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        IsTypeDescPi profile targetContext functionClassifier)
    (functionConverted : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        HasTypeDescPi profile targetContext functionTerm functionClassifier)
    (argumentConverted : ∃ argumentClassifier,
      Conv domainCode argumentClassifier ∧
        HasTypeDescPi profile targetContext argument argumentClassifier) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode argument) classifier' ∧
      HasTypeDescPi profile targetContext (appCell functionTerm argument) classifier' := by
  obtain ⟨flexClassifier, convPiToFlex, flexValid⟩ := functionFlexible
  obtain ⟨reductDomain, reductCodomain, flexReducesToPi, convDomainReduct, convCodomainReduct⟩ :=
    Conv.reducesToPiTyCode convPiToFlex.sym
  have piReductValid : IsTypeDescPi profile targetContext
      (piTyCodeCell reductDomain reductCodomain) :=
    validityRespectsReduction flexValid flexReducesToPi
  exact HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity functionConverted argumentConverted
    convDomainReduct convCodomainReduct piReductValid

/-! ## The formation base of the residual (UNCONDITIONAL)

`TypeCodeValidityRespectsReduction` is genuinely open for the GROWN engine (the type-level-computation
fragment).  But the FORMATION engine satisfies it UNCONDITIONALLY — because the formation subject reduction
`HasTypeDesc.subjectReduction` PRESERVES the classifier and is itself unconditional (its telescope arm re-types a
former's codomain under a stepped domain binder via the UNCONDITIONAL formation context-conversion
`convTelescope` — exactly the move the grown engine cannot make, which is why GrownCtxConv-5 is open).  So validity
survives reduction for free on the formation-typed fragment, precisely localizing the genuinely-open residual to
the genuinely-grown (type-level-computing) type codes. -/

/-- **Formation validity survives reduction — UNCONDITIONALLY.**  If `subjectType` is a formation type
(`IsTypeDesc`) and it reduces to `reductType`, then `reductType` is a formation type.  `HasTypeDesc.subjectReduction`
preserves the universe classifier at each step, iterated along the `StepStar` chain. -/
theorem IsTypeDesc.respectsReductionStar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subjectType reductType : RawTerm scope}
    (isType : IsTypeDesc profile context subjectType)
    (reduces : StepStar subjectType reductType) :
    IsTypeDesc profile context reductType := by
  induction reduces with
  | refl _ => exact isType
  | trans firstStep _restChain restIH =>
      obtain ⟨levelExpr, flag, subjectTyped⟩ := isType
      exact restIH ⟨levelExpr, flag, HasTypeDesc.subjectReduction subjectTyped _ firstStep⟩

/-- **The grown corollary: `TypeCodeValidityRespectsReduction` for formation-typed subjects.**  A formation-typed
type code that reduces stays GROWN-valid (`IsTypeDescPi`): `IsTypeDesc.respectsReductionStar` re-types the reduct
in the formation engine, then `ofFormation` lifts it to the grown engine.  This discharges the grown residual on
the formation fragment; only the genuinely-grown (type-level-computing) type codes remain — the logical-relation
obligation. -/
theorem HasTypeDescPi.validityRespectsReductionOfFormation {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subjectType reductType : RawTerm scope}
    (isType : IsTypeDesc profile context subjectType)
    (reduces : StepStar subjectType reductType) :
    IsTypeDescPi profile context reductType := by
  obtain ⟨levelExpr, flag, reductTyped⟩ := IsTypeDesc.respectsReductionStar isType reduces
  exact ⟨levelExpr, flag, HasTypeDescPi.ofFormation reductTyped⟩

/-- **The formation/grown boundary, named: codomain re-typing under a stepped domain binder is UNCONDITIONAL
for FORMATION codomains.**  If a codomain is a formation type under `context.cons domain` and the `domain`
steps to `domainReduct`, then the codomain is a formation type under `context.cons domainReduct`, at the SAME
universe classifier.  Proof: the single domain `Step` induces a `Conv domain domainReduct` (`Conv.fromStepStar`),
hence a pointwise context-conversion condition (`convContextCondition_consStep`), and the UNCONDITIONAL formation
context-conversion `HasTypeDesc.convContext` re-types the codomain (conv-backed to the same universe code via
`convBackToUniverseCode`).

This is the formation analogue of the grown `codomainReTyping` (GrownCtxConv-6, `#843`) — but UNCONDITIONAL, where the
grown one is gated on GrownCtxConv-5 (`#842`).  It IS the precise move the formation telescope subject reduction makes
internally, and it is EXACTLY the operation the grown engine cannot perform for genuinely-grown
(type-level-computing) codomains: that single asymmetry — formation context-conversion is unconditional, grown is
not — is the entire content of why GrownCtxConv-5 / the master-SR `genFormationPi` arm / `TypeCodeValidityRespectsReduction`
remain open and require the FX logical relation. Named here so the boundary is a citable presupposition. -/
theorem HasTypeDesc.codomainReTypingOfFormationStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {domain domainReduct : RawTerm scope}
    {codomain : RawTerm (scope + 1)} {level : LevelExpr} {flag : UniverseFlag}
    (codomainTyped : HasTypeDesc profile (context.cons domain) codomain
      (universeCodeCell level flag))
    (domainStep : Step domain domainReduct) :
    HasTypeDesc profile (context.cons domainReduct) codomain (universeCodeCell level flag) := by
  obtain ⟨reachedClassifier, convToReached, codomainUnderReduct⟩ :=
    HasTypeDesc.convContext codomainTyped (context.cons domainReduct)
      (convContextCondition_consStep
        (Conv.fromStepStar (StepStar.trans domainStep (StepStar.refl _))))
  exact codomainUnderReduct.convBackToUniverseCode convToReached

/-! ## The head-β extension of the unconditional fragment

`validityRespectsReductionOfFormation` (#1095) discharges `TypeCodeValidityRespectsReduction` for FORMATION-typed
subjects (`IsTypeDesc`).  A β-redex type code `(λ.body) arg` is NOT formation-typed (the formation engine types
neither `λ` nor application — those are the grown `piIntro` / `piElim` rules), so it lies OUTSIDE that fragment.
The shipped `HasTypeDescPi.betaSubjectReduction` (unconditional mod `WfContextDescPi`) discharges exactly this
HEAD-β case, extending the unconditionally-discharged fragment from "formation-typed" to "formation-typed OR
head-β-redex" type codes.

This is the precise unconditional boundary of the residual: a grown type code's only HEAD redex is β (the engine
types no type-level eliminators — a grown type code heads as a formation code, a `Π`-code, or an application), and
head-β is now discharged.  Everything still open is CONGRUENCE into a child — a former's codomain re-typed across a
stepped domain binder, or an argument reduced in a dependent position — i.e. exactly the grown context-conversion
`piElim` arm (`#842`) / the FX logical relation, per this file's header. -/

/-- **Grown head-β validity survives reduction — UNCONDITIONALLY (mod `WfContextDescPi`).**  A β-redex type code's
validity survives the contraction.  The grown head-computation companion to `validityRespectsReductionOfFormation`
(`#1095`, the formation fragment): a direct wrap of the shipped `HasTypeDescPi.betaSubjectReduction`, which re-types
the contractum at the redex's classifier via the substitution lemma + `classifierIsTypeDescPi`, no logical relation
needed.  Together with `#1095` this is the full UNCONDITIONAL fragment of `TypeCodeValidityRespectsReduction`; the
genuinely-open remainder is congruence into a type-level-computing child. -/
theorem HasTypeDescPi.validityRespectsBetaRedex {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    (isType : IsTypeDescPi profile context (appCell (lamCell domainAnn body) argument))
    (wellFormed : WfContextDescPi context) :
    IsTypeDescPi profile context (RawTerm.subst0 body argument) := by
  obtain ⟨level, flag, redexTyped⟩ := isType
  exact ⟨level, flag, HasTypeDescPi.betaSubjectReduction redexTyped wellFormed⟩

end FX1Poly.Typed
