import FX1Poly.Typed.ValidTyping

/-! # FX1Poly/Typed/LevelingBridge
    — the leveling bridge `HasTypeDescPi → ValidTyping`, var/conv/universeFormation arms (SN-022)

`HasTypeDescPi` is LEVEL-FREE (no explicit universe-level annotations); `ValidTyping` is LEVEL-ANNOTATED
(per-binder `contextLevels : Fin scope → Nat` + a `subjectLevel : Nat`).  The leveling bridge synthesizes the
levels: `HasTypeDescPi profile context subject classifier → ∃ contextLevels subjectLevel,
ValidTyping profile contextLevels subjectLevel context subject classifier`, by induction on the derivation.
Composed with the PROVEN `ValidTyping.fundamental`, the bridge yields unconditional dependent reducibility /
SN — the route `ValidTyping`'s own docstring names as the second of its two remaining pieces (the first,
the generic `genFormationPi` arm, landed in SN-021).

This file lands the per-arm building blocks for the var / conv / universeFormation cases (SN-022); the
binder / former arms (piIntro / piElim / Π-&Σ-formation / genFormationPi) are SN-023, and the full
inductive assembly — which threads a CONSISTENT `contextLevels` across the derivation and supplies the conv
arm's coordinated sub-derivations — is the later composition step (SN-027).

## Why the var and universeFormation arms are unconditional leaves

* **var (the off-by-one dodge, SN-024).**  A variable cell with its looked-up type is `ValidTyping`-derivable
  with NO hypothesis at all: `ValidTyping.var` concludes at exactly `subjectLevel := contextLevels index` —
  the variable's own context level — so `validTypingBridgeVar` is a direct constructor application.  This is
  precisely the coordination the uniform-level recursor route (`ScratchFT/FundamentalTheoremRec.lean`'s
  blocked `ofFormation` var case) could NOT achieve: it demanded `envLevels index = predLevel + 1` for
  independently-quantified `envLevels`/`predLevel`.  Baking `subjectLevel := contextLevels index` dissolves
  the wall.

* **universeFormation (any positive level).**  A universe code `Type@e` bridges to
  `ValidTyping.universeFormation` at any `predLevel + 1` (here `predLevel := 0`), with classifier the `lsucc`
  code — again a direct constructor application, no hypothesis.

## The conv arm carries its coordinated inputs

`validTypingBridgeConv` is the conv building block: GIVEN the subject valid at `subjectLevel` and the
reclassifier valid at `subjectLevel + 1` (the tarskiDecode `+1`) under the SAME `contextLevels`, it produces
the reclassified validity.  The real work of COORDINATING the two sub-derivation bridges to a shared
`contextLevels` and to the `subjectLevel`/`subjectLevel + 1` levels is the induction step's responsibility
(deferred to the assembly, SN-027); this lemma fixes the arm's target shape.

## Zero-axiom verification

Three direct `ValidTyping` constructor applications wrapped in existentials; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Leveling-bridge var arm.**  A variable cell bridges to `ValidTyping` at its OWN context level
(`subjectLevel := contextLevels index`), unconditionally — the off-by-one-free var leg (SN-024). -/
theorem validTypingBridgeVar {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (variableCell index) (context.lookup index) :=
  ⟨_, ValidTyping.var contextLevels context index⟩

/-- **Leveling-bridge universeFormation arm.**  A universe code bridges to `ValidTyping.universeFormation`
at a positive level (here `predLevel := 0`, so `subjectLevel := 1`), with the `lsucc` classifier,
unconditionally. -/
theorem validTypingBridgeUniverseFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨_, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩

/-- **Leveling-bridge conv arm (coordinated inputs).**  Given the subject valid at `subjectLevel` and the
reclassifier valid at `subjectLevel + 1` (the tarskiDecode `+1`) under the SAME `contextLevels`, the
reclassified subject is valid (at `subjectLevel`).  The cross-sub-derivation coordination that produces these
inputs at a shared `contextLevels` is the inductive assembly's job (SN-027); this fixes the conv arm's
target shape. -/
theorem validTypingBridgeConv {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped : ValidTyping profile contextLevels (subjectLevel + 1) context
      reclassifier (universeCodeCell levelExpr flag)) :
    ∃ resultLevel : Nat,
      ValidTyping profile contextLevels resultLevel context subject reclassifier :=
  ⟨_, ValidTyping.conv contextLevels subjectLevel typed converts reclassifierTyped⟩

/-! ## Binder + former bridge arms (SN-023)

Each arm below mirrors the matching `ValidTyping` constructor's level discipline: given the sub-derivations at
exactly the levels that constructor demands (its coordinated inputs), the arm produces the former/binder cell's
validity, existentially closed over the conclusion level.  As with the conv arm, the genuinely-hard work — the
inductive ASSEMBLY that threads a CONSISTENT `contextLevels` across the whole derivation, aligns the per-IH
levels (`ValidTyping` is NOT level-weakenable: `var` pins its level at `contextLevels index`), and PRODUCES the
`∀ aboveLevel` Π/Σ-formation domain premise (SN-025, where the universe-domain all-levels obstruction lives) —
is deferred to the composition step SN-027.  These arms fix the target shapes that assembly must hit.
-/

/-- **Bridge piIntro arm.**  The λ-introduction binder: domain/codomain codes at `predLevel + 1 + 1`, body at
`predLevel + 1` under the `levelCons (predLevel + 1)`-extended level vector — exactly `ValidTyping.piIntro`'s
discipline. -/
theorem validTypingBridgePiIntro {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ValidTyping profile contextLevels (predLevel + 1 + 1) context
      domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels) (predLevel + 1 + 1)
      (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag))
    (bodyTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels) (predLevel + 1)
      (context.cons domainCode) body codomainCode) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  ⟨_, ValidTyping.piIntro contextLevels predLevel domainTyped codomainTyped bodyTyped⟩

/-- **Bridge piElim arm.**  Application: function and argument share one `subjectLevel`; the result classifier
is the codomain substituted by the argument — exactly `ValidTyping.piElim`'s discipline. -/
theorem validTypingBridgePiElim {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped : ValidTyping profile contextLevels subjectLevel context
      functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : ValidTyping profile contextLevels subjectLevel context argument domainCode) :
    ∃ resultLevel : Nat,
      ValidTyping profile contextLevels resultLevel context
        (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  ⟨_, ValidTyping.piElim contextLevels subjectLevel functionTyped argumentTyped⟩

/-- **Bridge piFormation arm.**  The Π type former: domain reducible at EVERY level (`∀ aboveLevel`, the
fuel-polymorphic type-code premise SN-025 produces during assembly), codomain at `predLevel + 1` under one
`levelCons headLevel` — exactly `ValidTyping.piFormation`'s discipline. -/
theorem validTypingBridgePiFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ∀ aboveLevel : Nat,
      ValidTyping profile contextLevels (aboveLevel + 1) context
        domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : ∀ headLevel : Nat,
      ValidTyping profile (levelCons headLevel contextLevels) (predLevel + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) :=
  ⟨_, ValidTyping.piFormation (formerLevel := formerLevel) contextLevels predLevel domainTyped codomainTyped⟩

/-- **Bridge sigmaFormation arm.**  The Σ former twin: `∀ aboveLevel` domain, single-level codomain (Σ
formation is classified by SN of the domain alone) — exactly `ValidTyping.sigmaFormation`'s discipline. -/
theorem validTypingBridgeSigmaFormation {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ∀ aboveLevel : Nat,
      ValidTyping profile contextLevels (aboveLevel + 1) context
        domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels) (predLevel + 1)
      (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) :=
  ⟨_, ValidTyping.sigmaFormation (formerLevel := formerLevel) contextLevels predLevel
    domainTyped codomainTyped⟩

/-- **Bridge genFormationPi arm.**  The GENERIC table-driven former (SN-021's ctor): any `typingRuleDescOf`
former (Π/Σ as instances) with its `DescTelescopePi` premise telescope and the `telescopeFundamental`
reducibility of its children bridges to `ValidTyping.genFormationPi` — cascade-free former coverage. -/
theorem validTypingBridgeGenFormationPi {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    (generator : Generator) (payload : generator.payload scope)
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescopePi profile (currentDepth := 0) context levels flag children)
    (telescopeFundamental :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvVec contextLevels context substitution)
        (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length),
        TelescopeReducible flag 0 levels.length substitution levels (shapeEq ▸ children)) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (.mkGen generator payload children) (rule.outputType scope levels flag) :=
  ⟨_, ValidTyping.genFormationPi contextLevels predLevel generator payload isFormation
    premises telescopeFundamental⟩

/-! ## The `∀ aboveLevel` former-domain premise (SN-025) — the keystone obstruction

`ValidTyping.piFormation`/`sigmaFormation` demand the DOMAIN at EVERY level:
`∀ aboveLevel, ValidTyping contextLevels (aboveLevel + 1) context domainCode (universeCodeCell domainLevel
flag)` — the fuel-polymorphic shape reflecting that a type CODE's membership in a universe holds at every
level (SN-001 pinned why this is exactly where the fuel-0 universe-vacuity bites).  The GO-case producer is
below; the deferred case is noted honestly.

* **GO case — universe-code domain.**  When the domain IS a universe code `Type@innerLevel`,
  `validTypingForallAboveLevelUniverseDomain` produces the premise directly, because
  `ValidTyping.universeFormation` is LEVEL-POLYMORPHIC (any `predLevel + 1`): instantiate `predLevel :=
  aboveLevel` at each level.  This is the case the universe-domain former needs and the case SN-004's GO
  verdict (the universe-DOMAIN Π closes at classifier-level semantics) underwrites.

* **DEFERRED case — type-variable / neutral domain.**  When the domain is a bare type VARIABLE (a `var i`
  whose looked-up type is a universe code), the SYNTACTIC `ValidTyping.var` PINS its level at
  `contextLevels i` — it is NOT derivable at every level — so the `∀ aboveLevel` premise is NOT produced by
  the syntactic validity ctors here.  This is the SN-001 obstruction at the syntactic layer.  It is handled
  at the REDUCIBILITY level instead, by the shipped all-levels machinery
  (`IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain`, `ReducibleEnvAtAllLevels.consTypeVariable`,
  `allLevelsReducible_piOverNeutralVariableDomain` — a type variable inhabits `Type@e` reducibly at every
  level via `IsReducibleTypeAt.universeCode`), which the full bridge assembly (SN-027) routes the
  type-variable domain through rather than through `ValidTyping.piFormation`'s syntactic domain premise.
-/

/-- **The `∀ aboveLevel` former-domain premise for a UNIVERSE-CODE domain (the GO case).**  A universe code
`Type@innerLevel` is `ValidTyping`-valid at EVERY positive level (classifier the `lsucc` code), via the
level-polymorphic `ValidTyping.universeFormation` instantiated at `predLevel := aboveLevel`.  This is exactly
the fuel-polymorphic domain premise `ValidTyping.piFormation`/`sigmaFormation` require when the former's
domain is a universe code — the case SN-004's GO verdict underwrites. -/
theorem validTypingForallAboveLevelUniverseDomain {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (innerLevel : LevelExpr) (flag : UniverseFlag) :
    ∀ aboveLevel : Nat,
      ValidTyping profile contextLevels (aboveLevel + 1) context
        (universeCodeCell innerLevel flag) (universeCodeCell innerLevel.lsucc flag) :=
  fun aboveLevel => ValidTyping.universeFormation contextLevels aboveLevel context innerLevel flag

end FX1Poly.Typed
