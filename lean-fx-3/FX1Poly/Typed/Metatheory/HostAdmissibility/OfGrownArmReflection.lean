import FX1Poly.Typed.Metatheory.HostAdmissibility.HostEngineNativeOnlyReflection
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/Metatheory/HostAdmissibility/OfGrownArmReflection — the retired `ofGrown` arm reflects to the native kernel judgment (Retirement Brick 1)

The historic `HasTypeUnionOver.ofGrown` arm embedded a GROWN host derivation
(`HasTypeDescPi profile context subject classifier`) into the union judgment as an escape hatch.
This file packages the standing total host→native reflections
(`HasTypeDescPi.toNativeOnly` / `HasTypeDesc.toNativeOnly`, over the `ofGrown`-free
`HasTypeUnionNativeOnly`) with the native-only embedding (`HasTypeUnionNativeOnly.toUnion`) into a
single named capstone: EVERY grown host derivation is reproducible as a KERNEL `HasTypeUnion`
derivation built purely from the six native arms.

That is exactly the conclusion the retired `ofGrown` constructor produced —
`HasTypeDescPi profile context subject classifier → HasTypeUnion profile context subject classifier`
— now derived WITHOUT any `ofGrown`.  So the arm carried no classifying power the native arms lack:
this is the ADMISSIBILITY witness that unblocks re-homing the `ofGrown` consumers (they call
`ofGrownReflected` instead) and, in a later green-lit brick, deleting the grown engine.  The grown
engine (`HasTypeDescPi` / `HasTypeDesc`) is retained UNTOUCHED as the cross-check oracle — this file
is purely additive.

## Per-arm coverage

`OfGrownArmReflectionCoverage` records one field per grown arm — `ofFormation`, `conv`, `piIntro`
(λ), `piElim` (app), `genFormationPi` — each asserting that the arm's constructor, applied to
arbitrary grown premises, reflects to a native `HasTypeUnion` derivation.  Its witness
`ofGrownArmReflectionCoverageWitness` inhabits every field by BUILDING the arm and reflecting, so the
per-arm totality is exercised (constructed, not merely declared) and cannot silently regress.  Mirrors
the sibling gate `NativeUnionInversionCoverage`.

The only side condition is `context.isLockFreeContext = true` — the Fitch A1-RESTRICT
lock-accessibility discharge threaded by the underlying reflections, vacuous on the lock-free kernel.

## Zero-axiom

Composition of the shipped totals (`toNativeOnly` ∘ `toUnion`) plus grown-arm constructor
applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in
`FX1PolyAudit/Typed/Metatheory/HostAdmissibility/OfGrownArmReflection.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-! ## The headline capstone: the retired `ofGrown` conclusion, native -/

/-- **★ Every grown host derivation reflects to the native kernel judgment (the retired `ofGrown` arm,
admissible).**  The composition `HasTypeDescPi.toNativeOnly` (host → `ofGrown`-free
`HasTypeUnionNativeOnly`) with `HasTypeUnionNativeOnly.toUnion` (native-only ↪ kernel `HasTypeUnion`)
carries any grown `HasTypeDescPi` derivation to a KERNEL `HasTypeUnion` derivation with no `ofGrown`
anywhere in its tree.  This IS the conclusion the retired `HasTypeUnionOver.ofGrown` constructor
produced, now derived from the six native arms alone — so `ofGrown` was information-free over the
native table, and its consumers can re-home onto this lemma.  Needs only lock-freeness of the
context (vacuous on the lock-free kernel). -/
theorem HasTypeDescPi.ofGrownReflected {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeUnion profile context subject classifier :=
  (derivation.toNativeOnly contextLockFree).toUnion

/-- The formation-leg analogue: a FORMATION `HasTypeDesc` derivation reflects to the native kernel
judgment.  (`HasTypeDescPi.ofFormation` embeds this into the grown engine, so `ofGrownReflected`
already covers it; this names the formation-only route directly.) -/
theorem HasTypeDesc.ofGrownFormationReflected {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeUnion profile context subject classifier :=
  (derivation.toNativeOnly contextLockFree).toUnion

/-! ## The per-arm coverage gate -/

/-- **The `ofGrown`-arm reflection coverage record.**  One field per grown `HasTypeDescPi` arm; each
field asserts that the arm's constructor, over arbitrary premises, produces a subject reflectable to
the native kernel judgment `HasTypeUnion`.  An inhabitant certifies the reflection is TOTAL per grown
arm — no arm is silently unhandled — mirroring the sibling `NativeUnionInversionCoverage` gate. -/
structure OfGrownArmReflectionCoverage (profile : PolyProfile) : Prop where
  /-- The embedded FORMATION arm (`ofFormation`) reflects. -/
  ofFormationReflects : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDesc profile context subject classifier →
    context.isLockFreeContext = true →
    HasTypeUnion profile context subject classifier
  /-- The grown conversion arm (`conv`) reflects. -/
  convReflects : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile context subject classifier →
    Conv classifier reclassifier →
    HasTypeDescPi profile context reclassifier (universeCodeCell levelExpr flag) →
    context.isLockFreeContext = true →
    HasTypeUnion profile context subject reclassifier
  /-- The Π-introduction arm (`piIntro` / λ) reflects to the native `intro`@`gen_lam` derivation. -/
  piIntroReflects : ∀ {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) →
    HasTypeDescPi profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag) →
    HasTypeDescPi profile (context.cons domainCode) body codomainCode →
    context.isLockFreeContext = true →
    HasTypeUnion profile context (lamCell domainCode body)
      (piTyCodeCell domainCode codomainCode)
  /-- The Π-elimination arm (`piElim` / app) reflects to the native `elim`@`gen_app` derivation. -/
  piElimReflects : ∀ {scope : Nat} {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
    HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile context argument domainCode →
    context.isLockFreeContext = true →
    HasTypeUnion profile context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument)
  /-- The generic type-former formation arm (`genFormationPi`) reflects to the native `formationRule`
  derivation at the cumulative row. -/
  genFormationPiReflects : ∀ {scope : Nat} (context : TypingContext profile scope)
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc),
    typingRuleDescOf generator = some rule →
    DescTelescopePi profile (currentDepth := 0) context levels flag children →
    context.isLockFreeContext = true →
    HasTypeUnion profile context (.mkGen generator payload children)
      (rule.outputType scope levels flag)

/-- **★ The `ofGrown`-arm reflection coverage gate** — inhabited by BUILDING each grown arm and
reflecting it through `ofGrownReflected`, so every grown arm is witnessed reflectable to the native
kernel judgment and the per-arm totality cannot silently shrink. -/
theorem ofGrownArmReflectionCoverageWitness {profile : PolyProfile} :
    OfGrownArmReflectionCoverage profile where
  ofFormationReflects := fun formationTyped contextLockFree =>
    (HasTypeDescPi.ofFormation formationTyped).ofGrownReflected contextLockFree
  convReflects := fun levelExpr flag typed converts reclassifierTyped contextLockFree =>
    (HasTypeDescPi.conv levelExpr flag typed converts reclassifierTyped).ofGrownReflected
      contextLockFree
  piIntroReflects := fun domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped
      contextLockFree =>
    (HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped
      bodyTyped).ofGrownReflected contextLockFree
  piElimReflects := fun functionTyped argumentTyped contextLockFree =>
    (HasTypeDescPi.piElim functionTyped argumentTyped).ofGrownReflected contextLockFree
  genFormationPiReflects := fun context generator payload children levels flag rule isFormation
      premises contextLockFree =>
    (HasTypeDescPi.genFormationPi context generator payload children levels flag rule isFormation
      premises).ofGrownReflected contextLockFree

end FX1Poly.Typed
