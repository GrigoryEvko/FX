import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstColimits

/-! # FX1Poly/Tier0/Context/PushoutContexts — context-19 [pushout / HIT contexts; the strictness axiom]

`context-3` shipped the RIGHT/colimits leg of the substitution category — the INITIAL object (scope 0,
the empty context) and the binary COPRODUCT (scope addition).  `context-19` lands the next colimit
shape the HIT/pushout story owes: **PUSHOUTS of contexts** + the context-level **strictness** of the
gluing square — all on the context base, all zero-axiom.

## Variance — what a context pushout IS

`fxBaseSubstCategory.Morphism a b = SubstVec b a`, so `fxBaseSubstCategory = 𝒞ᵒᵖ` (the OPPOSITE of the
CwF category-of-contexts `𝒞`).  Consequently a PUSHOUT in `fxBaseSubstCategory` is a PULLBACK in `𝒞` —
the substitution / comprehension square is the canonical such pullback (context extension stable under
substitution; see `context-17`).  Specializing: a pushout OVER THE INITIAL object (scope 0) is a
pullback over `𝒞`'s TERMINAL object (the empty context), i.e. the context PRODUCT in `𝒞` — which is
exactly the binary COPRODUCT `context-3` already shipped in `fxBaseSubstCategory`.  So the context
category's most basic pushout is the context-coproduct, and that is what lands here as a concrete,
proved pushout.

## What is genuinely CONTEXT-SIDE here (all zero-axiom)

  * `IsPushout` — the full pushout universal property over an arbitrary `RawCategory`: a cocone
    (`injectLeft` / `injectRight`) whose `square` STRICTLY commutes, a `mediate`-ing morphism out of the
    pushout for every compatible cocone, the two β-laws, and η/uniqueness.  (The strong, dual-of-the-
    strong-pullback form: a genuine mediator function + a uniqueness law, not a mere `∃`.)
  * `IsPushout.mediateHomExt` — the pushout injections are JOINTLY EPIC: two maps out of a pushout
    agreeing after both injections are equal.
  * `IsPushout.uniqueUpToIso` — any two pushout objects of the same span are canonically ISOMORPHIC
    (the universal-property uniqueness; the "HIT is unique up to iso" at the context base).
  * `IsBinaryCoproduct.isPushoutOverInitial` — a coproduct + an initial object IS the pushout of the
    span over the initial object (the gluing-over-`∅` is the coproduct).
  * `IsPushout.ofIsoLeftLeg` — gluing along an ISO leg is STRICT-TRIVIAL: the pushout of a span whose
    left leg is an isomorphism is the opposite corner (the strictness/contractibility flavor — gluing
    along an equivalence adds nothing).
  * `fxBaseSubstPushoutOverInitial` — ★ the concrete context pushout: gluing two contexts over the
    empty context is their context coproduct (scope addition).
  * `fxBaseSubstGlueSquare_definitional` — ★ THE CONTEXT-SIDE STRICTNESS: the gluing square of the
    over-empty pushout commutes DEFINITIONALLY (`rfl`), because both legs out of the empty context are
    the unique empty substitution (`SubstVec _ 0 = PUnit`).  This strict (on-the-nose, not up-to-a-
    path) commutation is the context-level shadow the cubical `Glue` strictness will ride on.
  * `FxGluePushout` / `fxGluePushout` — the assembled witness (the context-pushout family + the strict
    square + the up-to-iso uniqueness).
  * `fxGluePushout_hasGlueWeldTypeFormers` — the honesty marker (`= false`); see below.

## Honest scope boundary (the `⊟SPLIT · core = Glue/Weld × type`)

This is the CONTEXT-SIDE pushout/strictness substrate, NOT the cubical strictness AXIOM and NOT the
`Glue` / `Weld` TYPE FORMERS:

  * The cubical strictness / realignment axiom is a property of the UNIVERSE (a partial type + a partial
    equivalence strictifies to a total type restricting on the nose) — an operation on the type
    presheaf, hence `×type`, deferred to `fib-1` / the type axis.  What lands here is only the
    elementary context-level fact that the gluing SQUARE commutes strictly.
  * `Glue` (partial-equivalence → total type) and its dual `Weld` are TYPE FORMERS: they consume the
    universe (`×type`) and partial elements over a cofibration / interval (the interval is a mode-theory
    object, `×mode`).  Both defer.  `fxGluePushout_hasGlueWeldTypeFormers = false` records their absence.
  * The HIT pushout TYPE itself (the point + glue PATH constructors with their computation rules) is
    likewise a type former (`×type`); `context-19` ships the base-category CONTEXT pushout it would
    fiber over, not the higher inductive type.
  * We do NOT claim `fxBaseSubstCategory` has ALL pushouts — dually `𝒞` lacks general pullbacks.  Only
    the over-initial pushout (the coproduct) and the iso-leg pushout land as concrete witnesses; the
    rest is the generic universal-property calculus.

Every declaration below is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1Poly.Tier0

open FX1Poly.Core

universe u v

/-! ## The generic pushout universal property over a `RawCategory` -/

/-- A PUSHOUT of the span `leftLeg ←spanLeft— apex —spanRight→ rightLeg`: an object with two injections
whose `square` commutes, such that every compatible cocone factors through it uniquely.  The strong
form (a `mediate` morphism + the two β-laws + an η/uniqueness law), the colimit dual of the strong
pullback. -/
structure IsPushout (category : RawCategory.{u, v})
    {apex leftLeg rightLeg : category.Object}
    (spanLeft : category.Morphism apex leftLeg)
    (spanRight : category.Morphism apex rightLeg)
    (pushoutObject : category.Object) where
  /-- The injection of the left corner into the pushout. -/
  injectLeft : category.Morphism leftLeg pushoutObject
  /-- The injection of the right corner into the pushout. -/
  injectRight : category.Morphism rightLeg pushoutObject
  /-- The pushout SQUARE commutes (the gluing condition). -/
  square : category.compose spanLeft injectLeft = category.compose spanRight injectRight
  /-- The mediating morphism out of the pushout, for any cocone compatible over the apex. -/
  mediate : ∀ {target : category.Object}
    (legLeft : category.Morphism leftLeg target)
    (legRight : category.Morphism rightLeg target),
    category.compose spanLeft legLeft = category.compose spanRight legRight →
    category.Morphism pushoutObject target
  /-- β-LEFT: `mediate` after the left injection is the left leg. -/
  mediateInjectLeft : ∀ {target : category.Object}
    (legLeft : category.Morphism leftLeg target)
    (legRight : category.Morphism rightLeg target)
    (compat : category.compose spanLeft legLeft = category.compose spanRight legRight),
    category.compose injectLeft (mediate legLeft legRight compat) = legLeft
  /-- β-RIGHT: `mediate` after the right injection is the right leg. -/
  mediateInjectRight : ∀ {target : category.Object}
    (legLeft : category.Morphism leftLeg target)
    (legRight : category.Morphism rightLeg target)
    (compat : category.compose spanLeft legLeft = category.compose spanRight legRight),
    category.compose injectRight (mediate legLeft legRight compat) = legRight
  /-- η / UNIQUENESS: any mediator agreeing with both legs after the injections is the `mediate`. -/
  mediateUnique : ∀ {target : category.Object}
    (mediator : category.Morphism pushoutObject target)
    (legLeft : category.Morphism leftLeg target)
    (legRight : category.Morphism rightLeg target)
    (compat : category.compose spanLeft legLeft = category.compose spanRight legRight),
    category.compose injectLeft mediator = legLeft →
    category.compose injectRight mediator = legRight →
    mediator = mediate legLeft legRight compat

/-- **JOINTLY EPIC injections.**  Two maps out of a pushout agreeing after both injections are equal —
both are the `mediate` of the common cocone (built from the first map's restrictions). -/
theorem IsPushout.mediateHomExt {category : RawCategory.{u, v}}
    {apex leftLeg rightLeg pushoutObject : category.Object}
    {spanLeft : category.Morphism apex leftLeg}
    {spanRight : category.Morphism apex rightLeg}
    (pushout : IsPushout category spanLeft spanRight pushoutObject)
    {target : category.Object}
    (firstMorphism secondMorphism : category.Morphism pushoutObject target)
    (afterLeft : category.compose pushout.injectLeft firstMorphism
      = category.compose pushout.injectLeft secondMorphism)
    (afterRight : category.compose pushout.injectRight firstMorphism
      = category.compose pushout.injectRight secondMorphism) :
    firstMorphism = secondMorphism := by
  have compat : category.compose spanLeft (category.compose pushout.injectLeft firstMorphism)
      = category.compose spanRight (category.compose pushout.injectRight firstMorphism) := by
    rw [← category.composeAssoc, ← category.composeAssoc, pushout.square]
  exact (pushout.mediateUnique firstMorphism
        (category.compose pushout.injectLeft firstMorphism)
        (category.compose pushout.injectRight firstMorphism) compat rfl rfl).trans
      (pushout.mediateUnique secondMorphism
        (category.compose pushout.injectLeft firstMorphism)
        (category.compose pushout.injectRight firstMorphism) compat
        afterLeft.symm afterRight.symm).symm

/-- **Pushouts are unique up to isomorphism.**  Given two pushouts of the SAME span, the mediator from
the first to the second is an isomorphism (its inverse is the symmetric mediator; both round-trips are
the identity by jointly-epic uniqueness).  The universal-property uniqueness — the "HIT is unique up to
iso" theorem at the context base. -/
def IsPushout.uniqueUpToIso {category : RawCategory.{u, v}}
    {apex leftLeg rightLeg pushoutObjectA pushoutObjectB : category.Object}
    {spanLeft : category.Morphism apex leftLeg}
    {spanRight : category.Morphism apex rightLeg}
    (pushoutA : IsPushout category spanLeft spanRight pushoutObjectA)
    (pushoutB : IsPushout category spanLeft spanRight pushoutObjectB) :
    IsIsomorphism category
      (pushoutA.mediate pushoutB.injectLeft pushoutB.injectRight pushoutB.square) where
  inverse := pushoutB.mediate pushoutA.injectLeft pushoutA.injectRight pushoutA.square
  leftInverse :=
    pushoutB.mediateHomExt _ _
      (by rw [← category.composeAssoc, pushoutB.mediateInjectLeft, pushoutA.mediateInjectLeft,
            category.identityRight])
      (by rw [← category.composeAssoc, pushoutB.mediateInjectRight, pushoutA.mediateInjectRight,
            category.identityRight])
  rightInverse :=
    pushoutA.mediateHomExt _ _
      (by rw [← category.composeAssoc, pushoutA.mediateInjectLeft, pushoutB.mediateInjectLeft,
            category.identityRight])
      (by rw [← category.composeAssoc, pushoutA.mediateInjectRight, pushoutB.mediateInjectRight,
            category.identityRight])

/-! ## Pushout over the initial object = the binary coproduct -/

/-- **A coproduct over the initial object IS a pushout.**  Gluing `leftSummand` and `rightSummand` over
the initial object (the span of the two unique maps out of `∅`) is their coproduct: the square commutes
because both composites are maps out of the initial object, the mediator is `copair`, and the β / η laws
are the coproduct's.  (The compatibility hypothesis on each cocone is automatic over an initial object,
so `copair` ignores it.) -/
def IsBinaryCoproduct.isPushoutOverInitial {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductObject : category.Object}
    (coproduct : IsBinaryCoproduct category leftSummand rightSummand coproductObject)
    {initialObject : category.Object}
    (initial : IsInitialObject category initialObject) :
    IsPushout category
      (initial.fromInitial leftSummand) (initial.fromInitial rightSummand) coproductObject where
  injectLeft := coproduct.injectLeft
  injectRight := coproduct.injectRight
  square := initial.homExt _ _
  mediate := fun legLeft legRight _compat => coproduct.copair legLeft legRight
  mediateInjectLeft := fun legLeft legRight _compat => coproduct.copairInjectLeft legLeft legRight
  mediateInjectRight := fun legLeft legRight _compat => coproduct.copairInjectRight legLeft legRight
  mediateUnique := fun mediator legLeft legRight _compat afterLeft afterRight =>
    coproduct.copairUnique mediator legLeft legRight afterLeft afterRight

/-! ## Gluing along an isomorphism is strict-trivial -/

/-- **Gluing along an ISO leg is the opposite corner.**  When the left leg of the span is an
isomorphism, the right corner `rightLeg` itself is the pushout: the right injection is the identity and
the left injection is `spanLeft⁻¹ ; spanRight`.  Gluing along an equivalence adds nothing — the
strictness/contractibility flavor at the context base. -/
def IsPushout.ofIsoLeftLeg {category : RawCategory.{u, v}}
    {apex leftLeg rightLeg : category.Object}
    {spanLeft : category.Morphism apex leftLeg}
    (spanLeftIso : IsIsomorphism category spanLeft)
    (spanRight : category.Morphism apex rightLeg) :
    IsPushout category spanLeft spanRight rightLeg where
  injectLeft := category.compose spanLeftIso.inverse spanRight
  injectRight := category.identity rightLeg
  square := by
    rw [← category.composeAssoc, spanLeftIso.rightInverse, category.identityLeft,
      category.identityRight]
  mediate := fun _legLeft legRight _compat => legRight
  mediateInjectLeft := fun legLeft legRight compat => by
    rw [category.composeAssoc, ← compat, ← category.composeAssoc, spanLeftIso.leftInverse,
      category.identityLeft]
  mediateInjectRight := fun _legLeft legRight _compat => category.identityLeft legRight
  mediateUnique := fun mediator _legLeft legRight _compat _afterLeft afterRight =>
    (category.identityLeft mediator).symm.trans afterRight

/-! ## The concrete context pushout: gluing over the empty context -/

/-- ★ **The context pushout over the empty context.**  Gluing the contexts `leftScope` and `rightScope`
over the empty context (scope 0, the initial object) is their context COPRODUCT (scope addition) — the
substitution category's most basic pushout, read straight off `context-3`'s coproduct + initial. -/
def fxBaseSubstPushoutOverInitial (leftScope rightScope : Nat) :
    IsPushout fxBaseSubstCategory
      (fxBaseSubstInitial.fromInitial leftScope)
      (fxBaseSubstInitial.fromInitial rightScope)
      (leftScope + rightScope) :=
  (fxBaseSubstBinaryCoproduct leftScope rightScope).isPushoutOverInitial fxBaseSubstInitial

/-- ★ **The context-side strictness.**  The gluing SQUARE of the over-empty pushout commutes
DEFINITIONALLY (`rfl`): both legs out of the empty context are the unique empty substitution
(`SubstVec _ 0 = PUnit`), so their composites with the injections are definitionally equal.  This
strict (on-the-nose, not up-to-a-path) commutation is the context-level shadow the cubical `Glue`
strictness rests on. -/
theorem fxBaseSubstGlueSquare_definitional (leftScope rightScope : Nat) :
    fxBaseSubstCategory.compose (fxBaseSubstInitial.fromInitial leftScope)
        (SubstVec.coproductInjectLeft leftScope rightScope)
      = fxBaseSubstCategory.compose (fxBaseSubstInitial.fromInitial rightScope)
        (SubstVec.coproductInjectRight leftScope rightScope) :=
  rfl

/-! ## The assembled witness -/

/-- The FX context base HAS the pushout / gluing data: the context-pushout family (gluing over the
empty context), the STRICT gluing square, and pushout uniqueness up to iso. -/
structure FxGluePushout where
  /-- The family of context pushouts — gluing any two contexts over the empty context. -/
  contextPushout : (leftScope rightScope : Nat) →
    IsPushout fxBaseSubstCategory
      (fxBaseSubstInitial.fromInitial leftScope)
      (fxBaseSubstInitial.fromInitial rightScope)
      (leftScope + rightScope)
  /-- ★ The context-side strictness: the gluing square commutes definitionally. -/
  glueSquareStrict : ∀ (leftScope rightScope : Nat),
    fxBaseSubstCategory.compose (fxBaseSubstInitial.fromInitial leftScope)
        (SubstVec.coproductInjectLeft leftScope rightScope)
      = fxBaseSubstCategory.compose (fxBaseSubstInitial.fromInitial rightScope)
        (SubstVec.coproductInjectRight leftScope rightScope)
  /-- ★ Pushout uniqueness: any other pushout of the same over-empty span is canonically isomorphic. -/
  pushoutUniqueUpToIso : ∀ (leftScope rightScope otherObject : Nat)
    (otherPushout : IsPushout fxBaseSubstCategory
      (fxBaseSubstInitial.fromInitial leftScope)
      (fxBaseSubstInitial.fromInitial rightScope) otherObject),
    IsIsomorphism fxBaseSubstCategory
      ((contextPushout leftScope rightScope).mediate
        otherPushout.injectLeft otherPushout.injectRight otherPushout.square)

/-- ★ The FX context base's gluing / pushout witness. -/
def fxGluePushout : FxGluePushout where
  contextPushout := fun leftScope rightScope => fxBaseSubstPushoutOverInitial leftScope rightScope
  glueSquareStrict := fun leftScope rightScope =>
    fxBaseSubstGlueSquare_definitional leftScope rightScope
  pushoutUniqueUpToIso := fun leftScope rightScope _otherObject otherPushout =>
    (fxBaseSubstPushoutOverInitial leftScope rightScope).uniqueUpToIso otherPushout

/-- **Honesty marker.**  The `Glue` / `Weld` TYPE FORMERS are NOT shipped at `context-19`: `Glue`
(partial equivalence → strict total type) and its dual `Weld` consume the universe (`×type`) and
partial elements over a cofibration / interval (`×mode`), and the cubical strictness/realignment AXIOM
is a universe operation (`×type`).  `context-19` ships only the context-side pushout structure + the
strict gluing square; the type formers defer to `fib-1` / the type axis. -/
def fxGluePushout_hasGlueWeldTypeFormers : Bool := false

/-! ## Smoke: gluing two singleton contexts -/

/-- Smoke: the left injection of the (1,1)-pushout (gluing two singleton contexts over `∅`) is the
context-coproduct injection into scope `2` — the pushout object is scope `1 + 1`, definitionally. -/
theorem fxGluePushout_glue_singletons_smoke :
    (fxBaseSubstPushoutOverInitial 1 1).injectLeft = SubstVec.coproductInjectLeft 1 1 :=
  rfl

end FX1Poly.Tier0
