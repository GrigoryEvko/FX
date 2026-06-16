import FX1Poly.Tier0.Context.RepresentableMapCategory

/-! # context-23 — the groupoid / setoid model (Hofmann–Streicher), context-side residue

`context-23` is the GROUPOID MODEL rung: the Hofmann–Streicher groupoid model of Martin-Löf type theory,
which interprets contexts and types as GROUPOIDS, the identity type `Id_A(a, b)` as the HOM-SET `Hom(a, b)`,
and — the landmark result — REFUTES uniqueness of identity proofs (UIP / Streicher's axiom K).  Because a
groupoid can have an object with a NON-TRIVIAL automorphism, its hom-set (the model's identity type) can have
two distinct elements, so `Id` is proof-RELEVANT — the first model to show this, the door to HoTT.

## What is context-side here, and what is deferred

The category of CONTEXTS of the groupoid model is `Grpd` — groupoids and functors.  That base, together with
the SEMANTIC reason UIP fails (a groupoid whose hom-set is not a subsingleton), is pure category-of-contexts
data; that is the CONTEXT-SIDE residue shipped here, in full and zero-axiom:

  * **`RawGroupoid`** — a groupoid (a category with an inverse for every morphism; the five laws are
    POINTWISE equalities in a hom-type, so funext-free), with **`toRawCategory`** the forgetful
    `Grpd ⟶ Cat` (a groupoid IS a category).
  * **`groupoidCategory`** — `Grpd` as a genuine `RawCategory` (objects are groupoids, morphisms are
    `GroupoidFunctor`s).  As in `□`/`Δ`, the three category laws hold DEFINITIONALLY — β/η on the underlying
    object/morphism maps plus definitional proof irrelevance of the functor laws — so each is `rfl`, no
    `funext`.
  * **`discreteGroupoid`** — the Set ↪ Grpd embedding (a set as a groupoid with only identity morphisms;
    hom `= PLift (a = b)`), with **`discreteGroupoidMap`** its functoriality, and
    **`discreteGroupoid_isSetoid`**: discrete groupoids satisfy UIP (their hom-sets are subsingletons by
    definitional proof irrelevance) — the SETOID side of the rung name.
  * ★ **`deloopZmod2`** — the UIP-REFUTING witness: the delooping `B(ℤ/2)` (one object, hom-set `= Bool`
    with `xor` composition, every element self-inverse — a genuine groupoid), together with
    **`deloopZmod2_hom_not_subsingleton`** (its hom-set has two distinct loops `false ≠ true`, so the
    model's identity type is proof-relevant) and **`deloopZmod2_not_setoid`** (it is NOT a setoid groupoid).
    This is the SEMANTIC CORE of the UIP refutation.
  * **`fxGroupoidModel`** — the model datum: `Grpd` as the base + the discrete (set) inclusion.

DEFERRED (honestly NOT here, the `×type` / full-model core, recorded by the `= false` markers):
  * the IDENTITY-TYPE-AS-HOM interpretation — `Id_A` as the hom-groupoid, the CwF/natural-model type
    structure over `Grpd` — `hasIdentityTypeAsHom = false`;
  * the GROUPOID UNIVERSE — the Hofmann–Streicher universe of (small) groupoids — `hasGroupoidUniverse = false`;
  * the UIP-REFUTATION THEOREM proper — the SYNTACTIC statement that K / UIP is NOT DERIVABLE in MLTT (which
    needs the full interpretation of the type theory into this model + soundness) — `hasUipRefutationTheorem
    = false`.  What ships here is the WITNESS groupoid whose hom-type is not a mere proposition — the
    semantic REASON UIP fails; the syntactic underivability is `×type` and the full model.

SCOPE NOTE: a groupoid here is a 1-groupoid (hom-sets are plain types).  The setoid model (proof-irrelevant
hom-sets, where UIP HOLDS) is the sub-case `IsSetoidGroupoid`; the full groupoid model (proof-relevant
hom-sets, where UIP FAILS) is witnessed by `deloopZmod2`.  Both live in the same `Grpd`.

Reference: Hofmann & Streicher, "The groupoid interpretation of type theory" (Twenty-Five Years of
Constructive Type Theory, 1998).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## Groupoids -/

/-- A **groupoid** — a category in which every morphism is invertible.  `Hom`-sets are plain types (so a
1-groupoid); the five laws are POINTWISE equalities in a hom-type (not equalities between functions), so they
are funext-free.  The inverse laws are what upgrade a `RawCategory` to a `RawGroupoid`. -/
structure RawGroupoid where
  /-- The objects. -/
  Object : Type
  /-- The hom-set between two objects (the model's identity type `Id_A`). -/
  Hom : Object → Object → Type
  /-- The identity morphism. -/
  identity : (object : Object) → Hom object object
  /-- Composition (apply `first`, then `second`). -/
  compose : {objectA objectB objectC : Object} →
            Hom objectA objectB → Hom objectB objectC → Hom objectA objectC
  /-- The inverse of every morphism — the groupoid structure. -/
  inverse : {source target : Object} → Hom source target → Hom target source
  /-- Composition is associative (pointwise). -/
  composeAssoc : ∀ {objectA objectB objectC objectD : Object}
    (first : Hom objectA objectB) (second : Hom objectB objectC) (third : Hom objectC objectD),
    compose (compose first second) third = compose first (compose second third)
  /-- Left identity (pointwise). -/
  identityLeft : ∀ {source target : Object} (edge : Hom source target),
    compose (identity source) edge = edge
  /-- Right identity (pointwise). -/
  identityRight : ∀ {source target : Object} (edge : Hom source target),
    compose edge (identity target) = edge
  /-- The inverse cancels on the left. -/
  inverseLeft : ∀ {source target : Object} (edge : Hom source target),
    compose (inverse edge) edge = identity target
  /-- The inverse cancels on the right. -/
  inverseRight : ∀ {source target : Object} (edge : Hom source target),
    compose edge (inverse edge) = identity source

/-- The forgetful `Grpd ⟶ Cat`: every groupoid IS a category (forget the inverse).  The three category laws
ARE the groupoid's own first three laws. -/
def RawGroupoid.toRawCategory (groupoid : RawGroupoid) : RawCategory where
  Object := groupoid.Object
  Morphism := groupoid.Hom
  identity := groupoid.identity
  compose := groupoid.compose
  composeAssoc := groupoid.composeAssoc
  identityLeft := groupoid.identityLeft
  identityRight := groupoid.identityRight

/-! ## The category of groupoids Grpd -/

/-- A **functor of groupoids** — an object map + a morphism map preserving identity and composition.  The two
preservation laws are `Prop`-valued and stated pointwise, so two functors are equal exactly when their
object/morphism maps are — which lets `Grpd`'s category laws hold definitionally. -/
structure GroupoidFunctor (source target : RawGroupoid) where
  /-- The action on objects. -/
  objectMap : source.Object → target.Object
  /-- The action on morphisms. -/
  morphismMap : {objectA objectB : source.Object} →
                source.Hom objectA objectB → target.Hom (objectMap objectA) (objectMap objectB)
  /-- Functors preserve identities (pointwise). -/
  preservesIdentity : ∀ (object : source.Object),
    morphismMap (source.identity object) = target.identity (objectMap object)
  /-- Functors preserve composition (pointwise). -/
  preservesCompose : ∀ {objectA objectB objectC : source.Object}
    (first : source.Hom objectA objectB) (second : source.Hom objectB objectC),
    morphismMap (source.compose first second) = target.compose (morphismMap first) (morphismMap second)

/-- The identity functor of groupoids. -/
def GroupoidFunctor.identityFunctor (groupoid : RawGroupoid) : GroupoidFunctor groupoid groupoid where
  objectMap := fun object => object
  morphismMap := fun edge => edge
  preservesIdentity := fun _ => rfl
  preservesCompose := fun _ _ => rfl

/-- Composition of groupoid functors (apply `functorOne`, then `functorTwo`); the preservation laws chain. -/
def GroupoidFunctor.composeFunctor {sourceGroupoid midGroupoid targetGroupoid : RawGroupoid}
    (functorOne : GroupoidFunctor sourceGroupoid midGroupoid)
    (functorTwo : GroupoidFunctor midGroupoid targetGroupoid) :
    GroupoidFunctor sourceGroupoid targetGroupoid where
  objectMap := fun object => functorTwo.objectMap (functorOne.objectMap object)
  morphismMap := fun edge => functorTwo.morphismMap (functorOne.morphismMap edge)
  preservesIdentity := fun object =>
    (congrArg functorTwo.morphismMap (functorOne.preservesIdentity object)).trans
      (functorTwo.preservesIdentity (functorOne.objectMap object))
  preservesCompose := fun first second =>
    (congrArg functorTwo.morphismMap (functorOne.preservesCompose first second)).trans
      (functorTwo.preservesCompose (functorOne.morphismMap first) (functorOne.morphismMap second))

/-- ★ **The category of groupoids, `Grpd`**, as a genuine `RawCategory` — the category of CONTEXTS of the
groupoid model.  As with `□`/`Δ`, all three laws hold DEFINITIONALLY (β/η on object/morphism maps + proof
irrelevance of the functor laws) — each `rfl`, no `funext`. -/
def groupoidCategory : RawCategory where
  Object := RawGroupoid
  Morphism := GroupoidFunctor
  identity := GroupoidFunctor.identityFunctor
  compose := GroupoidFunctor.composeFunctor
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## Setoids vs groupoids — where UIP holds and where it fails -/

/-- A groupoid is a **setoid groupoid** when its hom-sets are subsingletons (proof-irrelevant) — i.e. it
validates UIP: any two parallel morphisms (any two identity proofs) coincide.  The setoid model is exactly
the groupoid model restricted to these. -/
def IsSetoidGroupoid (groupoid : RawGroupoid) : Prop :=
  ∀ {source target : groupoid.Object} (edgeOne edgeTwo : groupoid.Hom source target), edgeOne = edgeTwo

/-- The **discrete groupoid on a type** — the Set ↪ Grpd embedding: objects are the elements, the only
morphisms are proofs of equality (`Hom a b = PLift (a = b)`).  Every law holds by definitional proof
irrelevance of `Eq`. -/
def discreteGroupoid (carrier : Type) : RawGroupoid where
  Object := carrier
  Hom := fun elementA elementB => PLift (elementA = elementB)
  identity := fun _ => PLift.up rfl
  compose := fun pathOne pathTwo => PLift.up (pathOne.down.trans pathTwo.down)
  inverse := fun path => PLift.up path.down.symm
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl
  inverseLeft := fun _ => rfl
  inverseRight := fun _ => rfl

/-- The discrete embedding is FUNCTORIAL: a function on carriers induces a groupoid functor (the action of
`Set ↪ Grpd` on morphisms).  Preservation holds by proof irrelevance. -/
def discreteGroupoidMap {carrierSource carrierTarget : Type} (onElements : carrierSource → carrierTarget) :
    GroupoidFunctor (discreteGroupoid carrierSource) (discreteGroupoid carrierTarget) where
  objectMap := onElements
  morphismMap := fun path => PLift.up (congrArg onElements path.down)
  preservesIdentity := fun _ => rfl
  preservesCompose := fun _ _ => rfl

/-- ★ A discrete groupoid (a set) is a SETOID groupoid — **UIP HOLDS** for sets: any two equality proofs
between fixed elements coincide, by definitional proof irrelevance.  This is the setoid model's defining
property; contrast `deloopZmod2_not_setoid`. -/
theorem discreteGroupoid_isSetoid (carrier : Type) : IsSetoidGroupoid (discreteGroupoid carrier) := by
  intro _ _ edgeOne edgeTwo
  cases edgeOne
  cases edgeTwo
  rfl

/-! ## The UIP-refuting witness — the delooping of ℤ/2 -/

/-- ★ The **delooping `B(ℤ/2)`** — one object, hom-set `Bool` with `xor` composition (the group ℤ/2), every
element its own inverse.  A genuine groupoid: the group axioms are the groupoid laws.  Its single hom-set has
TWO elements, so as a TYPE in the model its identity type is proof-RELEVANT — the witness that refutes UIP. -/
def deloopZmod2 : RawGroupoid where
  Object := Unit
  Hom := fun _ _ => Bool
  identity := fun _ => false
  compose := fun loopOne loopTwo => Bool.xor loopOne loopTwo
  inverse := fun loop => loop
  composeAssoc := fun first second third => by
    cases first <;> cases second <;> cases third <;> rfl
  identityLeft := fun edge => by cases edge <;> rfl
  identityRight := fun edge => by cases edge <;> rfl
  inverseLeft := fun edge => by cases edge <;> rfl
  inverseRight := fun edge => by cases edge <;> rfl

/-- ★ **The UIP refutation, semantic core.**  The hom-set of `B(ℤ/2)` is NOT a subsingleton: it has two
distinct loops at the basepoint (`false`, the identity, and `true`, the non-trivial automorphism).  Read in
the model where `Id_A = Hom`, these are two UNEQUAL proofs of `a = a` — UIP fails. -/
theorem deloopZmod2_hom_not_subsingleton :
    ∃ (loopOne loopTwo : deloopZmod2.Hom () ()), loopOne ≠ loopTwo :=
  ⟨false, true, fun loopsEqual => Bool.noConfusion loopsEqual⟩

/-- ★ `B(ℤ/2)` is NOT a setoid groupoid — the contrast with `discreteGroupoid_isSetoid`.  A single groupoid
in `Grpd` whose hom-sets are proof-relevant is all it takes to break UIP. -/
theorem deloopZmod2_not_setoid : ¬ IsSetoidGroupoid deloopZmod2 :=
  fun isSetoid => Bool.noConfusion (isSetoid (source := ()) (target := ()) false true)

/-! ## The model datum + honesty markers -/

/-- The context-side datum of the groupoid model: the base category `Grpd` and the Set ↪ Grpd inclusion. -/
structure GroupoidModelData where
  /-- The base — the category of groupoids `Grpd` (the contexts).  Objects are groupoids (`Type 1`), so the
  base category lives at `RawCategory.{1, 0}`. -/
  base : RawCategory.{1, 0}
  /-- The Set ↪ Grpd inclusion (a set is a discrete groupoid). -/
  setInclusion : Type → RawGroupoid

/-- ★ The FX groupoid-model datum: `Grpd` as the base, discrete groupoids as the included sets. -/
def fxGroupoidModel : GroupoidModelData where
  base := groupoidCategory
  setInclusion := discreteGroupoid

/-- **Honesty marker.**  The IDENTITY-TYPE-AS-HOM interpretation — `Id_A` as the hom-groupoid, the CwF /
natural-model type structure over `Grpd` — is `×type`, deferred.  `= false`. -/
def fxGroupoidModel_hasIdentityTypeAsHom : Bool := false

/-- **Honesty marker.**  The GROUPOID UNIVERSE — the Hofmann–Streicher universe of (small) groupoids — is
`×type`, deferred.  `= false`. -/
def fxGroupoidModel_hasGroupoidUniverse : Bool := false

/-- **Honesty marker.**  The UIP-REFUTATION THEOREM proper — the SYNTACTIC underivability of K / UIP in MLTT
(needs the full interpretation of the type theory into this model + soundness) — is `×type` and the full
model.  What ships is the semantic witness `deloopZmod2_hom_not_subsingleton`.  `= false`. -/
def fxGroupoidModel_hasUipRefutationTheorem : Bool := false

/-! ## Smoke -/

/-- Smoke: in a discrete groupoid (a set), the loops at a point are unique — UIP holds — the SETOID side, to
be contrasted with `deloopZmod2_hom_not_subsingleton`. -/
theorem discreteGroupoid_isSetoid_smoke (carrier : Type) (element : carrier)
    (loopOne loopTwo : (discreteGroupoid carrier).Hom element element) :
    loopOne = loopTwo :=
  discreteGroupoid_isSetoid carrier loopOne loopTwo

end FX1Poly.Tier0
