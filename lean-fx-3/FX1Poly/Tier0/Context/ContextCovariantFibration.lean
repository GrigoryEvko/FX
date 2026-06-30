import FX1Poly.Tier0.Context.ContextDirectedUnivalence

/-! # context-35 — covariant (cocartesian) fibrations ≃ functors into the DIRECTED universe

`context-35` (★, on the fib-* arc, →fib-1/4) is the DIRECTED GROTHENDIECK CLASSIFICATION at the context
category — the directed mirror of the symmetric "families ≃ display maps" picture, and the covariant analog of
"fibrations ≃ families".  It states — and ships a zero-axiom witness for — the classification
**covariant (cocartesian / opcartesian) fibrations over a base context category ≃ functors into the directed
universe**, the straightening / unstraightening of the directed Grothendieck construction, restricted to the
strict (1-categorical, set-fibration) fragment that keeps it zero-axiom.

It builds DIRECTLY on `context-34` (`ContextDirectedUnivalence.lean` / `ContextDirectedUniverse.lean`): there
the directed hom `Hom_U(A, B)` at the universe object computes to the function type `Fun(A, B)` — directed
univalence by computation.  Here that same directed universe (objects = type codes, morphisms = FORWARD
functions, NO `symm` — `DirectedCategoryHom`) becomes the CLASSIFIER: a functor `C ⟶ U` into it IS a covariant
fibration over `C`.

## The directed Grothendieck construction, and why it is funext-free here

For a copresheaf `F : C → Cat` (or `F : C → Set`) the covariant Grothendieck construction `∫F` is an
OPFIBRATION over `C`: its cocartesian (opcartesian) lifts go FORWARD along base morphisms.  Straightening
`∫F ↦ F` and unstraightening `F ↦ ∫F` are mutually inverse — the directed analog of "display maps ≃ families".
The full ∞-categorical statement (Riehl–Verity ∞-cosmos / Riehl–Shulman synthetic-(∞,1) straightening with
homotopy-coherent naturality) needs `funext` / `Quot.sound`, the fib-5-style wall the directed universe
generator `gen_universeD` defers.

The strict, set-fibration fragment is funext-free.  Take the directed universe to be the SMALL category of type
CODES and FORWARD functions, and a covariant fibration over `C` to be a STRICT copresheaf — a fiber assignment
`fiber : C → Code` plus a functorial cocartesian-lift operation `cocartesianLift : (a ⟶ b) → fiber a → fiber b`.
That data IS, field for field, a `RawFunctor C U` (the `mapObject` / `mapMorphism` / two functor laws).  So
`straighten` / `unstraighten` are repackagings that round-trip BY `rfl` (structure eta) — the classification at
the strict level, with no funext, no `Quot.sound`, exactly as `context-34`'s discrete witness stayed zero-axiom.

The genuine DIRECTEDNESS (distinguishing this from a symmetric "families ≃ display maps"): the universe's
morphisms are FORWARD functions only, the cocartesian lift goes FORWARD along the base morphism, and the total
category's cocartesian universal property is the OP-cartesian (initial-among-lifts) one — no backward transport,
no groupoid inverse.

## What lands here (all zero-axiom)

  * **`DirectedUniverseData` / `DirectedUniverseData.category`** — a small directed universe: a carrier of type
    codes + a decode-to-types, presented as a `RawCategory` whose hom `A ⟶ B` is the FORWARD function type
    `decode A → decode B` (the `context-34` `DirectedCategoryHom` realized: a forward morphism, no `symm`).
  * **`CovariantFibration`** — a covariant (cocartesian) fibration over a base context category: a fiber
    assignment + a functorial cocartesian-lift (opcartesian transport) operation.  The directed analog of a
    display map; lifts go FORWARD.
  * **`straighten` / `unstraighten`** — the directed Grothendieck construction both ways: a covariant fibration
    becomes a functor `C ⟶ U` into the directed universe, and back.  `unstraighten_straighten` /
    `straighten_unstraighten` are the classification equivalence — round-trip BY `rfl` (structure eta).
  * **`totalCategory` / `projection` / `cocartesianMorphism`** — the Grothendieck total category `∫F`, its
    projection opfibration to the base, and the chosen cocartesian lift of a base morphism.  The total-category
    laws hold by base-category laws + definitional proof irrelevance of the lies-over equality (`TotalMorphism.ext`).
  * **`cocartesianLift_isWeaklyInitial` + `cocartesianLift_mediatorUnique`** — the COCARTESIAN universal
    property at the strict level: the chosen lift is INITIAL among lifts over a base morphism (a unique mediator
    for every factorization).  Opcartesian, directed — no backward map.
  * **`TotalMorphism.instDecidableEq`** — the decidable-classification witness: total morphisms have decidable
    equality exactly when the base hom does (the lies-over proofs are proof-irrelevant), paralleling
    `context-34`'s decidable conversion.
  * **`constant` + smokes** — a canonical inhabitant (the constant fibration with identity transport) and the
    concrete round-trips.

## What is deferred (the honest wall)

  * The FULL ∞-cosmos / homotopy-coherent straightening–unstraightening (Riehl–Verity, Riehl–Shulman) — an
    EQUIVALENCE of `(∞,1)`-categories with coherent naturality — is NOT shipped: it needs `funext` /
    `Quot.sound`, the `×type` / type-axis wall the `gen_universeD` directed universe also defers
    (`fxCovariantFibration_hasFullInfinityCosmosStraightening = false`).
  * The classification + cocartesian universal property here are the SELF-CONTAINED Tier0 analog, NOT a Core
    `StepOverTable` iota row (`fxCovariantFibration_isOverCoreIotaTable = false`).

Imports only `ContextDirectedUnivalence` (its `context-34` sibling — the `RawCategory` / `RawFunctor` /
`DirectedCategoryHom` substrate).  A Tier0 design-lock must not import up into `Core/` / `Typed/`.  Zero
external dependencies — raw Lean 4 + Init only.

Reference: Riehl & Verity, "Elements of ∞-Category Theory", CUP 2022 (the ∞-cosmos straightening); Riehl &
Shulman, "A type theory for synthetic ∞-categories", HHA 2017; Grothendieck, SGA 1 (the 1-categorical
construction); the directed universe generator `gen_universeD`; the `context-34` siblings.
-/

namespace FX1Poly.Tier0

/-! ## The small directed universe — type codes and FORWARD functions -/

/-- A **small directed universe**: a carrier of type codes plus a decode to types.  This is the data the
context category's directed universe object reifies — a `Type`-small stand-in for the universe of types, so the
universe category below stays `RawCategory.{0, 0}` and matches the small base context categories. -/
structure DirectedUniverseData where
  /-- The type codes (objects of the universe). -/
  Code : Type
  /-- The decode: each code names a type — its fiber / collection of points. -/
  decode : Code → Type

/-- The **directed universe as a category**: objects are codes, and the hom `A ⟶ B` is the FORWARD function
type `decode A → decode B`.  Identity is `id`, composition is DIAGRAMMATIC function composition (apply the
first, then the second).  Every category law holds by `rfl`.  This is the `context-34` directed universe made
concrete: its morphisms are forward functions — a `DirectedCategoryHom` is exactly such a forward morphism, with
NO `symm` (the genuine directedness). -/
def DirectedUniverseData.category (univ : DirectedUniverseData) : RawCategory where
  Object := univ.Code
  Morphism := fun codeA codeB => univ.decode codeA → univ.decode codeB
  identity := fun _ => fun point => point
  compose := fun forwardF forwardG => fun point => forwardG (forwardF point)
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- A **functor into the directed universe** `C ⟶ U` — the straightened form of a covariant fibration.  A bare
abbreviation for the generic `RawFunctor` into `univ.category`, so the generic functor API (identity,
composition, the functor laws) applies. -/
abbrev DirectedUniverseFunctor (base : RawCategory.{0, 0}) (univ : DirectedUniverseData) :=
  RawFunctor base univ.category

/-! ## Covariant (cocartesian) fibrations over a base context category -/

/-- A **covariant (cocartesian / opcartesian) fibration** over a base context category, valued in a directed
universe: a fiber assignment `fiber` plus a functorial COCARTESIAN-LIFT operation `cocartesianLift` carrying
fiber points FORWARD along base morphisms.  The directed analog of a display map — lifts go forward, not
backward.  The two functor laws (`liftPreservesIdentity`, `liftPreservesComposition`) make this exactly a strict
copresheaf, i.e. a `RawFunctor` into the directed universe (`straighten`). -/
structure CovariantFibration (base : RawCategory.{0, 0}) (univ : DirectedUniverseData) where
  /-- The fiber over each base object — a code naming that fiber's type of points. -/
  fiber : base.Object → univ.Code
  /-- The COCARTESIAN LIFT: transport fiber points FORWARD along a base morphism (the opcartesian action). -/
  cocartesianLift : {baseSource baseTarget : base.Object} →
    base.Morphism baseSource baseTarget →
    univ.decode (fiber baseSource) → univ.decode (fiber baseTarget)
  /-- Functoriality (identity): lifting along an identity base morphism is the identity transport. -/
  liftPreservesIdentity : ∀ (baseObject : base.Object),
    cocartesianLift (base.identity baseObject) = fun fiberPoint => fiberPoint
  /-- Functoriality (composition): lifting along a composite is lifting along the first then the second. -/
  liftPreservesComposition : ∀ {baseSource baseMiddle baseTarget : base.Object}
    (firstMorphism : base.Morphism baseSource baseMiddle)
    (secondMorphism : base.Morphism baseMiddle baseTarget),
    cocartesianLift (base.compose firstMorphism secondMorphism)
      = fun fiberPoint => cocartesianLift secondMorphism (cocartesianLift firstMorphism fiberPoint)

/-! ## Straightening / unstraightening — the directed Grothendieck classification -/

/-- **Straighten** a covariant fibration into a functor `C ⟶ U` into the directed universe.  The fibration's
fiber assignment is the functor's action on objects, its cocartesian lift is the action on morphisms, and the
two functoriality laws are exactly the functor laws.  Half of the directed Grothendieck classification. -/
def CovariantFibration.straighten {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) : DirectedUniverseFunctor base univ where
  mapObject := fibration.fiber
  mapMorphism := fibration.cocartesianLift
  preservesIdentity := fibration.liftPreservesIdentity
  preservesComposition := fibration.liftPreservesComposition

/-- **Unstraighten** a functor `C ⟶ U` into the directed universe back into a covariant fibration.  The functor's
object map is the fiber assignment, its morphism map is the cocartesian lift, and its functor laws are the
functoriality of the lift.  The other half of the directed Grothendieck classification. -/
def CovariantFibration.unstraighten {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (functor : DirectedUniverseFunctor base univ) : CovariantFibration base univ where
  fiber := functor.mapObject
  cocartesianLift := functor.mapMorphism
  liftPreservesIdentity := functor.preservesIdentity
  liftPreservesComposition := functor.preservesComposition

/-- ★ **The directed Grothendieck classification (one round-trip).**  Unstraightening a straightened covariant
fibration recovers it — BY `rfl` (structure eta).  Half of "covariant fibrations ≃ functors into the directed
universe", at the strict level, funext-free. -/
theorem CovariantFibration.unstraighten_straighten {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) :
    CovariantFibration.unstraighten (CovariantFibration.straighten fibration) = fibration :=
  rfl

/-- ★ **The directed Grothendieck classification (other round-trip).**  Straightening an unstraightened functor
into the directed universe recovers it — BY `rfl` (structure eta).  The other half of the classification
equivalence. -/
theorem CovariantFibration.straighten_unstraighten {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (functor : DirectedUniverseFunctor base univ) :
    CovariantFibration.straighten (CovariantFibration.unstraighten functor) = functor :=
  rfl

/-! ## The Grothendieck total category `∫F` -/

/-- A **total object** of the Grothendieck construction `∫F`: a base object together with a point of its fiber. -/
structure CovariantFibration.TotalObject {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) where
  /-- The underlying base object. -/
  baseObject : base.Object
  /-- A point of the fiber over `baseObject`. -/
  fiberPoint : univ.decode (fibration.fiber baseObject)

/-- A **total morphism** `(a, x) ⟶ (b, y)` of `∫F`: a base morphism `u : a ⟶ b` whose cocartesian lift carries
`x` to `y`.  The lies-over component is an `Eq` (a `Prop`) — proof-irrelevant, so two total morphisms with the
same base morphism are definitionally equal (`TotalMorphism.ext`). -/
structure CovariantFibration.TotalMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {fibration : CovariantFibration base univ} (source target : fibration.TotalObject) where
  /-- The underlying base morphism. -/
  baseMorphism : base.Morphism source.baseObject target.baseObject
  /-- The morphism LIES OVER: its cocartesian lift carries the source point to the target point. -/
  liesOver : fibration.cocartesianLift baseMorphism source.fiberPoint = target.fiberPoint

/-- **Extensionality of total morphisms.**  Two total morphisms with the same base morphism are equal: the
lies-over components are proofs of an `Eq` (a `Prop`), hence definitionally equal by Lean's proof irrelevance —
no `propext`, no `Quot.sound`.  This is the engine making the total-category laws hold strictly. -/
theorem CovariantFibration.TotalMorphism.ext {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {fibration : CovariantFibration base univ} {source target : fibration.TotalObject}
    (firstMorphism secondMorphism : fibration.TotalMorphism source target)
    (baseEqual : firstMorphism.baseMorphism = secondMorphism.baseMorphism) :
    firstMorphism = secondMorphism := by
  cases firstMorphism with
  | mk baseOne overOne =>
    cases secondMorphism with
    | mk baseTwo overTwo =>
      cases baseEqual
      rfl

/-- The identity total morphism on `(a, x)` — the identity base morphism, lying over by functoriality of the
lift on identities. -/
def CovariantFibration.TotalMorphism.identity {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {fibration : CovariantFibration base univ} (object : fibration.TotalObject) :
    fibration.TotalMorphism object object where
  baseMorphism := base.identity object.baseObject
  liesOver := congrFun (fibration.liftPreservesIdentity object.baseObject) object.fiberPoint

/-- Composition of total morphisms — compose the base morphisms; the composite lies over by functoriality of the
lift on composites (`liftPreservesComposition`) threaded through the two factors' lies-over witnesses. -/
def CovariantFibration.TotalMorphism.compose {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    {fibration : CovariantFibration base univ} {source middle target : fibration.TotalObject}
    (firstMorphism : fibration.TotalMorphism source middle)
    (secondMorphism : fibration.TotalMorphism middle target) :
    fibration.TotalMorphism source target where
  baseMorphism := base.compose firstMorphism.baseMorphism secondMorphism.baseMorphism
  liesOver :=
    (congrFun (fibration.liftPreservesComposition firstMorphism.baseMorphism secondMorphism.baseMorphism)
        source.fiberPoint).trans
      ((congrArg (fibration.cocartesianLift secondMorphism.baseMorphism) firstMorphism.liesOver).trans
        secondMorphism.liesOver)

/-- ★ **The Grothendieck total category `∫F`.**  Objects are total objects (a base object + a fiber point),
morphisms are total morphisms; the category laws follow from the base category's laws plus `TotalMorphism.ext`
(the lies-over proofs are proof-irrelevant).  Zero-axiom. -/
def CovariantFibration.totalCategory {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) : RawCategory where
  Object := fibration.TotalObject
  Morphism := fun source target => fibration.TotalMorphism source target
  identity := fun object => CovariantFibration.TotalMorphism.identity object
  compose := fun firstMorphism secondMorphism =>
    CovariantFibration.TotalMorphism.compose firstMorphism secondMorphism
  composeAssoc := fun firstMorphism secondMorphism thirdMorphism =>
    CovariantFibration.TotalMorphism.ext _ _
      (base.composeAssoc firstMorphism.baseMorphism secondMorphism.baseMorphism thirdMorphism.baseMorphism)
  identityLeft := fun morphism =>
    CovariantFibration.TotalMorphism.ext _ _ (base.identityLeft morphism.baseMorphism)
  identityRight := fun morphism =>
    CovariantFibration.TotalMorphism.ext _ _ (base.identityRight morphism.baseMorphism)

/-- ★ **The projection opfibration `∫F ⟶ C`.**  Sends a total object to its base object and a total morphism to
its base morphism — a `RawFunctor`, strictly (the functor laws are `rfl`).  This is the covariant fibration as a
genuine map of categories. -/
def CovariantFibration.projection {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) : RawFunctor fibration.totalCategory base where
  mapObject := fun object => object.baseObject
  mapMorphism := fun morphism => morphism.baseMorphism
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-! ## The cocartesian lift and its universal property (initial among lifts) -/

/-- The chosen **cocartesian morphism** lifting a base morphism `u : a ⟶ b` at a fiber point `x` of `a`: the
total morphism `(a, x) ⟶ (b, cocartesianLift u x)` over `u`, lying over by `rfl`.  The opcartesian lift — it
goes FORWARD. -/
def CovariantFibration.cocartesianMorphism {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) {baseSource baseTarget : base.Object}
    (baseMorphism : base.Morphism baseSource baseTarget)
    (fiberPoint : univ.decode (fibration.fiber baseSource)) :
    fibration.TotalMorphism ⟨baseSource, fiberPoint⟩
      ⟨baseTarget, fibration.cocartesianLift baseMorphism fiberPoint⟩ where
  baseMorphism := baseMorphism
  liesOver := rfl

/-- ★ **The cocartesian universal property — existence (weak initiality).**  The chosen lift `χ` of `u` at `x`
is INITIAL among lifts over `u`: for every total object `target`, every continuation `v : b ⟶ target` in the
base, and every total morphism `candidate : (a, x) ⟶ target` whose base morphism FACTORS as `u ; v`, there is a
mediator `(b, cocartesianLift u x) ⟶ target` over `v` with `χ ; mediator = candidate`.  The opcartesian
universal property, at the strict level. -/
theorem CovariantFibration.cocartesianLift_isWeaklyInitial {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} (fibration : CovariantFibration base univ)
    {baseSource baseTarget : base.Object} (baseMorphism : base.Morphism baseSource baseTarget)
    (fiberPoint : univ.decode (fibration.fiber baseSource)) (target : fibration.TotalObject)
    (continuation : base.Morphism baseTarget target.baseObject)
    (candidate : fibration.TotalMorphism ⟨baseSource, fiberPoint⟩ target)
    (factors : candidate.baseMorphism = base.compose baseMorphism continuation) :
    ∃ mediator : fibration.TotalMorphism
        ⟨baseTarget, fibration.cocartesianLift baseMorphism fiberPoint⟩ target,
      mediator.baseMorphism = continuation ∧
        fibration.totalCategory.compose
          (fibration.cocartesianMorphism baseMorphism fiberPoint) mediator = candidate := by
  have liftedFactor :
      fibration.cocartesianLift (base.compose baseMorphism continuation) fiberPoint
        = fibration.cocartesianLift continuation (fibration.cocartesianLift baseMorphism fiberPoint) :=
    congrFun (fibration.liftPreservesComposition baseMorphism continuation) fiberPoint
  have candidateLands :
      fibration.cocartesianLift (base.compose baseMorphism continuation) fiberPoint = target.fiberPoint := by
    rw [← factors]; exact candidate.liesOver
  refine ⟨{ baseMorphism := continuation, liesOver := liftedFactor.symm.trans candidateLands }, rfl, ?_⟩
  exact CovariantFibration.TotalMorphism.ext _ _ factors.symm

/-- ★ **The cocartesian universal property — uniqueness.**  Any two mediators over the same continuation `v`
coincide: their base morphisms are both `v`, hence equal, so `TotalMorphism.ext` (proof irrelevance of the
lies-over witness) identifies them.  The strict uniqueness half of opcartesian initiality. -/
theorem CovariantFibration.cocartesianLift_mediatorUnique {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} {fibration : CovariantFibration base univ}
    {liftedObject target : fibration.TotalObject}
    (firstMediator secondMediator : fibration.TotalMorphism liftedObject target)
    (continuation : base.Morphism liftedObject.baseObject target.baseObject)
    (firstOver : firstMediator.baseMorphism = continuation)
    (secondOver : secondMediator.baseMorphism = continuation) :
    firstMediator = secondMediator :=
  CovariantFibration.TotalMorphism.ext firstMediator secondMediator (firstOver.trans secondOver.symm)

/-! ## Bridge to `context-34`: the lift as a directed hom of the universe -/

/-- Bridge to `ContextDirectedUniverse.lean`: the cocartesian lift along a base morphism, viewed in the directed
universe, is a `context-34` `DirectedCategoryHom` `fiber a ⟶ fiber b` — a single FORWARD morphism (a function),
no `symm`.  Straightening's action on morphisms IS a directed hom of the universe object. -/
def CovariantFibration.liftAsDirectedHom {base : RawCategory.{0, 0}} {univ : DirectedUniverseData}
    (fibration : CovariantFibration base univ) {baseSource baseTarget : base.Object}
    (baseMorphism : base.Morphism baseSource baseTarget) :
    DirectedCategoryHom univ.category (fibration.fiber baseSource) (fibration.fiber baseTarget) where
  forward := fibration.cocartesianLift baseMorphism

/-! ## Canonical witnesses -/

/-- The **constant covariant fibration** over any base, with identity transport: every base object maps to the
chosen code, and every base morphism lifts to the identity function.  The functoriality laws are `rfl`.  A
zero-axiom inhabitant of `CovariantFibration` — the canonical witness that the classification is non-vacuous. -/
def CovariantFibration.constant {base : RawCategory.{0, 0}} {univ : DirectedUniverseData} (code : univ.Code) :
    CovariantFibration base univ where
  fiber := fun _ => code
  cocartesianLift := fun _ => fun fiberPoint => fiberPoint
  liftPreservesIdentity := fun _ => rfl
  liftPreservesComposition := fun _ _ => rfl

/-- ★ **The decidable-classification witness.**  Total morphisms have decidable equality exactly when the base
hom does: the base morphisms are compared by the assumed decider, and the lies-over proofs contribute nothing
(proof irrelevance), so equality of the base morphisms decides equality of the total morphisms.  The directed
mirror of `context-34`'s decidable conversion. -/
instance CovariantFibration.TotalMorphism.instDecidableEq {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} {fibration : CovariantFibration base univ}
    {source target : fibration.TotalObject}
    [decBaseHom : DecidableEq (base.Morphism source.baseObject target.baseObject)] :
    DecidableEq (fibration.TotalMorphism source target) :=
  fun firstMorphism secondMorphism =>
    match decBaseHom firstMorphism.baseMorphism secondMorphism.baseMorphism with
    | isTrue baseEqual => isTrue (CovariantFibration.TotalMorphism.ext _ _ baseEqual)
    | isFalse baseDistinct =>
        isFalse (fun totalEqual => baseDistinct (congrArg (fun morphism => morphism.baseMorphism) totalEqual))

/-! ## Honesty markers -/

/-- **Honesty marker.**  The DIRECTED Grothendieck classification — covariant (cocartesian) fibrations ≃ functors
into the directed universe — is shipped at the STRICT level, with `straighten` / `unstraighten` round-tripping by
`rfl` (structure eta).  `= true`. -/
def fxCovariantFibration_hasStrictGrothendieckClassification : Bool := true

/-- **Honesty marker.**  The Grothendieck total category `∫F`, its projection opfibration, and the COCARTESIAN
(opcartesian) lift's universal property (initial among lifts: existence + uniqueness, strict level) are shipped
and proved.  `= true`. -/
def fxCovariantFibration_hasCocartesianUniversalProperty : Bool := true

/-- **Honesty marker.**  The FULL ∞-cosmos / homotopy-coherent straightening–unstraightening (Riehl–Verity;
Riehl–Shulman synthetic-(∞,1)) — an EQUIVALENCE of `(∞,1)`-categories with coherent naturality — is NOT shipped:
it entails `funext` / `Quot.sound`, the `×type` / type-axis wall the `gen_universeD` directed universe defers.
`= false`. -/
def fxCovariantFibration_hasFullInfinityCosmosStraightening : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Tier0 analog of a Core table-native directed-Grothendieck
row; a Tier0 design-lock cannot import the Core engine, so the classification and the cocartesian universal
property are re-shipped here as strict (1-categorical) constructions.  Gluing the Tier0 and Core forms is
cross-axis `×type`.  `= false`. -/
def fxCovariantFibration_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: the constant fibration round-trips through straighten / unstraighten — the classification, decided by
computation on a concrete inhabitant. -/
theorem CovariantFibration.constant_classifies_smoke {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} (code : univ.Code) :
    CovariantFibration.unstraighten (CovariantFibration.straighten
        (CovariantFibration.constant (base := base) code))
      = CovariantFibration.constant (base := base) code :=
  rfl

/-- Smoke: the chosen cocartesian morphism lifting `u` projects (via `projection`) back to `u` — the lift lies
over its base morphism, by `rfl`. -/
theorem CovariantFibration.cocartesianMorphism_projects_smoke {base : RawCategory.{0, 0}}
    {univ : DirectedUniverseData} (fibration : CovariantFibration base univ)
    {baseSource baseTarget : base.Object} (baseMorphism : base.Morphism baseSource baseTarget)
    (fiberPoint : univ.decode (fibration.fiber baseSource)) :
    (fibration.cocartesianMorphism baseMorphism fiberPoint).baseMorphism = baseMorphism :=
  rfl

end FX1Poly.Tier0
