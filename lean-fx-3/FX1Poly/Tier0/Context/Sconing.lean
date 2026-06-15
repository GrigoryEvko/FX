import FX1Poly.Tier0.Context.Strictification
import FX1Poly.Tier0.Context.RenamingInclusion

/-! # context-11 — synthetic Tait computability over the context base + relative induction

`context-11` is the SCONING / STC rung: Sterling's Synthetic Tait Computability (Sterling 2021;
Sterling–Angiuli; Bocquet–Kaposi–Sattler relative induction).  Classical Tait computability proves
normalization / canonicity by the method of COMPUTABILITY PREDICATES (reducibility candidates / logical
relations); STC reframes it categorically — a computability structure is just an object of the ARTIN
GLUING (the SCONE), and the fundamental lemma becomes the unique map out of the initial model (relative
induction).

The CONTEXT-SIDE residue, delivered here in full strength: the SCONE of the FX context base, realized as a
genuine category, with its display functor, its cartesian fibration structure, and the relative-induction
interface.  We glue along the TERM PRESHEAF `Tm` (`context-7`'s `reindexTerm` + its strict functor laws),
so the scone is the category of **computability predicates over terms, stable under substitution** — which
IS the reducibility-candidate / Tait-computability structure (hence the rung's name).

## The zero-axiom move (the wall `context-20` documented, sidestepped)

A scone morphism's predicate component is, in general, a function — proving the gluing's category laws would
need `funext` (= `Quot.sound`), exactly the wall the substitution 2-groupoid hit.  We sidestep it by taking
PROP-VALUED predicates (the SUB-scone): a computability structure is a `predicate → Prop`, and a morphism
carries only its base morphism plus a PROOF (a `Prop`) of preservation.  Two scone morphisms are then equal
IFF their base morphisms are — the preservation proofs are equal by Lean's DEFINITIONAL proof irrelevance,
no axiom.  So the gluing's three category laws reduce to the base category's laws (`SubsconeHom.ext`).

## What lands here (all zero-axiom)

  * `CovariantPointsFunctor` — a functor `category → Type` (pointwise identity/composition laws, so no
    `funext`), the thing the scone glues along;
  * `Subscone` / `SubsconeObject` / `SubsconeHom` / `SubsconeHom.ext` — ★ the Artin gluing as a genuine
    `RawCategory` (the three laws via the base + Prop-irrelevance);
  * `subsconeProjection` — the display functor `Subscone → category` (forget the predicate);
  * `subsconeReindex` / `subsconeCartesianHom` — ★ reindexing of computability structures along a base
    morphism + the cartesian lift, exhibiting the projection as a SPLIT FIBRATION (the substrate of
    relative induction: a logical relation is a displayed object that reindexes);
  * `ConvComputabilityModel` / `.sectionFunctor` / `.projection_section_*` — ★ a displayed computability
    model (a predicate per context, stable under substitution) IS a SECTION of the display functor; this is
    the relative-induction interface (a map out of the base into the scone splitting the projection);
  * `trivialComputabilityModel` — the terminal (`True`) computability model, the inhabitant witnessing the
    interface is realizable;
  * `fxTermPoints` — the term presheaf `Tm` as a `CovariantPointsFunctor` on `fxBaseSubstCategory`
    (`onObject = RawTerm`, `onMorphism = reindexTerm`, laws = `context-7`'s `reindexTerm_identity/compose`);
  * `fxReducibilityScone` — ★ the concrete Tait-computability scone over the FX context base;
  * `FxSconing` / `fxSconing` — the assembled witness;
  * `fxSconing_hasProofRelevantComputability` / `fxSconing_hasFundamentalTheorem` — the honesty markers
    (`= false`); see the deferral note;
  * `fxSconing_projection_section_smoke` — the section splits the display functor on the nose.

## SHIPPED vs DEFERRED

SHIPPED (context-side, zero-axiom): the scone is a genuine category; the display functor; the split
fibration (reindexing of computability structures); the relative-induction interface (displayed models =
sections) with the trivial model as inhabitant.  Built on `context-7`'s strict `Tm` presheaf.

DEFERRED (honestly NOT here, recorded by the `= false` markers):
  * PROOF-RELEVANT computability (`Set`/`Type`-valued structures — normal forms AS DATA, not a mere
    predicate) needs `funext` for the gluing's laws OR a `SubstVec`-style extensional representation;
    `×type+term` / a future extensional rep.  We ship the PROP-valued logical-predicate fragment.
  * The FUNDAMENTAL THEOREM (every well-typed term is computable) and the resulting NORMALIZATION /
    CANONICITY are the unique section OUT OF THE INITIAL (syntactic) model — that initiality lives on the
    type+term axes (`×type+term`), so it is the joint sconing of `fib-6`.  Here the only context-side
    inhabitant of the relative-induction interface is the trivial model.

The dual CANONICITY scone — gluing along `context-18`'s GLOBAL SECTIONS functor `globalSections`
(`Hom_𝒞(1, −)`, contravariant on `fxBaseSubstCategory`) instead of the covariant `Tm` — is the same
Prop-irrelevance machinery over `𝒞^op`; it is the natural sibling and is not instantiated here (this rung
fixes the covariant Tait scone, which the rung's name names).

Zero external dependencies.  Raw Lean 4 + Init only.  No `funext` (Prop-irrelevance does the work).
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The functor the scone glues along -/

/-- **A covariant points functor** `category → Type`.  The data the Artin gluing needs: a set of "points"
for each object and a functorial reindexing of points along morphisms.  The identity/composition laws are
stated POINTWISE (on a point `x`), so they carry no `funext` obligation — exactly what lets the `Tm`
presheaf (`reindexTerm`, whose laws `context-7` proved pointwise) instantiate it. -/
structure CovariantPointsFunctor (category : RawCategory.{0, 0}) where
  /-- The points of an object (the carrier the computability predicate refines). -/
  onObject : category.Object → Type
  /-- Reindexing a point along a morphism (the functorial action). -/
  onMorphism : {objectA objectB : category.Object} →
    category.Morphism objectA objectB → onObject objectA → onObject objectB
  /-- Reindexing along the identity is the identity (pointwise — no `funext`). -/
  mapId : ∀ {objectA : category.Object} (point : onObject objectA),
    onMorphism (category.identity objectA) point = point
  /-- Reindexing along a composite is the composite of reindexings (pointwise — no `funext`). -/
  mapComp : ∀ {objectA objectB objectC : category.Object}
    (morphismF : category.Morphism objectA objectB) (morphismG : category.Morphism objectB objectC)
    (point : onObject objectA),
    onMorphism (category.compose morphismF morphismG) point
      = onMorphism morphismG (onMorphism morphismF point)

/-! ## The Artin gluing (scone) as a category -/

/-- **A computability structure** — an object of the scone: a base object together with a PROP-VALUED
predicate on its points (a logical predicate / reducibility candidate). -/
structure SubsconeObject (category : RawCategory.{0, 0}) (points : CovariantPointsFunctor category) where
  /-- The underlying base object. -/
  base : category.Object
  /-- The computability predicate on its points. -/
  predicate : points.onObject base → Prop

/-- **A morphism of computability structures** — a base morphism that PRESERVES the predicate (if a point
is computable, its reindex is).  The preservation is a `Prop`; that is what makes morphism equality reduce
to base-morphism equality (Prop-irrelevance), keeping the gluing zero-axiom. -/
structure SubsconeHom {category : RawCategory.{0, 0}} {points : CovariantPointsFunctor category}
    (source target : SubsconeObject category points) where
  /-- The underlying base morphism. -/
  baseMor : category.Morphism source.base target.base
  /-- It preserves computability: a computable point maps to a computable point. -/
  preserves : ∀ (point : points.onObject source.base),
    source.predicate point → target.predicate (points.onMorphism baseMor point)

/-- **Scone morphisms are determined by their base morphism.**  The preservation witness is a `Prop`, so it
is definitionally irrelevant: two scone morphisms with equal base morphisms are equal.  This is the engine
that makes the gluing's category laws follow from the base category's laws WITHOUT `funext`. -/
theorem SubsconeHom.ext {category : RawCategory.{0, 0}} {points : CovariantPointsFunctor category}
    {source target : SubsconeObject category points} {firstHom secondHom : SubsconeHom source target}
    (hBaseMorEq : firstHom.baseMor = secondHom.baseMor) : firstHom = secondHom := by
  cases firstHom with
  | mk firstBaseMor firstPreserves =>
    cases secondHom with
    | mk secondBaseMor secondPreserves =>
      cases hBaseMorEq
      rfl

/-- ★ **The scone (Artin gluing) of a category along a points functor**, as a genuine `RawCategory`.
Objects are computability structures; morphisms are predicate-preserving base morphisms; the three category
laws are the base category's laws transported through `SubsconeHom.ext` (Prop-irrelevance), so the whole
construction is zero-axiom.  This is the synthetic home of logical relations / Tait computability. -/
def Subscone (category : RawCategory.{0, 0}) (points : CovariantPointsFunctor category) :
    RawCategory.{0, 0} where
  Object := SubsconeObject category points
  Morphism := fun source target => SubsconeHom source target
  identity := fun object =>
    { baseMor := category.identity object.base
      preserves := fun point isComputable => (points.mapId point).symm ▸ isComputable }
  compose := fun firstHom secondHom =>
    { baseMor := category.compose firstHom.baseMor secondHom.baseMor
      preserves := fun point isComputable =>
        (points.mapComp firstHom.baseMor secondHom.baseMor point).symm ▸
          secondHom.preserves _ (firstHom.preserves point isComputable) }
  composeAssoc := fun firstHom secondHom thirdHom =>
    SubsconeHom.ext (category.composeAssoc firstHom.baseMor secondHom.baseMor thirdHom.baseMor)
  identityLeft := fun morphism => SubsconeHom.ext (category.identityLeft morphism.baseMor)
  identityRight := fun morphism => SubsconeHom.ext (category.identityRight morphism.baseMor)

/-! ## The display functor -/

/-- **The display / projection functor** `Subscone → category` — forget the predicate, keep the base.  Its
functor laws hold definitionally (`rfl`): identity and composition in the scone are identity and composition
of base morphisms.  This is the display map whose fibers are the computability structures. -/
def subsconeProjection (category : RawCategory.{0, 0}) (points : CovariantPointsFunctor category) :
    RawFunctor (Subscone category points) category where
  mapObject := fun object => object.base
  mapMorphism := fun morphism => morphism.baseMor
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-! ## The split fibration: reindexing computability structures (the relative-induction substrate) -/

/-- **Reindexing a computability structure along a base morphism** — the cartesian lift's domain.  Pull a
target predicate `Q` back along `baseMor : A ⟶ target.base` to the predicate on `A` that holds of a point
exactly when its reindex satisfies `Q`.  This is how a logical relation transports along substitution. -/
def subsconeReindex {category : RawCategory.{0, 0}} {points : CovariantPointsFunctor category}
    {sourceBase : category.Object} (target : SubsconeObject category points)
    (baseMor : category.Morphism sourceBase target.base) : SubsconeObject category points where
  base := sourceBase
  predicate := fun point => target.predicate (points.onMorphism baseMor point)

/-- ★ **The cartesian lift** — `baseMor` lifts to a scone morphism out of the reindexed structure.
Preservation holds DEFINITIONALLY: the reindexed predicate IS "the image satisfies the target predicate".
This exhibits `subsconeProjection` as a split (cloven) fibration — the reindexing of computability
structures is functorial, which is precisely the structure relative induction reindexes over. -/
def subsconeCartesianHom {category : RawCategory.{0, 0}} {points : CovariantPointsFunctor category}
    {sourceBase : category.Object} (target : SubsconeObject category points)
    (baseMor : category.Morphism sourceBase target.base) :
    SubsconeHom (subsconeReindex target baseMor) target where
  baseMor := baseMor
  preserves := fun _ isComputable => isComputable

/-! ## Relative induction: displayed computability models are sections of the display functor -/

/-- **A displayed computability model** over the base — a computability predicate for every object, STABLE
under reindexing along every morphism.  This is exactly a SECTION of the display functor (`.sectionFunctor`
below): the synthetic form of "a logical relation over the whole syntax".  The relative-induction principle
(Bocquet–Kaposi–Sattler) says the INITIAL model has a unique section into any such displayed model — the
existence half lives on the type+term axes (`×type+term`); here we ship the interface and its splitting. -/
structure ConvComputabilityModel (category : RawCategory.{0, 0})
    (points : CovariantPointsFunctor category) where
  /-- The computability predicate at each object. -/
  predicate : (object : category.Object) → points.onObject object → Prop
  /-- Stability: a computable point reindexes to a computable point (the section's functoriality). -/
  stable : ∀ {objectA objectB : category.Object} (morphism : category.Morphism objectA objectB)
    (point : points.onObject objectA),
    predicate objectA point → predicate objectB (points.onMorphism morphism point)

/-- ★ **A displayed computability model IS a section of the display functor.**  It maps each base object to
its computability structure and each base morphism to the same morphism carrying the stability witness; the
functor laws hold by `SubsconeHom.ext rfl`.  Composing with `subsconeProjection` recovers the identity
(`projection_section_*` below) — so this is a genuine section, the relative-induction map. -/
def ConvComputabilityModel.sectionFunctor {category : RawCategory.{0, 0}}
    {points : CovariantPointsFunctor category} (model : ConvComputabilityModel category points) :
    RawFunctor category (Subscone category points) where
  mapObject := fun object => { base := object, predicate := model.predicate object }
  mapMorphism := fun morphism =>
    { baseMor := morphism, preserves := fun point isComputable => model.stable morphism point isComputable }
  preservesIdentity := fun _ => SubsconeHom.ext rfl
  preservesComposition := fun _ _ => SubsconeHom.ext rfl

/-- The section splits the display functor on objects (`projection ∘ section = id`). -/
theorem ConvComputabilityModel.projection_section_object {category : RawCategory.{0, 0}}
    {points : CovariantPointsFunctor category} (model : ConvComputabilityModel category points)
    (object : category.Object) :
    (subsconeProjection category points).mapObject (model.sectionFunctor.mapObject object) = object :=
  rfl

/-- The section splits the display functor on morphisms (`projection ∘ section = id`). -/
theorem ConvComputabilityModel.projection_section_morphism {category : RawCategory.{0, 0}}
    {points : CovariantPointsFunctor category} (model : ConvComputabilityModel category points)
    {objectA objectB : category.Object} (morphism : category.Morphism objectA objectB) :
    (subsconeProjection category points).mapMorphism (model.sectionFunctor.mapMorphism morphism)
      = morphism :=
  rfl

/-- **The terminal (trivial) computability model** — every point is computable (`True`).  The inhabitant
witnessing the relative-induction interface is realizable; the CONTENTFUL models (capturing normalization /
canonicity) are the fundamental theorem, deferred to `fib-6` (`×type+term`). -/
def trivialComputabilityModel (category : RawCategory.{0, 0}) (points : CovariantPointsFunctor category) :
    ConvComputabilityModel category points where
  predicate := fun _ _ => True
  stable := fun _ _ _ => True.intro

/-! ## The concrete Tait-computability scone over the FX context base -/

/-- **The term presheaf `Tm` as the points functor.**  `onObject = RawTerm`, `onMorphism = reindexTerm`
(substitution), and the functor laws ARE `context-7`'s strict `reindexTerm_identity` / `reindexTerm_compose`
(`Tm` shown split).  So the scone glued along this is the category of computability predicates over OPEN
TERMS, stable under substitution — the reducibility-candidate structure. -/
def fxTermPoints : CovariantPointsFunctor fxBaseSubstCategory where
  onObject := fun scope => RawTerm scope
  onMorphism := fun substitution term => SubstVec.reindexTerm substitution term
  mapId := fun term => SubstVec.reindexTerm_identity term
  mapComp := fun firstVec secondVec term => SubstVec.reindexTerm_compose firstVec secondVec term

/-- ★ **The Tait-computability scone over the FX context base** — the Artin gluing of `fxBaseSubstCategory`
along the term presheaf `Tm`.  Its objects are reducibility candidates (substitution-stable predicates on
terms); its display functor projects to contexts; it is a split fibration.  This is "synthetic Tait
computability over the context base", realized as a genuine zero-axiom category. -/
def fxReducibilityScone : RawCategory.{0, 0} := Subscone fxBaseSubstCategory fxTermPoints

/-! ## The assembled witness + honesty markers -/

/-- **The FX context base HAS a synthetic-Tait-computability scone**, gathered as one citable object: the
points functor (`Tm`), the scone category, its display functor, the cartesian/fibration reindexing, and the
relative-induction interface inhabited by the trivial computability model. -/
structure FxSconing where
  /-- The functor the scone glues along — the term presheaf `Tm`. -/
  pointsFunctor : CovariantPointsFunctor fxBaseSubstCategory
  /-- The scone (the Tait-computability category). -/
  scone : RawCategory.{0, 0}
  /-- The display functor `scone → context base`. -/
  display : RawFunctor scone fxBaseSubstCategory
  /-- The relative-induction interface is inhabited (the trivial displayed model). -/
  relativeInductionInhabited : ConvComputabilityModel fxBaseSubstCategory pointsFunctor

/-- ★ The assembled `context-11` witness over the FX context base. -/
def fxSconing : FxSconing where
  pointsFunctor := fxTermPoints
  scone := fxReducibilityScone
  display := subsconeProjection fxBaseSubstCategory fxTermPoints
  relativeInductionInhabited := trivialComputabilityModel fxBaseSubstCategory fxTermPoints

/-- **Honesty marker.**  Computability structures here are PROP-VALUED (logical predicates / reducibility
candidates).  PROOF-RELEVANT computability — `Set`/`Type`-valued structures carrying normal forms AS DATA —
would make the gluing's morphism equality a function equality, needing `funext` (= `Quot.sound`) or a
`SubstVec`-style extensional representation; that is deferred (`×type+term` / a future extensional rep).
`= false` records that proof-relevant computability is not shipped here. -/
def fxSconing_hasProofRelevantComputability : Bool := false

/-- **Honesty marker.**  The relative-induction INTERFACE is shipped (displayed models = sections), but the
CONTENTFUL section — the FUNDAMENTAL THEOREM that every well-typed term is computable, hence normalization /
canonicity — is the unique map out of the INITIAL (syntactic) model, whose initiality lives on the type+term
axes (`×type+term`, the joint sconing of `fib-6`).  The only context-side inhabitant here is the trivial
model.  `= false` records that the fundamental theorem is not shipped here. -/
def fxSconing_hasFundamentalTheorem : Bool := false

/-! ## Smoke: the relative-induction section splits the display functor -/

/-- Smoke: the trivial computability model's section, post-composed with the display functor, recovers the
context on the nose (`projection ∘ section = id` at every context) — the section property of relative
induction. -/
theorem fxSconing_projection_section_smoke (scope : Nat) :
    (subsconeProjection fxBaseSubstCategory fxTermPoints).mapObject
        ((trivialComputabilityModel fxBaseSubstCategory fxTermPoints).sectionFunctor.mapObject scope)
      = scope :=
  rfl

end FX1Poly.Tier0
