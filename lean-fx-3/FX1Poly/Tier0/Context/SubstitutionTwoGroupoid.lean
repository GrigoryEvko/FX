import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstCategory

/-! # FX1Poly/Tier0/Context/SubstitutionTwoGroupoid — context-20 [substitution ω-groupoid; dim-2 layer]

`context-0..3` built the substitution 1-category `fxBaseSubstCategory` (0-cells = scopes, 1-cells =
`SubstVec`s); `context-17` added the `End(𝒞)` strict 2-category of ENDOFUNCTORS.  `context-20` lands the
DIM-2 HOMOTOPY LAYER of the substitution category ITSELF — the 2-cells between PARALLEL substitutions,
making `fxBaseSubstCategory` a strict (2,1)-category and exhibiting the first rung of its substitution
ω-groupoid.

## What the dim-2 layer IS, honestly

The 1-cells of `fxBaseSubstCategory` are `SubstVec`s — and `SubstVec` is a SET (`RawTerm` is a concrete
inductive with decidable equality, `SubstVec` a product recursion over it).  So the substitution
category's intrinsic 2-cells between parallel 1-cells `σ, τ : a ⟶ b` are exactly their EQUALITIES
`σ = τ`, which assemble into a groupoid (every 2-cell is invertible — `Eq.symm`).  The substitution
category is therefore a strict (2,1)-category, and the genuinely substitution-specific reading is:

  **a 2-cell `σ ⟹ τ` IS a pointwise homotopy of lookups** — `(∀ index, σ.lookup index = τ.lookup index)`
  is equivalent to `σ = τ` (the `SubstVec.ext` extensionality the whole `SubstVec` design rests on).

## What lands here (all zero-axiom)

  * `RawCategory.whiskerLeft` / `whiskerRight` — left/right whiskering of a 2-cell by a 1-cell (the
    action of `compose` on equalities, `congrArg`), generic over any `RawCategory`.
  * `RawCategory.horizontalCompose` — the Godement / horizontal composite of two 2-cells.
  * `RawCategory.whiskerLeft_id` / `whiskerRight_id` / `whiskerLeft_vcomp` / `whiskerRight_vcomp` — the
    whisker functoriality laws (identity + vertical composition).
  * `RawCategory.whisker_exchange` — the two whisker orders agree (the exchange law).
  * `RawCategory.horizontalCompose_eq_whiskers` — `hcomp` decomposes into a whisker pair.
  * `RawCategory.interchange` — ★ THE INTERCHANGE LAW (middle-four): horizontal composition of vertical
    composites is the vertical composite of horizontal composites.  The defining (2,1)-category
    coherence relating dim-1 (`compose`) and dim-2 (`=`).
  * `SubstVec.twoCellOfPointwise` / `pointwiseOfTwoCell` — ★ the substitution-specific characterization:
    a 2-cell IS a pointwise lookup-homotopy (the `ext` ↔ `congrArg` pair).
  * `FxSubstitutionTwoGroupoid` / `fxSubstitutionTwoGroupoid` — the assembled witness (invertibility +
    interchange + the pointwise characterization).
  * `fxSubstitutionTwoGroupoid_higherCellsAreContentful` — the honesty marker (`= false`); see below.

## Honest scope boundary

What is PROVED here is the dim-2 (2,1)-category structure with 2-cells = equalities: whiskering,
horizontal composition, the interchange law, and the pointwise-homotopy characterization.  What is NOT
mechanized here (and is the honest boundary):

  * The 1-TRUNCATION — that the hom-types are SETS, so every higher cell (a 2-cell-between-2-cells, …)
    collapses to a single equality and the substitution ω-groupoid is discrete above dim 2.  This holds
    because `SubstVec` has decidable equality (`RawTerm` is a concrete inductive), whence Hedberg's
    theorem gives UIP — a STANDARD consequence, but not mechanized here (zero-axiom Hedberg for
    `SubstVec` is its own construction; no UIP/Hedberg infrastructure ships yet).  So the marker below
    records the DESIGN fact (the base is set-level), not a theorem proved in this file.
  * The genuinely CONTENTFUL higher cells (non-trivial homotopies / paths that do NOT collapse to
    equality) live at the type / identity layer — the univalent universe object, `Id`-types, transport
    — which is `×type` (`context-30`+ / the type axis), NOT a property of the substitution base.
  * The conversion 2-cells (a 2-cell as a pointwise REDUCTION `σ.lookup i ↝ τ.lookup i`) are the
    reduction-substrate (Core) layer, a separate construction, not the intrinsic equality 2-cells here.

`fxSubstitutionTwoGroupoid_higherCellsAreContentful = false` records the design stance.

Every declaration below is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1Poly.Tier0

open FX1Poly.Core

universe u v

/-! ## The generic equality-2-cell structure over a `RawCategory`

A 2-cell between PARALLEL 1-cells `f, g : a ⟶ b` is an equality `f = g`; vertical composition is
`Eq.trans`, the identity 2-cell is `rfl`, and every 2-cell is invertible via `Eq.symm` — the
(2,1)-category of equalities.  The content below is how this dim-2 layer interacts with dim-1
(`compose`): whiskering, horizontal composition, and the interchange law. -/

/-- **Left whiskering.**  Whisker a 2-cell `cell : f = g` (parallel 1-cells `b ⟶ c`) by a 1-cell
`preMorphism : a ⟶ b` on the left, yielding a 2-cell `preMorphism ; f = preMorphism ; g`. -/
def RawCategory.whiskerLeft (category : RawCategory.{u, v}) {objectA objectB objectC : category.Object}
    (preMorphism : category.Morphism objectA objectB)
    {firstMorphism secondMorphism : category.Morphism objectB objectC}
    (cell : firstMorphism = secondMorphism) :
    category.compose preMorphism firstMorphism = category.compose preMorphism secondMorphism :=
  congrArg (fun morphism => category.compose preMorphism morphism) cell

/-- **Right whiskering.**  Whisker a 2-cell `cell : f = g` (parallel 1-cells `a ⟶ b`) by a 1-cell
`postMorphism : b ⟶ c` on the right, yielding a 2-cell `f ; postMorphism = g ; postMorphism`. -/
def RawCategory.whiskerRight (category : RawCategory.{u, v}) {objectA objectB objectC : category.Object}
    {firstMorphism secondMorphism : category.Morphism objectA objectB}
    (cell : firstMorphism = secondMorphism) (postMorphism : category.Morphism objectB objectC) :
    category.compose firstMorphism postMorphism = category.compose secondMorphism postMorphism :=
  congrArg (fun morphism => category.compose morphism postMorphism) cell

/-- **Horizontal (Godement) composition** of two 2-cells `cellLeft : f = f'` and `cellRight : g = g'`,
yielding `f ; g = f' ; g'`. -/
def RawCategory.horizontalCompose (category : RawCategory.{u, v}) {objectA objectB objectC : category.Object}
    {firstMorphism firstMorphism' : category.Morphism objectA objectB}
    {secondMorphism secondMorphism' : category.Morphism objectB objectC}
    (cellLeft : firstMorphism = firstMorphism') (cellRight : secondMorphism = secondMorphism') :
    category.compose firstMorphism secondMorphism = category.compose firstMorphism' secondMorphism' := by
  cases cellLeft; cases cellRight; rfl

/-- Left whiskering preserves the identity 2-cell. -/
theorem RawCategory.whiskerLeft_id (category : RawCategory.{u, v}) {objectA objectB objectC : category.Object}
    (preMorphism : category.Morphism objectA objectB) (morphism : category.Morphism objectB objectC) :
    category.whiskerLeft preMorphism (rfl : morphism = morphism) = rfl := rfl

/-- Right whiskering preserves the identity 2-cell. -/
theorem RawCategory.whiskerRight_id (category : RawCategory.{u, v}) {objectA objectB objectC : category.Object}
    (morphism : category.Morphism objectA objectB) (postMorphism : category.Morphism objectB objectC) :
    category.whiskerRight (rfl : morphism = morphism) postMorphism = rfl := rfl

/-- Left whiskering preserves vertical composition. -/
theorem RawCategory.whiskerLeft_vcomp (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object} (preMorphism : category.Morphism objectA objectB)
    {firstMorphism secondMorphism thirdMorphism : category.Morphism objectB objectC}
    (firstCell : firstMorphism = secondMorphism) (secondCell : secondMorphism = thirdMorphism) :
    category.whiskerLeft preMorphism (firstCell.trans secondCell)
      = (category.whiskerLeft preMorphism firstCell).trans
          (category.whiskerLeft preMorphism secondCell) := by
  cases firstCell; cases secondCell; rfl

/-- Right whiskering preserves vertical composition. -/
theorem RawCategory.whiskerRight_vcomp (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object}
    {firstMorphism secondMorphism thirdMorphism : category.Morphism objectA objectB}
    (firstCell : firstMorphism = secondMorphism) (secondCell : secondMorphism = thirdMorphism)
    (postMorphism : category.Morphism objectB objectC) :
    category.whiskerRight (firstCell.trans secondCell) postMorphism
      = (category.whiskerRight firstCell postMorphism).trans
          (category.whiskerRight secondCell postMorphism) := by
  cases firstCell; cases secondCell; rfl

/-- **The exchange law.**  Right-whiskering then left-whiskering equals left-whiskering then
right-whiskering — the two ways of sliding two 2-cells past each other agree. -/
theorem RawCategory.whisker_exchange (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object}
    {firstMorphism firstMorphism' : category.Morphism objectA objectB}
    {secondMorphism secondMorphism' : category.Morphism objectB objectC}
    (cellLeft : firstMorphism = firstMorphism') (cellRight : secondMorphism = secondMorphism') :
    (category.whiskerRight cellLeft secondMorphism).trans
        (category.whiskerLeft firstMorphism' cellRight)
      = (category.whiskerLeft firstMorphism cellRight).trans
          (category.whiskerRight cellLeft secondMorphism') := by
  cases cellLeft; cases cellRight; rfl

/-- Horizontal composition decomposes into a whisker pair (right-then-left). -/
theorem RawCategory.horizontalCompose_eq_whiskers (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object}
    {firstMorphism firstMorphism' : category.Morphism objectA objectB}
    {secondMorphism secondMorphism' : category.Morphism objectB objectC}
    (cellLeft : firstMorphism = firstMorphism') (cellRight : secondMorphism = secondMorphism') :
    category.horizontalCompose cellLeft cellRight
      = (category.whiskerRight cellLeft secondMorphism).trans
          (category.whiskerLeft firstMorphism' cellRight) := by
  cases cellLeft; cases cellRight; rfl

/-- **The interchange law** at the (2,1)-truncation.  Horizontal composition of vertical composites is the
vertical composite of horizontal composites.  HONESTY: at this truncation the 2-cells are EQUALITIES of 1-cells
(`Prop`), so this — and the whisker laws above — hold by definitional PROOF IRRELEVANCE (each is
`Subsingleton.elim`-trivial); there is no genuine dim-1/dim-2 interaction to verify here.  The contentful,
non-proof-irrelevant interchange is `RawEndofunctorTransformation.interchange_component` (natural-transformation
components are real morphisms).  Kept as the named law completing the (2,1)-coherence interface. -/
theorem RawCategory.interchange (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object}
    {f f' f'' : category.Morphism objectA objectB} {g g' g'' : category.Morphism objectB objectC}
    (leftFirst : f = f') (leftSecond : f' = f'')
    (rightFirst : g = g') (rightSecond : g' = g'') :
    category.horizontalCompose (leftFirst.trans leftSecond) (rightFirst.trans rightSecond)
      = (category.horizontalCompose leftFirst rightFirst).trans
          (category.horizontalCompose leftSecond rightSecond) := by
  cases leftFirst; cases leftSecond; cases rightFirst; cases rightSecond; rfl

/-! ## The substitution-specific characterization: a 2-cell is a pointwise lookup-homotopy -/

/-- ★ **A pointwise lookup-homotopy IS a 2-cell.**  If two substitutions agree on every variable's
image, they are equal — a 2-cell `sigma ⟹ tau` in the substitution category (this is exactly
`SubstVec.ext`, the extensionality the `SubstVec` representation was built to provide). -/
def SubstVec.twoCellOfPointwise {target source : Nat} {sigma tau : SubstVec target source}
    (pointwise : ∀ index : Fin source, sigma.lookup index = tau.lookup index) : sigma = tau :=
  SubstVec.ext sigma tau pointwise

/-- ★ **A 2-cell IS a pointwise lookup-homotopy.**  Every 2-cell `sigma ⟹ tau` restricts to an equality
of images at each variable — the converse of `twoCellOfPointwise`, exhibiting the dim-2 layer of the
substitution category as the pointwise homotopies of lookups. -/
def SubstVec.pointwiseOfTwoCell {target source : Nat} {sigma tau : SubstVec target source}
    (cell : sigma = tau) (index : Fin source) : sigma.lookup index = tau.lookup index :=
  congrArg (fun vec => vec.lookup index) cell

/-! ### REVISIT — the round-trip (`twoCellOfPointwise` / `pointwiseOfTwoCell` form an equivalence)

These two directions are NOT assembled into an equivalence here, and deliberately so: the forward
round-trip `pointwiseOfTwoCell ∘ twoCellOfPointwise = id` is an equality of `(∀ index, …)`-FUNCTIONS,
which at this META level needs Lean's `funext` (derived from `Quot.sound`, excluded by the zero-axiom
gate); the backward round-trip needs UIP on the hom-type.  This is NOT patchable at the meta level —
Lean is anti-univalent (definitional `Prop`-irrelevance + UIP), so Voevodsky's `ua ⟹ funext` does not
apply to Lean's `=`.

The genuine resolution is one level down: once the dim-2 layer is RE-EXPRESSED at the type / identity
layer (where these equalities become contentful `Id` of the kernel) AND the kernel gains funext from
DEFINITIONAL UNIVALENCE (`ua ⟹ funext` run at the kernel universe — ideally a definitional `Conv` rule),
the round-trip becomes an OBJECT statement that object-funext closes.  Revisit this characterization THEN,
as the identity-layer reincarnation — do not retrofit the Lean-meta proof above. -/

/-! ## The assembled witness -/

/-- The FX substitution category carries the dim-2 homotopy layer: every 2-cell is invertible (the
(2,1)-groupoid), the interchange law holds, and 2-cells are exactly pointwise lookup-homotopies. -/
structure FxSubstitutionTwoGroupoid where
  /-- Every 2-cell (equality of parallel substitutions) is invertible — the (2,1)-groupoid structure. -/
  twoCellsInvertible : ∀ {objectA objectB : Nat}
    {firstMorphism secondMorphism : fxBaseSubstCategory.Morphism objectA objectB},
    firstMorphism = secondMorphism → secondMorphism = firstMorphism
  /-- ★ The interchange law for the substitution category. -/
  interchange : ∀ {objectA objectB objectC : Nat}
    {f f' f'' : fxBaseSubstCategory.Morphism objectA objectB}
    {g g' g'' : fxBaseSubstCategory.Morphism objectB objectC}
    (leftFirst : f = f') (leftSecond : f' = f'')
    (rightFirst : g = g') (rightSecond : g' = g''),
    fxBaseSubstCategory.horizontalCompose (leftFirst.trans leftSecond) (rightFirst.trans rightSecond)
      = (fxBaseSubstCategory.horizontalCompose leftFirst rightFirst).trans
          (fxBaseSubstCategory.horizontalCompose leftSecond rightSecond)
  /-- ★ A 2-cell is a pointwise lookup-homotopy (the substitution-specific dim-2 characterization). -/
  pointwiseCharacterization : ∀ {target source : Nat} {sigma tau : SubstVec target source},
    (∀ index : Fin source, sigma.lookup index = tau.lookup index) → sigma = tau

/-- ★ The FX substitution category's dim-2 homotopy witness. -/
def fxSubstitutionTwoGroupoid : FxSubstitutionTwoGroupoid where
  twoCellsInvertible := fun cell => cell.symm
  interchange := fun leftFirst leftSecond rightFirst rightSecond =>
    fxBaseSubstCategory.interchange leftFirst leftSecond rightFirst rightSecond
  pointwiseCharacterization := fun pointwise => SubstVec.twoCellOfPointwise pointwise

/-- **Honesty marker.**  The dim-2 layer shipped here is STRICT: 2-cells are equalities (the equality
(2,1)-groupoid).  The base is set-level (so the ω-groupoid is 1-truncated, every higher cell discrete) —
a DESIGN fact following from `SubstVec`'s decidable equality via Hedberg, recorded here but not
mechanized (see the honest-boundary note above).  Genuinely contentful higher homotopies (paths that do
not collapse to equality) are the type / identity layer (`×type`: the univalent universe + `Id`-types),
NOT a property of the substitution base.  The value is `false`. -/
def fxSubstitutionTwoGroupoid_higherCellsAreContentful : Bool := false

/-! ## Smoke: whiskering the identity 2-cell -/

/-- Smoke: left-whiskering the identity 2-cell on the identity substitution is the identity 2-cell. -/
theorem fxSubstitutionTwoGroupoid_whiskerLeft_id_smoke {scope : Nat}
    (preMorphism : fxBaseSubstCategory.Morphism scope scope) :
    fxBaseSubstCategory.whiskerLeft preMorphism
        (rfl : fxBaseSubstCategory.identity scope = fxBaseSubstCategory.identity scope) = rfl :=
  rfl

end FX1Poly.Tier0
