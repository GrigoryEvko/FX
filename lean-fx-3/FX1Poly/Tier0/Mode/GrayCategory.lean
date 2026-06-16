import FX1Poly.Tier0.Mode.TwoCategoryCore

/-! # mode-5 — the Gray tensor / semistrict 3-category + tricategory coherence (the dim-3 rung)

`mode-1` gave the STRICT 2-category interface (`RawTwoCategory`); `mode-3` added the free 2-cells and the
oriented 3-cell rewrites, but DEFERRED the INTERCHANGE law (the exchange of independent whiskerings) — in a
strict 3-category that exchange is an on-the-nose equation, the convergence crux
(`fxMode_hasInterchangeAndWhiskerFunctoriality`).  `mode-5` is the SEMISTRICT resolution: a GRAY-CATEGORY
(after Gray, Gordon–Power–Street) keeps composition strictly associative/unital but replaces that interchange
EQUATION with a specified INVERTIBLE 3-CELL — the **interchanger** `σ₁ ⇛ σ₂` between the two whisker-orders.
This is the semistrict normal form every tricategory is triequivalent to (the GPS coherence theorem).

## What this file ships (each piece zero-axiom)

  * **`RawTwoCategory.interchangeSource` / `interchangeTarget`** — the two whisker-order 2-cells the interchanger
    mediates: `σ₁ = (α ▷ g) ⊟ (f' ◁ β)` and `σ₂ = (f ◁ β) ⊟ (α ▷ g')`, both of boundary `(f∘g) ⇒ (f'∘g')`
    (cast-free — exactly the parallel pair `mode-3`'s deferred interchange is about).
  * **`RawGrayCategory`** — the semistrict 3-category interface: a base `RawTwoCategory`, a `ThreeCell` family
    (3-cells between PARALLEL 2-cells), identity + vertical composition of 3-cells, and the ★ INTERCHANGER
    `σ₁ ⇛ σ₂` with a two-sided inverse (the two invertibility laws) — an INVERTIBLE 3-cell, the Gray datum.
  * **`locallyDiscreteGrayCategory`** — a genuine `RawGrayCategory` over any `RawCategory`: 3-cells are
    EQUALITIES of 2-cells (which are themselves equalities of 1-cells), so the interchanger is the trivial
    (proof-irrelevant) iso and every Gray law holds by definitional proof irrelevance (`rfl`).  The strict
    3-category seen as a degenerate Gray-category.
  * **`freeModeGrayCategory`** — the free mode 1-category exhibited as a (strict) Gray-category, the mode axis
    reaching dimension 3.

## What is DEFERRED (recorded by `= false` markers)

  * a NON-TRIVIAL interchanger (a genuinely non-identity invertible 3-cell) needs TYPE-valued free 3-cells (the
    dimension-3 polygraph generators) — `mode-6` / `mode-21` (`hasNonTrivialInterchanger = false`).  Here the
    interchanger is proof-irrelevant (the (3,2)-truncation).
  * the GRAY TENSOR PRODUCT `A ⊗_Gray B` of 2-categories as a bifunctor (the monoidal structure on `2Cat` whose
    enrichment IS a Gray-category) — combinatorial, deferred (`hasGrayTensorProduct = false`).
  * the GORDON–POWER–STREET tricategory COHERENCE THEOREM (every tricategory is triequivalent to a
    Gray-category) — the deep coherence result, deferred (`hasTricategoryCoherence = false`).

Zero external dependencies beyond the `mode-1` 2-category core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The interchanger boundary: the two whisker orders -/

/-- The FIRST whisker order `σ₁ = (α ▷ g) ⊟ (f' ◁ β)` — whisker `α : f ⇒ f'` past `g` on the right, then `β`
under `f'` on the left.  A 2-cell `(f∘g) ⇒ (f'∘g')`. -/
def RawTwoCategory.interchangeSource (twoCat : RawTwoCategory)
    {objectA objectB objectC : twoCat.base.Object}
    {oneCellF oneCellFPrime : twoCat.base.Morphism objectA objectB}
    {oneCellG oneCellGPrime : twoCat.base.Morphism objectB objectC}
    (cellAlpha : twoCat.TwoCell oneCellF oneCellFPrime)
    (cellBeta : twoCat.TwoCell oneCellG oneCellGPrime) :
    twoCat.TwoCell (twoCat.base.compose oneCellF oneCellG)
      (twoCat.base.compose oneCellFPrime oneCellGPrime) :=
  twoCat.vcomp (twoCat.whiskerRight oneCellG cellAlpha) (twoCat.whiskerLeft oneCellFPrime cellBeta)

/-- The SECOND whisker order `σ₂ = (f ◁ β) ⊟ (α ▷ g')` — the OTHER order.  Same boundary `(f∘g) ⇒ (f'∘g')`;
in a STRICT 3-category `σ₁ = σ₂` (interchange), in a GRAY-category they are linked by the invertible
interchanger 3-cell. -/
def RawTwoCategory.interchangeTarget (twoCat : RawTwoCategory)
    {objectA objectB objectC : twoCat.base.Object}
    {oneCellF oneCellFPrime : twoCat.base.Morphism objectA objectB}
    {oneCellG oneCellGPrime : twoCat.base.Morphism objectB objectC}
    (cellAlpha : twoCat.TwoCell oneCellF oneCellFPrime)
    (cellBeta : twoCat.TwoCell oneCellG oneCellGPrime) :
    twoCat.TwoCell (twoCat.base.compose oneCellF oneCellG)
      (twoCat.base.compose oneCellFPrime oneCellGPrime) :=
  twoCat.vcomp (twoCat.whiskerLeft oneCellF cellBeta) (twoCat.whiskerRight oneCellGPrime cellAlpha)

/-! ## The semistrict 3-category (Gray-category) interface -/

/-- A **Gray-category** (semistrict 3-category): a base strict 2-category, a `ThreeCell` family of 3-cells
between parallel 2-cells with identity + vertical composition, and the ★ INTERCHANGER — an INVERTIBLE 3-cell
`σ₁ ⇛ σ₂` between the two whisker orders (with a two-sided inverse).  The interchanger replacing the strict
interchange EQUATION by an invertible 3-cell is exactly what makes the structure SEMISTRICT rather than strict.
Naturality of the interchanger and the full Gray coherence (the higher axioms) are deferred with the markers. -/
structure RawGrayCategory where
  /-- The base strict 2-category (0/1/2-cells). -/
  twoCategory : RawTwoCategory
  /-- 3-cells between a PARALLEL pair of 2-cells. -/
  ThreeCell {objectA objectB : twoCategory.base.Object}
    {oneCellF oneCellG : twoCategory.base.Morphism objectA objectB} :
    twoCategory.TwoCell oneCellF oneCellG → twoCategory.TwoCell oneCellF oneCellG → Type
  /-- The identity 3-cell on a 2-cell. -/
  idThree {objectA objectB : twoCategory.base.Object}
    {oneCellF oneCellG : twoCategory.base.Morphism objectA objectB}
    (cell : twoCategory.TwoCell oneCellF oneCellG) : ThreeCell cell cell
  /-- Vertical composition of 3-cells. -/
  vcompThree {objectA objectB : twoCategory.base.Object}
    {oneCellF oneCellG : twoCategory.base.Morphism objectA objectB}
    {cellP cellQ cellR : twoCategory.TwoCell oneCellF oneCellG}
    (threeAlpha : ThreeCell cellP cellQ) (threeBeta : ThreeCell cellQ cellR) : ThreeCell cellP cellR
  /-- ★ The **interchanger** — the 3-cell `σ₁ ⇛ σ₂` mediating the two whisker orders. -/
  interchanger {objectA objectB objectC : twoCategory.base.Object}
    {oneCellF oneCellFPrime : twoCategory.base.Morphism objectA objectB}
    {oneCellG oneCellGPrime : twoCategory.base.Morphism objectB objectC}
    (cellAlpha : twoCategory.TwoCell oneCellF oneCellFPrime)
    (cellBeta : twoCategory.TwoCell oneCellG oneCellGPrime) :
    ThreeCell (twoCategory.interchangeSource cellAlpha cellBeta)
      (twoCategory.interchangeTarget cellAlpha cellBeta)
  /-- The interchanger's inverse `σ₂ ⇛ σ₁` (it is INVERTIBLE — the Gray semistrictness). -/
  interchangerInverse {objectA objectB objectC : twoCategory.base.Object}
    {oneCellF oneCellFPrime : twoCategory.base.Morphism objectA objectB}
    {oneCellG oneCellGPrime : twoCategory.base.Morphism objectB objectC}
    (cellAlpha : twoCategory.TwoCell oneCellF oneCellFPrime)
    (cellBeta : twoCategory.TwoCell oneCellG oneCellGPrime) :
    ThreeCell (twoCategory.interchangeTarget cellAlpha cellBeta)
      (twoCategory.interchangeSource cellAlpha cellBeta)
  /-- Invertibility (one side): interchanger then inverse is the identity 3-cell. -/
  interchanger_leftInverse {objectA objectB objectC : twoCategory.base.Object}
    {oneCellF oneCellFPrime : twoCategory.base.Morphism objectA objectB}
    {oneCellG oneCellGPrime : twoCategory.base.Morphism objectB objectC}
    (cellAlpha : twoCategory.TwoCell oneCellF oneCellFPrime)
    (cellBeta : twoCategory.TwoCell oneCellG oneCellGPrime) :
    vcompThree (interchanger cellAlpha cellBeta) (interchangerInverse cellAlpha cellBeta)
      = idThree (twoCategory.interchangeSource cellAlpha cellBeta)
  /-- Invertibility (other side): inverse then interchanger is the identity 3-cell. -/
  interchanger_rightInverse {objectA objectB objectC : twoCategory.base.Object}
    {oneCellF oneCellFPrime : twoCategory.base.Morphism objectA objectB}
    {oneCellG oneCellGPrime : twoCategory.base.Morphism objectB objectC}
    (cellAlpha : twoCategory.TwoCell oneCellF oneCellFPrime)
    (cellBeta : twoCategory.TwoCell oneCellG oneCellGPrime) :
    vcompThree (interchangerInverse cellAlpha cellBeta) (interchanger cellAlpha cellBeta)
      = idThree (twoCategory.interchangeTarget cellAlpha cellBeta)

/-- ★ The **locally-discrete Gray-category** over any `RawCategory`: 3-cells are EQUALITIES of 2-cells (which
are themselves `PLift` of 1-cell equalities, `mode-1`).  The two whisker orders are equal by definitional proof
irrelevance, so the interchanger is the trivial invertible 3-cell and both invertibility laws are `rfl` — the
strict 3-category as a degenerate Gray-category. -/
def locallyDiscreteGrayCategory (category : RawCategory) : RawGrayCategory where
  twoCategory := locallyDiscreteTwoCategory category
  ThreeCell := fun cellSource cellTarget => PLift (cellSource = cellTarget)
  idThree := fun _ => PLift.up rfl
  vcompThree := fun threeAlpha threeBeta => PLift.up (threeAlpha.down.trans threeBeta.down)
  interchanger := fun _ _ => PLift.up rfl
  interchangerInverse := fun _ _ => PLift.up rfl
  interchanger_leftInverse := fun _ _ => rfl
  interchanger_rightInverse := fun _ _ => rfl

/-- ★ The free mode 1-category, exhibited as a (strict, locally-discrete) Gray-category — the mode axis
reaching dimension 3. -/
def freeModeGrayCategory (graph : ModeGraph) : RawGrayCategory :=
  locallyDiscreteGrayCategory (freeModeCategory graph)

/-- Round-trip: the free mode Gray-category's base 2-category IS the free mode 2-category, definitionally. -/
theorem freeModeGrayCategory_twoCategory (graph : ModeGraph) :
    (freeModeGrayCategory graph).twoCategory = freeModeTwoCategory graph :=
  rfl

/-- Smoke: in a locally-discrete Gray-category the two whisker orders genuinely coincide (the interchanger is
the identity equality) — strict interchange recovered as the degenerate Gray case. -/
theorem locallyDiscreteGrayCategory_interchanger_isRefl (category : RawCategory)
    {objectA objectB objectC : category.Object}
    {oneCellF oneCellFPrime : category.Morphism objectA objectB}
    {oneCellG oneCellGPrime : category.Morphism objectB objectC}
    (cellAlpha : (locallyDiscreteTwoCategory category).TwoCell oneCellF oneCellFPrime)
    (cellBeta : (locallyDiscreteTwoCategory category).TwoCell oneCellG oneCellGPrime) :
    (locallyDiscreteTwoCategory category).interchangeSource cellAlpha cellBeta
      = (locallyDiscreteTwoCategory category).interchangeTarget cellAlpha cellBeta :=
  rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  A NON-TRIVIAL interchanger (a genuinely non-identity invertible 3-cell, the heart of a
proper Gray-category) needs TYPE-valued free 3-cells — the dimension-3 polygraph generators — which are the
weak ω-category structure of `mode-6` / `mode-21`.  The shipped instance has a proof-irrelevant (trivial)
interchanger (the (3,2)-truncation).  `= false`. -/
def fxMode_hasNonTrivialInterchanger : Bool := false

/-- **Honesty marker.**  The GRAY TENSOR PRODUCT `A ⊗_Gray B` of 2-categories as a bifunctor (the monoidal
structure on `2Cat` whose enriched categories ARE Gray-categories) is a combinatorial construction, deferred.
`= false`. -/
def fxMode_hasGrayTensorProduct : Bool := false

/-- **Honesty marker.**  The GORDON–POWER–STREET tricategory COHERENCE THEOREM — every tricategory is
triequivalent to a Gray-category — is the deep coherence result this rung's `RawGrayCategory` is the TARGET of;
its proof is deferred.  `= false`. -/
def fxMode_hasTricategoryCoherence : Bool := false

end FX1Poly.Tier0
