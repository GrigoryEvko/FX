import FX1Poly.Polygraph.Rewriting.Coherence.SquierCoherence

/-! # Axis/Term — the free strict ω-category on the term polygraph + the Gray tensor (term-17)

The term-axis mirror of `mode-5` (the Gray / semistrict 3-category).  Where `mode-5` builds a
`RawGrayCategory` over the mode-1 `RawTwoCategory`, the term axis already carries a genuine
PROOF-RELEVANT rewriting 2-category from `term-4` (`Rewrite/SquierCoherence.lean`): the 1-cells are
`RewritePath` (reduction sequences as DATA, with `comp` associative + unital), and the 2-cells are
`RewriteHomotopy` (the Squier diamonds generate the homotopy relation on parallel paths).  This file
ships the two genuine pieces of the free STRICT ω-category on that polygraph (each zero-axiom):

  * **The free-category universal property at dimension 1.**  `RewritePath.foldMap` is the unique
    structure-preserving extension of a generator-map `onStep` to all reduction paths — the recursor
    of the free category on the step graph.  `foldMap_comp` is FUNCTORIALITY (★ — it sends path
    composition to target composition) and `foldMap_unique` is the UNIQUENESS half of the universal
    property (★ — any composition-respecting map IS the fold).  This is the proof-RELEVANT free
    category; `term-2`'s `ReflTransClosure.mediate` was only the thin (`Prop`-truncated) shadow.
  * **Strict interchange at dimension 2.**  `rewriteInterchange_strict` (★) — the two whisker orders
    of a horizontal composite of 2-cells (`interchangeWhiskerSource` via `α` then `β`,
    `interchangeWhiskerTarget` via `β` then `α`) agree ON THE NOSE.  Because `RewriteHomotopy` is
    thin (proof-irrelevant), interchange holds strictly, so this exhibits the free STRICT 2-category
    — the Gray interchanger degenerates to the identity (the locally-discrete / strict case, exactly
    as `mode-5`'s `locallyDiscreteGrayCategory` had its interchanger be `refl`).

## Honest scope

Shipped: the free-category UP (existence as `foldMap`, functoriality, uniqueness) + the identity-functor
round-trip witness (`foldMap_id`) + the strict interchange law at dimension 2.  DEFERRED (mirroring
`mode-5`'s three `false` markers `fxMode_hasGrayTensorProduct` / `fxMode_hasTricategoryCoherence` /
`fxMode_hasNonTrivialInterchanger`): the genuine Gray TENSOR PRODUCT bifunctor `⊗` of two ω-categories
with its NON-trivial coherent interchange isomorphism, and the tricategory coherence theorem — both
need Type-valued (non-thin) higher cells, which the thin `RewriteHomotopy` layer does not provide.

## Zero-axiom verification

`foldMap` is structural recursion on `RewritePath`; `foldMap_comp`/`foldMap_unique`/`foldMap_id` are
structural induction on the path using `term-4`'s `nil_comp`/`cons_comp` laws + the supplied
associativity/left-unit hypotheses; `rewriteInterchange_strict` is `rfl` (definitional proof
irrelevance on the thin `RewriteHomotopy` `Prop`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditAxisTermFreeStrictOmega.lean`.
-/

namespace FX1Poly.Core

variable {Carrier : Type}

/-! ## The free category on the step graph — the dimension-1 universal property -/

/-- The **free-category recursor**: extend a generator-map `onStep` (sending each `Step` to a target
1-cell) to ALL reduction paths, sending `nil` to the target identity and `cons` to target
composition.  This is the action-on-morphisms of the unique functor out of the free category on the
step graph. -/
def RewritePath.foldMap {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
    (idTarget : {point : Carrier} → Target point point)
    (compTarget : {first second third : Carrier} →
      Target first second → Target second third → Target first third)
    (onStep : {source target : Carrier} → Step source target → Target source target) :
    {source target : Carrier} → RewritePath Step source target → Target source target
  | _, _, .nil => idTarget
  | _, _, .cons step rest => compTarget (onStep step) (RewritePath.foldMap idTarget compTarget onStep rest)

/-- `foldMap` sends the empty path to the target identity (the unit-preservation half of functor-hood). -/
theorem RewritePath.foldMap_nil {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
    (idTarget : {point : Carrier} → Target point point)
    (compTarget : {first second third : Carrier} →
      Target first second → Target second third → Target first third)
    (onStep : {source target : Carrier} → Step source target → Target source target)
    {point : Carrier} :
    RewritePath.foldMap idTarget compTarget onStep (RewritePath.nil (Step := Step) (point := point))
      = idTarget := rfl

/-- `foldMap` of a single-step path is `onStep` of that step, post-composed with the identity. -/
theorem RewritePath.foldMap_single {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
    (idTarget : {point : Carrier} → Target point point)
    (compTarget : {first second third : Carrier} →
      Target first second → Target second third → Target first third)
    (onStep : {source target : Carrier} → Step source target → Target source target)
    {source target : Carrier} (step : Step source target) :
    RewritePath.foldMap idTarget compTarget onStep (RewritePath.single step)
      = compTarget (onStep step) idTarget := rfl

/-- ★ **Functoriality of `foldMap`** — the fold sends path composition to target composition.  This is
the existence half of the universal property: `foldMap` is a (the) functor from the free category.
Requires the target composition to be associative and left-unital. -/
theorem RewritePath.foldMap_comp {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
    (idTarget : {point : Carrier} → Target point point)
    (compTarget : {first second third : Carrier} →
      Target first second → Target second third → Target first third)
    (onStep : {source target : Carrier} → Step source target → Target source target)
    (compTarget_assoc : ∀ {first second third fourth : Carrier}
      (left : Target first second) (middle : Target second third) (right : Target third fourth),
      compTarget (compTarget left middle) right = compTarget left (compTarget middle right))
    (compTarget_idLeft : ∀ {first second : Carrier} (value : Target first second),
      compTarget idTarget value = value)
    {source middle target : Carrier}
    (firstPath : RewritePath Step source middle) (secondPath : RewritePath Step middle target) :
    RewritePath.foldMap idTarget compTarget onStep (firstPath.comp secondPath)
      = compTarget (RewritePath.foldMap idTarget compTarget onStep firstPath)
          (RewritePath.foldMap idTarget compTarget onStep secondPath) := by
  induction firstPath with
  | nil =>
      rw [RewritePath.nil_comp]
      dsimp only [RewritePath.foldMap]
      rw [compTarget_idLeft]
  | cons step rest inductionHypothesis =>
      rw [RewritePath.cons_comp]
      dsimp only [RewritePath.foldMap]
      rw [inductionHypothesis, compTarget_assoc]

/-- ★ **Uniqueness of `foldMap`** — any map `candidate` that sends `nil` to the identity and each
`cons` to a target composition with `onStep` IS the fold.  Together with `foldMap_comp` this is the
universal property of the free category on the step graph. -/
theorem RewritePath.foldMap_unique {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
    (idTarget : {point : Carrier} → Target point point)
    (compTarget : {first second third : Carrier} →
      Target first second → Target second third → Target first third)
    (onStep : {source target : Carrier} → Step source target → Target source target)
    (candidate : {source target : Carrier} → RewritePath Step source target → Target source target)
    (candidate_nil : ∀ {point : Carrier},
      candidate (RewritePath.nil (Step := Step) (point := point)) = idTarget)
    (candidate_cons : ∀ {source middle target : Carrier}
      (step : Step source middle) (rest : RewritePath Step middle target),
      candidate (RewritePath.cons step rest) = compTarget (onStep step) (candidate rest))
    {source target : Carrier} (path : RewritePath Step source target) :
    candidate path = RewritePath.foldMap idTarget compTarget onStep path := by
  induction path with
  | nil => rw [candidate_nil]; rfl
  | cons step rest inductionHypothesis =>
      rw [candidate_cons step rest, inductionHypothesis]
      rfl

/-- A concrete witness: folding with the free category's own identity/composition/embedding recovers
the path unchanged — the IDENTITY FUNCTOR on the free category. -/
theorem RewritePath.foldMap_id {Step : Carrier → Carrier → Type}
    {source target : Carrier} (path : RewritePath Step source target) :
    RewritePath.foldMap (Target := RewritePath Step)
      (fun {point} => RewritePath.nil (point := point))
      (fun left right => left.comp right)
      (fun step => RewritePath.single step) path = path := by
  induction path with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      dsimp only [RewritePath.foldMap]
      rw [inductionHypothesis]
      rw [RewritePath.single, RewritePath.cons_comp, RewritePath.nil_comp]

/-! ## Strict interchange at dimension 2 — the Gray interchanger degenerates -/

/-- One whisker order of the horizontal composite of two 2-cells `α : p ⟹ p'` and `β : q ⟹ q'`:
whisker `α` past `q` first, then `β` past `p'`. -/
def interchangeWhiskerSource {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {objectA objectB objectC : Carrier}
    {pathP pathPPrime : RewritePath Step objectA objectB}
    {pathQ pathQPrime : RewritePath Step objectB objectC}
    (cellAlpha : RewriteHomotopy diamond pathP pathPPrime)
    (cellBeta : RewriteHomotopy diamond pathQ pathQPrime) :
    RewriteHomotopy diamond (pathP.comp pathQ) (pathPPrime.comp pathQPrime) :=
  RewriteHomotopy.trans (cellAlpha.whiskerRightPath pathQ) (cellBeta.whiskerLeftPath pathPPrime)

/-- The other whisker order of the same horizontal composite: whisker `β` past `p` first, then `α`
past `q'`. -/
def interchangeWhiskerTarget {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {objectA objectB objectC : Carrier}
    {pathP pathPPrime : RewritePath Step objectA objectB}
    {pathQ pathQPrime : RewritePath Step objectB objectC}
    (cellAlpha : RewriteHomotopy diamond pathP pathPPrime)
    (cellBeta : RewriteHomotopy diamond pathQ pathQPrime) :
    RewriteHomotopy diamond (pathP.comp pathQ) (pathPPrime.comp pathQPrime) :=
  RewriteHomotopy.trans (cellBeta.whiskerLeftPath pathP) (cellAlpha.whiskerRightPath pathQPrime)

/-- ★ **Strict interchange** — the two whisker orders of a horizontal composite agree ON THE NOSE.
Because `RewriteHomotopy` is a thin (proof-irrelevant) 2-cell layer, the Gray interchanger between
the two orders is the identity: the free rewriting ω-category is genuinely STRICT at dimension 2.
This is the term-axis analogue of `mode-5`'s locally-discrete (strict / `refl`) interchanger. -/
theorem rewriteInterchange_strict {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {objectA objectB objectC : Carrier}
    {pathP pathPPrime : RewritePath Step objectA objectB}
    {pathQ pathQPrime : RewritePath Step objectB objectC}
    (cellAlpha : RewriteHomotopy diamond pathP pathPPrime)
    (cellBeta : RewriteHomotopy diamond pathQ pathQPrime) :
    interchangeWhiskerSource diamond cellAlpha cellBeta
      = interchangeWhiskerTarget diamond cellAlpha cellBeta := rfl

/-! ## The dimension-2 universal property — completing the free strict ω-category to both dimensions -/

/-- ★ **The dimension-2 universal property** of the free strict 2-category (consuming the `term-4`
substrate's `RewriteHomotopy.toModel`): every 2-cell (homotopy) maps into ANY model of the homotopy
congruence — the diamonds GENERATE the 2-cells.  Paired with `RewritePath.foldMap` (the dimension-1 UP)
this exhibits the free strict ω-category's universal property at BOTH dimensions, not just dimension 1. -/
theorem freeStrictTwoCategory_dim2UniversalProperty {Step : Carrier → Carrier → Type}
    {diamond : SquierDiamond Step} (model : HomotopyModel diamond)
    {source target : Carrier} {leftPath rightPath : RewritePath Step source target}
    (homotopy : RewriteHomotopy diamond leftPath rightPath) :
    model.rel leftPath rightPath :=
  homotopy.toModel model

/-- The dimension-2 factorization is UNIQUE: any two factorizations of a 2-cell through a model agree
(`model.rel` is a thin `Prop`).  Existence (`freeStrictTwoCategory_dim2UniversalProperty`) together with
this uniqueness is the FULL dimension-2 universal property. -/
theorem freeStrictTwoCategory_dim2Uniqueness {Step : Carrier → Carrier → Type}
    {diamond : SquierDiamond Step} (model : HomotopyModel diamond)
    {source target : Carrier} {leftPath rightPath : RewritePath Step source target}
    (firstFactorization secondFactorization : model.rel leftPath rightPath) :
    firstFactorization = secondFactorization := rfl

end FX1Poly.Core
