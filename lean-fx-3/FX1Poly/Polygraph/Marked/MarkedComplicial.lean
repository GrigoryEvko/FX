import FX1Poly.Polygraph.Rewriting.Coherence.SquierCoherence

/-! # Axis/Term — the marked / complicial structure of the term rewriting ω-category (term-18)

The term-axis mirror of `mode-7` (semistrictification / the thin-cell structure).  A COMPLICIAL set
(Verity) is a simplicial set equipped with a STRATIFICATION — a distinguished set of MARKED ("thin")
cells in each positive dimension — where the marked cells are exactly the EQUIVALENCES; an
(∞,n)-category is a complicial set in which every cell above dimension `n` is thin.  This file ships the
marked/complicial structure on `term-4`'s proof-relevant rewriting ω-category (`RewritePath` 1-cells,
`RewriteHomotopy` 2-cells), each piece zero-axiom:

  * **The dimension-1 marking** (`IsRewriteEquivalence`): a reduction path is THIN iff it is an
    EQUIVALENCE — invertible up to homotopy (it has a two-sided inverse path, both composites homotopic
    to the identity).  This is Verity's "thin = equivalence" exactly.
  * **The elementary stratification axiom** (`rewriteEquivalence_nil` ★): every identity (the empty
    path / degeneracy) is thin — the marking contains the degeneracies.
  * **Closure under composition** (`rewriteEquivalence_comp` ★): the composite of two thin 1-cells is
    thin — the genuine complicial closure, proved by whiskering the inverse homotopies through the
    composite and reassociating.  Together with `rewriteEquivalence_symm` (the inverse of a thin cell is
    thin) this makes the marking a sub-`(2,1)`-category.
  * **2-triviality** (`rewriteOmega_twoTrivial` ★): every 2-cell is thin — any two parallel 2-cells are
    equal (the thin `RewriteHomotopy` `Prop` is proof-irrelevant).  So the marked rewriting ω-category
    is 2-TRIVIAL: it presents an (∞,1)-category complicially.
  * **The packaged object** (`RewriteMarking` + `equivalenceMarking`): the stratification interface
    (marking + the two stratification axioms) and its canonical instance.

## Honest scope

Shipped: the dimension-1 equivalence marking, the elementary stratification axioms (degeneracies thin +
thin closed under composition + inversion), and 2-triviality (the (∞,1) presentation).  DEFERRED: the
full Verity WEAK-COMPLICIAL horn-filling conditions (thin inner horns have thin fillers, the complicial
identities at every dimension), the SATURATION 2-out-of-3, and the general (∞,n) marking for `n > 1`
(which needs Type-valued non-thin higher cells beyond the thin `RewriteHomotopy` layer).

## Zero-axiom verification

`rewriteEquivalence_nil`/`_symm` are direct witnesses; `rewriteEquivalence_comp` reassociates with
`term-4`'s `comp_assoc` (`rw`) then chains `whiskerLeftPath`/`whiskerRightPath`/`trans`;
`rewriteOmega_twoTrivial` is `rfl` (definitional proof irrelevance on the thin `RewriteHomotopy`
`Prop`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditAxisTermMarkedComplicial.lean`.
-/

namespace FX1Poly.Core

variable {Carrier : Type}

/-! ## The dimension-1 marking — thin 1-cell = equivalence -/

/-- A reduction path is **thin** (marked) iff it is an EQUIVALENCE: it has a two-sided inverse path
whose composites with it are both homotopic to the identity (the empty path).  This is the complicial
"thin = equivalence" marking at dimension 1. -/
def IsRewriteEquivalence {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source target : Carrier} (path : RewritePath Step source target) : Prop :=
  ∃ inverse : RewritePath Step target source,
    RewriteHomotopy diamond (path.comp inverse) RewritePath.nil ∧
    RewriteHomotopy diamond (inverse.comp path) RewritePath.nil

/-- ★ **Elementary stratification axiom** — every identity (the empty path / degeneracy) is thin. -/
theorem rewriteEquivalence_nil {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {point : Carrier} :
    IsRewriteEquivalence diamond (RewritePath.nil (Step := Step) (point := point)) :=
  ⟨RewritePath.nil, RewriteHomotopy.refl _, RewriteHomotopy.refl _⟩

/-- The inverse of a thin cell is thin — the marking is closed under inversion (so each marked hom is an
equivalence both ways). -/
theorem rewriteEquivalence_symm {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source target : Carrier} {path : RewritePath Step source target}
    {inverse : RewritePath Step target source}
    (rightInverse : RewriteHomotopy diamond (path.comp inverse) RewritePath.nil)
    (leftInverse : RewriteHomotopy diamond (inverse.comp path) RewritePath.nil) :
    IsRewriteEquivalence diamond inverse :=
  ⟨path, leftInverse, rightInverse⟩

/-- ★ **Closure under composition** — the composite of two thin 1-cells is thin.  The inverse of
`firstPath.comp secondPath` is `inverseSecond.comp inverseFirst`; each composite collapses by whiskering
the inner inverse-homotopy through and reassociating. -/
theorem rewriteEquivalence_comp {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source middle target : Carrier}
    {firstPath : RewritePath Step source middle} {secondPath : RewritePath Step middle target}
    (firstThin : IsRewriteEquivalence diamond firstPath)
    (secondThin : IsRewriteEquivalence diamond secondPath) :
    IsRewriteEquivalence diamond (firstPath.comp secondPath) := by
  obtain ⟨inverseFirst, firstRightInverse, firstLeftInverse⟩ := firstThin
  obtain ⟨inverseSecond, secondRightInverse, secondLeftInverse⟩ := secondThin
  refine ⟨inverseSecond.comp inverseFirst, ?_, ?_⟩
  · rw [RewritePath.comp_assoc, ← RewritePath.comp_assoc secondPath inverseSecond inverseFirst]
    exact RewriteHomotopy.trans
      ((secondRightInverse.whiskerRightPath inverseFirst).whiskerLeftPath firstPath) firstRightInverse
  · rw [RewritePath.comp_assoc, ← RewritePath.comp_assoc inverseFirst firstPath secondPath]
    exact RewriteHomotopy.trans
      ((firstLeftInverse.whiskerRightPath secondPath).whiskerLeftPath inverseSecond) secondLeftInverse

/-! ## Saturation — homotopy-invariance + the 2-out-of-3 for thin cells -/

/-- The marking is **homotopy-invariant**: a 1-cell homotopic to a thin cell is itself thin (the same
inverse works — transport its inverse-witnesses along the homotopy by whiskering).  This is what makes the
marking a SATURATED class. -/
theorem rewriteEquivalence_respectsHomotopy {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source target : Carrier} {path pathPrime : RewritePath Step source target}
    (homotopy : RewriteHomotopy diamond path pathPrime)
    (primeThin : IsRewriteEquivalence diamond pathPrime) :
    IsRewriteEquivalence diamond path := by
  obtain ⟨inverse, rightInverse, leftInverse⟩ := primeThin
  refine ⟨inverse, ?_, ?_⟩
  · exact RewriteHomotopy.trans (homotopy.whiskerRightPath inverse) rightInverse
  · exact RewriteHomotopy.trans (homotopy.whiskerLeftPath inverse) leftInverse

/-- ★ **Saturation (2-out-of-3), cancel-left**: if `firstPath` and `firstPath.comp secondPath` are thin
then `secondPath` is thin.  `secondPath` is homotopic to `inverseFirst.comp (firstPath.comp secondPath)`
(reassociate and collapse `inverseFirst.comp firstPath ≃ nil`), which is a composite of thin cells. -/
theorem rewriteEquivalence_cancelLeft {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source middle target : Carrier}
    {firstPath : RewritePath Step source middle} {secondPath : RewritePath Step middle target}
    (firstThin : IsRewriteEquivalence diamond firstPath)
    (compositeThin : IsRewriteEquivalence diamond (firstPath.comp secondPath)) :
    IsRewriteEquivalence diamond secondPath := by
  obtain ⟨inverseFirst, firstRightInverse, firstLeftInverse⟩ := firstThin
  have homotopy :
      RewriteHomotopy diamond secondPath (inverseFirst.comp (firstPath.comp secondPath)) := by
    apply RewriteHomotopy.symm
    rw [← RewritePath.comp_assoc]
    exact firstLeftInverse.whiskerRightPath secondPath
  exact rewriteEquivalence_respectsHomotopy diamond homotopy
    (rewriteEquivalence_comp diamond
      (rewriteEquivalence_symm diamond firstRightInverse firstLeftInverse) compositeThin)

/-- ★ **Saturation (2-out-of-3), cancel-right**: if `secondPath` and `firstPath.comp secondPath` are thin
then `firstPath` is thin.  `firstPath` is homotopic to `(firstPath.comp secondPath).comp inverseSecond`
(reassociate and collapse `secondPath.comp inverseSecond ≃ nil`), a composite of thin cells. -/
theorem rewriteEquivalence_cancelRight {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source middle target : Carrier}
    {firstPath : RewritePath Step source middle} {secondPath : RewritePath Step middle target}
    (secondThin : IsRewriteEquivalence diamond secondPath)
    (compositeThin : IsRewriteEquivalence diamond (firstPath.comp secondPath)) :
    IsRewriteEquivalence diamond firstPath := by
  obtain ⟨inverseSecond, secondRightInverse, secondLeftInverse⟩ := secondThin
  have homotopy :
      RewriteHomotopy diamond firstPath ((firstPath.comp secondPath).comp inverseSecond) := by
    apply RewriteHomotopy.symm
    rw [RewritePath.comp_assoc]
    refine RewriteHomotopy.trans (secondRightInverse.whiskerLeftPath firstPath) ?_
    rw [RewritePath.comp_nil]
    exact RewriteHomotopy.refl firstPath
  exact rewriteEquivalence_respectsHomotopy diamond homotopy
    (rewriteEquivalence_comp diamond compositeThin
      (rewriteEquivalence_symm diamond secondRightInverse secondLeftInverse))

/-! ## 2-triviality — every 2-cell is thin (the (∞,1) presentation) -/

/-- ★ **2-triviality** — any two parallel 2-cells are equal: the thin `RewriteHomotopy` layer is
proof-irrelevant, so every 2-cell is marked.  The marked rewriting ω-category is therefore 2-TRIVIAL —
a complicial presentation of an (∞,1)-category. -/
theorem rewriteOmega_twoTrivial {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
    {source target : Carrier} {leftPath rightPath : RewritePath Step source target}
    (firstCell secondCell : RewriteHomotopy diamond leftPath rightPath) :
    firstCell = secondCell := rfl

/-! ## The packaged marked rewriting ω-category -/

/-- A **stratification (marking)** of the rewriting ω-category: a thinness predicate on 1-cells closed
under the two elementary stratification axioms — identities are thin, and thin cells compose to thin. -/
structure RewriteMarking {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step) where
  /-- The dimension-1 marking: which reduction paths are thin. -/
  isThin : {source target : Carrier} → RewritePath Step source target → Prop
  /-- Degeneracies (identities) are thin. -/
  thin_nil : ∀ {point : Carrier}, isThin (RewritePath.nil (Step := Step) (point := point))
  /-- Thin cells are closed under composition. -/
  thin_comp : ∀ {source middle target : Carrier}
    {firstPath : RewritePath Step source middle} {secondPath : RewritePath Step middle target},
    isThin firstPath → isThin secondPath → isThin (firstPath.comp secondPath)

/-- The **canonical marking**: the thin 1-cells are exactly the equivalences. -/
def equivalenceMarking {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step) :
    RewriteMarking diamond where
  isThin := IsRewriteEquivalence diamond
  thin_nil := rewriteEquivalence_nil diamond
  thin_comp := fun firstThin secondThin => rewriteEquivalence_comp diamond firstThin secondThin

end FX1Poly.Core
