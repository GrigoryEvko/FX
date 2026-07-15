import FX1Poly.Axis.Context.ContextSyntheticInfinityCategory

/-! # context-36 — the MARKED / COMPLICIAL structure of the context (∞,ω)-category

`context-36` (★, tagged CwF-completion → Core/fib-8) puts the MARKED / COMPLICIAL structure on the context
category's directed (∞,ω)-category — the context-axis mirror of the COMPLETED `term-18`
(`Axis/Term/Rewrite/MarkedComplicial.lean`, the marked/complicial term ω-category) and of `mode-7`'s thin-cell
structure.  A COMPLICIAL set (Verity) is a simplicial set with a STRATIFICATION — a distinguished set of MARKED
("thin") cells in each positive dimension — where the marked cells are exactly the EQUIVALENCES; an
(∞,n)-category is a complicial set in which every cell above dimension `n` is thin.  This file ships the
marking on `context-33`/`context-34`'s directed context category (`DirectedCategoryHom` 1-cells, their `Eq`
2-cells), each piece zero-axiom:

  * **The dimension-1 marking** (`IsContextEquivalence`): a directed hom is THIN iff it is an EQUIVALENCE — it
    has a two-sided inverse directed hom whose composites are the identity homs.  Verity's "thin =
    equivalence" exactly, at the directed-hom level.
  * **The elementary stratification axioms**: every identity directed hom is thin (`contextEquivalence_id` ★);
    thin cells are closed under inverse (`contextEquivalence_symm`) and under composition
    (`contextEquivalence_comp` ★) — the genuine complicial closure, proved by inverting the composite as
    `invSecond ; invFirst` and collapsing via the strict associativity / unit laws (`context-33`).  Together
    this makes the marking a sub-`(2,1)`-category.
  * **Saturation (2-out-of-3)** (`contextEquivalence_cancelLeft` / `_cancelRight` ★): if two of `firstHom`,
    `secondHom`, `firstHom ; secondHom` are thin so is the third — the SATURATED marking.
  * **2-triviality** (`contextOmega_twoTrivial` ★): any two parallel 2-cells (the `Eq`s between parallel
    directed homs) are equal — the 2-cell layer is proof-irrelevant.  So the marked context category is
    2-TRIVIAL: it presents an (∞,1)-category complicially.
  * **The packaged object** (`MarkedContextCategory` + `equivalenceMarking`): the stratification interface
    (marking + the two stratification axioms) and its canonical instance.
  * **The bridge to `context-33`** (`DirectedHomIso.isContextEquivalence`): every directed ISO (the Rezk
    equivalence of `context-33`) is, in particular, a marked (thin) directed hom — so the marking selects
    exactly the cells Rezk-completeness collapses to identity paths.

## Honest scope

Shipped: the dimension-1 equivalence marking, the elementary stratification axioms (identities thin + thin
closed under composition + inversion), the saturation 2-out-of-3, and 2-triviality (the (∞,1) presentation).
DEFERRED — the full Verity WEAK-COMPLICIAL horn-filling conditions (thin inner horns have thin fillers, the
complicial identities at every dimension) and the general (∞,n) marking for `n > 1` (which needs Type-valued
non-thin higher cells beyond the proof-irrelevant `Eq` 2-cell layer).  This mirrors `term-18`'s honest scope
exactly.

## Zero-axiom verification

`contextEquivalence_id`/`_symm` and the bridge are direct `∃`-witnesses; `contextEquivalence_comp` and the
two saturation cancellations reassociate with `context-33`'s strict `directedComposition_assoc` /
`_identityLeft` / `_identityRight` (`rw`); `contextOmega_twoTrivial` is `rfl` (definitional proof irrelevance
on the `Eq` 2-cell `Prop`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Imports only `ContextSyntheticInfinityCategory` (its `context-33` sibling — the directed-hom /
`composeHom` / strict-law / `DirectedHomIso` substrate).  A Axis design-lock must not import up into `Core/` /
`Typed/`.  Zero external dependencies — raw Lean 4 + Init only.

Reference: Verity, "Weak complicial sets" (the stratification / thin cells); the COMPLETED `term-18`
(`Axis/Term/Rewrite/MarkedComplicial.lean`); the `context-33` synthetic ∞-category
(`ContextSyntheticInfinityCategory.lean`).
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## The dimension-1 marking — thin directed hom = equivalence -/

/-- A directed hom is **thin** (marked) iff it is an EQUIVALENCE: it has a two-sided inverse directed hom whose
composites with it are the identity directed homs.  This is the complicial "thin = equivalence" marking at
dimension 1, at the level of `context-34`'s `DirectedCategoryHom`. -/
def IsContextEquivalence (category : RawCategory) {objectA objectB : category.Object}
    (path : DirectedCategoryHom category objectA objectB) : Prop :=
  ∃ inverse : DirectedCategoryHom category objectB objectA,
    DirectedCategoryHom.composeHom path inverse = DirectedCategoryHom.identityHom category objectA ∧
    DirectedCategoryHom.composeHom inverse path = DirectedCategoryHom.identityHom category objectB

/-- ★ **Elementary stratification axiom** — every identity directed hom is thin (its own inverse, composites
the strict unit law). -/
theorem contextEquivalence_id (category : RawCategory) {object : category.Object} :
    IsContextEquivalence category (DirectedCategoryHom.identityHom category object) :=
  ⟨DirectedCategoryHom.identityHom category object,
    directedComposition_identityLeft (DirectedCategoryHom.identityHom category object),
    directedComposition_identityLeft (DirectedCategoryHom.identityHom category object)⟩

/-- The inverse of a thin cell is thin — the marking is closed under inversion (so each marked hom is an
equivalence both ways).  Swap the two inverse witnesses. -/
theorem contextEquivalence_symm {category : RawCategory} {objectA objectB : category.Object}
    {path : DirectedCategoryHom category objectA objectB}
    {inverse : DirectedCategoryHom category objectB objectA}
    (rightInverse :
      DirectedCategoryHom.composeHom path inverse = DirectedCategoryHom.identityHom category objectA)
    (leftInverse :
      DirectedCategoryHom.composeHom inverse path = DirectedCategoryHom.identityHom category objectB) :
    IsContextEquivalence category inverse :=
  ⟨path, leftInverse, rightInverse⟩

/-- ★ **Closure under composition** — the composite of two thin directed homs is thin.  The inverse of
`firstPath ; secondPath` is `invSecond ; invFirst`; each composite collapses by reassociating
(`directedComposition_assoc`) and cancelling the inner inverse pair to an identity (`context-33`'s strict
laws). -/
theorem contextEquivalence_comp {category : RawCategory} {source middle target : category.Object}
    {firstPath : DirectedCategoryHom category source middle}
    {secondPath : DirectedCategoryHom category middle target}
    (firstThin : IsContextEquivalence category firstPath)
    (secondThin : IsContextEquivalence category secondPath) :
    IsContextEquivalence category (DirectedCategoryHom.composeHom firstPath secondPath) := by
  obtain ⟨invFirst, firstRight, firstLeft⟩ := firstThin
  obtain ⟨invSecond, secondRight, secondLeft⟩ := secondThin
  refine ⟨DirectedCategoryHom.composeHom invSecond invFirst, ?_, ?_⟩
  · rw [directedComposition_assoc, ← directedComposition_assoc secondPath invSecond invFirst,
      secondRight, directedComposition_identityLeft, firstRight]
  · rw [directedComposition_assoc, ← directedComposition_assoc invFirst firstPath secondPath,
      firstLeft, directedComposition_identityLeft, secondLeft]

/-! ## Saturation — the 2-out-of-3 for thin cells -/

/-- The marking is **closed under equality** (homotopy-invariant at the strict level): a directed hom equal to
a thin one is itself thin.  Trivial by substitution — the strict-level analog of `term-18`'s
homotopy-invariance, what makes the marking a SATURATED class. -/
theorem contextEquivalence_ofEq {category : RawCategory} {objectA objectB : category.Object}
    {path pathPrime : DirectedCategoryHom category objectA objectB}
    (pathEq : path = pathPrime) (primeThin : IsContextEquivalence category pathPrime) :
    IsContextEquivalence category path := by
  subst pathEq
  exact primeThin

/-- ★ **Saturation (2-out-of-3), cancel-left**: if `firstPath` and `firstPath ; secondPath` are thin then
`secondPath` is thin.  `secondPath` equals `invFirst ; (firstPath ; secondPath)` (reassociate and collapse
`invFirst ; firstPath = identity`), a composite of thin cells. -/
theorem contextEquivalence_cancelLeft {category : RawCategory} {source middle target : category.Object}
    {firstPath : DirectedCategoryHom category source middle}
    {secondPath : DirectedCategoryHom category middle target}
    (firstThin : IsContextEquivalence category firstPath)
    (compositeThin :
      IsContextEquivalence category (DirectedCategoryHom.composeHom firstPath secondPath)) :
    IsContextEquivalence category secondPath := by
  obtain ⟨invFirst, firstRight, firstLeft⟩ := firstThin
  have secondPathEq :
      DirectedCategoryHom.composeHom invFirst (DirectedCategoryHom.composeHom firstPath secondPath)
        = secondPath := by
    rw [← directedComposition_assoc, firstLeft, directedComposition_identityLeft]
  exact contextEquivalence_ofEq secondPathEq.symm
    (contextEquivalence_comp (contextEquivalence_symm firstRight firstLeft) compositeThin)

/-- ★ **Saturation (2-out-of-3), cancel-right**: if `secondPath` and `firstPath ; secondPath` are thin then
`firstPath` is thin.  `firstPath` equals `(firstPath ; secondPath) ; invSecond` (reassociate and collapse
`secondPath ; invSecond = identity`), a composite of thin cells. -/
theorem contextEquivalence_cancelRight {category : RawCategory} {source middle target : category.Object}
    {firstPath : DirectedCategoryHom category source middle}
    {secondPath : DirectedCategoryHom category middle target}
    (secondThin : IsContextEquivalence category secondPath)
    (compositeThin :
      IsContextEquivalence category (DirectedCategoryHom.composeHom firstPath secondPath)) :
    IsContextEquivalence category firstPath := by
  obtain ⟨invSecond, secondRight, secondLeft⟩ := secondThin
  have firstPathEq :
      DirectedCategoryHom.composeHom (DirectedCategoryHom.composeHom firstPath secondPath) invSecond
        = firstPath := by
    rw [directedComposition_assoc, secondRight, directedComposition_identityRight]
  exact contextEquivalence_ofEq firstPathEq.symm
    (contextEquivalence_comp compositeThin (contextEquivalence_symm secondRight secondLeft))

/-! ## 2-triviality — every 2-cell is thin (the (∞,1) presentation) -/

/-- ★ **2-triviality** — any two parallel 2-cells are equal: the 2-cell layer is the `Eq` between parallel
directed homs, a `Prop`, hence proof-irrelevant, so every 2-cell is marked.  The marked context category is
therefore 2-TRIVIAL — a complicial presentation of an (∞,1)-category, exactly as `term-18`. -/
theorem contextOmega_twoTrivial {category : RawCategory} {objectA objectB : category.Object}
    {leftHom rightHom : DirectedCategoryHom category objectA objectB}
    (firstCell secondCell : leftHom = rightHom) : firstCell = secondCell := rfl

/-! ## The packaged marked context category -/

/-- A **stratification (marking)** of the context (∞,ω)-category: a thinness predicate on directed homs closed
under the two elementary stratification axioms — identities are thin, and thin cells compose to thin. -/
structure MarkedContextCategory (category : RawCategory) where
  /-- The dimension-1 marking: which directed homs are thin. -/
  isThin : {objectA objectB : category.Object} → DirectedCategoryHom category objectA objectB → Prop
  /-- Identities (degeneracies) are thin. -/
  thin_identity : ∀ {object : category.Object},
    isThin (DirectedCategoryHom.identityHom category object)
  /-- Thin cells are closed under composition. -/
  thin_comp : ∀ {source middle target : category.Object}
    {firstHom : DirectedCategoryHom category source middle}
    {secondHom : DirectedCategoryHom category middle target},
    isThin firstHom → isThin secondHom → isThin (DirectedCategoryHom.composeHom firstHom secondHom)

/-- The **canonical marking**: the thin directed homs are exactly the equivalences. -/
def equivalenceMarking (category : RawCategory) : MarkedContextCategory category where
  isThin := IsContextEquivalence category
  thin_identity := contextEquivalence_id category
  thin_comp := fun firstThin secondThin => contextEquivalence_comp firstThin secondThin

/-! ## Bridge to `context-33`: directed isos are marked -/

/-- Bridge to `ContextSyntheticInfinityCategory.lean`: every directed ISO (the Rezk equivalence of
`context-33`) is a marked (thin) directed hom — its backward hom is the required two-sided inverse.  So the
marking selects exactly the cells that `context-33`'s Rezk-completeness collapses to identity paths. -/
def DirectedHomIso.isContextEquivalence {category : RawCategory} {objectA objectB : category.Object}
    (iso : DirectedHomIso category objectA objectB) :
    IsContextEquivalence category iso.forward :=
  ⟨iso.backward, iso.forwardBackward, iso.backwardForward⟩

/-! ## Honesty markers -/

/-- **Honesty marker.**  The STRICT MARKING is shipped: identities are thin (`contextEquivalence_id`), the
marking is closed under inversion (`contextEquivalence_symm`) and composition (`contextEquivalence_comp`) — a
sub-`(2,1)`-category, the elementary complicial stratification axioms.  `= true`. -/
def fxMarkedContextCategory_hasStrictMarking : Bool := true

/-- **Honesty marker.**  The marking is SATURATED — the 2-out-of-3 property holds
(`contextEquivalence_cancelLeft` / `_cancelRight`): if two of `f`, `g`, `f ; g` are thin so is the third.
`= true`. -/
def fxMarkedContextCategory_hasSaturationTwoOutOfThree : Bool := true

/-- **Honesty marker.**  The marked context category is 2-TRIVIAL (`contextOmega_twoTrivial`): its 2-cells are
the proof-irrelevant `Eq`s between parallel directed homs, so it presents an (∞,1)-category complicially.
`= true`. -/
def fxMarkedContextCategory_hasTwoTriviality : Bool := true

/-- **Honesty marker.**  The FULL Verity WEAK-COMPLICIAL horn-filling — thin inner horns have thin fillers, the
complicial identities at every dimension, and the general (∞,n) marking for `n > 1` (Type-valued non-thin
higher cells beyond the proof-irrelevant `Eq` 2-cell layer) — is NOT shipped.  This is the `×type` wall, the
same scope `term-18` honestly defers.  `= false`. -/
def fxMarkedContextCategory_hasFullComplicialHornFilling : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis analog of a Core table-native marked-complicial row;
a Axis design-lock cannot import the Core engine, so the marking is re-shipped here as a strict
construction.  Gluing the Axis and Core forms is cross-axis `×type`.  `= false`. -/
def fxMarkedContextCategory_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: in the canonical marking, the identity directed hom is thin — the elementary stratification axiom,
read off the packaged object. -/
theorem equivalenceMarking_thin_identity_smoke (category : RawCategory) {object : category.Object} :
    (equivalenceMarking category).isThin (DirectedCategoryHom.identityHom category object) :=
  (equivalenceMarking category).thin_identity

/-- Smoke: every directed iso is thin in the canonical marking — the `context-33` bridge, read off the
packaged object. -/
theorem directedHomIso_isThin_smoke {category : RawCategory} {objectA objectB : category.Object}
    (iso : DirectedHomIso category objectA objectB) :
    (equivalenceMarking category).isThin iso.forward :=
  DirectedHomIso.isContextEquivalence iso

end FX1Poly.Axis
