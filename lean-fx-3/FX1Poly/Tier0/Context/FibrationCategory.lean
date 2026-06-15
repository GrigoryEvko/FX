import FX1Poly.Tier0.Context.RepresentableMapCategory

/-! # context-15 — the model structure: the AKL fibration category on contexts, context-side residue

`context-15` is the MODEL-STRUCTURE rung: Avigad–Kapulkin–Lumsdaine's theorem that the category of contexts
of a type theory carries the structure of a BROWN FIBRATION CATEGORY — a category with a terminal object,
a class of FIBRATIONS, and a class of WEAK EQUIVALENCES satisfying the Brown axioms — which is what lets one
do homotopy theory (homotopy limits, etc.) inside the syntax.

## What is context-side here, and what is deferred

The fibration-category STRUCTURE is pure category-of-contexts data — that is the CONTEXT-SIDE residue
shipped here, zero-axiom:

  * **`BrownFibrationStructure`** — the fibration-category interface: a base category, a fibration
    predicate, a weak-equivalence predicate, a fibrant terminal object, and the Brown closure axioms
    (fibrations contain identities and compose; weak equivalences contain isomorphisms, compose, and
    satisfy a 2-out-of-3 direction).
  * the REUSABLE weak-equivalence base — **`IsIsomorphism.identityWitness`** (identities are isomorphisms)
    and **`IsIsomorphism.composeWitness`** (isomorphisms compose) — the generic facts that make
    isomorphisms a sub-class of weak equivalences in ANY model/fibration structure (proved from the bare
    category laws).
  * **`terminalCategory` / `terminalFibrationCategory`** — the point as a fibration category: a genuine
    witness inhabiting the interface (all laws by `rfl` / `True.intro`, via `PUnit`'s definitional eta).

DEFERRED (honestly NOT here, recorded by the `= false` markers):
  * the genuine FX witness — `fxBaseSubstCategory`'s DISPLAY MAPS as the fibrations (`context-10` already
    proved them a split fibration: closed under composition and stable under pullback) — assembled as a
    full fibration category; `hasDisplayMapWitness = false` (the non-terminal model);
  * FACTORIZATION — every map factors as a weak equivalence followed by a fibration —
    `hasFactorization = false` (the deep AKL content);
  * FIBRATION PULLBACK STABILITY as a fibration-category axiom — `hasFibrationPullbackStability = false`
    (`context-10` has it for display maps; generically deferred);
  * PATH OBJECTS / the homotopy-theoretic weak equivalences — `hasPathObjects = false` (`×type`, needs the
    Id-type / path-object structure).

Reference: Avigad, Kapulkin & Lumsdaine, "Homotopy limits in type theory", Math. Struct. Comp. Sci.
25 (2015) (arXiv:1304.0680); K.S. Brown, "Abstract homotopy theory and generalized sheaf cohomology" (1973).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## The reusable weak-equivalence base: isomorphisms form a 2-out-of-3 class -/

/-- Identities are isomorphisms (with the identity as their own inverse). -/
def IsIsomorphism.identityWitness (category : RawCategory) (object : category.Object) :
    IsIsomorphism category (category.identity object) where
  inverse := category.identity object
  leftInverse := category.identityLeft (category.identity object)
  rightInverse := category.identityRight (category.identity object)

/-- Isomorphisms are closed under composition: the inverse of `f ∘ g` is `g⁻¹ ∘ f⁻¹`.  Proved from the
bare category laws (associativity + the inverse equations), no extensionality. -/
def IsIsomorphism.composeWitness {category : RawCategory} {objectA objectB objectC : category.Object}
    {morphismF : category.Morphism objectA objectB} {morphismG : category.Morphism objectB objectC}
    (isoF : IsIsomorphism category morphismF) (isoG : IsIsomorphism category morphismG) :
    IsIsomorphism category (category.compose morphismF morphismG) where
  inverse := category.compose isoG.inverse isoF.inverse
  leftInverse := by
    rw [category.composeAssoc, ← category.composeAssoc isoF.inverse morphismF morphismG,
        isoF.leftInverse, category.identityLeft, isoG.leftInverse]
  rightInverse := by
    rw [category.composeAssoc, ← category.composeAssoc morphismG isoG.inverse isoF.inverse,
        isoG.rightInverse, category.identityLeft, isoF.rightInverse]

/-! ## The Brown fibration-category structure -/

/-- A **Brown fibration category** (the AKL structure on contexts): a base category with a fibration
predicate and a weak-equivalence predicate, a fibrant terminal object, and the closure axioms — fibrations
contain identities and compose; weak equivalences contain isomorphisms, compose, and satisfy 2-out-of-3.
(Factorization and fibration pullback-stability are the deep content, deferred — see the markers.) -/
structure BrownFibrationStructure where
  /-- The base category (of contexts). -/
  base : RawCategory
  /-- The class of fibrations. -/
  isFibration : {source target : base.Object} → base.Morphism source target → Prop
  /-- The class of weak equivalences. -/
  isWeakEquivalence : {source target : base.Object} → base.Morphism source target → Prop
  /-- The terminal object. -/
  terminalObject : base.Object
  /-- The unique map to the terminal object. -/
  toTerminal : (object : base.Object) → base.Morphism object terminalObject
  /-- The map to the terminal object is unique (terminality). -/
  toTerminalUnique : ∀ {object : base.Object} (morphism : base.Morphism object terminalObject),
    morphism = toTerminal object
  /-- Every object is FIBRANT: its map to the terminal object is a fibration. -/
  toTerminalIsFibration : ∀ (object : base.Object), isFibration (toTerminal object)
  /-- Identities are fibrations. -/
  identityIsFibration : ∀ (object : base.Object), isFibration (base.identity object)
  /-- Fibrations are closed under composition. -/
  fibrationCompose : ∀ {a b c : base.Object} (fibA : base.Morphism a b) (fibB : base.Morphism b c),
    isFibration fibA → isFibration fibB → isFibration (base.compose fibA fibB)
  /-- Isomorphisms are weak equivalences. -/
  isoIsWeakEquivalence : ∀ {source target : base.Object} (morphism : base.Morphism source target),
    IsIsomorphism base morphism → isWeakEquivalence morphism
  /-- Weak equivalences are closed under composition. -/
  weakEquivalenceCompose : ∀ {a b c : base.Object} (weA : base.Morphism a b) (weB : base.Morphism b c),
    isWeakEquivalence weA → isWeakEquivalence weB → isWeakEquivalence (base.compose weA weB)
  /-- 2-out-of-3 (the relevant direction): if `f` and `f ∘ g` are weak equivalences, so is `g`. -/
  weakEquivalence2of3 : ∀ {a b c : base.Object} (weA : base.Morphism a b) (morphismG : base.Morphism b c),
    isWeakEquivalence weA → isWeakEquivalence (base.compose weA morphismG) → isWeakEquivalence morphismG

/-! ## The point as a fibration category -/

/-- The terminal category — one object, one morphism (the point). -/
def terminalCategory : RawCategory where
  Object := PUnit
  Morphism := fun _ _ => PUnit
  identity := fun _ => PUnit.unit
  compose := fun _ _ => PUnit.unit
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- ★ The point IS a Brown fibration category: every map is both a fibration and a weak equivalence, and
all axioms hold trivially (via `PUnit`'s definitional eta and `True`).  A genuine, if minimal, witness that
the fibration-category interface is inhabited. -/
def terminalFibrationCategory : BrownFibrationStructure where
  base := terminalCategory
  isFibration := fun _ => True
  isWeakEquivalence := fun _ => True
  terminalObject := PUnit.unit
  toTerminal := fun _ => PUnit.unit
  toTerminalUnique := fun _ => rfl
  toTerminalIsFibration := fun _ => True.intro
  identityIsFibration := fun _ => True.intro
  fibrationCompose := fun _ _ _ _ => True.intro
  isoIsWeakEquivalence := fun _ _ => True.intro
  weakEquivalenceCompose := fun _ _ _ _ => True.intro
  weakEquivalence2of3 := fun _ _ _ _ => True.intro

/-! ## Honesty markers -/

/-- **Honesty marker.**  The genuine FX witness — `fxBaseSubstCategory`'s DISPLAY MAPS as the fibrations
(`context-10` proved them a split fibration: closed under composition, stable under pullback) — assembled
as a full fibration category is not shipped here.  `= false`. -/
def fibrationCategory_hasDisplayMapWitness : Bool := false

/-- **Honesty marker.**  FACTORIZATION (every map = a weak equivalence then a fibration) is the deep AKL
content; not shipped here.  `= false`. -/
def fibrationCategory_hasFactorization : Bool := false

/-- **Honesty marker.**  FIBRATION PULLBACK STABILITY as a fibration-category axiom (`context-10` has it
for display maps) is deferred generically.  `= false`. -/
def fibrationCategory_hasFibrationPullbackStability : Bool := false

/-- **Honesty marker.**  PATH OBJECTS / the homotopy-theoretic weak equivalences need the Id-type /
path-object structure — `×type`, deferred to the type axis / `fib`.  `= false`. -/
def fibrationCategory_hasPathObjects : Bool := false

/-! ## Smoke -/

/-- Smoke: in the terminal fibration category, the identity is a weak equivalence — exercising
`isoIsWeakEquivalence` on the generic `identityWitness`. -/
theorem terminalFibrationCategory_identityIsWeakEquivalence_smoke :
    terminalFibrationCategory.isWeakEquivalence (terminalFibrationCategory.base.identity PUnit.unit) :=
  terminalFibrationCategory.isoIsWeakEquivalence _
    (IsIsomorphism.identityWitness terminalFibrationCategory.base PUnit.unit)

end FX1Poly.Tier0
