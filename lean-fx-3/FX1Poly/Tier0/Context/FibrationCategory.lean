import FX1Poly.Polygraph.Category.Pullback
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstCategory

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
  * the REUSABLE weak-equivalence base — **`IsIsomorphism.identityWitness`** (identities are isomorphisms),
    **`IsIsomorphism.composeWitness`** (isomorphisms compose), **`IsIsomorphism.inverseIso`** (the inverse of
    an iso is an iso), and **`IsIsomorphism.twoOutOfThreeRight`** (the 2-out-of-3 law) — the generic facts
    that make isomorphisms a 2-out-of-3 class, the weak-equivalence backbone of ANY model structure (proved
    from the bare category laws).
  * **`terminalCategory` / `terminalFibrationCategory`** — the point as a fibration category (all laws by
    `rfl` / `True.intro`).
  * ★ **`RawCategory.opposite` / `fxContextCategory` / `fxContextFibrationCategory`** — the GENUINE category
    of contexts `𝒞` (= `fxBaseSubstCategory`ᵒᵖ) as a Brown fibration category, NOT the point: weak
    equivalences are the isomorphisms (Brown axioms via the iso lemmas above), the empty context `◇` is the
    fibrant terminal (uniqueness by `rfl`, since `Γ ⟶ ◇` is `SubstVec Γ 0 = PUnit`).  The fibrations are the
    trivial class here; the display-map refinement is the deferred part.

DEFERRED (honestly NOT here, recorded by the `= false` markers):
  * the DISPLAY-MAP fibration refinement — taking the fibrations of `fxContextFibrationCategory` to be
    `fxBaseSubstCategory`'s DISPLAY MAPS specifically (`context-10` proved them a split fibration: closed
    under composition and stable under pullback) instead of the trivial all-maps class —
    `hasDisplayMapFibrations = false` (the homotopy-meaningful refinement);
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
open FX1Poly.Polygraph

/-! ## The reusable weak-equivalence base: isomorphisms form a 2-out-of-3 class -/

/-- Identities are isomorphisms (with the identity as their own inverse). -/
def _root_.FX1Poly.Polygraph.IsIsomorphism.identityWitness (category : RawCategory) (object : category.Object) :
    IsIsomorphism category (category.identity object) where
  inverse := category.identity object
  leftInverse := category.identityLeft (category.identity object)
  rightInverse := category.identityRight (category.identity object)

/-- Isomorphisms are closed under composition: the inverse of `f ∘ g` is `g⁻¹ ∘ f⁻¹`.  Proved from the
bare category laws (associativity + the inverse equations), no extensionality. -/
def _root_.FX1Poly.Polygraph.IsIsomorphism.composeWitness {category : RawCategory} {objectA objectB objectC : category.Object}
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

/-- The inverse of an isomorphism is itself an isomorphism (with the original morphism as its inverse). -/
def _root_.FX1Poly.Polygraph.IsIsomorphism.inverseIso {category : RawCategory} {objectA objectB : category.Object}
    {morphism : category.Morphism objectA objectB} (iso : IsIsomorphism category morphism) :
    IsIsomorphism category iso.inverse where
  inverse := morphism
  leftInverse := iso.rightInverse
  rightInverse := iso.leftInverse

/-- ★ The 2-out-of-3 law for isomorphisms (the direction the fibration category needs): if `f` and
`f ∘ g` are isomorphisms, then so is `g` — because `g = f⁻¹ ∘ (f ∘ g)`, a composite of isomorphisms.
This is what makes isomorphisms a 2-out-of-3 class, the weak-equivalence backbone of any model structure. -/
def _root_.FX1Poly.Polygraph.IsIsomorphism.twoOutOfThreeRight {category : RawCategory}
    {objectA objectB objectC : category.Object}
    (morphismF : category.Morphism objectA objectB) (morphismG : category.Morphism objectB objectC)
    (isoF : IsIsomorphism category morphismF)
    (isoComposite : IsIsomorphism category (category.compose morphismF morphismG)) :
    IsIsomorphism category morphismG :=
  have decomposition :
      category.compose isoF.inverse (category.compose morphismF morphismG) = morphismG := by
    rw [← category.composeAssoc, isoF.leftInverse, category.identityLeft]
  decomposition ▸ IsIsomorphism.composeWitness isoF.inverseIso isoComposite

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

/-! ## The genuine category of contexts as a fibration category -/

/-- The OPPOSITE of a category — same objects, morphisms reversed.  All three laws transport from the
original (associativity by `symm`, the identity laws swapped) — no extensionality. -/
def _root_.FX1Poly.Polygraph.RawCategory.opposite (category : RawCategory) : RawCategory where
  Object := category.Object
  Morphism := fun source target => category.Morphism target source
  identity := fun object => category.identity object
  compose := fun first second => category.compose second first
  composeAssoc := fun first second third => (category.composeAssoc third second first).symm
  identityLeft := fun morphism => category.identityRight morphism
  identityRight := fun morphism => category.identityLeft morphism

/-- ★ The genuine **category of contexts** `𝒞` — the OPPOSITE of `fxBaseSubstCategory` (which is `𝒞ᵒᵖ`, by
the variance `Morphism a b = SubstVec b a`).  Its objects are scopes, its morphisms are context maps, and
the empty context `◇` (scope `0`) is its TERMINAL object. -/
def fxContextCategory : RawCategory := RawCategory.opposite fxBaseSubstCategory

/-- ★ The genuine context category `𝒞` IS a Brown fibration category — NOT the point.  Fibrations are all
maps (the trivial structure; the display-map refinement is deferred — see the marker), weak equivalences
are the ISOMORPHISMS, and the empty context `◇` is the fibrant terminal object whose uniqueness holds by
`rfl` (the map `Γ ⟶ ◇` is `SubstVec Γ 0 = PUnit`).  The Brown axioms for the weak equivalences use the
shipped iso lemmas: `isoIsWeakEquivalence`/`weakEquivalenceCompose`/`weakEquivalence2of3` are
`composeWitness` / `twoOutOfThreeRight` on the genuine category. -/
def fxContextFibrationCategory : BrownFibrationStructure where
  base := fxContextCategory
  isFibration := fun _ => True
  isWeakEquivalence := fun morphism => Nonempty (IsIsomorphism fxContextCategory morphism)
  terminalObject := Nat.zero
  toTerminal := fun _ => PUnit.unit
  toTerminalUnique := fun _ => rfl
  toTerminalIsFibration := fun _ => True.intro
  identityIsFibration := fun _ => True.intro
  fibrationCompose := fun _ _ _ _ => True.intro
  isoIsWeakEquivalence := fun _ iso => ⟨iso⟩
  weakEquivalenceCompose := fun _ _ ⟨isoA⟩ ⟨isoB⟩ => ⟨IsIsomorphism.composeWitness isoA isoB⟩
  weakEquivalence2of3 := fun weakA morphismG ⟨isoA⟩ ⟨isoComposite⟩ =>
    ⟨IsIsomorphism.twoOutOfThreeRight weakA morphismG isoA isoComposite⟩

/-! ## Honesty markers -/

/-- **Honesty marker.**  The DISPLAY-MAP refinement — taking `fxContextFibrationCategory`'s fibrations to
be `fxBaseSubstCategory`'s DISPLAY MAPS specifically (`context-10` proved them a split fibration: closed
under composition, stable under pullback) rather than the trivial all-maps class — is not shipped here.
`= false`. -/
def fibrationCategory_hasDisplayMapFibrations : Bool := false

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

/-- Smoke: in the GENUINE category of contexts `𝒞`, the identity on any context is a weak equivalence —
exercising the real `fxContextFibrationCategory` and the iso base. -/
theorem fxContextFibrationCategory_identityIsWeakEquivalence_smoke
    (context : fxContextFibrationCategory.base.Object) :
    fxContextFibrationCategory.isWeakEquivalence (fxContextFibrationCategory.base.identity context) :=
  fxContextFibrationCategory.isoIsWeakEquivalence _
    (IsIsomorphism.identityWitness fxContextFibrationCategory.base context)

end FX1Poly.Tier0
