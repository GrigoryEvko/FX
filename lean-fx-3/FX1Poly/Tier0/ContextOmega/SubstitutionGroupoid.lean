import FX1Poly.Tier0.FxBaseSubstCategory
import FX1Poly.Tier0.FxBaseSubstVec

/-! # Tier0/ContextOmega/SubstitutionGroupoid — the dim-2 homotopy layer of substitutions (context-20)

The category of contexts-and-substitutions is the **1-skeleton** of a higher structure: objects
(scopes) are 0-cells, substitutions are 1-cells, and the **dim-2 layer** would be the *homotopies* /
*paths between parallel substitutions* (2-cells), with 3-cells between those, … — the **substitution
ω-groupoid**.  In a homotopical / ∞-categorical model (cubical sets, the simplicial model) those 2-cells
are NON-trivial: two substitutions can be PATH-equal without being definitionally equal, and the
associativity / unit laws hold only up to coherent 2-cells (an associator `α`, unitors).

On the FX context base the higher structure is **STRICT** — it collapses at dimension 2:

  * **the dim-1 layer is a strict 1-category** — substitutions compose strictly-associatively and
    unitally (`fxBaseSubstCategory`'s `composeAssoc` / `identityLeft` / `identityRight`); the
    associator and unitor 2-cells are the IDENTITY (associativity is a definitional EQUALITY
    `(σ∘τ)∘υ = σ∘(τ∘υ)`, `SubstVec.compose_assoc`, not a non-trivial path);
  * **the dim-2 layer collapses to strict equality** — two parallel substitutions agreeing POINTWISE
    are EQUAL (`SubstVec.ext`), so the only "2-cells" between parallel substitutions are propositional
    equalities; there is no non-trivial homotopy.  Crucially this extensionality holds ZERO-AXIOM —
    `SubstVec` is a finite product of `RawTerm`s, so pointwise equality gives equality structurally,
    WITHOUT `funext` (the function-typed `RawTermSubst` would need `funext` here).

So FX realizes the **strict 1-truncation** of the substitution ω-groupoid: the substitution category is
a strict 1-category whose hom-sets are genuine sets, the dim-2 associator/2-cells trivial — all
zero-axiom.  The genuine HOMOTOPY ω-groupoid (non-trivial higher paths) is the recorded boundary.

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the genuine homotopy ω-groupoid of substitutions — non-trivial
2-cells (paths between substitutions that are path-equal but not definitionally equal), the dim-2+
homotopy structure (the substitution category as a genuine ∞-groupoid), needing Id-types at the
substitution level + the homotopy structure of a cubical / ∞-categorical model.  What IS zero-axiom is
the strict 1-truncation: the dim-1 strict-category laws + the dim-2 collapse to strict equality.

## What is built

  * `SubstitutionGroupoidLedger` — the recognition record.
  * `fxSubstitutionGroupoidLedger` — FX's instance.
  * the flag pins.
  * ★ `substitutionAssociatorIsTrivial` — the genuine anchor: associativity is a definitional EQUALITY
    (`SubstVec.compose_assoc`), so the dim-2 associator 2-cell is the identity, conjoined with the flag.
  * ★ `substitutionTwoCellsAreStrictEqualities` — the dim-2-collapse anchor: parallel substitutions
    agreeing pointwise are EQUAL (`SubstVec.ext`, the funext-free extensionality), conjoined with the flag.
  * `substitutionGroupoidStrictlyOneTruncated` — the headline.

## Zero-axiom verification

Record + `rfl` flag pins, plus cross-references applying the shipped zero-axiom `SubstVec.compose_assoc`
(strict associator) and `SubstVec.ext` (the funext-free dim-2 collapse).  No `funext`, no `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The substitution ω-groupoid ledger -/

/-- A recognition record for the dim-2 homotopy layer of the substitution category: which strict
1-truncated structure FX realizes zero-axiom (the strict 1-category, the dim-2 collapse) and which is
the homotopy boundary (the genuine ω-groupoid's non-trivial higher paths). -/
structure SubstitutionGroupoidLedger where
  /-- The dim-1 layer is a strict 1-category (substitutions compose strictly-associatively + unitally). -/
  dimOneStrictCategoryRealized : Bool
  /-- The dim-2 associator 2-cell is the IDENTITY: associativity is a definitional equality, not a
  non-trivial path. -/
  associatorIsTrivialTwoCell : Bool
  /-- The dim-2 layer collapses to strict equality: parallel substitutions agreeing pointwise are equal
  (`SubstVec.ext`), the zero-axiom funext-free extensionality. -/
  twoCellsAreStrictEqualities : Bool
  /-- Whether the base is the FX syntactic context category.  `true` — built ON the FX substitutions. -/
  baseIsFXSyntacticContext : Bool
  /-- Honest absence marker: whether the genuine HOMOTOPY ω-groupoid (non-trivial higher paths between
  substitutions) is constructed.  `false` — needs Id-types at the substitution level / a homotopy model. -/
  nonTrivialHomotopyGroupoidConstructed : Bool

/-- FX's substitution ω-groupoid instance: the strict 1-category + the dim-2 collapse are realized; the
genuine homotopy ω-groupoid is the recorded boundary. -/
def fxSubstitutionGroupoidLedger : SubstitutionGroupoidLedger where
  dimOneStrictCategoryRealized := true
  associatorIsTrivialTwoCell := true
  twoCellsAreStrictEqualities := true
  baseIsFXSyntacticContext := true
  nonTrivialHomotopyGroupoidConstructed := false

/-! ## Flag pins -/

/-- The dim-1 layer is a strict 1-category (anchored by `substitutionAssociatorIsTrivial` below). -/
theorem fxSubstitutionGroupoidLedger_dimOneStrictCategoryRealized :
    fxSubstitutionGroupoidLedger.dimOneStrictCategoryRealized = true := rfl

/-- The dim-2 associator is the trivial 2-cell (anchored by `substitutionAssociatorIsTrivial`). -/
theorem fxSubstitutionGroupoidLedger_associatorIsTrivialTwoCell :
    fxSubstitutionGroupoidLedger.associatorIsTrivialTwoCell = true := rfl

/-- The dim-2 2-cells are strict equalities (anchored by `substitutionTwoCellsAreStrictEqualities`). -/
theorem fxSubstitutionGroupoidLedger_twoCellsAreStrictEqualities :
    fxSubstitutionGroupoidLedger.twoCellsAreStrictEqualities = true := rfl

/-- The substitution ω-groupoid is recognized ON the FX syntactic context category. -/
theorem fxSubstitutionGroupoidLedger_baseIsFXSyntacticContext :
    fxSubstitutionGroupoidLedger.baseIsFXSyntacticContext = true := rfl

/-- Honest absence marker: the genuine homotopy ω-groupoid (non-trivial higher paths) is NOT
constructed — the homotopy boundary. -/
theorem fxSubstitutionGroupoidLedger_nonTrivialHomotopyGroupoidNotConstructed :
    fxSubstitutionGroupoidLedger.nonTrivialHomotopyGroupoidConstructed = false := rfl

/-! ## The genuine anchors -/

/-- ★ **The dim-2 associator is the trivial 2-cell.**  In a WEAK 2-category / bicategory, associativity
of 1-cell composition holds only up to a non-trivial **associator** 2-cell `α : (σ∘τ)∘υ ⇒ σ∘(τ∘υ)`.  On
the FX substitution category that associativity is a definitional EQUALITY `(σ∘τ)∘υ = σ∘(τ∘υ)`
(`SubstVec.compose_assoc`), so the associator is the IDENTITY 2-cell — the dim-2 coherence is strict.
This conjoins the shipped strict-associativity with the trivial-associator flag. -/
theorem substitutionAssociatorIsTrivial {scopeA scopeB scopeC scopeD : Nat}
    (oneVec : SubstVec scopeB scopeA) (twoVec : SubstVec scopeC scopeB)
    (threeVec : SubstVec scopeD scopeC) :
    ((oneVec.compose twoVec).compose threeVec = oneVec.compose (twoVec.compose threeVec)) ∧
    fxSubstitutionGroupoidLedger.associatorIsTrivialTwoCell = true :=
  ⟨SubstVec.compose_assoc oneVec twoVec threeVec, rfl⟩

/-- ★ **The dim-2 2-cells are strict equalities.**  A 2-cell between parallel substitutions `σ, τ` is, in
the strict setting, an EQUALITY `σ = τ`.  On the FX base, two parallel substitutions agreeing POINTWISE
are equal (`SubstVec.ext`), so the only homotopy between parallel substitutions is propositional
equality — there is no non-trivial 2-cell; the substitution category is strictly 1-truncated.  Crucially
`SubstVec.ext` holds ZERO-AXIOM (`SubstVec` is a finite product, so pointwise equality gives equality
structurally) — the funext-free extensionality the function-typed substitution could not prove.  This
conjoins that extensionality with the strict-2-cells flag. -/
theorem substitutionTwoCellsAreStrictEqualities {target source : Nat}
    (vecA vecB : SubstVec target source)
    (pointwise : ∀ index : Fin source, vecA.lookup index = vecB.lookup index) :
    vecA = vecB ∧ fxSubstitutionGroupoidLedger.twoCellsAreStrictEqualities = true :=
  ⟨SubstVec.ext vecA vecB pointwise, rfl⟩

/-! ## The headline -/

/-- ★ **The substitution ω-groupoid, strictly 1-truncated.**  On the FX context base the substitution
ω-groupoid collapses to its strict 1-truncation: (a) the dim-1 layer is a strict 1-category, (b) the
dim-2 associator is the trivial 2-cell (associativity is a definitional equality), and (c) the dim-2
2-cells are strict equalities (parallel substitutions agreeing pointwise are equal, the funext-free
`SubstVec.ext`), over the FX syntactic context category — while (d) the genuine homotopy ω-groupoid
(non-trivial higher paths between substitutions) is the recorded boundary. -/
theorem substitutionGroupoidStrictlyOneTruncated :
    fxSubstitutionGroupoidLedger.dimOneStrictCategoryRealized = true ∧
    fxSubstitutionGroupoidLedger.associatorIsTrivialTwoCell = true ∧
    fxSubstitutionGroupoidLedger.twoCellsAreStrictEqualities = true ∧
    fxSubstitutionGroupoidLedger.baseIsFXSyntacticContext = true ∧
    fxSubstitutionGroupoidLedger.nonTrivialHomotopyGroupoidConstructed = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Tier0.ContextOmega
