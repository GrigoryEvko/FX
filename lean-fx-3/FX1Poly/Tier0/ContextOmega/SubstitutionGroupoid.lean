import FX1Poly.Tier0.FxBaseSubstCategory
import FX1Poly.Tier0.FxBaseSubstVec

/-! # Tier0/ContextOmega/SubstitutionGroupoid — the strict 1-truncation of the substitution category (context-20)

The category of contexts-and-substitutions is the 1-skeleton of a higher structure: scopes are 0-cells,
substitutions are 1-cells, and the dim-2 layer would be the homotopies between parallel substitutions.
On the FX context base that higher structure is STRICT and collapses at dimension 2:

  * the dim-1 layer is a strict 1-category — substitutions compose strictly-associatively
    (`SubstVec.compose_assoc`), so the dim-2 associator 2-cell is the IDENTITY (associativity is a
    definitional EQUALITY `(σ∘τ)∘υ = σ∘(τ∘υ)`, not a non-trivial path);
  * the dim-2 layer collapses to strict equality — two parallel substitutions agreeing POINTWISE are
    EQUAL (`SubstVec.ext`), so the only "2-cells" between parallel substitutions are propositional
    equalities.  Crucially this extensionality holds ZERO-AXIOM — `SubstVec` is a finite product of
    `RawTerm`s, so pointwise equality gives equality structurally, WITHOUT `funext` (the function-typed
    `RawTermSubst` would need `funext` here).

So FX realizes the strict 1-truncation of the substitution ω-groupoid.  The genuine HOMOTOPY ω-groupoid
(non-trivial higher paths between substitutions, needing Id-types at the substitution level and the
homotopy structure of a cubical / ∞-categorical model) is NOT mechanized — it is the recorded boundary.

Raw Lean 4 + Init only; the anchors apply the shipped zero-axiom `SubstVec.compose_assoc` and
`SubstVec.ext`.  No `funext`, `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- **The dim-2 associator is the trivial 2-cell.**  In a weak 2-category / bicategory, associativity of
1-cell composition holds only up to a non-trivial associator 2-cell `α : (σ∘τ)∘υ ⇒ σ∘(τ∘υ)`.  On the FX
substitution category that associativity is a definitional EQUALITY (`SubstVec.compose_assoc`), so the
associator is the IDENTITY 2-cell — the dim-2 coherence is strict. -/
theorem substitutionAssociatorIsTrivial {scopeA scopeB scopeC scopeD : Nat}
    (oneVec : SubstVec scopeB scopeA) (twoVec : SubstVec scopeC scopeB)
    (threeVec : SubstVec scopeD scopeC) :
    (oneVec.compose twoVec).compose threeVec = oneVec.compose (twoVec.compose threeVec) :=
  SubstVec.compose_assoc oneVec twoVec threeVec

/-- **The dim-2 2-cells are strict equalities.**  A 2-cell between parallel substitutions `σ, τ` is, in
the strict setting, an EQUALITY `σ = τ`.  On the FX base, two parallel substitutions agreeing POINTWISE
are equal (`SubstVec.ext`), so the only homotopy between parallel substitutions is propositional equality
— the substitution category is strictly 1-truncated.  Crucially `SubstVec.ext` holds ZERO-AXIOM
(`SubstVec` is a finite product, so pointwise equality gives equality structurally) — the funext-free
extensionality the function-typed substitution could not prove. -/
theorem substitutionTwoCellsAreStrictEqualities {target source : Nat}
    (vecA vecB : SubstVec target source)
    (pointwise : ∀ index : Fin source, vecA.lookup index = vecB.lookup index) :
    vecA = vecB :=
  SubstVec.ext vecA vecB pointwise

end FX1Poly.Tier0.ContextOmega
