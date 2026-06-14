import FX1Poly.Tier0.ContextOmega.Biequivalence
import FX1Poly.Tier0.FxBaseSubstDisplayMap

/-! # Tier0/ContextOmega/Strictification — the FX context base is already split (context-7)

The coherence problem of categorical type theory: in a SEMANTIC model (a locally cartesian closed
category, a comprehension category) reindexing a type `A` along a substitution `σ` is computed by
PULLBACK of `A`'s display map along `σ`.  Pullbacks are only defined UP TO ISOMORPHISM, so
reindexing is only PSEUDO-functorial: `A[σ∘τ] ≅ A[σ][τ]` and `A[id] ≅ A` hold up to a coherent
isomorphism, not on the nose.  But the syntax of type theory demands STRICT functoriality
(`A[σ∘τ] = A[σ][τ]` as an equality — substitutions compose definitionally).  The **strictification /
coherence theorem** bridges the two: every pseudo-functorial model is equivalent to a STRICT (split)
one.  The two classical constructions are Hofmann's right-adjoint splitting and Lumsdaine–Warren's
**local universes** ("an overlooked coherence construction for dependent type theories", 2015), where
a type is repackaged as a classifying map into a local universe and reindexing becomes PRECOMPOSITION
— strictly functorial because composition is strictly associative.

## What is built — the FX base IS its own strictification

The FX context base `fxBaseSubstCategory` is a SYNTACTIC model: its reindexing is de Bruijn
substitution, which is strictly functorial ON THE NOSE.  So the coherence problem is VACUOUS here —
the FX base is already split, and the local-universes construction applied to it is the IDENTITY
strictification (the coherence isomorphisms are reflexivity).  This module exhibits that:

  * `reindexType` — reindex a type-position cell along a substitution morphism (the comprehension
    category's display-map pullback), computed as the `SubstActionFamily` action.
  * ★ `reindexType_identity` — the strict identity coherence `A[id] = A` (an EQUALITY, the
    coherence iso is `rfl`); it is the family's `mapsIdentity`.
  * ★ `reindexType_compose` — the strict functoriality coherence `A[σ∘τ] = A[σ][τ]` (an EQUALITY);
    it is the family's `mapsComposition`.  This is the law the local-universes construction exists to
    enforce; on the FX base it holds because substitution composition is strictly associative.
  * `substitutionStrictlyAssociative` / `…UnitalLeft` / `…UnitalRight` — the local-universes
    precomposition essence: reindexing reduces to PRECOMPOSITION of classifying maps, and its strict
    functoriality is the base category's `composeAssoc` / `identityLeft` / `identityRight` — strict
    equalities, the reason the FX base is split.
  * `reindexType_typeCellFamily` — for the type-cell family the classifier IS the type cell and
    reindexing IS syntactic substitution (`RawTerm.subst`), `rfl`: the natural-model classifying map
    reindexed by precomposition.
  * `familyReindexingStrictlyFunctorial` / `fxBaseSubstCategoryIsStrict` / ★ `fxBaseIsSplitModel` —
    the headline: every `SubstActionFamily` is a STRICT (not pseudo) presheaf of types and the base
    is a strict (not bi-) category, so the FX context base is a SPLIT model — coherence solved on the
    nose, no local-universes repackaging needed.

## Honest boundary (recorded, not faked)

The GENERAL strictification theorem — "every PSEUDO-functorial comprehension category is equivalent
to a split one" — is a statement about ARBITRARY models: it builds the local-universes model and a
biequivalence to the original, whose comparison functors carry naturality coherences comparing whole
presheaf maps (`SubstFamilyMap.component`, the `morphismMap` of a functor) — infinite function
families → `funext` = `Quot.sound`-derived, OFF the zero-axiom path (the same boundary as
context-3/4/5/6).  What IS zero-axiom is that the FX SYNTACTIC base needs no strictification: its
reindexing is strictly functorial and its composition strictly associative, definitionally.

## Zero-axiom verification

`reindexType_identity` / `_compose` are the family's `mapsIdentity` / `mapsComposition`; the base
strictness theorems are `fxBaseSubstCategory`'s `composeAssoc` / `identityLeft` / `identityRight`
(via `by exact`, default transparency — context-4's recipe for the def-projected base); the headline
bundles conjoin them.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## Type reindexing — the display-map pullback -/

/-- **Reindex a type-position cell along a substitution morphism** of the context base.  In the
comprehension-category view this is the PULLBACK of the type's display map along `substMorphism`; on
the FX base it is computed strictly by the `SubstActionFamily` action.  A morphism
`targetScope ⟶ sourceScope` of `fxBaseSubstCategory` is a `SubstVec targetScope sourceScope`, and it
reindexes a type over `sourceScope` to a type over `targetScope`. -/
def reindexType {sourceScope targetScope : Nat} (family : SubstActionFamily)
    (substMorphism : SubstVec targetScope sourceScope) (typeCell : family.sections sourceScope) :
    family.sections targetScope :=
  family.substAction substMorphism typeCell

/-- ★ **Strict identity coherence** `A[id] = A`.  Reindexing along the identity substitution is the
identity on types — ON THE NOSE, not up to a coherence isomorphism.  In a pseudo-functorial semantic
model this would be a chosen iso `A[id] ≅ A`; on the split FX base it is an EQUALITY (the coherence
iso is `rfl`).  It is the family's `mapsIdentity`. -/
theorem reindexType_identity (family : SubstActionFamily) (scope : Nat)
    (typeCell : family.sections scope) :
    reindexType family (SubstVec.identity scope) typeCell = typeCell :=
  family.mapsIdentity scope typeCell

/-- ★ **Strict functoriality coherence** `A[σ∘τ] = A[σ][τ]`.  Reindexing along a composite
substitution is reindexing twice — ON THE NOSE.  This is THE coherence the local-universes
construction is built to enforce in a semantic model (where it would be a chosen isomorphism
`A[σ∘τ] ≅ A[σ][τ]`); on the split FX base it is a definitional EQUALITY, because substitution
composition is strictly associative.  It is the family's `mapsComposition`. -/
theorem reindexType_compose (family : SubstActionFamily) {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (typeCell : family.sections scopeA) :
    reindexType family (firstVec.compose secondVec) typeCell =
      reindexType family secondVec (reindexType family firstVec typeCell) :=
  family.mapsComposition firstVec secondVec typeCell

/-! ## The base is strict — the local-universes precomposition essence -/

/-- **Substitution composition is strictly associative.**  In the local-universes construction a type
over `Γ` is a classifying map and reindexing is PRECOMPOSITION; strict functoriality of reindexing
reduces to associativity of composition in the base.  On the FX context base that associativity is
`fxBaseSubstCategory`'s `composeAssoc` — an EQUALITY, not a chosen isomorphism (this is why the FX
base needs no strictification). -/
theorem substitutionStrictlyAssociative {scopeA scopeB scopeC scopeD : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (thirdVec : SubstVec scopeD scopeC) :
    (firstVec.compose secondVec).compose thirdVec =
      firstVec.compose (secondVec.compose thirdVec) := by
  exact fxBaseSubstCategory.composeAssoc firstVec secondVec thirdVec

/-- **Left identity is strict** `id ∘ σ = σ` — the unit half of precomposition functoriality, the
base category's `identityLeft`, holding as an equality. -/
theorem substitutionStrictlyUnitalLeft {sourceScope targetScope : Nat}
    (someVec : SubstVec targetScope sourceScope) :
    (SubstVec.identity sourceScope).compose someVec = someVec := by
  exact fxBaseSubstCategory.identityLeft someVec

/-- **Right identity is strict** `σ ∘ id = σ` — the other unit half, the base category's
`identityRight`, holding as an equality. -/
theorem substitutionStrictlyUnitalRight {sourceScope targetScope : Nat}
    (someVec : SubstVec targetScope sourceScope) :
    someVec.compose (SubstVec.identity targetScope) = someVec := by
  exact fxBaseSubstCategory.identityRight someVec

/-! ## The natural-model classifier specialization -/

/-- **Reindexing a type-cell is syntactic substitution.**  For the type-cell family the classifying
map IS the type cell, and reindexing it along a substitution is exactly applying that substitution
(`RawTerm.subst`) — the natural-model classifying map reindexed by precomposition, `rfl` by
construction.  Strict functoriality is then visibly the substitution-composition law. -/
theorem reindexType_typeCellFamily {sourceScope targetScope : Nat}
    (substMorphism : SubstVec targetScope sourceScope) (typeCell : RawTerm sourceScope) :
    reindexType typeCellFamily substMorphism typeCell =
      RawTerm.subst substMorphism.toRawTermSubst typeCell := rfl

/-! ## The headline — the FX context base is a SPLIT model -/

/-- ★ **Every `SubstActionFamily` reindexes strictly functorially.**  A type-family over the FX
context base is a STRICT (not pseudo-) presheaf of types: reindexing satisfies `A[id] = A` and
`A[σ∘τ] = A[σ][τ]` as equalities, simultaneously.  So no coherence repackaging is needed — the
family is already split. -/
theorem familyReindexingStrictlyFunctorial (family : SubstActionFamily) :
    (∀ (scope : Nat) (typeCell : family.sections scope),
        reindexType family (SubstVec.identity scope) typeCell = typeCell) ∧
    (∀ (scopeA scopeB scopeC : Nat) (firstVec : SubstVec scopeB scopeA)
        (secondVec : SubstVec scopeC scopeB) (typeCell : family.sections scopeA),
        reindexType family (firstVec.compose secondVec) typeCell =
          reindexType family secondVec (reindexType family firstVec typeCell)) :=
  ⟨reindexType_identity family,
   fun _scopeA _scopeB _scopeC firstVec secondVec typeCell =>
     reindexType_compose family firstVec secondVec typeCell⟩

/-- ★ **The FX context base is a strict (not bi-) category.**  Composition of substitutions is
strictly associative and strictly unital — the base of the model is split, not merely coherent up to
isomorphism. -/
theorem fxBaseSubstCategoryIsStrict :
    (∀ (scopeA scopeB scopeC scopeD : Nat) (firstVec : SubstVec scopeB scopeA)
        (secondVec : SubstVec scopeC scopeB) (thirdVec : SubstVec scopeD scopeC),
        (firstVec.compose secondVec).compose thirdVec =
          firstVec.compose (secondVec.compose thirdVec)) ∧
    (∀ (sourceScope targetScope : Nat) (someVec : SubstVec targetScope sourceScope),
        (SubstVec.identity sourceScope).compose someVec = someVec) ∧
    (∀ (sourceScope targetScope : Nat) (someVec : SubstVec targetScope sourceScope),
        someVec.compose (SubstVec.identity targetScope) = someVec) :=
  ⟨fun _a _b _c _d firstVec secondVec thirdVec =>
     substitutionStrictlyAssociative firstVec secondVec thirdVec,
   fun _s _t someVec => substitutionStrictlyUnitalLeft someVec,
   fun _s _t someVec => substitutionStrictlyUnitalRight someVec⟩

/-- ★ **The FX context base is a SPLIT model — the local-universes coherence is the identity.**  The
type-cell family reindexes strictly functorially AND the base category is strict, so the syntactic FX
model is already split: the coherence problem the local-universes / right-adjoint-splitting
constructions solve is VACUOUS here (the comparison isomorphisms are equalities).  The general
"every pseudo-model strictifies" theorem is the recorded funext boundary. -/
theorem fxBaseIsSplitModel :
    (∀ (scope : Nat) (typeCell : typeCellFamily.sections scope),
        reindexType typeCellFamily (SubstVec.identity scope) typeCell = typeCell) ∧
    (∀ (scopeA scopeB scopeC : Nat) (firstVec : SubstVec scopeB scopeA)
        (secondVec : SubstVec scopeC scopeB) (typeCell : typeCellFamily.sections scopeA),
        reindexType typeCellFamily (firstVec.compose secondVec) typeCell =
          reindexType typeCellFamily secondVec (reindexType typeCellFamily firstVec typeCell)) ∧
    (∀ (scopeA scopeB scopeC scopeD : Nat) (firstVec : SubstVec scopeB scopeA)
        (secondVec : SubstVec scopeC scopeB) (thirdVec : SubstVec scopeD scopeC),
        (firstVec.compose secondVec).compose thirdVec =
          firstVec.compose (secondVec.compose thirdVec)) :=
  ⟨(familyReindexingStrictlyFunctorial typeCellFamily).1,
   (familyReindexingStrictlyFunctorial typeCellFamily).2,
   fun _a _b _c _d firstVec secondVec thirdVec =>
     substitutionStrictlyAssociative firstVec secondVec thirdVec⟩

end FX1Poly.Tier0.ContextOmega
