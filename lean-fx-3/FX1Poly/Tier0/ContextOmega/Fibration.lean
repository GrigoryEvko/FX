import FX1Poly.Tier0.ContextOmega.SubstitutionFree
import FX1Poly.Tier0.ContextOmega.Comprehension
import FX1Poly.Tier0.ContextOmega.Uemura

/-! # Tier0/ContextOmega/Fibration — the comprehension category / Jacobs fibred adjoints (context-10)

Jacobs' "Categorical Logic and Type Theory" frames dependent type theory as a **fibration**
`p : E → B`: the base `B` is contexts-and-substitutions (here `fxBaseSubstCategory`), and the fibre
`E_Γ` over a context is the types-in-context-Γ.  A **comprehension category** is a functor
`P : E → B^→` into the arrow category with `cod ∘ P = p` that sends Cartesian morphisms to pullback
squares; `P(A)` is the **display map** `π_A : Γ.A → Γ` and the comprehension `{Γ.A}` is context
extension.  The fibred structure adds the **adjoint string** `Σ_A ⊣ π_A^* ⊣ Π_A` (dependent sum ⊣
weakening ⊣ dependent product) and the **Beck-Chevalley condition**: substitution commutes with the
fibred adjoints (the canonical comparison map is an iso).

On the FX context base this is already realized.  The display map is `SubstVec.weakening`
(context-6's `naturalModelDisplayProjection`); comprehension is `SubstVec.cons` with its universal
property `SubstVec.cons_unique` (context-1); the fibred weakening `π^*` is `reindexType` along the
display map (context-7), STRICTLY functorial (the fibration is split); Σ is comprehension itself
(context-1's `comprehensionBijection`) and Π is the representable Π-former (context-2's
`piFormerComprehension`).  This module exhibits the comprehension fibration and proves its
operational heart — the **Beck-Chevalley square** — zero-axiom.

## What is built

  * `fibredWeakening` — the Jacobs fibred weakening functor `π^*`: reindexing a type along the
    display map `SubstVec.weakening` (context-7's `reindexType`), carrying a type over `Γ` to a type
    over `Γ.A`.
  * ★ `beckChevalleyDisplaySquare` — the **Beck-Chevalley naturality square**: weakening followed by
    the lifted substitution equals the substitution followed by weakening
    (`weakening ∘ (lift σ) = σ ∘ weakening`).  This is the genuinely-new zero-axiom theorem — the
    pullback-stability of the display map, the heart of "substitution commutes with the comprehension
    structure" — proved directly from the comprehension β-cancellation `weakening_compose_cons` (the
    lift is definitionally `⟨v0, σ∘↑⟩`, and weakening cancels the head).
  * `cartesianLift` — the Cartesian morphism `σ⁺ = liftUnderBinder σ` covering `σ` over the display
    map; `beckChevalleyDisplaySquare` is exactly the statement that it covers `σ`.
  * `fibrationIsSplit` — the cleavage is STRICTLY functorial (`A[id]=A`, `A[σ∘τ]=A[σ][τ]`): the FX
    comprehension fibration is a SPLIT fibration (context-7's `familyReindexingStrictlyFunctorial`).
  * `comprehensionPullbackUniversalProperty` — the display map is representable / the comprehension
    is the pullback of the universal display map (context-1's `SubstVec.cons_unique`).
  * `dependentSumAdjunctionBijection` — Σ ⊣ π^* operationally: the comprehension hom-bijection
    `Hom(Δ, Γ.A) ≅ Hom(Δ, Γ) × Tm(Δ)` IS the dependent-sum adjunction (context-1).
  * `dependentProductIsRepresentableFormer` — π^* ⊣ Π operationally: the Π former is a representable
    natural transformation (context-2).
  * ★ `jacobsComprehensionFibrationCore` — the headline: Beck-Chevalley ∧ split-cleavage ∧
    Π-representability, the operational core of the Jacobs comprehension fibration.

## Honest boundary (recorded, not faked)

The FULL fibred adjunctions `Σ_A ⊣ π_A^* ⊣ Π_A` as hom-set bijections over ARBITRARY type families,
and the full Beck-Chevalley iso comparing `Σ`/`Π` with reindexing along an arbitrary pullback square,
compare whole `SubstFamilyMap`/section families at every fibre — the same `funext` boundary as
context-3..9 (off the zero-axiom path).  What IS zero-axiom is the OPERATIONAL core: the
Beck-Chevalley SQUARE on substitutions (the display map's pullback-stability), the split cleavage, and
the Σ/Π operational adjoint cores (comprehension + representable former).

## Zero-axiom verification

`beckChevalleyDisplaySquare` is `weakening_compose_cons` applied at the lifted-substitution's head and
tail (the lift is definitionally a `cons`); `fibredWeakening` is `reindexType` along `weakening`;
`fibrationIsSplit` is the shipped `familyReindexingStrictlyFunctorial`;
`comprehensionPullbackUniversalProperty` is `SubstVec.cons_unique`; the Σ/Π cores are
`comprehensionBijection` / `piFormerComprehension`.  No `funext`, no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The fibred weakening functor `π^*` -/

/-- **The Jacobs fibred weakening functor `π_A^*`.**  Reindexing a type over context `scope` along the
display map `SubstVec.weakening scope : scope ⟶ scope + 1` (context-7's `reindexType`), carrying a
type over `Γ` to its weakening over the extended context `Γ.A`.  The fibred functor the dependent-sum
and dependent-product adjoints sit on either side of (`Σ_A ⊣ π_A^* ⊣ Π_A`). -/
def fibredWeakening (family : SubstActionFamily) (scope : Nat)
    (typeCell : family.sections scope) : family.sections (scope + 1) :=
  reindexType family (SubstVec.weakening scope) typeCell

/-- The fibred weakening IS reindexing along the display map (`rfl`). -/
theorem fibredWeakening_eq_reindexAlongDisplay (family : SubstActionFamily) (scope : Nat)
    (typeCell : family.sections scope) :
    fibredWeakening family scope typeCell =
      reindexType family (SubstVec.weakening scope) typeCell := rfl

/-! ## The Cartesian lift -/

/-- **The Cartesian lift `σ⁺` over the display map.**  The morphism `liftUnderBinder σ` covering `σ`:
the unique lift of a substitution `σ : Γ ⟶ Δ` to the extended contexts `Γ.A[σ] ⟶ Δ.A`.  In the
comprehension fibration this is the Cartesian morphism over `σ` at `A`. -/
def cartesianLift {target source : Nat} (substVec : SubstVec target source) :
    SubstVec (target + 1) (source + 1) :=
  substVec.liftUnderBinder

/-! ## Beck-Chevalley: substitution commutes with the display map -/

/-- ★ **The Beck-Chevalley naturality square.**  Composing the display map with the Cartesian lift of
`σ` equals composing `σ` with the display map: `weakening ∘ (lift σ) = σ ∘ weakening`.  This is the
PULLBACK-STABILITY of the display map — reindexing the display map `π` along `σ` gives the display map
of the reindexed type — and the genuine content of "substitution commutes with the comprehension
structure" (the Beck-Chevalley condition for the comprehension fibration).  Proved directly: the lift
is definitionally `⟨v0, σ∘↑⟩`, and the display map's β-cancellation `weakening_compose_cons` projects
it back to the tail `σ∘↑`. -/
theorem beckChevalleyDisplaySquare {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) :
    (SubstVec.weakening sourceScope).compose substVec.liftUnderBinder =
      substVec.compose (SubstVec.weakening targetScope) :=
  SubstVec.weakening_compose_cons
    (RawTerm.mkGen .gen_var ⟨0, Nat.succ_pos targetScope⟩ .childNil)
    (substVec.compose (SubstVec.weakening targetScope))

/-- **The Cartesian lift covers its base substitution** — Beck-Chevalley restated in the fibration
vocabulary: the Cartesian morphism `σ⁺` over the display map projects (via `weakening`) back to `σ`
composed with weakening, so it genuinely lies over `σ`. -/
theorem cartesianLift_coversBase {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) :
    (SubstVec.weakening sourceScope).compose (cartesianLift substVec) =
      substVec.compose (SubstVec.weakening targetScope) :=
  beckChevalleyDisplaySquare substVec

/-! ## The fibration is split + the comprehension pullback -/

/-- **The comprehension fibration is SPLIT.**  The cleavage (reindexing `reindexType`) is STRICTLY
functorial — `A[id] = A` and `A[σ∘τ] = A[σ][τ]` as EQUALITIES, not just coherent isos — so the FX
comprehension fibration is a split fibration (context-7's `familyReindexingStrictlyFunctorial`, the
syntactic base needs no strictification). -/
theorem fibrationIsSplit (family : SubstActionFamily) :
    (∀ (scope : Nat) (typeCell : family.sections scope),
        reindexType family (SubstVec.identity scope) typeCell = typeCell) ∧
    (∀ {scopeA scopeB scopeC : Nat} (firstVec : SubstVec scopeB scopeA)
        (secondVec : SubstVec scopeC scopeB) (typeCell : family.sections scopeA),
        reindexType family (firstVec.compose secondVec) typeCell =
          reindexType family secondVec (reindexType family firstVec typeCell)) :=
  familyReindexingStrictlyFunctorial family

/-- **The comprehension is the pullback of the universal display map** (the display map is a
representable map).  The extension `cons headTerm tailVec` is the UNIQUE morphism whose display
projection is `tailVec` and whose generic element (zeroth lookup) is `headTerm` — context-1's
`SubstVec.cons_unique`, the universal property that makes `P` a comprehension category (Cartesian
morphisms ↦ pullbacks). -/
theorem comprehensionPullbackUniversalProperty {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (candidate : SubstVec target (source + 1))
    (projectsToTail : (SubstVec.weakening source).compose candidate = tailVec)
    (zerothIsHead : candidate.lookup ⟨0, Nat.succ_pos source⟩ = headTerm) :
    candidate = SubstVec.cons headTerm tailVec :=
  SubstVec.cons_unique headTerm tailVec candidate projectsToTail zerothIsHead

/-! ## The fibred adjoints Σ ⊣ π^* ⊣ Π (operational cores) -/

/-- **Σ ⊣ π^* — the dependent-sum adjunction (operational core).**  The comprehension hom-bijection
`Hom(Δ, Γ.A) ≅ Hom(Δ, Γ) × Tm(Δ)` (context-1's `comprehensionBijection`) IS the left-adjoint
`Σ_A ⊣ π_A^*` at the democratic level: a substitution into the extended context `Γ.A` is exactly a
substitution into `Γ` together with a term, the Σ-introduction pairing. -/
theorem dependentSumAdjunctionBijection {targetScope sourceScope : Nat} :
    (∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
    (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended) :=
  comprehensionBijection

/-- **π^* ⊣ Π — the dependent-product adjunction (operational core).**  The Π type-former is a
REPRESENTABLE natural transformation `(A : U, B : U^A) → Ty` (context-2's `piFormerComprehension`):
Π is the right adjoint to weakening, realized as the representable former that the Uemura bijection
pairs with the display-map pullback. -/
theorem dependentProductIsRepresentableFormer : IsRepresentableFormer piFormerMap :=
  piFormerComprehension

/-! ## The headline -/

/-- ★ **The Jacobs comprehension fibration, operational core.**  On the FX context base the
comprehension fibration `p : E → B` satisfies (a) the **Beck-Chevalley square** — substitution
commutes with the display map (the display map is pullback-stable); (b) **split cleavage** —
reindexing is strictly functorial (`A[id] = A`); and (c) **Π-representability** — the dependent
product is a representable former (the right adjoint `π^* ⊣ Π`).  With Σ as comprehension
(`dependentSumAdjunctionBijection`) and the comprehension UP
(`comprehensionPullbackUniversalProperty`), this is the operational heart of the Jacobs fibred
adjoints `Σ_A ⊣ π_A^* ⊣ Π_A` + Beck-Chevalley.  (The full hom-set adjunctions over arbitrary families
are the recorded funext boundary.) -/
theorem jacobsComprehensionFibrationCore {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) (family : SubstActionFamily)
    (typeCell : family.sections sourceScope) :
    (SubstVec.weakening sourceScope).compose substVec.liftUnderBinder =
      substVec.compose (SubstVec.weakening targetScope) ∧
    reindexType family (SubstVec.identity sourceScope) typeCell = typeCell ∧
    IsRepresentableFormer piFormerMap :=
  ⟨beckChevalleyDisplaySquare substVec,
   reindexType_identity family sourceScope typeCell,
   piFormerComprehension⟩

end FX1Poly.Tier0.ContextOmega
