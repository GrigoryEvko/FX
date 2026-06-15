import FX1Poly.Tier0.Context.ComprehensionCategory
import FX1Poly.Tier0.Context.ModalLock

/-! # context-17 — Beck–Chevalley coherence: the dependent-adjoint naturality at full strength

`context-1` shipped the two basic Beck–Chevalley squares — `weakening_compose_lift` (the display map `p`)
and `cons_compose` (the Σ-introduction `⟨−,−⟩`).  `context-10` assembled them into the split comprehension
category.  `context-17` upgrades the naturality to FULL STRENGTH:

  * the display map is packaged as a GENUINE NATURAL TRANSFORMATION (`id ⇒ extension`), whose naturality
    square is `weakening_compose_lift` AT EVERY morphism — not a fact about specific maps but a coherence
    law of the whole substitution category;
  * the Beck–Chevalley squares PASTE: the BC square of a composite `τ ∘ σ` is the horizontal pasting of the
    component BC squares (the dependent-adjoint naturality is coherent under composition);
  * the Σ-introduction and the display projection are each natural in the context, and agree.

Everything is CONTEXT-SIDE (morphisms of the substitution / extension category) and assembled from shipped
zero-axiom lemmas (`weakening_compose_lift`, `cons_compose`, `weakening_compose_cons`, `compose_assoc`) —
no new substrate.

## What lands here (all zero-axiom)

  * **`fxDisplayTransformation`** — ★ the display map as a `RawEndofunctorTransformation` from the identity
    endofunctor to `fxContextExtensionFunctor` (`context-7`): the component at `Γ` is the display projection
    `weakening : Γ ⟶ Γ.A`, and NATURALITY is exactly `weakening_compose_lift` at every morphism.  This is "the
    dependent-adjoint (display) naturality at full strength" made a first-class natural transformation.
  * **`SubstVec.beckChevalley_paste`** — ★ the BC PASTING coherence: `p ∘ (τ⁺ ∘ σ⁺) = (τ ∘ σ) ∘ p`.  The
    Beck–Chevalley square of a composite is the horizontal pasting of the two component BC squares.  Proof:
    `compose_assoc` brackets, `weakening_compose_lift` peels each square.  This is the coherence that makes
    reindexing's naturality stable under composition — the "full strength".
  * **`SubstVec.weakening_compose_cons_natural`** — the display PROJECTION is stable under reindexing:
    `p ∘ (⟨head, tail⟩ ∘ σ) = tail ∘ σ` (the p-law commutes with substitution).
  * **`FxBeckChevalleyCoherence` / `fxBeckChevalleyCoherence`** — the assembled object: the display natural
    transformation, the BC pasting coherence, the Σ-introduction naturality (`cons_compose`), and the display
    projection stability, gathered as "the Beck–Chevalley coherence of the FX context base, at full strength".

NOT in scope here (different objects, not deferrals of THIS task): the substitution square's UNIVERSAL
property is — because `fxBaseSubstCategory` is the substitution (≈ opposite) category — a PUSHOUT (a colimit),
which belongs to the colimit layer (`context-3` / `context-20`), not the BC-naturality task.  The Π-direction
Beck–Chevalley (`f* ∘ g_* ⇒ k_* ∘ h*`) needs the Π right adjoint (LCC, `×type → context-16`), per
`context-10`'s honesty marker.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The display map as a genuine natural transformation -/

/-- ★ **The display projection is a natural transformation** `id ⇒ extension`.  The component at the context
`Γ` (scope `n`) is the display map `weakening : Γ ⟶ Γ.A` (`n ⟶ n+1`), and NATURALITY holds for EVERY
substitution `σ`: `σ ∘ p = p ∘ σ⁺` — exactly the Beck–Chevalley square `weakening_compose_lift`.  Packaging
the display map as a `RawEndofunctorTransformation` is "the dependent-adjoint naturality at full strength": the
square is not a fact about particular maps but a coherence law of the whole substitution category, between the
identity endofunctor and the `context-7` context-extension endofunctor `fxContextExtensionFunctor`. -/
def fxDisplayTransformation :
    RawEndofunctorTransformation (RawEndofunctor.identity fxBaseSubstCategory) fxContextExtensionFunctor where
  component := fun scope => SubstVec.weakening scope
  naturality := fun morphism => (SubstVec.weakening_compose_lift morphism).symm

/-! ## Beck–Chevalley pasting: the BC square of a composite is the pasting of the squares -/

/-- ★ **Beck–Chevalley pasting coherence.**  The display Beck–Chevalley square of a COMPOSITE `τ ∘ σ` equals
the horizontal pasting of the BC squares of `σ` and `τ`: `p ∘ (τ⁺ ∘ σ⁺) = (τ ∘ σ) ∘ p`.  This is the coherence
that makes the dependent-adjoint (reindexing) naturality stable under composition — the "full strength" of
Beck–Chevalley.  Proof: reassociate (`compose_assoc`) to expose `p ∘ τ⁺`, peel it to `τ ∘ p`
(`weakening_compose_lift τ`), reassociate to expose `p ∘ σ⁺`, peel it to `σ ∘ p`
(`weakening_compose_lift σ`), reassociate back. -/
theorem SubstVec.beckChevalley_paste {innerScope midScope outerScope : Nat}
    (sigma : SubstVec outerScope midScope) (tau : SubstVec midScope innerScope) :
    (SubstVec.weakening innerScope).compose (tau.lift.compose sigma.lift)
      = (tau.compose sigma).compose (SubstVec.weakening outerScope) := by
  rw [← SubstVec.compose_assoc, SubstVec.weakening_compose_lift, SubstVec.compose_assoc,
      SubstVec.weakening_compose_lift, ← SubstVec.compose_assoc]

/-! ## The display projection is natural (stable under reindexing) -/

/-- **The display projection commutes with substitution.**  Projecting a substituted extension equals
substituting the projection: `p ∘ (⟨head, tail⟩ ∘ σ) = tail ∘ σ`.  The Σ-introduction's tail (the p-law) is
natural in the context.  Proof: `cons_compose` pushes the substitution inside the extension, then the p-law
`weakening_compose_cons` projects. -/
theorem SubstVec.weakening_compose_cons_natural {sourceScope midScope targetScope : Nat}
    (headTerm : RawTerm midScope) (tailVec : SubstVec midScope sourceScope)
    (sigma : SubstVec targetScope midScope) :
    (SubstVec.weakening sourceScope).compose ((SubstVec.cons headTerm tailVec).compose sigma)
      = tailVec.compose sigma := by
  rw [SubstVec.cons_compose, SubstVec.weakening_compose_cons]

/-! ## The Beck–Chevalley coherence, assembled -/

/-- **The Beck–Chevalley coherence of the FX context base, at full strength**, gathered as one citable
object: the display map is a natural transformation; the BC squares paste; and the Σ-introduction and the
display projection are each natural in the context.  This is `context-17`'s "dependent-adjoint naturality at
full strength" delivered as one value. -/
structure FxBeckChevalleyCoherence where
  /-- The display map is a natural transformation `id ⇒ extension` (naturality = the BC square). -/
  displayNatural : RawEndofunctorTransformation
      (RawEndofunctor.identity fxBaseSubstCategory) fxContextExtensionFunctor
  /-- ★ Beck–Chevalley pasting: the BC square of a composite is the pasting of the component squares. -/
  pasting : ∀ {innerScope midScope outerScope : Nat}
      (sigma : SubstVec outerScope midScope) (tau : SubstVec midScope innerScope),
      (SubstVec.weakening innerScope).compose (tau.lift.compose sigma.lift)
        = (tau.compose sigma).compose (SubstVec.weakening outerScope)
  /-- The Σ-introduction (comprehension extension) is natural in the context. -/
  sigmaIntroNatural : ∀ {sourceScope midScope targetScope : Nat} (headTerm : RawTerm midScope)
      (tailVec : SubstVec midScope sourceScope) (sigma : SubstVec targetScope midScope),
      (SubstVec.cons headTerm tailVec).compose sigma
        = SubstVec.cons (RawTerm.subst sigma.toRawTermSubst headTerm) (tailVec.compose sigma)
  /-- The display projection (the p-law) is natural in the context. -/
  displayProjectionNatural : ∀ {sourceScope midScope targetScope : Nat} (headTerm : RawTerm midScope)
      (tailVec : SubstVec midScope sourceScope) (sigma : SubstVec targetScope midScope),
      (SubstVec.weakening sourceScope).compose ((SubstVec.cons headTerm tailVec).compose sigma)
        = tailVec.compose sigma

/-- ★ The FX context base HAS Beck–Chevalley coherence at full strength — the witness wiring the display
natural transformation, the pasting law, and the two naturality squares. -/
def fxBeckChevalleyCoherence : FxBeckChevalleyCoherence where
  displayNatural := fxDisplayTransformation
  pasting := fun sigma tau => SubstVec.beckChevalley_paste sigma tau
  sigmaIntroNatural := fun headTerm tailVec sigma => SubstVec.cons_compose headTerm tailVec sigma
  displayProjectionNatural := fun headTerm tailVec sigma =>
    SubstVec.weakening_compose_cons_natural headTerm tailVec sigma

/-! ## Smoke: the display transformation's component is the weakening display map -/

/-- Smoke: the natural transformation's component at every context is the display projection `weakening`. -/
theorem fxDisplayTransformation_component_smoke (scope : Nat) :
    fxDisplayTransformation.component scope = SubstVec.weakening scope :=
  rfl

end FX1Poly.Tier0
