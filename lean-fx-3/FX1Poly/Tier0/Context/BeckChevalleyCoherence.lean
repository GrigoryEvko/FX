import FX1Poly.Tier0.Context.ComprehensionCategory
import FX1Poly.Tier0.Context.ModalLock
import FX1Poly.Tier0.Context.FibrationCategory

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
  * **`fxDisplayTowerTransformation`** — ★ the ITERATED display tower `id ⇒ extension ∘ extension`, the
    HORIZONTAL (Godement) composite of the display 2-cell with itself, built with `context-4`'s strict
    2-category `End(𝒞)`.  Its naturality is FREE: Beck–Chevalley for a TELESCOPE of extensions is the
    2-categorical composite of the single-step squares — the sharpest form of "naturality at full strength",
    the BC square is a 2-cell that COMPOSES.
  * **`SubstVec.weakening_tower_natural`** — ★ the explicit, directly-citable telescope BC `p² ∘ σ⁺⁺ = σ ∘ p²`
    (the SubstVec form of the tower transformation's naturality; the Beck–Chevalley reading of `context-6`'s
    `fatherTower`).
  * **`fxComprehensionPullback`** — ★ THE categorical heart: the substitution/display square is a genuine
    PULLBACK in the real category of contexts `𝒞` (`context-15`'s `fxBaseSubstCategory.opposite`).  "Display
    maps are stable under pullback" IS Beck–Chevalley — this upgrades the commuting square
    (`weakening_compose_lift`) to its full universal property (`PullbackSquare`), the mediator being the
    comprehension pairing and the factorisations the v/p-laws (`comprehensionBackward_forward`).
  * **`FxBeckChevalleyCoherence` / `fxBeckChevalleyCoherence`** — the assembled object: the display natural
    transformation, the BC pasting coherence, the Σ-introduction naturality (`cons_compose`), the display
    projection stability, the iterated display tower, the telescope BC, AND the genuine pullback, gathered as
    "the Beck–Chevalley coherence of the FX context base, at full strength".

NOW IN SCOPE via `context-15` (the upgrade): the substitution square's UNIVERSAL property — formerly noted
as a PUSHOUT in `fxBaseSubstCategory = 𝒞ᵒᵖ` (colimit layer, `context-3` / `context-20`) — lands HERE as a
genuine PULLBACK in `𝒞 = fxBaseSubstCategory.opposite` (`fxComprehensionPullback`), the natural home for
"Beck–Chevalley".  STILL deferred: the Π-direction Beck–Chevalley (`f* ∘ g_* ⇒ k_* ∘ h*`) needs the Π right
adjoint (LCC, `×type → context-16`), per `context-10`'s honesty marker.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0
open FX1Poly.Polygraph

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

/-! ## The display tower: Beck–Chevalley composes 2-categorically (the Godement product) -/

/-- ★ **The iterated display tower is a natural transformation** `id ⇒ extension ∘ extension`.  The
HORIZONTAL (Godement) composite `fxDisplayTransformation ⋆ fxDisplayTransformation` of the display 2-cell
with itself is the 2-fold display projection `Γ.A.B ⟶ Γ` (`weakening` then `weakening`), and its NATURALITY
comes FOR FREE from `context-4`'s strict 2-category `End(𝒞)` (the `hcomp` Godement product): Beck–Chevalley
for a TELESCOPE of extensions is the 2-categorical composite of the single-step squares, NOT a separately
proved fact.  This is the sharpest reading of "naturality at full strength" — the display BC square is a
2-cell that COMPOSES.  The `n`-fold tower follows by iterating `hcomp`. -/
def fxDisplayTowerTransformation :
    RawEndofunctorTransformation (RawEndofunctor.identity fxBaseSubstCategory)
      (fxContextExtensionFunctor.compose fxContextExtensionFunctor) :=
  fxDisplayTransformation.hcomp fxDisplayTransformation

/-- The tower transformation's component at `Γ` is the 2-fold display projection `p ∘ p` (`weakening scope`
then `weakening (scope+1)`): the C-system father map iterated twice. -/
theorem fxDisplayTowerTransformation_component (scope : Nat) :
    fxDisplayTowerTransformation.component scope
      = (SubstVec.weakening scope).compose (SubstVec.weakening (scope + 1)) :=
  rfl

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

/-- ★ **Beck–Chevalley for the display TOWER** — `p² ∘ σ⁺⁺ = σ ∘ p²`.  The 2-fold display projection
`Γ.A.B ⟶ Γ` is natural in `Γ`: it commutes with the twice-lifted substitution.  This is the explicit,
directly-citable `SubstVec` form of `fxDisplayTowerTransformation`'s (free) naturality, and the
Beck–Chevalley reading of `context-6`'s `fatherTower` (the C-system descent to the root, iterated).  Proof:
two applications of the single-step square `weakening_compose_lift`, bracketed by `compose_assoc`. -/
theorem SubstVec.weakening_tower_natural {sourceScope targetScope : Nat}
    (sigma : SubstVec targetScope sourceScope) :
    ((SubstVec.weakening sourceScope).compose (SubstVec.weakening (sourceScope + 1))).compose
        sigma.lift.lift
      = sigma.compose
          ((SubstVec.weakening targetScope).compose (SubstVec.weakening (targetScope + 1))) := by
  rw [SubstVec.compose_assoc (SubstVec.weakening sourceScope) (SubstVec.weakening (sourceScope + 1))
        sigma.lift.lift,
      SubstVec.weakening_compose_lift sigma.lift,
      ← SubstVec.compose_assoc (SubstVec.weakening sourceScope) sigma.lift
        (SubstVec.weakening (targetScope + 1)),
      SubstVec.weakening_compose_lift sigma,
      SubstVec.compose_assoc sigma (SubstVec.weakening targetScope)
        (SubstVec.weakening (targetScope + 1))]

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

/-! ## Beck–Chevalley at FULL strength: the substitution square is a genuine PULLBACK in 𝒞 -/

/-- ★ **The Beck–Chevalley square is a pullback in the real category of contexts `𝒞`.**  For a
substitution `σ : Δ ⟶ Γ` and the display map `p : Γ.A ⟶ Γ`, the comprehension `Δ.A[σ]`, with its display
`p : Δ.A[σ] ⟶ Δ` and the lift `σ⁺ : Δ.A[σ] ⟶ Γ.A`, IS the pullback of `p` along `σ`.  This builds the
`PullbackSquare` (mediator EXISTENCE); `fxComprehensionPullback_isStrict` proves the mediator is also UNIQUE,
upgrading it to a genuine STRICT pullback (a real limit, not merely a weakly-universal cone).  "Display maps are
stable under pullback" is exactly what Beck–Chevalley asserts — so this is the categorical heart of the
coherence, upgraded from the commuting square (`weakening_compose_lift`) to the full universal property.

Stated in `context-15`'s genuine `𝒞 = fxBaseSubstCategory.opposite` (a pullback there; in
`fxBaseSubstCategory = 𝒞ᵒᵖ` the same square is a PUSHOUT, the colimit-layer reading).  The mediator out of
a cone `(toBase : X ⟶ Δ, toExtension : X ⟶ Γ.A)` is `⟨q[toExtension], toBase⟩` — the comprehension pairing
of `toBase` with the `A`-component `q[toExtension] = toExtension.lookup 0` of `toExtension`.  The two
factorisations are the p-law (`weakening_compose_cons`) and the comprehension round-trip
(`comprehensionBackward_forward`, the v/p-laws), the cone condition supplying the tail.  Funext-free: the
universal property here is EXISTENCE of the mediator (`PullbackSquare.isUniversal`), and `cons` is a `Prod`,
so its η is definitional. -/
def fxComprehensionPullback {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    PullbackSquare fxContextCategory (objectA := contextScope) (objectB := baseScope + 1)
      (objectC := baseScope) sigma (SubstVec.weakening baseScope) where
  pullbackObject := contextScope + 1
  projectionLeft := SubstVec.weakening contextScope
  projectionRight := sigma.lift
  commutes := by
    show sigma.compose (SubstVec.weakening contextScope)
        = (SubstVec.weakening baseScope).compose sigma.lift
    exact (SubstVec.weakening_compose_lift sigma).symm
  isUniversal := fun candidateObject candidateToBase candidateToExtension coneCondition => by
    refine ⟨SubstVec.cons (candidateToExtension.lookup ⟨0, Nat.succ_pos baseScope⟩)
              candidateToBase, ?_, ?_⟩
    · show (SubstVec.weakening contextScope).compose
            (SubstVec.cons (candidateToExtension.lookup ⟨0, Nat.succ_pos baseScope⟩)
              candidateToBase)
          = candidateToBase
      exact SubstVec.weakening_compose_cons _ candidateToBase
    · have coneBase : sigma.compose candidateToBase
          = (SubstVec.weakening baseScope).compose candidateToExtension := coneCondition
      show (SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos contextScope⟩)
              (sigma.compose (SubstVec.weakening contextScope))).compose
            (SubstVec.cons (candidateToExtension.lookup ⟨0, Nat.succ_pos baseScope⟩)
              candidateToBase)
          = candidateToExtension
      rw [SubstVec.cons_compose, SubstVec.subst_varCell, SubstVec.cons_lookup_zero,
          SubstVec.compose_assoc, SubstVec.weakening_compose_cons, coneBase]
      exact SubstVec.comprehensionBackward_forward candidateToExtension

/-- ★ **The comprehension pullback is a GENUINE (strict) pullback** — the mediator is UNIQUE, not merely
existent.  `PullbackSquare` records only mediator existence (`isUniversal` is `∃`), so `fxComprehensionPullback`
on its own is a WEAK pullback; this theorem supplies the missing uniqueness half, upgrading it to a real
categorical limit.  This is the faithful form of Uemura's AXIOM 1 for the FX DISPLAY maps (the non-degenerate
representable class — not the iso class the shipped `RepresentableMapCategory` instances use).

Proof: a morphism `m : X ⟶ Δ.A[σ]` into the pullback is determined by its comprehension projections
`(q[m], p ∘ m) = comprehensionForward m` (the bijection `comprehensionBackward_forward`).  Agreement with
`projectionLeft = p` fixes the tail `p ∘ m`; agreement with `projectionRight = σ⁺` fixes the head `q[m]`
(the `q`-projection of `σ⁺ ∘ m` is `m`'s zeroth variable, by `subst_varCell`).  So two mediators agreeing on
both projections have equal `comprehensionForward`, hence are equal.  Funext-free (`cons` is a `Prod`). -/
theorem fxComprehensionPullback_isStrict {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    (fxComprehensionPullback sigma).IsStrict := by
  intro apexScope mediatorOne mediatorTwo projLeftEq projRightEq
  have qProjection : ∀ (mediator : SubstVec apexScope (contextScope + 1)),
      (sigma.lift.compose mediator).lookup ⟨0, Nat.succ_pos baseScope⟩
        = mediator.lookup ⟨0, Nat.succ_pos contextScope⟩ := fun mediator =>
    (SubstVec.lookup_compose sigma.lift mediator ⟨0, Nat.succ_pos baseScope⟩).trans
      (SubstVec.subst_varCell mediator ⟨0, Nat.succ_pos contextScope⟩)
  have tailEq : (SubstVec.weakening contextScope).compose mediatorOne
      = (SubstVec.weakening contextScope).compose mediatorTwo := projLeftEq
  have liftEq : sigma.lift.compose mediatorOne = sigma.lift.compose mediatorTwo := projRightEq
  have headEq : mediatorOne.lookup ⟨0, Nat.succ_pos contextScope⟩
      = mediatorTwo.lookup ⟨0, Nat.succ_pos contextScope⟩ :=
    (qProjection mediatorOne).symm.trans
      ((congrArg (fun composed => composed.lookup ⟨0, Nat.succ_pos baseScope⟩) liftEq).trans
        (qProjection mediatorTwo))
  have forwardEq : SubstVec.comprehensionForward mediatorOne
      = SubstVec.comprehensionForward mediatorTwo := by
    show (mediatorOne.lookup ⟨0, Nat.succ_pos contextScope⟩,
            (SubstVec.weakening contextScope).compose mediatorOne)
       = (mediatorTwo.lookup ⟨0, Nat.succ_pos contextScope⟩,
            (SubstVec.weakening contextScope).compose mediatorTwo)
    rw [headEq, tailEq]
  exact (SubstVec.comprehensionBackward_forward mediatorOne).symm.trans
    ((congrArg SubstVec.comprehensionBackward forwardEq).trans
      (SubstVec.comprehensionBackward_forward mediatorTwo))

/-! ## Uemura AXIOM 3 strictly: the display TOWER (a composite of displays) has a strict pullback -/

/-- ★ **The display TOWER's pullback in `𝒞`, via the pasting lemma.**  The 2-fold display
`p² = p_{Γ.A} ∘ p_Γ : Γ.A.B ⟶ Γ` (a COMPOSITE of representable display maps) pulled back along any
substitution `σ` is the genuine pullback obtained by PASTING two comprehension pullbacks
(`PullbackSquare.paste` of the two single-display pullbacks, each oriented by `swap`).  This is the
categorical content of Uemura AXIOM 3 — representable maps closed under composition AND pullback-stable —
for the FX displays: the pulled-back tower is `σ⁺⁺` over the new 2-fold display `Δ.A[σ].B[σ⁺] ⟶ Δ`. -/
def fxComprehensionTowerPullback {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    PullbackSquare fxContextCategory (objectA := baseScope + 2) (objectB := contextScope)
      (objectC := baseScope)
      ((SubstVec.weakening baseScope).compose (SubstVec.weakening (baseScope + 1))) sigma := by
  exact (fxComprehensionPullback sigma).swap.paste (fxComprehensionPullback sigma.lift).swap

/-- ★ **The display tower's pullback is STRICT** — the pasting of two strict pullbacks is strict
(`PullbackSquare.paste_isStrict`).  So Uemura AXIOM 3 holds STRICTLY for the FX display maps: composites of
representables have genuine (unique-mediator) pullbacks, not merely weakly-universal cones. -/
theorem fxComprehensionTowerPullback_isStrict {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    (fxComprehensionTowerPullback sigma).IsStrict :=
  PullbackSquare.paste_isStrict
    (PullbackSquare.swap_isStrict (fxComprehensionPullback_isStrict sigma))
    (PullbackSquare.swap_isStrict (fxComprehensionPullback_isStrict sigma.lift))

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
  /-- ★ The iterated display tower `id ⇒ extension ∘ extension` — Beck–Chevalley composes 2-categorically
  (the `End(𝒞)` Godement product); the tower's naturality is free. -/
  displayTowerNatural : RawEndofunctorTransformation
      (RawEndofunctor.identity fxBaseSubstCategory)
      (fxContextExtensionFunctor.compose fxContextExtensionFunctor)
  /-- ★ Beck–Chevalley for the display tower: `p² ∘ σ⁺⁺ = σ ∘ p²` (the telescope square, the explicit
  SubstVec form of `displayTowerNatural`'s naturality). -/
  towerNatural : ∀ {sourceScope targetScope : Nat} (sigma : SubstVec targetScope sourceScope),
      ((SubstVec.weakening sourceScope).compose (SubstVec.weakening (sourceScope + 1))).compose
          sigma.lift.lift
        = sigma.compose
            ((SubstVec.weakening targetScope).compose (SubstVec.weakening (targetScope + 1)))
  /-- ★ Beck–Chevalley as a genuine PULLBACK in the real category of contexts `𝒞`: for every substitution
  `σ`, the comprehension/display square is the pullback of the display map along `σ` — display maps are
  stable under pullback, the categorical heart of Beck–Chevalley (upgrading the commuting square to its
  full universal property). -/
  displayPullback : ∀ {contextScope baseScope : Nat} (sigma : SubstVec contextScope baseScope),
      PullbackSquare fxContextCategory (objectA := contextScope) (objectB := baseScope + 1)
        (objectC := baseScope) sigma (SubstVec.weakening baseScope)

/-- ★ The FX context base HAS Beck–Chevalley coherence at full strength — the witness wiring the display
natural transformation, the pasting law, the two single-step naturality squares, the iterated display tower
(BC composes 2-categorically), and the telescope BC square. -/
def fxBeckChevalleyCoherence : FxBeckChevalleyCoherence where
  displayNatural := fxDisplayTransformation
  pasting := fun sigma tau => SubstVec.beckChevalley_paste sigma tau
  sigmaIntroNatural := fun headTerm tailVec sigma => SubstVec.cons_compose headTerm tailVec sigma
  displayProjectionNatural := fun headTerm tailVec sigma =>
    SubstVec.weakening_compose_cons_natural headTerm tailVec sigma
  displayTowerNatural := fxDisplayTowerTransformation
  towerNatural := fun sigma => SubstVec.weakening_tower_natural sigma
  displayPullback := fun sigma => fxComprehensionPullback sigma

/-! ## Smoke: the display transformation's component is the weakening display map -/

/-- Smoke: the natural transformation's component at every context is the display projection `weakening`. -/
theorem fxDisplayTransformation_component_smoke (scope : Nat) :
    fxDisplayTransformation.component scope = SubstVec.weakening scope :=
  rfl

/-- Smoke: the Beck–Chevalley pullback's right projection is the lift `σ⁺` — the pullback object is the
substituted comprehension `Δ.A[σ]`, not a degenerate cone. -/
theorem fxComprehensionPullback_projectionRight_smoke {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    (fxComprehensionPullback sigma).projectionRight = sigma.lift :=
  rfl

end FX1Poly.Tier0
