import FX1Poly.Tier0.Context.BeckChevalleyCoherence
import FX1Poly.Tier0.Context.MultimodalNormalization

/-! # context-21 [CAPSTONE] — the standalone modal Representable Map Category `𝒞`

`context-21` is the CAPSTONE of the context axis: it gathers the shipped context-side structures of
`context-4 … context-20` into ONE standalone value — the modal Representable Map Category (Uemura's CwR,
arXiv:1904.04097) on the FX category of contexts `𝒞 = fxBaseSubstCategory.opposite` (`context-15`).  Marked
`⟦core=𝒞 standalone; assembly→Core/fib⟧`: the CORE is the standalone context category with its
comprehension / representability / modal-lock / normalization structure (all context-side, shipped); the
cross-axis MODEL assembly — gluing the type, term, and mode axes so the RMC becomes a genuine model of the
full type-theory presentation — is `fib` work (`fib-3`/`fib-5`/`fib-8`), deferred.

## What this capstone bundles (every field a shipped context-side witness)

  * **`comprehension`** (`context-10` `fxComprehensionCategory`) — the split display fibration + the Uemura
    representability bijection `Sub(Δ, Γ.A) ≅ Sub(Δ, Γ) × Tm(Δ, A)` (the `cartesianUniversal` cleavage) +
    the fibred Σ Beck–Chevalley squares.  This is the COMPREHENSION + the Uemura representable-object data.
  * **`modalLock`** (`context-4` `fxIdentityLock`) — the modal lock adjunction `◐_μ ⊣ ⟨μ|−⟩` on the
    substitution base (here the trivial-mode base point `◐_id`; the lock MONOID `ContextLock.identity` /
    `ContextLock.compose` carries the LOCK 2-functoriality, and `fxWeakeningLock` is a non-trivial lock).
    This is the MODAL part.
  * **`beckChevalley`** (`context-17` `fxBeckChevalleyCoherence`) — Beck–Chevalley at full strength: the
    display natural transformation, the BC pasting, the iterated display tower, AND the genuine display
    PULLBACK in `𝒞`.  This is the ADJOINT-NATURALITY coherence.
  * **`normalization`** (`context-12` `fxMultimodalNbe`) — the NbE retraction on the substitution calculus
    (eval = `context-8` denote, reify) with σ-rewriting invariance.  This is the NORMALIZATION.
  * **`displayClosedUnderPullback`** — ★ Uemura's AXIOM 1 (representable maps closed under pullback) for the
    DISPLAY maps, witnessed by `context-17`'s `fxComprehensionPullback`: every display map pulled back along
    any substitution is again a display, in `𝒞`.  (Uemura AXIOM 3 — closure under composition — is the
    display TOWER `displayTowerNatural` inside `beckChevalley`; AXIOM 2 — isos representable — is the
    standard inclusion.)

The supporting rungs feed in transitively: `context-7` strictification (the split cleavage laws),
`context-8` explicit substitution (NbE's eval), `context-9` SFMTT (the substitution-free normal form),
`context-11` sconing, `context-13…16` the semantic models, `context-18` global sections, `context-19`
pushout contexts, `context-20` the dim-2 substitution 2-groupoid.

DEFERRED (the honest `= false` markers):
  * the genuine `RepresentableMapCategory` (Uemura Def 2.1) over the substitution base PACKAGED as ONE value
    — the representable-map MorphismCLASS with all three closure axioms — `hasFullUemuraMorphismClass`
    (the AXIOM-1 pullback ships here; the renaming-base RMC `fxBaseRenamingVecRMC` is the shipped Def-2.1
    witness; the substitution-base class-packaging is the completion);
  * the RMC as a genuine MODEL of the full presentation (gluing type/term/mode through the fibration) —
    `hasCrossAxisModelAssembly` (`→ Core/fib`);
  * the modal lock THREADED through normalization (Gratzer mode-relative NbE) — `hasModalLockThreadedNbe`
    (`×mode → fib-3`).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The standalone modal RMC, assembled -/

/-- **The standalone modal Representable Map Category of FX contexts** — the `context-21` capstone, gathering
the comprehension / Uemura representability, the modal lock adjunction, the Beck–Chevalley coherence (incl.
the display pullback), and the NbE normalization of the context axis into one citable value over the standalone
`𝒞`.  `contextCategory` is the carrier (Uemura's `underlying`); the remaining fields are the structure it
carries. -/
structure StandaloneModalRMC where
  /-- The carrier: the standalone category of contexts `𝒞` (= `fxBaseSubstCategory.opposite`). -/
  contextCategory : RawCategory
  /-- The split comprehension category / display fibration + the Uemura representability bijection. -/
  comprehension : FxComprehensionCategory
  /-- The modal lock adjunction `◐_μ ⊣ ⟨μ|−⟩` on the substitution base. -/
  modalLock : ContextLock fxBaseSubstCategory
  /-- Beck–Chevalley at full strength, including the genuine display pullback in `𝒞`. -/
  beckChevalley : FxBeckChevalleyCoherence
  /-- The NbE normalization retraction over the substitution base. -/
  normalization : FxMultimodalNbe
  /-- ★ Uemura AXIOM 1: the display maps are closed under pullback — every display pulled back along any
  substitution is again a display, in `𝒞` (`context-17`'s `fxComprehensionPullback`). -/
  displayClosedUnderPullback : ∀ {contextScope baseScope : Nat} (sigma : SubstVec contextScope baseScope),
      PullbackSquare fxContextCategory (objectA := contextScope) (objectB := baseScope + 1)
        (objectC := baseScope) sigma (SubstVec.weakening baseScope)

/-- ★ **The FX context axis HAS a standalone modal RMC** — the capstone witness wiring `context-10`'s
comprehension, `context-4`'s modal lock, `context-17`'s Beck–Chevalley coherence (with the pullback),
`context-12`'s normalization, and the Uemura AXIOM-1 display-pullback closure, all over the one standalone
`𝒞`. -/
def fxStandaloneModalRMC : StandaloneModalRMC where
  contextCategory := fxContextCategory
  comprehension := fxComprehensionCategory
  modalLock := fxIdentityLock
  beckChevalley := fxBeckChevalleyCoherence
  normalization := fxMultimodalNbe
  displayClosedUnderPullback := fun sigma => fxComprehensionPullback sigma

/-! ## Coherence: the bundled pieces talk about ONE base `𝒞` -/

/-- The capstone's carrier IS the standalone `𝒞 = fxBaseSubstCategory.opposite` (`context-15`). -/
theorem fxStandaloneModalRMC_contextCategory_isOppositeBase :
    fxStandaloneModalRMC.contextCategory = RawCategory.opposite fxBaseSubstCategory :=
  rfl

/-- The bundled modal lock is the TRIVIAL-mode base point: its lock endofunctor is the identity (the FX
context axis sits at the trivial modality; the lock monoid carries the non-trivial modes). -/
theorem fxStandaloneModalRMC_modalLock_isTrivialMode :
    fxStandaloneModalRMC.modalLock.lock = RawEndofunctor.identity fxBaseSubstCategory :=
  rfl

/-- ★ Coherence: the capstone's Uemura AXIOM-1 (display closed under pullback) IS `beckChevalley`'s display
pullback — the representable-map closure and the Beck–Chevalley coherence are the SAME `fxComprehensionPullback`,
not two separate facts. -/
theorem fxStandaloneModalRMC_axiom1_isBeckChevalleyPullback
    {contextScope baseScope : Nat} (sigma : SubstVec contextScope baseScope) :
    fxStandaloneModalRMC.displayClosedUnderPullback sigma
      = fxStandaloneModalRMC.beckChevalley.displayPullback sigma :=
  rfl

/-- ★ Coherence: the capstone's Uemura AXIOM-1 pullback is a GENUINE (strict) pullback — the mediator is
UNIQUE (`fxComprehensionPullback_isStrict`).  So the representable-map closure for the FX DISPLAY maps is
faithful (a real limit), not the weak/existence-only form a bare `PullbackSquare` records.  This is the
sharpest reachable point of faithfulness: AXIOM 1 holds STRICTLY for the genuine (display) representable
maps over the genuine context category `𝒞`. -/
theorem fxStandaloneModalRMC_displayPullback_isStrict {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    (fxStandaloneModalRMC.displayClosedUnderPullback sigma).IsStrict :=
  fxComprehensionPullback_isStrict sigma

/-- ★ Uemura AXIOM 3, strictly: the COMPOSITE of display maps (the 2-fold display tower `p²`) has a genuine
STRICT pullback in `𝒞` (`fxComprehensionTowerPullback_isStrict`, via the generic pasting lemma
`PullbackSquare.paste_isStrict`).  So the FX display maps are closed under composition AND pullback-stable as
real limits: AXIOM 1 (`displayPullback`) and AXIOM 3 both hold STRICTLY for the genuine (display) representable
class — the maximal faithful Uemura content reachable over `𝒞` without the full `MorphismClass` packaging. -/
theorem fxStandaloneModalRMC_displayTowerPullback_isStrict {contextScope baseScope : Nat}
    (sigma : SubstVec contextScope baseScope) :
    (fxComprehensionTowerPullback sigma).IsStrict :=
  fxComprehensionTowerPullback_isStrict sigma

/-! ## Honesty markers (the `→ Core/fib` cross-axis assembly) -/

/-- **Honesty marker.**  The genuine `RepresentableMapCategory` (Uemura Def 2.1) over the substitution base
PACKAGED as ONE value — the representable-map `MorphismClass` with all three closure axioms — is not assembled
here (the AXIOM-1 pullback ships; the renaming-base `fxBaseRenamingVecRMC` is the shipped Def-2.1 witness).
`= false`. -/
def standaloneModalRMC_hasFullUemuraMorphismClass : Bool := false

/-- **Honesty marker.**  The RMC as a genuine MODEL of the full type-theory presentation — gluing the type,
term, and mode axes through the fibration — is the cross-axis assembly, deferred to `Core/fib`
(`fib-3`/`fib-5`/`fib-8`).  `= false`. -/
def standaloneModalRMC_hasCrossAxisModelAssembly : Bool := false

/-- **Honesty marker.**  Threading the modal lock `◐_μ` through normalization (Gratzer's mode-relative NbE)
is `×mode`, deferred to `fib-3`; the bundled `normalization` fixes NbE over the substitution base without
the lock action.  `= false`. -/
def standaloneModalRMC_hasModalLockThreadedNbe : Bool := false

/-- **Honesty marker.**  No shipped `RepresentableMapCategory` takes the DISPLAY maps as its representable
class: both `fxBaseRenamingVecRMC` and `thinScopeRMC` use the ISOMORPHISM class — type-theoretically trivial
as a model (no non-trivial type families) — and Uemura's representability-BY-A-UNIVERSE (the natural-model
classifier `Tm ↠ Ty`) is the type axis.  The FX display maps' genuine, NON-degenerate AXIOM-1 content ships
here as a STRICT pullback (`fxStandaloneModalRMC_displayPullback_isStrict`), but packaging displays-as-
representables into a full RMC (the `MorphismClass` decidability + the data-morphism funext wall) is
`fxBaseRMC` proper, `→ Core/fib`.  `= false`. -/
def standaloneModalRMC_hasDisplayRepresentableClass : Bool := false

/-! ## Smoke -/

/-- Smoke: the capstone's Uemura representability is a genuine bijection — its round-trip recovers any
morphism into a comprehension `Γ.A` (the representable-object universal property). -/
theorem fxStandaloneModalRMC_representability_smoke {target source : Nat}
    (vec : SubstVec target (source + 1)) :
    (fxStandaloneModalRMC.comprehension.representability).backward
        ((fxStandaloneModalRMC.comprehension.representability).forward vec) = vec :=
  (fxStandaloneModalRMC.comprehension.representability).backward_forward vec

end FX1Poly.Tier0
