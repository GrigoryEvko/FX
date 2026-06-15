import FX1Poly.Tier0.Context.Strictification

/-! # context-10 — the comprehension category / display fibration (Jacobs fibred Σ + Beck–Chevalley)

`context-10` views the FX context base — the substitution category `fxBaseSubstCategory` with its
context-extension / comprehension structure — as a COMPREHENSION CATEGORY in the sense of Jacobs: the
display maps (context projections `p : Γ.A → Γ`) form a fibration over the base, reindexing is the de
Bruijn lift `(−)⁺`, and the dependent sum Σ is the comprehension extension, stable under substitution
(Beck–Chevalley).

Everything assembled here is CONTEXT-SIDE — it is about morphisms of the substitution / extension category
and needs no separate type axis.  The pieces are all shipped: `context-1` (comprehension + the Frobenius Σ
square `cons_compose`), `context-2` (the slice / generic display), and `context-7` (the STRICT
context-extension endofunctor `fxContextExtensionFunctor` + `lift_identity` / `lift_compose`).  `context-10`
ASSEMBLES them into the comprehension-category / split-fibration object and proves the fibred-Σ
Beck–Chevalley naturality of the comprehension representability.

## What lands here (all zero-axiom)

  * **`IsSplitDisplayFibration` / `fxDisplaySplitFibration`** — the display maps form a SPLIT (Grothendieck)
    fibration over the base.  The cleavage is the de Bruijn lift `(−)⁺` (= `fxContextExtensionFunctor`'s
    morphism action, `context-7`), STRICT (split) because lifting preserves identities (`lift_identity`) and
    composition ON THE NOSE (`lift_compose`, the strictification crux), and the display projection is
    CARTESIAN — the Beck–Chevalley square `p ∘ σ⁺ = σ ∘ p` (`weakening_compose_lift`).  The cartesian lift's
    universal property is exactly the comprehension universal property (`cons_unique`, carried in the
    `comprehension` field), so the cartesian lifts are genuine, not merely commuting.
  * **`SubstVec.comprehensionBackward_natural`** — ★ the fibred Σ Beck–Chevalley (the dependent SUM commutes
    with reindexing): the comprehension extension / Σ-introduction is NATURAL in the context,
    `⟨head, tail⟩ ∘ σ = ⟨head[σ], tail ∘ σ⟩`.  This is `cons_compose` read as naturality of the
    representability's backward map.
  * **`SubstVec.comprehensionForward_natural`** — the dual projection law: reindexing a morphism and then
    projecting equals projecting then reindexing, `χ(vec ∘ σ) = (χ(vec).fst[σ], χ(vec).snd ∘ σ)`.  Together
    with the backward law the representability bijection `comprehensionIso` is NATURAL — the Σ fibred-adjoint
    coherence in the natural-model presentation.
  * **`FxComprehensionCategory` / `fxComprehensionCategory`** — the assembled object: the split display
    fibration, the comprehension structure (`fxContextComprehension`: v/p-laws, the cartesian-lift universal
    property, Σ substitution-stability), the representability bijection, and the Σ Beck–Chevalley squares,
    gathered as "the FX context base IS a split comprehension category".

The Jacobs fibred Σ is delivered in its NATURAL-MODEL form: the comprehension representability
`comprehensionIso` (`Sub(Δ, Γ.A) ≅ Sub(Δ, Γ) × Tm(Δ, A)`) being natural in `Δ`.  Naturality + the
cartesian-lift universal property together ARE the fibred dependent-sum adjoint over this base.

DEFERRED (honestly NOT shipped here — see `fxComprehensionCategory_hasFibredPiRightAdjoint = false`):
  * The fibred Π RIGHT adjoint to reindexing requires LOCAL CARTESIAN CLOSURE of the base — that is
    `context-16` (democracy + LCC, `⟦⊟SPLIT · core=democracy×type→fib-1⟧`), cross-axis `×type`.  Only the Σ
    LEFT-adjoint / comprehension half is unconditional and context-side.
  * The Σ here is the COMPREHENSION / context-extension Σ (a context-category universal property), DISTINCT
    from the Σ-TYPE former `gen_sigmaTyCode` / `gen_pair` (`×type` / `×term`), which lives on the type / term
    axes.
  * The unit/counit slice-fibred packaging of `Σ ⊣ p*` over varying fibres is the heavier equivalent of the
    natural-model representability shipped here.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The display maps form a split (Grothendieck) fibration -/

/-- **The display-map split fibration of the FX context base.**  The three facts that make the de Bruijn
context extension a SPLIT (Grothendieck) fibration over `fxBaseSubstCategory`: the cleavage (reindexing =
the lift `(−)⁺`) is strictly functorial (preserves identities and composition on the nose — what SPLIT
means), and the display projection `p = weakening` is CARTESIAN (the Beck–Chevalley square `p ∘ σ⁺ = σ ∘ p`).
The cleavage is `fxContextExtensionFunctor`'s morphism action; its universal property is the comprehension
universal property `cons_unique`. -/
structure IsSplitDisplayFibration where
  /-- The cleavage (reindexing = the lift `(−)⁺`) preserves identities: `id⁺ = id`. -/
  reindexPreservesIdentity : ∀ (scope : Nat),
      SubstVec.lift (SubstVec.identity scope) = SubstVec.identity (scope + 1)
  /-- The cleavage preserves composition ON THE NOSE — what makes the fibration SPLIT: `(σ ∘ τ)⁺ = σ⁺ ∘ τ⁺`. -/
  reindexPreservesComposition : ∀ {sourceScope midScope targetScope : Nat}
      (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope),
      SubstVec.lift (firstVec.compose secondVec)
        = (SubstVec.lift firstVec).compose (SubstVec.lift secondVec)
  /-- The display projection is CARTESIAN — the Beck–Chevalley square of the display map `p ∘ σ⁺ = σ ∘ p`. -/
  displayCartesian : ∀ {sourceScope targetScope : Nat} (sigma : SubstVec targetScope sourceScope),
      (SubstVec.weakening sourceScope).compose sigma.lift
        = sigma.compose (SubstVec.weakening targetScope)

/-- ★ The FX context base's display maps form a SPLIT fibration — the witness wiring the shipped
`context-7` strictification laws (`lift_identity`, `lift_compose`) and the `context-1` display
Beck–Chevalley square (`weakening_compose_lift`).  The cleavage IS `fxContextExtensionFunctor`. -/
def fxDisplaySplitFibration : IsSplitDisplayFibration where
  reindexPreservesIdentity := SubstVec.lift_identity
  reindexPreservesComposition := fun firstVec secondVec => SubstVec.lift_compose firstVec secondVec
  displayCartesian := fun sigma => SubstVec.weakening_compose_lift sigma

/-! ## The fibred Σ Beck–Chevalley: the comprehension representability is natural -/

/-- ★ **Fibred Σ Beck–Chevalley (extension / backward).**  The comprehension extension — the Σ-introduction
`⟨head, tail⟩` — is NATURAL in the context: reindexing the extension along `σ` equals extending the reindexed
pieces, `⟨head, tail⟩ ∘ σ = ⟨head[σ], tail ∘ σ⟩`.  This is exactly the dependent sum commuting with
substitution (the Frobenius / Beck–Chevalley square `cons_compose`), read as naturality of the
representability's backward map `comprehensionBackward`. -/
theorem SubstVec.comprehensionBackward_natural {sourceScope midScope targetScope : Nat}
    (pair : RawTerm midScope × SubstVec midScope sourceScope)
    (sigma : SubstVec targetScope midScope) :
    (SubstVec.comprehensionBackward pair).compose sigma
      = SubstVec.comprehensionBackward
          (RawTerm.subst sigma.toRawTermSubst pair.1, pair.2.compose sigma) :=
  SubstVec.cons_compose pair.1 pair.2 sigma

/-- **Fibred Σ Beck–Chevalley (projection / forward).**  Reindexing a morphism `vec : Δ ⟶ Γ.A` along `σ`
and then projecting (zeroth lookup = the `q`-projection, display composite = the `p`-projection) equals
projecting then reindexing: `χ(vec ∘ σ) = (χ(vec).fst[σ], χ(vec).snd ∘ σ)`.  Proof: the zeroth lookup of a
composite substitutes (`lookup_compose`); the display composite reassociates (`compose_assoc`). -/
theorem SubstVec.comprehensionForward_natural {sourceScope midScope targetScope : Nat}
    (vec : SubstVec midScope (sourceScope + 1)) (sigma : SubstVec targetScope midScope) :
    SubstVec.comprehensionForward (vec.compose sigma)
      = (RawTerm.subst sigma.toRawTermSubst (SubstVec.comprehensionForward vec).1,
         (SubstVec.comprehensionForward vec).2.compose sigma) := by
  show ((vec.compose sigma).lookup ⟨0, Nat.succ_pos sourceScope⟩,
        (SubstVec.weakening sourceScope).compose (vec.compose sigma))
      = (RawTerm.subst sigma.toRawTermSubst (vec.lookup ⟨0, Nat.succ_pos sourceScope⟩),
         ((SubstVec.weakening sourceScope).compose vec).compose sigma)
  rw [SubstVec.lookup_compose, SubstVec.compose_assoc]

/-! ## The comprehension category, assembled -/

/-- **The FX context base as a split comprehension category**, gathered as one citable object: the display
maps form a split fibration; the comprehension structure provides the v/p-laws, the cartesian-lift universal
property, and Σ substitution-stability; the representability bijection presents the dependent sum; and the Σ
Beck–Chevalley squares make it stable under reindexing.  This is `context-10`'s "comprehension category /
fibration: the Jacobs fibred Σ + Beck–Chevalley" delivered as one value.  The fibred Π right adjoint
(`×type` / LCC) and the Σ-as-type-former (`×type` / `×term`) are honest deferrals (see the module docstring). -/
structure FxComprehensionCategory where
  /-- The display maps form a split (Grothendieck) fibration. -/
  splitFibration : IsSplitDisplayFibration
  /-- The comprehension structure: v/p-laws, the cartesian-lift universal property, Σ substitution-stability. -/
  comprehension : FxContextComprehension
  /-- The Σ representability bijection `Sub(Δ, Γ.A) ≅ Sub(Δ, Γ) × Tm(Δ, A)`. -/
  representability : ∀ {target source : Nat},
      Bijection (SubstVec target (source + 1)) (RawTerm target × SubstVec target source)
  /-- ★ Fibred Σ Beck–Chevalley: the comprehension extension (Σ-introduction) is natural in the context. -/
  sigmaBeckChevalleyExtension : ∀ {sourceScope midScope targetScope : Nat}
      (pair : RawTerm midScope × SubstVec midScope sourceScope) (sigma : SubstVec targetScope midScope),
      (SubstVec.comprehensionBackward pair).compose sigma
        = SubstVec.comprehensionBackward
            (RawTerm.subst sigma.toRawTermSubst pair.1, pair.2.compose sigma)
  /-- Fibred Σ Beck–Chevalley: the comprehension projection is natural in the context. -/
  sigmaBeckChevalleyProjection : ∀ {sourceScope midScope targetScope : Nat}
      (vec : SubstVec midScope (sourceScope + 1)) (sigma : SubstVec targetScope midScope),
      SubstVec.comprehensionForward (vec.compose sigma)
        = (RawTerm.subst sigma.toRawTermSubst (SubstVec.comprehensionForward vec).1,
           (SubstVec.comprehensionForward vec).2.compose sigma)

/-- ★ The FX context axis HAS a split comprehension category — the witness wiring the split display
fibration, the shipped comprehension structure, the representability iso, and the Σ Beck–Chevalley squares. -/
def fxComprehensionCategory : FxComprehensionCategory where
  splitFibration := fxDisplaySplitFibration
  comprehension := fxContextComprehension
  representability := SubstVec.comprehensionIso
  sigmaBeckChevalleyExtension := fun pair sigma => SubstVec.comprehensionBackward_natural pair sigma
  sigmaBeckChevalleyProjection := fun vec sigma => SubstVec.comprehensionForward_natural vec sigma

/-- **Honesty marker.**  The fibred Π RIGHT adjoint to reindexing is NOT shipped at `context-10`: it requires
LOCAL CARTESIAN CLOSURE of the context base, which is `context-16` (democracy + LCC, `×type → fib-1`).
`context-10` ships only the unconditional, context-side Σ LEFT-adjoint / comprehension half. -/
def fxComprehensionCategory_hasFibredPiRightAdjoint : Bool := false

/-! ## Smoke: the assembled representability backward map IS the comprehension extension -/

/-- Smoke: the bundle's representability is wired to the comprehension iso — its backward map is the
extension `cons head tail`, the Σ-introduction. -/
theorem fxComprehensionCategory_representability_backward_smoke {target source : Nat}
    (pair : RawTerm target × SubstVec target source) :
    (fxComprehensionCategory.representability (target := target) (source := source)).backward pair
      = SubstVec.cons pair.1 pair.2 :=
  rfl

end FX1Poly.Tier0
