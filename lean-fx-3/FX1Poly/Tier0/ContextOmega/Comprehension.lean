import FX1Poly.Tier0.ContextOmega.Interface
import FX1Poly.Tier0.FxBaseSubstComprehension

/-! # Tier0/ContextOmega/Comprehension — the LEFT adjoint (context-1)

The LEFT side of the context ω-category: context extension `Γ.A` as
comprehension.  Over the FX term-carrying context base (`fxBaseSubstCategory`,
objects = scopes, morphisms = `SubstVec`), the comprehension universal property
is realised as an EXPLICIT bijection

    Hom(Δ, Γ.A)  ≅  Hom(Δ, Γ) × Tm(Δ)

i.e. a substitution into the extended context `Γ.A = scope + 1` is exactly a
substitution into the base `Γ` (its display-projection) together with a term
`Δ ⊢ head` (its zeroth lookup).  At the well-scoped base `Tm(Δ) = RawTerm Δ`
and `SubstVec target (source + 1) = RawTerm target × SubstVec target source`
DEFINITIONALLY, so the bijection's two legs (`comprehensionSplit` /
`comprehensionPair`) are total functions and the round-trips are the shipped
comprehension laws:

  * `comprehensionPair_comprehensionSplit` (pair ∘ split = id) — the
    comprehension UNIVERSAL PROPERTY (`SubstVec.cons_unique`).
  * `comprehensionSplit_comprehensionPair` (split ∘ pair = id) — the p-law
    (`SubstVec.weakening_compose_cons`) on the tail + the v-law
    (`SubstVec.cons_lookup_zero`) on the head.

This is the genuine context-extension content (the right adjoint to the
display-projection forgetful — the democratic structure of contexts).

## Honest boundaries (recorded, not faked)

  * The bijection lives over the term-carrying base `fxBaseSubstCategory`, which
    is a `RawCategory` but NOT yet a full `RepresentableMapCategory` (it lacks
    the representable display-map class + the three CwR axioms — that is
    `fxBaseSubstRMC`, the context-2 / SN-088 work).  So this does NOT yet flip
    `fxContextOmega`'s ledger (its base is the renaming RMC with isos as
    representable), and `ContextOmega.ComprehensionStructure fxContextOmega`
    stays a skeleton until context-2 promotes the representable class to the
    genuine display maps.  The bijection here is the CONTENT that promotion
    wires in.
  * The dependent-sum `Σ_A` as the Frobenius LEFT adjoint to reindexing
    (`Σ_A ⊣ A*`) + Beck-Chevalley is the FIBRATIONAL left adjoint; it is
    deferred to the display fibration (context-10 #1544 / fib-1 #1579), since it
    needs the Tm-↠-Ty display structure, not just the scope-extension base.

Zero-axiom: two total projection/pairing functions + two round-trip theorems,
each discharged by the shipped zero-axiom comprehension laws (`ext` pointwise,
no `funext`).  No `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- **The forward leg of the comprehension bijection.**  A substitution into the
extended context `Γ.A` splits into its display-projection (the substitution into
the base `Γ`, recovered by composing the `weakening` display map after it) and
its head term (the zeroth lookup). -/
def comprehensionSplit {targetScope sourceScope : Nat}
    (extended : SubstVec targetScope (sourceScope + 1)) :
    SubstVec targetScope sourceScope × RawTerm targetScope :=
  ((SubstVec.weakening sourceScope).compose extended,
   extended.lookup ⟨0, Nat.succ_pos sourceScope⟩)

/-- **The backward leg of the comprehension bijection.**  A base substitution
together with a head term pair into the extension `cons head tail`. -/
def comprehensionPair {targetScope sourceScope : Nat}
    (baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope) :
    SubstVec targetScope (sourceScope + 1) :=
  SubstVec.cons baseAndHead.2 baseAndHead.1

/-- **Round-trip (split ∘ pair = id).**  Splitting a freshly paired extension
recovers the base substitution (the p-law, `weakening_compose_cons`) and the
head term (the v-law, `cons_lookup_zero`). -/
theorem comprehensionSplit_comprehensionPair {targetScope sourceScope : Nat}
    (baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope) :
    comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead := by
  obtain ⟨baseSubst, headTerm⟩ := baseAndHead
  have projectsToBase :
      (SubstVec.weakening sourceScope).compose (SubstVec.cons headTerm baseSubst) = baseSubst :=
    SubstVec.weakening_compose_cons headTerm baseSubst
  have zerothIsHead :
      (SubstVec.cons headTerm baseSubst).lookup ⟨0, Nat.succ_pos sourceScope⟩ = headTerm :=
    SubstVec.cons_lookup_zero headTerm baseSubst (Nat.succ_pos sourceScope)
  show ((SubstVec.weakening sourceScope).compose (SubstVec.cons headTerm baseSubst),
        (SubstVec.cons headTerm baseSubst).lookup ⟨0, Nat.succ_pos sourceScope⟩) =
       (baseSubst, headTerm)
  rw [projectsToBase, zerothIsHead]

/-- **Round-trip (pair ∘ split = id) — the comprehension UNIVERSAL PROPERTY.**
Pairing an extension's display-projection with its head term recovers the
extension itself: the extension is the UNIQUE morphism with that projection and
that head (`SubstVec.cons_unique`). -/
theorem comprehensionPair_comprehensionSplit {targetScope sourceScope : Nat}
    (extended : SubstVec targetScope (sourceScope + 1)) :
    comprehensionPair (comprehensionSplit extended) = extended := by
  show SubstVec.cons (extended.lookup ⟨0, Nat.succ_pos sourceScope⟩)
        ((SubstVec.weakening sourceScope).compose extended) = extended
  exact (SubstVec.cons_unique
    (extended.lookup ⟨0, Nat.succ_pos sourceScope⟩)
    ((SubstVec.weakening sourceScope).compose extended)
    extended rfl rfl).symm

/-- **The comprehension bijection, bundled.**  Both round-trips hold, so the two
legs are mutually inverse — the comprehension universal property
`Hom(Δ, Γ.A) ≅ Hom(Δ, Γ) × Tm(Δ)` over the FX term base. -/
theorem comprehensionBijection {targetScope sourceScope : Nat} :
    (∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
    (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended) :=
  ⟨comprehensionSplit_comprehensionPair, comprehensionPair_comprehensionSplit⟩

end FX1Poly.Tier0.ContextOmega
