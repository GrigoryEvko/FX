import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstComprehension
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstCategory

/-! # Comprehension + the Frobenius Σ (`context-1`, the LEFT/Σ leg proper)

`context-1`'s two named deliverables are **context extension as comprehension** and
**the Frobenius Σ**.  This file lands them on the FX substitution base.

## Status of the two halves before this file

* *Comprehension* was already shipped as the SUBSTVEC-4 bricks
  (`FxBaseSubstComprehension.lean`): the extension `SubstVec.cons`, the **v-law**
  (`cons_lookup_zero`), the **p-law / β-cancellation** (`weakening_compose_cons`), and the
  **universal property** (`cons_unique`).  Those are the complete CwR comprehension
  structure — but scattered as raw `SubstVec` lemmas, never gathered as a context-axis
  deliverable.
* *The Frobenius Σ* — the substitution-stability of comprehension, the Beck–Chevalley
  square that makes the dependent sum commute with substitution — was **not** shipped
  anywhere.  It is the genuine content gap, and it lands here.

## What lands here (all zero-axiom)

  * **`SubstVec.cons_compose`** — the NEW content: the Beck–Chevalley / Frobenius
    substitution-stability square.  Extending then substituting equals substituting the
    pieces then extending:
    `(cons head tail) ∘ σ = cons (head[σ]) (tail ∘ σ)`.
    This is exactly the law that makes Σ-types stable under substitution — the syntactic
    heart of Frobenius reciprocity at the comprehension level.  It holds pointwise:
    `lookup_compose` turns each side into a `subst`, and the v/p-laws line the two up.
  * `FxContextComprehension` — the four comprehension laws (v-law, p-law, universal
    property, substitution-stability) gathered as ONE citable structure, so `context-1`
    owns a single comprehension object rather than four loose lemmas.
  * `fxContextComprehension` — the witness, wiring the shipped SUBSTVEC-4 lemmas plus the
    new stability square.  Because `fxBaseSubstCategory.compose` is defeq to
    `SubstVec.compose` (the `rfl`-proven `fxBaseSubstCategory_compose_eq`), the square holds
    verbatim for the actual context category `context-0` ships, not just the raw operation.

## Honest scope boundary

This is the comprehension structure + the Beck–Chevalley square that makes Σ
substitution-stable — the LIGHT, syntactic form of "Frobenius Σ".  It is NOT the full
fibred left adjoint `Σ_A ⊣ p_A*` on slice categories with reciprocity
`Σ_A(X ×_{Γ.A} p*Y) ≅ Σ_A(X) ×_Γ Y`: that is the Jacobs fibred-adjoint construction,
which is `context-10`'s deliverable and ships in `Core/`.  The renaming ⊂ substitution
inclusion (`RenamingInclusion.lean`) is the complementary Uemura mode-separation piece,
not part of this LEFT/Σ leg.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-- **Beck–Chevalley / Frobenius substitution-stability of comprehension.**  Composing an
extension `cons head tail` with a substitution `σ` equals extending the substituted pieces:
`(cons head tail) ∘ σ = cons (head[σ]) (tail ∘ σ)`.  This is the law that makes the
dependent sum commute with substitution — the syntactic core of Frobenius reciprocity.

It holds pointwise: at the fresh variable both sides are `head[σ]` (v-law); at every
inherited variable both sides are `(tail.lookup _)[σ]` (`lookup_compose` on the right,
v-law-on-successor then `lookup_compose` on the left). -/
theorem SubstVec.cons_compose {sourceScope midScope targetScope : Nat}
    (headTerm : RawTerm midScope) (tailVec : SubstVec midScope sourceScope)
    (sigma : SubstVec targetScope midScope) :
    (SubstVec.cons headTerm tailVec).compose sigma =
      SubstVec.cons (RawTerm.subst sigma.toRawTermSubst headTerm) (tailVec.compose sigma) :=
  SubstVec.ext _ _ (fun index =>
    match index with
    | ⟨0, _⟩ => by
        rw [SubstVec.lookup_compose, SubstVec.cons_lookup_zero, SubstVec.cons_lookup_zero]
    | ⟨_position + 1, _isLt⟩ => by
        rw [SubstVec.lookup_compose, SubstVec.cons_lookup_succ, SubstVec.cons_lookup_succ,
            SubstVec.lookup_compose])

/-- **The comprehension structure of the FX substitution category**, gathered as one
citable object: the v-law (the fresh variable recovers the head), the p-law (the display
map projects an extension back onto its base), the universal property (the extension is
the UNIQUE such morphism), and the Beck–Chevalley substitution-stability square (the
Frobenius content).  Together these are the CwR comprehension structure of `context-1`. -/
structure FxContextComprehension where
  /-- v-law: the freshly-bound variable recovers the head term. -/
  vLaw : ∀ {target source : Nat} (headTerm : RawTerm target)
           (tailVec : SubstVec target source) (isLt : 0 < source + 1),
         (SubstVec.cons headTerm tailVec).lookup ⟨0, isLt⟩ = headTerm
  /-- p-law: the display map projects an extension back onto its base. -/
  pLaw : ∀ {target source : Nat} (headTerm : RawTerm target)
           (tailVec : SubstVec target source),
         (SubstVec.weakening source).compose (SubstVec.cons headTerm tailVec) = tailVec
  /-- Universal property: the extension is the UNIQUE morphism projecting to the tail with
  the given head. -/
  universalProperty : ∀ {target source : Nat} (headTerm : RawTerm target)
           (tailVec : SubstVec target source) (candidate : SubstVec target (source + 1)),
           (SubstVec.weakening source).compose candidate = tailVec →
           candidate.lookup ⟨0, Nat.succ_pos source⟩ = headTerm →
           candidate = SubstVec.cons headTerm tailVec
  /-- Beck–Chevalley: comprehension is stable under substitution (the Frobenius Σ law). -/
  substStability : ∀ {sourceScope midScope targetScope : Nat} (headTerm : RawTerm midScope)
           (tailVec : SubstVec midScope sourceScope) (sigma : SubstVec targetScope midScope),
           (SubstVec.cons headTerm tailVec).compose sigma =
             SubstVec.cons (RawTerm.subst sigma.toRawTermSubst headTerm) (tailVec.compose sigma)

/-- ★ The FX context axis HAS comprehension with a substitution-stable Σ — the witness
wiring the shipped SUBSTVEC-4 laws (v-law, p-law, universal property) plus the new
Beck–Chevalley square `cons_compose`.  This is `context-1`'s "context extension as
comprehension + the Frobenius Σ" delivered as one object. -/
def fxContextComprehension : FxContextComprehension where
  vLaw := fun headTerm tailVec isLt => SubstVec.cons_lookup_zero headTerm tailVec isLt
  pLaw := fun headTerm tailVec => SubstVec.weakening_compose_cons headTerm tailVec
  universalProperty := fun headTerm tailVec candidate projectsToTail zerothIsHead =>
    SubstVec.cons_unique headTerm tailVec candidate projectsToTail zerothIsHead
  substStability := fun headTerm tailVec sigma => SubstVec.cons_compose headTerm tailVec sigma

end FX1Poly.Tier0
