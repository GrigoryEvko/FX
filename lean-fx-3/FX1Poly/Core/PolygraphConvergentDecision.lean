import FX1Poly.Core.ConvNormalForm
import FX1Poly.Core.RawTermDecEq

/-! # Foundation/PolyCell/Core/PolygraphConvergentDecision
    — Path B: Conv = normal-form word equality on the convergent polygraph presentation

The FX kernel IS a polygraph: the `Generator`s are the generating cells and `Step` is the rewrite
system.  polycell.md §2.3 (Path B — Makkai-Mimram word problem) reduces decidable conversion to a
WORD PROBLEM: "FX rewrite as convergent presentation (SN + cd_lemma confluence) → word equality in the
free ω-category decidable via Makkai's algorithm → Conv = word equality", and frames Conv as
membership in the saturated marking (cd_lemma = the marking is closed under composition).

This file ships the DECIDER CORE of that chain, INDEPENDENTLY of Path A's reducibility logical
relation: once the presentation is CONVERGENT — a normalizer sends each cell to a unique normal form
(the strongly-normalizing leg, shared with Path A reducibility and Path C sconing) and the rewrite is
confluent (`StepStar.HasConfluence`) — conversion of two cells is EXACTLY equality of their normal
forms (the "word equality"), which the propext-free `DecidableEq (RawTerm)` decides.  Built on the
shipped `Conv.eq_of_noStep` (on no-step normal forms, Conv collapses to Eq) and
`Conv.trans_of_confluence`.

The `Normalizer` and `HasConfluence` are explicit hypotheses: they are precisely WHAT THE FULL DECIDER
NEEDS.  Makkai's / Forest's algorithm is the explicit construction of the normalizer (the word normal
form); `cd_lemma` (shipped) feeds confluence.  This is the Path-B cross-check that converges on the
SAME `Decidable (Conv a b)` as Path A's NbE-readback decider — agreement across two methods sharing no
proof machinery beyond the rewrite substrate.

## Zero-axiom verification

The biconditional destructures the `Join` existential and applies `Conv.eq_of_noStep` / transitivity;
the decision instance is `decidable_of_iff` over `instDecidableEqRawTerm`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- A normalizer for the raw rewrite system: a total normal-form function, each cell reducing to its
normal form, the normal form having no outgoing `Step`.  Its EXISTENCE is the strong-normalization
leg of a convergent presentation — shared across all three metatheory paths; Makkai's word algorithm
is one explicit construction of it. -/
structure Normalizer (scope : Nat) where
  normalForm : RawTerm scope → RawTerm scope
  reducesToNormalForm : ∀ term : RawTerm scope, StepStar term (normalForm term)
  normalFormHasNoStep : ∀ term reduct : RawTerm scope, Step (normalForm term) reduct → False

/-- **Conv = normal-form word equality** (Path B decider core): under a convergent presentation
(a `Normalizer` plus confluence), conversion of two cells is exactly equality of their normal forms.
Forward — both cells convert to their normal forms, so by `trans_of_confluence` the normal forms
convert, and on no-step normal forms conversion is equality (`Conv.eq_of_noStep`).  Backward — equal
normal forms expose a common reduct, hence a conversion. -/
theorem Conv.iff_normalForm_eq {scope : Nat} (normalizer : Normalizer scope)
    (hasConfluence : StepStar.HasConfluence) (leftTerm rightTerm : RawTerm scope) :
    Conv leftTerm rightTerm ↔ normalizer.normalForm leftTerm = normalizer.normalForm rightTerm := by
  constructor
  · intro convertibility
    have leftToNormal : Conv leftTerm (normalizer.normalForm leftTerm) :=
      Conv.fromStepStar (normalizer.reducesToNormalForm leftTerm)
    have rightToNormal : Conv rightTerm (normalizer.normalForm rightTerm) :=
      Conv.fromStepStar (normalizer.reducesToNormalForm rightTerm)
    have normalFormsConvert :
        Conv (normalizer.normalForm leftTerm) (normalizer.normalForm rightTerm) :=
      Conv.trans_of_confluence hasConfluence
        (Conv.trans_of_confluence hasConfluence (Conv.sym leftToNormal) convertibility) rightToNormal
    exact Conv.eq_of_noStep (normalizer.normalFormHasNoStep leftTerm)
      (normalizer.normalFormHasNoStep rightTerm) normalFormsConvert
  · intro normalFormsEqual
    exact ⟨normalizer.normalForm rightTerm,
      normalFormsEqual ▸ normalizer.reducesToNormalForm leftTerm,
      normalizer.reducesToNormalForm rightTerm⟩

/-- **Decidable Conv from a convergent presentation** (the Path B decider): given a `Normalizer` and
confluence, conversion is decidable — it is normal-form word equality, decided by the propext-free
`DecidableEq (RawTerm)`.  The full decider awaits the (Makkai/Forest) normalizer construction; this is
the reduction of that construction to a decision. -/
def Conv.decidableOfNormalizer {scope : Nat} (normalizer : Normalizer scope)
    (hasConfluence : StepStar.HasConfluence) (leftTerm rightTerm : RawTerm scope) :
    Decidable (Conv leftTerm rightTerm) :=
  decidable_of_iff _ (Conv.iff_normalForm_eq normalizer hasConfluence leftTerm rightTerm).symm

end FX1Poly.Core
