import FX1Poly.Core.Rewriting.Confluence.Newman
import FX1Poly.Core.Rewriting.Confluence.KnuthBendixCompletion

/-! # Tier0/Term — the word problem: the decidability BOUNDARY (term-20, CAPSTONE)

The term-axis CAPSTONE.  The word problem for a rewrite system is its convertibility `⟷*`
(`EquationalTheory`); the capstone result is that it is DECIDABLE AS A FUNCTION OF CONVERGENCE — a
CONFLUENT + TERMINATING (convergent) system decides `a ⟷* b` by normalizing both sides and comparing.

That POSITIVE decision is NOT re-proved here — it already exists as a SINGLE parametrized engine that this
rung cites, plus its two carrier-specific twins:

  * `term-7`'s `ConvergentNormalizer.equationalTheory_iff` / `decidableEquationalTheory` — THE engine: over
    any abstract `rel` with a normalizer, `a ⟷* b ↔ a↓ = b↓` and hence `Decidable`.  This is what the
    `term-20` marker (`fxTerm_wordProblemBoundary_isBacked`) cites for its positive leg.
  * Path A (primary): the kernel's `Conv.decidableOfStronglyNormalizing` / `Normalizer.decidableConv`
    (typed `Conv` on the SN fragment) — the design-lock `fxTerm_hasNormalizerConvDecision`.  A TWIN over a
    different carrier (`RawTerm`).
  * Path B (crosscheck): `FX1Poly.OmegacE`'s `OmegacEWord.ConvertibleModulo.decidableOfNormalizer` — a TWIN
    over a different carrier (Makkai ωcE scaffold words, concrete convergent systems).

What this file genuinely contributes — found nowhere else — is the DECIDABILITY BOUNDARY: a proof that
convergence is NECESSARY, not merely sufficient, for the normalize-and-compare decision.

  * CONFLUENCE is necessary (uniqueness of normal forms): `forkStep` — `apex` forks to two DISTINCT normal
    forms `leftLeaf`/`rightLeaf` (`forkStep_apex_hasTwoDistinctNormalForms`), so it is NOT confluent
    (`forkStep_notConfluent`) and `↓` is not well-defined.
  * TERMINATION (SN) is necessary (existence of normal forms): `term-19`'s `unionStep_hasNoNormalForm` — a
    system with no normal form at all (cited in the `term-20` marker, not re-stated here).

Together: the word-problem decision needs BOTH confluence (unique `↓`) and SN (existent `↓`) — exactly the
hypotheses of the cited positive engine.

## Honest scope

Shipped here: the two necessity witnesses pinning the convergence boundary.  The positive decision is the
`term-7` engine (cited, not duplicated).  DEFERRED — THE UNDECIDABILITY FRONTIER: genuine UNDECIDABILITY of
the general word problem (Markov-Post; a halting-problem reduction) is a classical computability metatheorem
requiring a model of computation — OUT OF SCOPE for the zero-axiom, `Init`-only kernel.  The undecidable
side is NAMED, not mechanized; and no rung claims the kernel's full `Conv` or the full Makkai ωcE decision
UNCONDITIONALLY (the latter is `fxOmegacE_hasNoMakkaiWordEquality = false`, the retracted "decidable via
ωcE morphism search" overclaim — Path A primary, Path B crosscheck).

## Zero-axiom verification

The fork witnesses are enum case analysis with `ForkCarrier.noConfusion` + `normalForm_blocks_reduction`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditTier0TermWordProblem.lean`.
-/

namespace FX1Poly.Core

/-! ## The boundary — confluence is necessary (uniqueness of normal forms) -/

/-- A **non-confluent** system: `apex` forks to two distinct leaves, each a normal form. -/
inductive ForkCarrier where
  /-- The forking source. -/
  | apex
  /-- The left normal form. -/
  | leftLeaf
  /-- The right normal form. -/
  | rightLeaf

/-- The fork relation: `apex → leftLeaf` and `apex → rightLeaf`; the leaves are normal. -/
def forkStep (current next : ForkCarrier) : Prop :=
  (current = ForkCarrier.apex ∧ next = ForkCarrier.leftLeaf) ∨
    (current = ForkCarrier.apex ∧ next = ForkCarrier.rightLeaf)

/-- `apex` steps to the left leaf. -/
theorem forkStep_apex_leftLeaf : forkStep ForkCarrier.apex ForkCarrier.leftLeaf := Or.inl ⟨rfl, rfl⟩

/-- `apex` steps to the right leaf. -/
theorem forkStep_apex_rightLeaf : forkStep ForkCarrier.apex ForkCarrier.rightLeaf := Or.inr ⟨rfl, rfl⟩

/-- The left leaf is a normal form (no outgoing step). -/
theorem forkStep_leftLeaf_normal : ∀ next, ¬ forkStep ForkCarrier.leftLeaf next := by
  intro next step
  cases step with
  | inl atApex => exact ForkCarrier.noConfusion atApex.1
  | inr atApex => exact ForkCarrier.noConfusion atApex.1

/-- The right leaf is a normal form (no outgoing step). -/
theorem forkStep_rightLeaf_normal : ∀ next, ¬ forkStep ForkCarrier.rightLeaf next := by
  intro next step
  cases step with
  | inl atApex => exact ForkCarrier.noConfusion atApex.1
  | inr atApex => exact ForkCarrier.noConfusion atApex.1

/-- The two leaves are distinct. -/
theorem forkLeaves_distinct : ForkCarrier.leftLeaf ≠ ForkCarrier.rightLeaf := by
  intro leavesEqual
  exact ForkCarrier.noConfusion leavesEqual

/-- ★ `apex` reduces to TWO DISTINCT normal forms — so normal forms are NOT unique without confluence, and
the normalize-and-compare decision is ill-defined.  Confluence is necessary. -/
theorem forkStep_apex_hasTwoDistinctNormalForms :
    (ReflTransClosure forkStep ForkCarrier.apex ForkCarrier.leftLeaf
        ∧ ∀ next, ¬ forkStep ForkCarrier.leftLeaf next)
      ∧ (ReflTransClosure forkStep ForkCarrier.apex ForkCarrier.rightLeaf
        ∧ ∀ next, ¬ forkStep ForkCarrier.rightLeaf next)
      ∧ ForkCarrier.leftLeaf ≠ ForkCarrier.rightLeaf :=
  ⟨⟨ReflTransClosure.single forkStep_apex_leftLeaf, forkStep_leftLeaf_normal⟩,
   ⟨ReflTransClosure.single forkStep_apex_rightLeaf, forkStep_rightLeaf_normal⟩,
   forkLeaves_distinct⟩

/-- ★ The fork system is NOT confluent: its two normal forms are reachable from `apex` but not joinable
(each is normal and they are distinct).  So CONFLUENCE is necessary for the word-problem decision. -/
theorem forkStep_notConfluent : ¬ Confluent forkStep := by
  intro confluent
  obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ :=
    confluent (ReflTransClosure.single forkStep_apex_leftLeaf)
      (ReflTransClosure.single forkStep_apex_rightLeaf)
  have leftEq : ForkCarrier.leftLeaf = commonReduct :=
    normalForm_blocks_reduction forkStep_leftLeaf_normal leftToCommon
  have rightEq : ForkCarrier.rightLeaf = commonReduct :=
    normalForm_blocks_reduction forkStep_rightLeaf_normal rightToCommon
  exact forkLeaves_distinct (leftEq.trans rightEq.symm)

end FX1Poly.Core
