import FX1Poly.Core.Rewriting.Confluence.Newman
import FX1Poly.Core.Rewriting.Confluence.KnuthBendixCompletion
import FX1Poly.Tier0.Term.Rewrite.ModularSNBoundary

/-! # Tier0/Term — the word problem: decidable Conv as a function of convergence (term-20, CAPSTONE)

The term-axis CAPSTONE.  The word problem for a rewrite system is its convertibility relation
`⟷*` (`EquationalTheory`); deciding it is "given `a`, `b`, is `a ⟷* b`?".  The capstone result —
the punchline of Knuth-Bendix and the term-axis as a whole — is that the word problem is DECIDABLE AS A
FUNCTION OF CONVERGENCE: a CONFLUENT + TERMINATING (convergent) system decides its word problem by
normalizing both sides and comparing.  This file anchors that result at the word-problem level and pins
the EXACT decidability BOUNDARY (each piece zero-axiom):

  * **The positive half** (`decidableWordProblem_of_convergent` ★, `wordProblem_iff_normalFormEq` ★): a
    convergent system (a `ConvergentNormalizer` + `Confluent`) over a decidable-equality carrier decides
    the word problem, because `a ⟷* b ↔ a↓ = b↓` (the word problem IS normal-form equality).  This is the
    word-problem face of the design-lock `fxTerm_hasNormalizerConvDecision` (the kernel's
    `Conv.decidableOfStronglyNormalizing` / `Normalizer.decidableConv`), here stated abstractly over any
    convergent relation via `term-7`'s `ConvergentNormalizer`.
  * **The boundary — convergence is NECESSARY for the normalize-and-compare decision.**
    - CONFLUENCE necessary (uniqueness of normal forms): `forkStep` — `apex` forks to two DISTINCT normal
      forms `leftLeaf`/`rightLeaf` (`forkStep_apex_hasTwoDistinctNormalForms`), so it is NOT confluent
      (`forkStep_notConfluent`) and normal forms are not unique — the decision-by-comparison is ill-defined.
    - TERMINATION (SN) necessary (existence of normal forms): `term-19`'s `unionStep` has NO normal form
      (`unionStep_hasNoNormalForm`) — without termination there is nothing to normalize to.
    Together: the word-problem decision needs BOTH confluence (unique `↓`) and SN (existent `↓`) — i.e.
    convergence — exactly the hypotheses of the positive half.

## Relationship to the other "convergent ⟹ decidable word problem" packagings

The GENUINE contribution of this file is the decidability BOUNDARY (the two necessity witnesses); the
positive half is the term-axis WORD-PROBLEM naming of a pattern that already recurs across the kernel —
it directly wraps `term-7`'s engine and is NOT a re-proof:
  * Path A (primary): the kernel's `Conv.decidableOfStronglyNormalizing` / `Normalizer.decidableConv`
    (typed `Conv` on the SN fragment) — the design-lock `fxTerm_hasNormalizerConvDecision`.
  * `term-7`: `ConvergentNormalizer.decidableEquationalTheory` / `equationalTheory_iff` — the abstract
    Knuth-Bendix decision that `decidableWordProblem_of_convergent` / `wordProblem_iff_normalFormEq` wrap.
  * Path B (crosscheck): `FX1Poly.OmegacE`'s `OmegacEWord.ConvertibleModulo.decidableOfNormalizer` — the
    Makkai ωcE-scaffold-word twin (concrete convergent systems: sorting / transposition / idempotent /
    absorption).
This file does NOT claim the kernel's full `Conv`, nor the full Makkai ωcE word-equality decision,
UNCONDITIONALLY: like every twin, the decision is CONDITIONAL on a convergent presentation (the latter's
unconditional form is `fxOmegacE_hasNoMakkaiWordEquality = false`, the retracted "decidable via ωcE
morphism search" overclaim — Path A primary, Path B crosscheck).

## Honest scope

Shipped: the positive decision as a function of convergence + the decision characterization
(`⟷* ↔ ↓ =`) + the two necessity witnesses pinning the convergence boundary.  DEFERRED — THE UNDECIDABILITY
FRONTIER: genuine UNDECIDABILITY of the general word problem (Markov-Post: a finitely-presented system with
undecidable word problem; equivalently a halting-problem reduction) is a classical computability metatheorem
that requires a model of computation and is OUT OF SCOPE for the zero-axiom, `Init`-only kernel.  What is
shipped here is the sharp boundary of the DECIDABLE side; the undecidable side is named, not mechanized.

## Zero-axiom verification

The positive half wraps `term-7`'s `ConvergentNormalizer.decidableEquationalTheory` /
`equationalTheory_iff`; the fork witnesses are `Bool`-style enum case analysis with `ForkCarrier.noConfusion`
and `normalForm_blocks_reduction`; the SN-necessity is `term-19`'s `unionStep_hasNoNormalForm`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTier0TermWordProblem.lean`.
-/

namespace FX1Poly.Core

/-! ## The word problem + the positive decision (as a function of convergence) -/

/-- The **word problem** of a rewrite relation: its convertibility (`⟷*`, the equational theory).

KINDA-DUPLICATION / DIFFERENT-PATHS NOTE: this is the SAME notion as the Path-B word-equality
`FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo` (over ωcE scaffold words) and the kernel's typed `Conv`
(Path A) — just the term-axis abstract naming.  It is a `def`-alias of `EquationalTheory` purely to give the
capstone a "word problem" surface; nothing here is re-proved (see the per-declaration citations below and the
module-header "Relationship to the other packagings"). -/
def WordProblem {Carrier : Type} (rewrite : Carrier → Carrier → Prop) (leftValue rightValue : Carrier) :
    Prop :=
  EquationalTheory rewrite leftValue rightValue

/-- ★ **The word problem is normal-form equality** for a convergent system: `a ⟷* b ↔ a↓ = b↓`.  The
characterization the decision rests on.

KINDA-DUPLICATION NOTE: this DIRECTLY wraps `term-7`'s `ConvergentNormalizer.equationalTheory_iff` (it is
literally that lemma, re-stated through the `WordProblem` alias — not a re-proof).  The same fact lives on
the other paths under different names: Path B is `FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.iff_normalize_eq`
(ωcE words); Path A's kernel `Conv` decision rests on the analogous normal-form comparison
(`Conv.decidableOfStronglyNormalizing`). -/
theorem wordProblem_iff_normalFormEq {Carrier : Type} {rewrite : Carrier → Carrier → Prop}
    (normalizer : ConvergentNormalizer rewrite) (confluent : Confluent rewrite)
    (leftValue rightValue : Carrier) :
    WordProblem rewrite leftValue rightValue
      ↔ normalizer.normalize leftValue = normalizer.normalize rightValue :=
  normalizer.equationalTheory_iff confluent

/-- ★ **The word problem is DECIDABLE as a function of CONVERGENCE.**  A confluent system equipped with a
normalizer (convergence) over a decidable-equality carrier decides `a ⟷* b` — by comparing `a↓` and `b↓`.
The term-axis capstone, at the word-problem level.

KINDA-DUPLICATION / DIFFERENT-PATHS NOTE: this WRAPS `term-7`'s `ConvergentNormalizer.decidableEquationalTheory`
(no new proof).  It is the term-axis member of a family of TWINS — the same "convergent ⟹ decidable word
problem" decision, packaged once per path:
  * Path A (primary, kernel): `Conv.decidableOfStronglyNormalizing` / `Normalizer.decidableConv` (typed `Conv`
    on the SN fragment) — design-lock `fxTerm_hasNormalizerConvDecision`;
  * `term-7` (abstract Knuth-Bendix): `ConvergentNormalizer.decidableEquationalTheory` — the engine wrapped here;
  * Path B (crosscheck, ωcE / Makkai): `FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.decidableOfNormalizer`.
The duplication is deliberate (one named decision per axis); the genuine NEW content of this file is the
decidability BOUNDARY below (`forkStep_notConfluent` + `term-19`'s `unionStep_hasNoNormalForm`), which the
twins do not carry. -/
def decidableWordProblem_of_convergent {Carrier : Type} [DecidableEq Carrier]
    {rewrite : Carrier → Carrier → Prop} (normalizer : ConvergentNormalizer rewrite)
    (confluent : Confluent rewrite) (leftValue rightValue : Carrier) :
    Decidable (WordProblem rewrite leftValue rightValue) :=
  normalizer.decidableEquationalTheory confluent leftValue rightValue

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
(each is normal and they are distinct). -/
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
