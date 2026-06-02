import FX1Poly.OmegacE.Confluence

/-! # FX1Poly/OmegacE/WordProblem
    — the Makkai word problem DECIDED by a convergent presentation (Path B)

`Confluence.lean` reduced convertibility to joinability under Church-Rosser.  This file closes the decision:
given confluence AND a terminating normalizer (a function to a reachable normal form), convertibility modulo
the system is DECIDABLE — normalize both words and compare.  This is the ωcE/Path-B twin of the term-layer
`Conv.decidableOfStronglyNormalizing` (`FX1Poly/Core/Normalize.lean`): a CONVERGENT (confluent + terminating)
presentation makes the Makkai word problem decidable.

* `WordNormalizer system` — the convergence interface: `normalize` to a reachable (`reaches`) normal form
  (`blocksStep`: the output takes no one-step rewrite).  The Path-B twin of the term layer's `Normalizer`.
* `rewritesMany_eq_of_blocksStep` — rigidity: a step-blocked word reduces only to itself.
* `Joinable.iff_normalize_eq` — under confluence + a normalizer, joinability IS normal-form equality (the
  forward direction merges the two reductions against the normal forms via the diamond + rigidity).
* `ConvertibleModulo.iff_normalize_eq` — convertibility IS normal-form equality (chaining Church-Rosser:
  convertible ↔ joinable ↔ same NF).
* `ConvertibleModulo.decidableOfNormalizer` — therefore `Decidable (ConvertibleModulo …)`, by
  `decidable_of_iff` over the derived word `DecidableEq` (which is propext-free).

## Honest scope

The decision is CONDITIONAL on `HasConfluence` + a `WordNormalizer` — both discharged per concrete system
later (a concrete confluence proof via Newman/critical-pairs, and a terminating normalizer from a well-founded
measure, e.g. length under a length-reducing system).  This is the standard "convergent ⟹ decidable word
problem" packaged abstractly, exactly as the term layer packages `decidableOfStronglyNormalizing` against an
SN hypothesis.  The FX-Step↔ωcE-rewrite bridge (kernel ↔ Path B) remains the separate connecting atom.

## Zero-axiom verification

Structural; the convertibility characterization composes the two `Iff`s by `Iff.trans` (NOT `rw [← iff]`,
which would pull `propext`); the decision is `decidable_of_iff` over the propext-free word `DecidableEq`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- A **normalizer** for a rule system: a function to a reachable normal form — the convergence interface that
makes the word problem decidable.  `reaches`: every word rewrites to its normal form; `blocksStep`: the normal
form takes no further one-step rewrite. -/
structure WordNormalizer {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) where
  /-- The normal form of a word. -/
  normalize : OmegacEWord dimension → OmegacEWord dimension
  /-- Every word rewrites (many-step) to its normal form. -/
  reaches : ∀ word : OmegacEWord dimension,
    OmegacEWord.RewritesMany system word (normalize word)
  /-- The normal form admits no one-step rewrite. -/
  blocksStep : ∀ (word reduct : OmegacEWord dimension),
    ¬ OmegacEWord.RewritesOneStep system (normalize word) reduct

/-- **Rigidity**: a word that admits no one-step rewrite reduces only to itself.  `cases` on the reduction —
`refl` gives equality, `step` exposes a first step contradicting the no-step hypothesis. -/
theorem OmegacEWord.rewritesMany_eq_of_blocksStep {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {word target : OmegacEWord dimension}
    (blocked : ∀ reduct : OmegacEWord dimension,
      ¬ OmegacEWord.RewritesOneStep system word reduct)
    (many : OmegacEWord.RewritesMany system word target) :
    word = target := by
  cases many with
  | refl _word => rfl
  | step head _tail => exact absurd head (blocked _)

/-- **Joinability is normal-form equality** (confluence + a normalizer): two words are joinable iff they
normalize to the same word.  Forward: each word and the common reduct meet (confluence) at the word's normal
form (rigidity collapses the meet onto the NF), so the common reduct reaches both NFs, which then meet and
coincide (both rigid).  Backward: both reach the shared normal form. -/
theorem OmegacEWord.Joinable.iff_normalize_eq {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (confluence : HasConfluence system) (normalizer : WordNormalizer system)
    {firstWord secondWord : OmegacEWord dimension} :
    OmegacEWord.Joinable system firstWord secondWord ↔
      normalizer.normalize firstWord = normalizer.normalize secondWord := by
  constructor
  · intro joinable
    obtain ⟨commonWord, firstToCommon, secondToCommon⟩ := joinable
    obtain ⟨firstMerge, firstNfToMerge, commonToFirstMerge⟩ :=
      confluence (normalizer.reaches firstWord) firstToCommon
    have firstNfEqMerge : normalizer.normalize firstWord = firstMerge :=
      OmegacEWord.rewritesMany_eq_of_blocksStep (normalizer.blocksStep firstWord) firstNfToMerge
    have commonToFirstNf :
        OmegacEWord.RewritesMany system commonWord (normalizer.normalize firstWord) := by
      rw [firstNfEqMerge]; exact commonToFirstMerge
    obtain ⟨secondMerge, secondNfToMerge, commonToSecondMerge⟩ :=
      confluence (normalizer.reaches secondWord) secondToCommon
    have secondNfEqMerge : normalizer.normalize secondWord = secondMerge :=
      OmegacEWord.rewritesMany_eq_of_blocksStep (normalizer.blocksStep secondWord) secondNfToMerge
    have commonToSecondNf :
        OmegacEWord.RewritesMany system commonWord (normalizer.normalize secondWord) := by
      rw [secondNfEqMerge]; exact commonToSecondMerge
    obtain ⟨finalMerge, firstNfToFinal, secondNfToFinal⟩ :=
      confluence commonToFirstNf commonToSecondNf
    have firstNfEqFinal : normalizer.normalize firstWord = finalMerge :=
      OmegacEWord.rewritesMany_eq_of_blocksStep (normalizer.blocksStep firstWord) firstNfToFinal
    have secondNfEqFinal : normalizer.normalize secondWord = finalMerge :=
      OmegacEWord.rewritesMany_eq_of_blocksStep (normalizer.blocksStep secondWord) secondNfToFinal
    exact firstNfEqFinal.trans secondNfEqFinal.symm
  · intro normalizeEq
    refine ⟨normalizer.normalize firstWord, normalizer.reaches firstWord, ?_⟩
    rw [normalizeEq]; exact normalizer.reaches secondWord

/-- **Convertibility is normal-form equality** (confluence + a normalizer): the headline word-problem
characterization, chaining Church-Rosser — `ConvertibleModulo ↔ Joinable ↔ same NF` — by `Iff.trans` (no
`rw [← iff]`, which would pull `propext`). -/
theorem OmegacEWord.ConvertibleModulo.iff_normalize_eq {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (confluence : HasConfluence system) (normalizer : WordNormalizer system)
    {firstWord secondWord : OmegacEWord dimension} :
    OmegacEWord.ConvertibleModulo system firstWord secondWord ↔
      normalizer.normalize firstWord = normalizer.normalize secondWord :=
  (convertibleModulo_iff_joinable_of_churchRosser
      (churchRosser_of_confluence confluence)).trans
    (OmegacEWord.Joinable.iff_normalize_eq confluence normalizer)

/-- **The Makkai word problem is DECIDED by a convergent presentation.**  Given confluence and a terminating
normalizer, convertibility modulo the system is decidable: normalize both words and compare (`decidable_of_iff`
over the propext-free word `DecidableEq`).  The Path-B twin of `Conv.decidableOfStronglyNormalizing`. -/
def OmegacEWord.ConvertibleModulo.decidableOfNormalizer {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (confluence : HasConfluence system) (normalizer : WordNormalizer system)
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo system firstWord secondWord) :=
  decidable_of_iff (normalizer.normalize firstWord = normalizer.normalize secondWord)
    (OmegacEWord.ConvertibleModulo.iff_normalize_eq confluence normalizer).symm

end FX1Poly.OmegacE
