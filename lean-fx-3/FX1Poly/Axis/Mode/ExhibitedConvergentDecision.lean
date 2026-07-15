import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionDecision
import FX1Poly.Polygraph.Rewriting.Confluence.KnuthBendixCompletion
import FX1Poly.Polygraph.Rewriting.Standardization

/-! # Axis/Mode/ExhibitedConvergentDecision — the Tier-C (exhibited-convergent) 2-cell decision (Squier / KB)

Between Gratzer's thin band (Tier B, `TierBThinDecision`) and the rung-3 undecidability wall (FLAG A) sits
the SQUIER / KNUTH-BENDIX band: a finitely presented mode theory whose relations you can EXHIBIT as a
CONVERGENT (terminating + confluent) rewrite system decides its word problem — reduce both sides to normal
form and compare (Knuth-Bendix 1970; the shipped abstract engine
`FX1Poly.Core.ConvergentNormalizer.decidableEquationalTheory`).

This file exhibits the walking involution `<s | s.s = id>` as ITS OWN convergent presentation, wiring the
shipped KB engine onto it, and proves the resulting `EquationalTheory` coincides with the Tier-B relation
`InvolutionOneCellConv` — so Tiers B and C decide the SAME object from two directions (thin classifier vs.
convergent rewriting).

## The convergent presentation (one rule, no critical pairs)

The oriented rule is `s.s -> id`, whiskered under a leading `s` (`InvolutionRewrite`).  It is:

  * **TERMINATING** — every step drops the word length by 2 (`involutionRewrite_lengthDecreases`), so the
    reduction is strongly normalizing (`involutionRewriteWellFounded`, via the shipped measure helper
    `developmentsAreFinite` — no `WellFounded.fix`).
  * **CONFLUENT** — over the one-letter alphabet there are NO critical pairs; confluence is proven by the
    parity-normal-form FUNNEL (every reduct reaches `parityNF` of its Z/2 parity,
    `reducesToParityNF`; parity is a reduction invariant, `involutionRewriteStar_preservesParity`), so two
    reducts of a common source share a parity and join at the common `parityNF`
    (`involutionRewriteConfluent`) — no critical-pair analysis.

The normalizer is `parityNF . involutionParityOf` supplied as DATA (the KB engine leaves `normalize` as
data because `WellFounded.fix` is unavailable zero-axiom), bundled into a `ConvergentNormalizer`
(`involutionConvergentNormalizer`); with confluence it DECIDES the theory
(`decideInvolutionEquationalTheory`).

## Tier B <-> Tier C tie

`equationalTheory_iff_involutionOneCellConv` : `EquationalTheory InvolutionRewrite w1 w2` iff
`InvolutionOneCellConv w1 w2`.  So the KB decision route decides exactly the Tier-B thin relation on the
same walking-involution object — the two bands meet.

## Honest caveats (do not overclaim)

  * **EXHIBITED, not completed.**  Convergence is exhibited by hand; the completion ALGORITHM (orient /
    deduce critical pairs / fairness, Bachmair-Dershowitz) is NOT mechanized — the engine consumes an
    already-convergent presentation plus a normalizer as data.  Mirrors the term axis's
    `fxTerm_hasKnuthBendixCompletion = false` while `…ConvergenceCriterion = true`.
  * **Squier: not a decidability criterion.**  A finitely presented monoid can have a DECIDABLE word
    problem yet admit NO finite convergent presentation (Squier 1987, the left-FP3 homological obstruction;
    Guiraud-Malbos, *Polygraphs of finite derivation type*, arXiv:1402.2587).  So {finite convergent
    presentation} is a PROPER subclass of {decidable word problem}: this tier decides presentations you
    exhibit as convergent, it is not a completeness criterion.
  * **Does not lift past this presentation** — the rung-3 wall (arbitrary finite presentations,
    Markov/Post) stands unchanged.

Lives in `Axis/Mode/` (cross-layer top file — the ledger pins reference it) although its declarations are
in `FX1Poly.Polygraph`, mirroring `DecidableCeilingLedger`.  The WalkingInvolution files are imported as a
READ-ONLY instance source.  Raw Lean 4 + Init; structural inductions on the rewrite / closure inductives
(free-variable indices, propext-clean), the normalizer is data, `DecidableEq` is manual `isTrue rfl` on
single-constructor generators — every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open FX1Poly.Core

/-! ## The oriented rewrite rule `s.s -> id` -/

/-- ★ The **oriented involution rewrite** `s.s -> id`, whiskered under a leading `s`.  Unlike the two-sided
convertibility `InvolutionOneCellConv`, this keeps only the length-REDUCING orientation, so it is a genuine
terminating rewrite. -/
inductive InvolutionRewrite :
    ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point →
    ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point → Prop where
  /-- The rule `s.s.rest -> rest` (a double `s` at the front cancels). -/
  | ssId (rest : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
      InvolutionRewrite
        (ModalityPath.cons InvolutionModality.s (ModalityPath.cons InvolutionModality.s rest)) rest
  /-- Congruence under a leading `s` (the only 1-cell context). -/
  | consCongr {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point} :
      InvolutionRewrite word1 word2 →
      InvolutionRewrite (ModalityPath.cons InvolutionModality.s word1)
        (ModalityPath.cons InvolutionModality.s word2)

/-! ## Termination — every step drops the length by 2 -/

/-- ★ Every rewrite step strictly DECREASES the word length (by 2): `ssId` erases two generators, `consCongr`
threads the drop under a `cons`. -/
theorem involutionRewrite_lengthDecreases
    {origin reduct : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (step : InvolutionRewrite origin reduct) : reduct.length < origin.length := by
  induction step with
  | ssId rest =>
      show rest.length < (ModalityPath.cons InvolutionModality.s
        (ModalityPath.cons InvolutionModality.s rest)).length
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rest.length) (Nat.le_succ _)
  | consCongr _ inductiveHypothesis => exact Nat.succ_lt_succ inductiveHypothesis

/-- ★ The rewrite is strongly normalizing — every word is accessible — via the shipped strictly-decreasing
`Nat`-measure helper `developmentsAreFinite` (structural on a bound, no `WellFounded.fix`). -/
theorem involutionRewriteTerminating
    (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    Acc (fun reduct origin => InvolutionRewrite origin reduct) word :=
  developmentsAreFinite InvolutionRewrite (fun candidate => candidate.length)
    (fun _origin _reduct step => involutionRewrite_lengthDecreases step) word

/-- ★ Termination in the exact `WellFounded` form Knuth-Bendix consumes. -/
theorem involutionRewriteWellFounded :
    WellFounded (fun reduct origin => InvolutionRewrite origin reduct) :=
  WellFounded.intro involutionRewriteTerminating

/-! ## Parity is a reduction invariant -/

/-- A single rewrite step preserves the Z/2 parity (`s.s` drops two, parity unchanged). -/
theorem involutionRewrite_preservesParity
    {origin reduct : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (step : InvolutionRewrite origin reduct) :
    involutionParityOf origin = involutionParityOf reduct := by
  induction step with
  | ssId rest =>
      show involutionParityOf (ModalityPath.cons InvolutionModality.s
        (ModalityPath.cons InvolutionModality.s rest)) = involutionParityOf rest
      rw [involutionParityOf_cons, involutionParityOf_cons, involutionBoolNotNot]
  | consCongr _ inductiveHypothesis =>
      rw [involutionParityOf_cons, involutionParityOf_cons, inductiveHypothesis]

/-- Parity is preserved along a whole reduction chain. -/
theorem involutionRewriteStar_preservesParity
    {origin reduct : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (chain : ReflTransClosure InvolutionRewrite origin reduct) :
    involutionParityOf origin = involutionParityOf reduct := by
  induction chain with
  | refl _ => rfl
  | head first _rest inductiveHypothesis =>
      exact (involutionRewrite_preservesParity first).trans inductiveHypothesis

/-! ## The parity-normal-form funnel — every reduct reaches `parityNF` of its parity -/

/-- A reduction chain lifts under a leading `s` (each step by `consCongr`). -/
theorem involutionRewriteStar_consCongr
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (chain : ReflTransClosure InvolutionRewrite word1 word2) :
    ReflTransClosure InvolutionRewrite (ModalityPath.cons InvolutionModality.s word1)
      (ModalityPath.cons InvolutionModality.s word2) := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head first _rest inductiveHypothesis =>
      exact ReflTransClosure.head (InvolutionRewrite.consCongr first) inductiveHypothesis

/-- The `cons`-step of the funnel: if `rest` reduces to `parityNF bit`, then `s.rest` reduces to
`parityNF (!bit)`.  `false`: lift only (`parityNF false = id ↦ parityNF true = s`).  `true`: lift then fire
the rule once (`parityNF true = s ↦ s.s.id -> id = parityNF false`). -/
theorem reducesToParityNF_consStep (bit : Bool)
    {rest : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (reduction : ReflTransClosure InvolutionRewrite rest (parityNF bit)) :
    ReflTransClosure InvolutionRewrite (ModalityPath.cons InvolutionModality.s rest) (parityNF (!bit)) := by
  cases bit with
  | false => exact involutionRewriteStar_consCongr reduction
  | true =>
      exact ReflTransClosure.trans (involutionRewriteStar_consCongr reduction)
        (ReflTransClosure.single (InvolutionRewrite.ssId (involutionNil)))

/-- The funnel, generalized over the word LENGTH so the recursion is on a plain `Nat` (the reduction-level
twin of `conv_toParityNF_ofLength`). -/
theorem reducesToParityNF_ofLength :
    ∀ (bound : Nat) (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point),
      word.length = bound →
      ReflTransClosure InvolutionRewrite word (parityNF (involutionParityOf word)) := by
  intro bound
  induction bound with
  | zero =>
      intro word wordLengthEqZero
      match word with
      | .nil _ => exact ReflTransClosure.refl _
      | .cons .s _ => exact absurd wordLengthEqZero (by intro isZero; cases isZero)
  | succ predecessor inductiveHypothesis =>
      intro word wordLengthEqSucc
      match word with
      | .nil _ => exact absurd wordLengthEqSucc (by intro isSucc; cases isSucc)
      | .cons .s rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          exact reducesToParityNF_consStep (involutionParityOf rest)
            (inductiveHypothesis rest restLengthEqPredecessor)

/-- ★ Every word reduces to the parity normal form of its parity (the funnel at the word's own length). -/
theorem reducesToParityNF
    (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    ReflTransClosure InvolutionRewrite word (parityNF (involutionParityOf word)) :=
  reducesToParityNF_ofLength word.length word rfl

/-! ## The two normal forms are irreducible -/

/-- `id` (the empty word) has no outgoing rewrite step. -/
theorem involutionNil_isNormal : ∀ next, ¬ InvolutionRewrite involutionNil next := by
  intro next step
  cases step

/-- `s` (the single generator) has no outgoing rewrite step: `ssId` needs `s.s.…`, `consCongr` needs
`s.word1` with `word1` reducible, but `id` is irreducible. -/
theorem involutionS_isNormal : ∀ next, ¬ InvolutionRewrite involutionS next := by
  intro next step
  cases step with
  | consCongr inner => cases inner

/-- Every parity normal form is irreducible (either `id` or `s`). -/
theorem parityNF_isNormal (bit : Bool) : ∀ next, ¬ InvolutionRewrite (parityNF bit) next := by
  cases bit with
  | false => exact involutionNil_isNormal
  | true => exact involutionS_isNormal

/-! ## Confluence via the funnel (no critical pairs) -/

/-- ★ **Confluence.**  Two reducts of a common source share the source's parity
(`involutionRewriteStar_preservesParity`), so both reach the SAME `parityNF` (`reducesToParityNF`) and join
there.  No critical-pair analysis — the one-letter, one-rule system has none. -/
theorem involutionRewriteConfluent : Confluent InvolutionRewrite := by
  intro source leftReduct rightReduct leftChain rightChain
  have leftParity : involutionParityOf source = involutionParityOf leftReduct :=
    involutionRewriteStar_preservesParity leftChain
  have rightParity : involutionParityOf source = involutionParityOf rightReduct :=
    involutionRewriteStar_preservesParity rightChain
  refine ⟨parityNF (involutionParityOf source), ?_, ?_⟩
  · rw [leftParity]; exact reducesToParityNF leftReduct
  · rw [rightParity]; exact reducesToParityNF rightReduct

/-! ## The convergent normalizer + the decision -/

/-- ★ The **convergent normalizer** of the involution presentation: `normalize = parityNF . parity`, with
the funnel supplying reach and the two-element normal form supplying irreducibility.  Supplied as data — the
KB engine takes `normalize` as data because `WellFounded.fix` is unavailable zero-axiom. -/
def involutionConvergentNormalizer : ConvergentNormalizer InvolutionRewrite where
  normalize word := parityNF (involutionParityOf word)
  reducesToNormalForm := reducesToParityNF
  normalFormIsNormal word := parityNF_isNormal (involutionParityOf word)

/-! ## Decidable equality of the carrier -/

/-- Decidable equality of the single involution mode (one constructor). -/
def involutionModeDecEq : DecidableEq InvolutionMode
  | .point, .point => isTrue rfl

/-- Decidable equality of the involution generators (one constructor at the sole parallel pair). -/
def involutionModalityDecEq :
    (sourceMode targetMode : InvolutionMode) →
      DecidableEq (InvolutionModality sourceMode targetMode)
  | .point, .point => fun modalityOne modalityTwo =>
      match modalityOne, modalityTwo with
      | .s, .s => isTrue rfl

/-- Decidable equality of the free involution 1-cells (via the shipped `modalityPathDecEq`). -/
instance involutionModalityPathDecEq :
    DecidableEq (ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :=
  fun leftPath rightPath =>
    modalityPathDecEq involutionModeDecEq involutionModalityDecEq leftPath rightPath

/-- ★ **The KB decision.**  A convergent presentation with a normalizer DECIDES its equational theory
(reduce both sides, compare normal forms) — the shipped
`ConvergentNormalizer.decidableEquationalTheory` fired on the involution. -/
def decideInvolutionEquationalTheory
    (word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    Decidable (EquationalTheory InvolutionRewrite word1 word2) :=
  involutionConvergentNormalizer.decidableEquationalTheory involutionRewriteConfluent word1 word2

/-! ## Tier B <-> Tier C tie: the KB theory IS the thin convertibility -/

/-- A single oriented rewrite is a (two-sided) involution convertibility. -/
theorem involutionRewrite_toConv
    {origin reduct : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (step : InvolutionRewrite origin reduct) : InvolutionOneCellConv origin reduct := by
  induction step with
  | ssId rest => exact InvolutionOneCellConv.ssId rest
  | consCongr _ inductiveHypothesis => exact InvolutionOneCellConv.consCongr inductiveHypothesis

/-- The equational theory of the rewrite lifts under a leading `s`. -/
theorem involutionEquationalTheory_consCongr
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (conv : EquationalTheory InvolutionRewrite word1 word2) :
    EquationalTheory InvolutionRewrite (ModalityPath.cons InvolutionModality.s word1)
      (ModalityPath.cons InvolutionModality.s word2) := by
  induction conv with
  | rule step => exact EquationalTheory.rule (InvolutionRewrite.consCongr step)
  | refl _ => exact EquationalTheory.refl _
  | symm _ inductiveHypothesis => exact EquationalTheory.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EquationalTheory.trans firstInductiveHypothesis secondInductiveHypothesis

/-- The KB equational theory implies the thin convertibility (forward direction of the tie). -/
theorem involutionOneCellConv_of_equationalTheory
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (conv : EquationalTheory InvolutionRewrite word1 word2) : InvolutionOneCellConv word1 word2 := by
  induction conv with
  | rule step => exact involutionRewrite_toConv step
  | refl point => exact InvolutionOneCellConv.refl point
  | symm _ inductiveHypothesis => exact InvolutionOneCellConv.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact InvolutionOneCellConv.trans firstInductiveHypothesis secondInductiveHypothesis

/-- The thin convertibility implies the KB equational theory (backward direction of the tie). -/
theorem equationalTheory_of_involutionOneCellConv
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (conv : InvolutionOneCellConv word1 word2) : EquationalTheory InvolutionRewrite word1 word2 := by
  induction conv with
  | ssId rest => exact EquationalTheory.rule (InvolutionRewrite.ssId rest)
  | consCongr _ inductiveHypothesis => exact involutionEquationalTheory_consCongr inductiveHypothesis
  | refl word => exact EquationalTheory.refl word
  | symm _ inductiveHypothesis => exact EquationalTheory.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EquationalTheory.trans firstInductiveHypothesis secondInductiveHypothesis

/-- ★ **Tier B <-> Tier C tie.**  The KB equational theory of `InvolutionRewrite` COINCIDES with the Tier-B
thin relation `InvolutionOneCellConv` — the convergent-rewriting decision and the thin-classifier decision
decide the SAME walking-involution word problem. -/
theorem equationalTheory_iff_involutionOneCellConv
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point} :
    EquationalTheory InvolutionRewrite word1 word2 ↔ InvolutionOneCellConv word1 word2 :=
  ⟨involutionOneCellConv_of_equationalTheory, equationalTheory_of_involutionOneCellConv⟩

/-! ## Non-vacuity — the decision genuinely discriminates -/

/-- Positive witness: `s.s ~ id` holds in the KB theory (a single rule application). -/
theorem involutionEquationalTheory_double_nil :
    EquationalTheory InvolutionRewrite
      (ModalityPath.cons InvolutionModality.s involutionS) involutionNil :=
  EquationalTheory.rule (InvolutionRewrite.ssId involutionNil)

/-- Negative witness: `s ~ id` does NOT hold in the KB theory — via the tie and the involution's parity
separation.  Together with the positive witness the decision is neither always-true nor always-false. -/
theorem involutionEquationalTheory_notSingle_nil :
    ¬ EquationalTheory InvolutionRewrite involutionS involutionNil := by
  intro conv
  exact involutionNotConv_single_nil (involutionOneCellConv_of_equationalTheory conv)

/-! ## The Tier-C flag -/

/-- ★ **Tier C — exhibited-convergent — DECIDED.**  The involution presentation `<s | s.s = id>` is
CONVERGENT (terminating: length drops by 2, `involutionRewriteWellFounded`; confluent: the parity-NF funnel,
`involutionRewriteConfluent`, one letter / one rule / no critical pairs), so the shipped Knuth-Bendix engine
`ConvergentNormalizer.decidableEquationalTheory` DECIDES its equational theory
(`decideInvolutionEquationalTheory`), which COINCIDES with the Tier-B thin relation
(`equationalTheory_iff_involutionOneCellConv`) — tying Tiers B and C on the SAME object.  CAVEATS: convergence
is EXHIBITED by hand (the completion algorithm / fairness is not mechanized; the normalizer is data); by
Squier this is NOT a decidability criterion (finitely presented monoids with decidable word problem but no
finite convergent presentation exist, arXiv:1402.2587); does NOT lift past this presentation (rung-3 wall
stands).  `= true`. -/
def fxMode_hasExhibitedConvergentDecision : Bool := true

/-- The Tier-C flag is pinned to the involution's decided-word-problem marker (the convergent presentation is
the involution's own), so the tier cannot claim decided without the backing involution decision. -/
theorem fxMode_hasExhibitedConvergentDecision_matchesInvolutionMarker :
    fxMode_hasExhibitedConvergentDecision = fxInvolution_hasOneCellWordProblemDecided := rfl

end FX1Poly.Polygraph
