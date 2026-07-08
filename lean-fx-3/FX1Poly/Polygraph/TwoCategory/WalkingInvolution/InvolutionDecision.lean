import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionParity

/-! # WalkingInvolution/InvolutionDecision — COMPLETENESS, the total decision, and the session-duality tie

Soundness (`InvolutionParity`) gives distinct-parity ⟹ not-convertible.  This file closes the walking-involution
1-cell word problem with the other direction — COMPLETENESS: equal parity ⟹ convertible — via a two-element
normal form (`parityNF false = id`, `parityNF true = s`), a reconstruction `conv_toParityNF` (every word is
convertible to the `parityNF` of its parity), and hence a TOTAL `Decidable (InvolutionOneCellConv _ _)` that
compares the two words' parities in Z/2.

## The session-duality decision (Wadler `S̄̄ = S`, fx_design.md §11.2)

`s` is session-type DUALITY (`dual`).  The decidable question "does a chain of `dual`s equal the identity protocol
transform?" is exactly `InvolutionOneCellConv word (nil)`, decided by `involutionParityOf word = false` — an even
number of `dual`s is the identity (`S̄̄ = S`), an odd number is a single `dual`.  So FX's `dual(dual(P)) = P` is a
DECIDABLE fact about protocol transforms, and this file is the machine-checked proof of that decidability.

Raw Lean 4 + Init; the reconstruction is a structural recursion, the decision is `DecidableEq Bool`, so every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The two-element normal form -/

/-- The **parity normal form**: the canonical representative of each Z/2 class — `false ↦ id` (the empty word),
`true ↦ s` (the single generator).  Every word is convertible to the `parityNF` of its parity. -/
def parityNF : Bool → ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point
  | false => involutionNil
  | true => involutionS

/-! ## COMPLETENESS: every word reduces to its parity normal form -/

/-- The `cons`-step of the reconstruction: prepending an `s` flips both the word and its normal form.  If `rest`
is convertible to `parityNF bit`, then `s.rest` is convertible to `parityNF (!bit)`.  Both cases are a single
`cons`-congruence; the `true` case additionally cancels the exposed `s.s` at the front by the involution law. -/
theorem consCongr_parityNF (bit : Bool)
    {rest : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (reduction : InvolutionOneCellConv rest (parityNF bit)) :
    InvolutionOneCellConv (ModalityPath.cons InvolutionModality.s rest) (parityNF (!bit)) := by
  cases bit with
  | false => exact InvolutionOneCellConv.consCongr reduction
  | true =>
      exact InvolutionOneCellConv.trans (InvolutionOneCellConv.consCongr reduction)
        (InvolutionOneCellConv.ssId (involutionNil))

/-- The reconstruction, generalized over the word LENGTH so the recursion is on a plain `Nat` (structural
recursion on the word itself, as a proof-valued `def` matching `.cons .s`, refines the modality index and leaks
`propext`; recursing on the length and destructuring the word in a TACTIC `match` is propext-free).  `nil` is
`refl` at `parityNF false = id`; `s.rest` lifts the tail's reconstruction through `consCongr_parityNF` (which
fires the involution law exactly when the tail's parity is `true`). -/
theorem conv_toParityNF_ofLength :
    ∀ (bound : Nat) (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point),
      word.length = bound → InvolutionOneCellConv word (parityNF (involutionParityOf word)) := by
  intro bound
  induction bound with
  | zero =>
      intro word wordLengthEqZero
      match word with
      | .nil _ => exact InvolutionOneCellConv.refl involutionNil
      | .cons .s _ => exact absurd wordLengthEqZero (by intro isZero; cases isZero)
  | succ predecessor inductiveHypothesis =>
      intro word wordLengthEqSucc
      match word with
      | .nil _ => exact absurd wordLengthEqSucc (by intro isSucc; cases isSucc)
      | .cons .s rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          exact consCongr_parityNF (involutionParityOf rest)
            (inductiveHypothesis rest restLengthEqPredecessor)

/-- ★ **The reconstruction**: every word is convertible to the parity normal form of its parity (the
length-generalized `conv_toParityNF_ofLength` at the word's own length). -/
theorem conv_toParityNF
    (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    InvolutionOneCellConv word (parityNF (involutionParityOf word)) :=
  conv_toParityNF_ofLength word.length word rfl

/-- ★ **Completeness of the Z/2 model**: words with EQUAL parity are convertible.  Route both words through their
common parity normal form: `word1 ≈ parityNF (parity word1) = parityNF (parity word2) ≈ word2`.  This is the
YES-direction of the decision (the reconstruction). -/
theorem involutionOneCellConv_of_parity_eq
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (paritiesEqual : involutionParityOf word1 = involutionParityOf word2) :
    InvolutionOneCellConv word1 word2 := by
  have reductionOne : InvolutionOneCellConv word1 (parityNF (involutionParityOf word2)) := by
    rw [← paritiesEqual]; exact conv_toParityNF word1
  exact InvolutionOneCellConv.trans reductionOne (InvolutionOneCellConv.symm (conv_toParityNF word2))

/-! ## The TOTAL decision -/

/-- ★ **Decide walking-involution 1-cell convertibility** — TOTAL.  Compare the two words' Z/2 parities: equal
parities ⟹ `isTrue` (via completeness `involutionOneCellConv_of_parity_eq`); distinct parities ⟹ `isFalse`
(soundness `involutionParityOf_congr_of_conv` would force them equal).  Both branches discharged — the word
problem is genuinely decided. -/
def decideInvolutionOneCellConv
    (word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    Decidable (InvolutionOneCellConv word1 word2) :=
  match (inferInstance : Decidable (involutionParityOf word1 = involutionParityOf word2)) with
  | isTrue paritiesEqual => isTrue (involutionOneCellConv_of_parity_eq paritiesEqual)
  | isFalse paritiesDiffer =>
      isFalse (fun conv => paritiesDiffer (involutionParityOf_congr_of_conv conv))

/-- The walking involution's 1-cell convertibility as a `Decidable` instance (so `decide` fires on it). -/
instance instDecidableInvolutionOneCellConv
    (word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    Decidable (InvolutionOneCellConv word1 word2) :=
  decideInvolutionOneCellConv word1 word2

/-! ## Non-vacuity smokes — the decider genuinely discriminates -/

/-- Positive witness: `s.s ≈ id` (the double dual is the identity) — a convertible pair. -/
theorem involutionConv_double_nil :
    InvolutionOneCellConv
      (ModalityPath.cons InvolutionModality.s involutionS)
      (involutionNil) :=
  involutionLawHolds

/-- Negative witness: `s` is NOT convertible to `id` (a single dual is not the identity) — via soundness, since
their parities are `true` and `false`.  The two ends of the decision are genuinely separated. -/
theorem involutionNotConv_single_nil :
    ¬ InvolutionOneCellConv involutionS (involutionNil) := by
  intro conv
  have contradiction : (true : Bool) = false := involutionParityOf_congr_of_conv conv
  exact Bool.noConfusion contradiction

/-- ★ Non-vacuity by the DECIDER (positive): `decide` on the convertible pair `s.s ≈ id` returns `true` — the total
decider actually fires and accepts. -/
theorem involutionDecide_true_on_double :
    decide (InvolutionOneCellConv (ModalityPath.cons InvolutionModality.s involutionS)
      (involutionNil)) = true := rfl

/-- ★ Non-vacuity by the DECIDER (negative): `decide` on the separated pair `s ≟ id` returns `false` — the total
decider actually fires and rejects.  Together with the positive smoke this witnesses the decision is neither
always-true nor always-false. -/
theorem involutionDecide_false_on_single :
    decide (InvolutionOneCellConv involutionS (involutionNil)) = false := rfl

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The walking-involution 1-cell word problem `⟨s | s.s = id⟩` is DECIDED, zero-axiom and
non-vacuously: the Z/2 model `involutionParityOf` is SOUND (`involutionParityOf_congr_of_conv`) and COMPLETE
(`involutionOneCellConv_of_parity_eq`, via the two-element `parityNF` reconstruction `conv_toParityNF`), and the
total decider `decideInvolutionOneCellConv` accepts the convertible pair `s.s ≈ id`
(`involutionDecide_true_on_double`) and rejects the separated pair `s ≟ id` (`involutionDecide_false_on_single`).
Since the 2-signature is free on nothing (`involution_no_two_generators`), 2-cell equality IS this 1-cell
equality.  This is the machine-checked decidability of session-duality parity (`dual(dual(P)) = P`, fx_design.md
§11.2 / Wadler `S̄̄ = S`).  `= true`. -/
def fxInvolution_hasOneCellWordProblemDecided : Bool := true

end FX1Poly.Polygraph
