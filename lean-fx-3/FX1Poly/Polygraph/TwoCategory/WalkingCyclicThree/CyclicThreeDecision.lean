import FX1Poly.Polygraph.Computad.Signature

/-! # WalkingCyclicThree/CyclicThreeDecision — the walking cyclic-3 `s.s.s = id` 1-cell word problem, DECIDED

The walking cyclic-3 `⟨s | s.s.s = id⟩` is the mod-3 sibling of the walking involution `⟨s | s.s = id⟩`: ONE
mode `point`, ONE endo-1-generator `s : point ⟶ point`, and the strict relation `s.s.s = id` at the 1-CELL
level.  Its 1-cell monoid is `Z/3` — a word in `s` is determined, modulo `s.s.s = id`, by its LENGTH mod 3.
This file mirrors the involution decider exactly, but mod THREE: it ships the whole word-problem decision in one
place — the seed (quiver + free 1-cells + degenerate 2-signature), the `s.s.s = id` 1-cell convertibility
`CyclicThreeOneCellConv`, the `Z/3` model `cyclicThreeResidueOf` (word length mod 3), SOUNDNESS (convertible
words have equal residue), COMPLETENESS (equal residue ⟹ convertible, via a THREE-element normal form
reconstruction), and hence a TOTAL `Decidable (CyclicThreeOneCellConv _ _)` comparing the two words' `Z/3`
residues.

This closes the DECISION-ledger gap the census hides: `WordProblemDecisionLedger` records cyclic-3 as
`decisionNotShipped` (`fxWpLedger_cyclicThreeDecisionUnshipped`) — the SOLE decided-family rung with a coherent
Omega presentation (`cyclicThreeWalkerCoherentPresentation`) and a homology read-off (`H1 = Z/3`) but no shipped
word-problem decider.  Here it is shipped, zero-axiom.

## Where cyclic-3 differs from the involution (NOT a verbatim clone)

  * The relation generator cancels THREE `s`'s at a time (`sssId : s.(s.(s.rest)) ≈ rest`), not two.  The
    `Z/2` semantic content `!!b = b` becomes the `Z/3` content `shiftResidue³ = id` (`shiftResidueTripleIsIdentity`).
  * The residue is a THREE-element type `CyclicThreeResidue` (not `Bool`), with a manual full-enumeration
    `DecidableEq` (`cyclicThreeResidueDecEq`) — no `DecidableEq` for the `Z/3` carrier is shipped anywhere in
    the homology lane, which deliberately avoids it.
  * The normal form has THREE representatives (`residueNF`: `id`, `s`, `s.s`), not two, and each leading `s`
    advances the residue by `shiftResidue` (a 3-cycle `zero → one → two → zero`), firing the `s.s.s = id` law
    exactly when the tail's residue is the top one (`residueTwo`).

## The propext-free load-bearing tricks (copied from the involution)

  * The `Z/3` model is routed through `ModalityPath.length` (`natMod3 ∘ length`), both structural, so
    `cyclicThreeResidueOf (s.rest) = shiftResidue (cyclicThreeResidueOf rest)` holds DEFINITIONALLY — unlike a
    direct modality-refining recursion whose matcher would not reduce and would leak `propext`.
  * The reconstruction recurses on a plain `Nat` (the word length `bound`), destructuring the word in a TACTIC
    `match` — a proof-valued `def` matching `.cons .s` directly would refine the modality index and leak
    `propext`.
  * The residue arithmetic uses FULL-ENUMERATION matches (no wildcard `_ =>` arms), the decision is
    `DecidableEq CyclicThreeResidue`, and impossible length cases are discharged by `cases` on a `Nat`
    equation of distinct constructors — no `omega`, no `decide`-by-reflection, no `Classical`.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The walking cyclic-3 quiver: one object, one endo-generator -/

/-- The single mode (0-cell) of the walking cyclic-3. -/
inductive CyclicThreeMode where
  /-- The unique object. -/
  | point

/-- The single generating modality (1-cell) of the walking cyclic-3: the endo-generator `s : point ⟶ point`
(the order-3 rotation). -/
inductive CyclicThreeModality : CyclicThreeMode → CyclicThreeMode → Type where
  /-- The generating endo-1-cell `s`. -/
  | s : CyclicThreeModality CyclicThreeMode.point CyclicThreeMode.point

/-- The walking cyclic-3 quiver: one mode, one endo-modality. -/
def cyclicThreeGraph : ModeGraph where
  Mode := CyclicThreeMode
  Modality := CyclicThreeModality

/-- The identity 1-cell at `point` (the empty word — the RHS of the cyclic-3 law `s.s.s = id`). -/
def cyclicThreeNil : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point :=
  ModalityPath.nil (graph := cyclicThreeGraph) CyclicThreeMode.point

/-- The generating endo-1-cell `s` as the length-1 free 1-cell (the single-step path). -/
def cyclicThreeS : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point :=
  singletonModalityPath CyclicThreeModality.s

/-- The length-2 free 1-cell `s.s` — the residue-`two` normal-form representative. -/
def cyclicThreeSS : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point :=
  ModalityPath.cons CyclicThreeModality.s cyclicThreeS

/-- The length-3 free 1-cell `s.s.s` — the cyclic-3 law's left-hand side. -/
def cyclicThreeSSS : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point :=
  ModalityPath.cons CyclicThreeModality.s cyclicThreeSS

/-- ★ The **walking cyclic-3 mode signature** — the degenerate 2-computad: the cyclic-3 quiver with NO
generating 2-cells (`twoCell` is `Empty` on every parallel pair).  The cyclic-3's only relation lives at the
1-cell level (`s.s.s = id`, the `CyclicThreeOneCellConv` below); at the 2-cell level the signature is FREE ON
NOTHING, so 2-cell equality collapses to 1-cell equality. -/
def cyclicThreeModeSignature : ModeSignature where
  graph := cyclicThreeGraph
  twoCell := fun _ _ => Empty

/-! ## Freeness / degeneracy smokes -/

/-- Smoke: `s` is the length-1 1-cell. -/
theorem cyclicThreeS_length : cyclicThreeS.length = 1 := rfl

/-- Smoke: `s.s.s` (the cyclic-3 relation's left-hand side) is the length-3 1-cell. -/
theorem cyclicThreeSSS_length : cyclicThreeSSS.length = 3 := rfl

/-- Smoke: the 2-signature is FREE ON NOTHING — there is no generating 2-cell between any parallel pair (here
`s ⇒ s`), so 2-cell equality is 1-cell equality. -/
theorem cyclicThree_no_two_generators
    (generatingTwoCell : cyclicThreeModeSignature.twoCell cyclicThreeS cyclicThreeS) : False :=
  nomatch generatingTwoCell

/-! ## The `s.s.s = id` 1-cell convertibility -/

/-- ★ The **`s.s.s = id` 1-cell convertibility** of the walking cyclic-3 — the free-1-category convertibility of
the cyclic-3 quiver plus the single cyclic-3 law `s.s.s ≈ id`, closed under the `cons`-congruence and
`refl`/`symm`/`trans` into a genuine congruence.  Two words in `s` are equal AS 1-cells of the walking cyclic-3
`⟨s | s.s.s = id⟩` exactly when they are `CyclicThreeOneCellConv`-related.  Because there is exactly ONE
generating 1-cell `s`, the only context is `cons s _`, so the front-firing law `sssId` plus the `cons`-congruence
plus `symm`/`trans` generate the full two-sided congruence. -/
inductive CyclicThreeOneCellConv :
    ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point →
    ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point → Prop where
  /-- The **cyclic-3 law** `s.s.s ≈ id`, whiskered on the right by an arbitrary suffix `rest`:
  `s.(s.(s.rest)) ≈ rest` (a triple `s` at the front cancels). -/
  | sssId (rest : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) :
      CyclicThreeOneCellConv
        (ModalityPath.cons CyclicThreeModality.s
          (ModalityPath.cons CyclicThreeModality.s
            (ModalityPath.cons CyclicThreeModality.s rest))) rest
  /-- Congruence under a leading `s` (the only 1-cell context): `word1 ≈ word2 ⟹ s.word1 ≈ s.word2`. -/
  | consCongr {word1 word2 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point} :
      CyclicThreeOneCellConv word1 word2 →
      CyclicThreeOneCellConv (ModalityPath.cons CyclicThreeModality.s word1)
        (ModalityPath.cons CyclicThreeModality.s word2)
  /-- Reflexivity. -/
  | refl (word : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) :
      CyclicThreeOneCellConv word word
  /-- Symmetry. -/
  | symm {word1 word2 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point} :
      CyclicThreeOneCellConv word1 word2 → CyclicThreeOneCellConv word2 word1
  /-- Transitivity. -/
  | trans {word1 word2 word3 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point} :
      CyclicThreeOneCellConv word1 word2 → CyclicThreeOneCellConv word2 word3 →
      CyclicThreeOneCellConv word1 word3

/-- ★ **The cyclic-3 law holds** — `s.s.s ≈ id` (at the empty suffix): the triple rotation cancels to the
identity. -/
theorem cyclicThreeLawHolds :
    CyclicThreeOneCellConv cyclicThreeSSS cyclicThreeNil :=
  CyclicThreeOneCellConv.sssId cyclicThreeNil

/-- Smoke: the cyclic-3 law fires UNDER a leading `s` — `s.(s.s.s) ≈ s.id = s` — exercising the
`cons`-congruence with the law generator (the whiskered cyclic-3 law). -/
theorem cyclicThreeLawWhiskeredHolds :
    CyclicThreeOneCellConv
      (ModalityPath.cons CyclicThreeModality.s cyclicThreeSSS)
      (ModalityPath.cons CyclicThreeModality.s cyclicThreeNil) :=
  CyclicThreeOneCellConv.consCongr cyclicThreeLawHolds

/-! ## The Z/3 residue type and its arithmetic -/

/-- The **Z/3 residue** carrier — a three-element enumerable type (`zero`, `one`, `two`).  The `Z/3` analogue of
`Bool`, with a manual `DecidableEq` below (no `Z/3` `DecidableEq` is shipped in the homology lane). -/
inductive CyclicThreeResidue where
  /-- Residue 0 — the identity class. -/
  | residueZero
  /-- Residue 1 — the `s` class. -/
  | residueOne
  /-- Residue 2 — the `s.s` class. -/
  | residueTwo

/-- The **residue shift** — advance by one (a 3-cycle `zero → one → two → zero`).  Each leading `s` applies it;
its CUBE is the identity (`shiftResidueTripleIsIdentity`), the semantic content of `s.s.s = id`. -/
def shiftResidue : CyclicThreeResidue → CyclicThreeResidue
  | .residueZero => .residueOne
  | .residueOne => .residueTwo
  | .residueTwo => .residueZero

/-- ★ The **cubed shift is the identity** (the `Z/3` relation `residue(s.s.s) = residue(id)`), by the
three-case split — propext-free.  The mod-3 analogue of the involution's `!!b = b`. -/
theorem shiftResidueTripleIsIdentity (residue : CyclicThreeResidue) :
    shiftResidue (shiftResidue (shiftResidue residue)) = residue := by
  cases residue with
  | residueZero => rfl
  | residueOne => rfl
  | residueTwo => rfl

/-- Decidable equality of `Z/3` residues — a MANUAL full-enumeration `decEq` (nine cases: three `isTrue rfl`,
six `isFalse` via `noConfusion`), propext-free.  The homology lane deliberately ships no `DecidableEq` for its
`Z/3` carrier, so the decider needs this one. -/
def cyclicThreeResidueDecEq :
    (firstResidue secondResidue : CyclicThreeResidue) → Decidable (firstResidue = secondResidue)
  | .residueZero, .residueZero => isTrue rfl
  | .residueOne, .residueOne => isTrue rfl
  | .residueTwo, .residueTwo => isTrue rfl
  | .residueZero, .residueOne => isFalse (fun residuesEqual => CyclicThreeResidue.noConfusion residuesEqual)
  | .residueZero, .residueTwo => isFalse (fun residuesEqual => CyclicThreeResidue.noConfusion residuesEqual)
  | .residueOne, .residueZero => isFalse (fun residuesEqual => CyclicThreeResidue.noConfusion residuesEqual)
  | .residueOne, .residueTwo => isFalse (fun residuesEqual => CyclicThreeResidue.noConfusion residuesEqual)
  | .residueTwo, .residueZero => isFalse (fun residuesEqual => CyclicThreeResidue.noConfusion residuesEqual)
  | .residueTwo, .residueOne => isFalse (fun residuesEqual => CyclicThreeResidue.noConfusion residuesEqual)

/-- The `Z/3` residues have decidable equality (so the decider's `inferInstance` fires). -/
instance instDecidableEqCyclicThreeResidue : DecidableEq CyclicThreeResidue := cyclicThreeResidueDecEq

/-! ## The Z/3 model: word length mod 3 -/

/-- The residue of a natural number mod 3: `0 ↦ zero`, and each successor SHIFTS.  Plain `Nat` structural
recursion, so its defining equations hold DEFINITIONALLY — the reason the model is routed through `length`. -/
def natMod3 : Nat → CyclicThreeResidue
  | 0 => .residueZero
  | count + 1 => shiftResidue (natMod3 count)

/-- ★ The **Z/3 model** of the walking cyclic-3: the residue of a word in `s` — `zero` for the identity, and
each leading `s` SHIFTS the residue by one.  Computed as `natMod3` of the word's LENGTH (matching `cons`
generically through the already-clean `length`, so `cyclicThreeResidueOf (s.rest) = shiftResidue
(cyclicThreeResidueOf rest)` holds DEFINITIONALLY).  This is the invariant that decides the 1-cell word problem,
because `s.s.s = id` preserves it (`shiftResidue³ = id`). -/
def cyclicThreeResidueOf
    (word : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) : CyclicThreeResidue :=
  natMod3 word.length

/-- The defining equation on `nil` — the identity has residue `zero`. -/
theorem cyclicThreeResidueOf_nil :
    cyclicThreeResidueOf cyclicThreeNil = CyclicThreeResidue.residueZero := rfl

/-- The defining equation on `cons s` — a leading `s` shifts the residue. -/
theorem cyclicThreeResidueOf_cons
    (rest : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) :
    cyclicThreeResidueOf (ModalityPath.cons CyclicThreeModality.s rest)
      = shiftResidue (cyclicThreeResidueOf rest) := rfl

/-- Smoke: `s` has residue `one`. -/
theorem cyclicThreeResidueOf_cyclicThreeS :
    cyclicThreeResidueOf cyclicThreeS = CyclicThreeResidue.residueOne := rfl

/-- Smoke: `s.s` has residue `two`. -/
theorem cyclicThreeResidueOf_cyclicThreeSS :
    cyclicThreeResidueOf cyclicThreeSS = CyclicThreeResidue.residueTwo := rfl

/-- Smoke: `s.s.s` has residue `zero` — the triple rotation IS the identity in `Z/3`. -/
theorem cyclicThreeResidueOf_cyclicThreeSSS :
    cyclicThreeResidueOf cyclicThreeSSS = CyclicThreeResidue.residueZero := rfl

/-! ## SOUNDNESS: convertible words have equal residue -/

/-- ★ **Soundness of the Z/3 model**: `s.s.s = id`-convertible words have EQUAL residue.  By induction on the
convertibility: the cyclic-3 law `sssId` is exactly `shiftResidue³ = id` (`shiftResidueTripleIsIdentity`), the
`cons`-congruence shifts both sides equally (`congrArg shiftResidue`), and `refl`/`symm`/`trans` are the
equivalence closure.  This is the NO-direction of the decision (distinct residue ⟹ not convertible). -/
theorem cyclicThreeResidueOf_congr_of_conv
    {word1 word2 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point}
    (conv : CyclicThreeOneCellConv word1 word2) :
    cyclicThreeResidueOf word1 = cyclicThreeResidueOf word2 := by
  induction conv with
  | sssId rest => exact shiftResidueTripleIsIdentity (cyclicThreeResidueOf rest)
  | consCongr _ ih => exact congrArg shiftResidue ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The three-element normal form -/

/-- The **residue normal form**: the canonical representative of each `Z/3` class — `zero ↦ id`, `one ↦ s`,
`two ↦ s.s`.  Every word is convertible to the `residueNF` of its residue. -/
def residueNF : CyclicThreeResidue → ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point
  | .residueZero => cyclicThreeNil
  | .residueOne => cyclicThreeS
  | .residueTwo => cyclicThreeSS

/-! ## COMPLETENESS: every word reduces to its residue normal form -/

/-- The `cons`-step of the reconstruction: prepending an `s` shifts both the word and its normal form.  If `rest`
is convertible to `residueNF residue`, then `s.rest` is convertible to `residueNF (shiftResidue residue)`.  The
`zero`/`one` cases are a single `cons`-congruence; the `two` case additionally cancels the exposed `s.s.s` at the
front by the cyclic-3 law. -/
theorem consCongr_residueNF (residue : CyclicThreeResidue)
    {rest : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point}
    (reduction : CyclicThreeOneCellConv rest (residueNF residue)) :
    CyclicThreeOneCellConv (ModalityPath.cons CyclicThreeModality.s rest)
      (residueNF (shiftResidue residue)) := by
  cases residue with
  | residueZero => exact CyclicThreeOneCellConv.consCongr reduction
  | residueOne => exact CyclicThreeOneCellConv.consCongr reduction
  | residueTwo =>
      exact CyclicThreeOneCellConv.trans (CyclicThreeOneCellConv.consCongr reduction)
        (CyclicThreeOneCellConv.sssId cyclicThreeNil)

/-- The reconstruction, generalized over the word LENGTH so the recursion is on a plain `Nat` (a proof-valued
`def` matching `.cons .s` directly refines the modality index and leaks `propext`; recursing on the length and
destructuring the word in a TACTIC `match` is propext-free).  `nil` is `refl` at `residueNF zero = id`; `s.rest`
lifts the tail's reconstruction through `consCongr_residueNF` (which fires the cyclic-3 law exactly when the
tail's residue is `two`). -/
theorem conv_toResidueNF_ofLength :
    ∀ (bound : Nat)
      (word : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point),
      word.length = bound → CyclicThreeOneCellConv word (residueNF (cyclicThreeResidueOf word)) := by
  intro bound
  induction bound with
  | zero =>
      intro word wordLengthEqZero
      match word with
      | .nil _ => exact CyclicThreeOneCellConv.refl cyclicThreeNil
      | .cons .s _ => exact absurd wordLengthEqZero (by intro isZero; cases isZero)
  | succ predecessor inductiveHypothesis =>
      intro word wordLengthEqSucc
      match word with
      | .nil _ => exact absurd wordLengthEqSucc (by intro isSucc; cases isSucc)
      | .cons .s rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          exact consCongr_residueNF (cyclicThreeResidueOf rest)
            (inductiveHypothesis rest restLengthEqPredecessor)

/-- ★ **The reconstruction**: every word is convertible to the residue normal form of its residue (the
length-generalized `conv_toResidueNF_ofLength` at the word's own length). -/
theorem conv_toResidueNF
    (word : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) :
    CyclicThreeOneCellConv word (residueNF (cyclicThreeResidueOf word)) :=
  conv_toResidueNF_ofLength word.length word rfl

/-- ★ **Completeness of the Z/3 model**: words with EQUAL residue are convertible.  Route both words through
their common residue normal form: `word1 ≈ residueNF (residue word1) = residueNF (residue word2) ≈ word2`.  This
is the YES-direction of the decision (the reconstruction). -/
theorem cyclicThreeOneCellConv_of_residue_eq
    {word1 word2 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point}
    (residuesEqual : cyclicThreeResidueOf word1 = cyclicThreeResidueOf word2) :
    CyclicThreeOneCellConv word1 word2 := by
  have reductionOne : CyclicThreeOneCellConv word1 (residueNF (cyclicThreeResidueOf word2)) := by
    rw [← residuesEqual]; exact conv_toResidueNF word1
  exact CyclicThreeOneCellConv.trans reductionOne (CyclicThreeOneCellConv.symm (conv_toResidueNF word2))

/-! ## The TOTAL decision -/

/-- ★ **Decide walking cyclic-3 1-cell convertibility** — TOTAL.  Compare the two words' `Z/3` residues: equal
residues ⟹ `isTrue` (via completeness `cyclicThreeOneCellConv_of_residue_eq`); distinct residues ⟹ `isFalse`
(soundness `cyclicThreeResidueOf_congr_of_conv` would force them equal).  Both branches discharged — the word
problem is genuinely decided. -/
def decideCyclicThreeOneCellConv
    (word1 word2 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) :
    Decidable (CyclicThreeOneCellConv word1 word2) :=
  match (inferInstance : Decidable (cyclicThreeResidueOf word1 = cyclicThreeResidueOf word2)) with
  | isTrue residuesEqual => isTrue (cyclicThreeOneCellConv_of_residue_eq residuesEqual)
  | isFalse residuesDiffer =>
      isFalse (fun conv => residuesDiffer (cyclicThreeResidueOf_congr_of_conv conv))

/-- The walking cyclic-3's 1-cell convertibility as a `Decidable` instance (so `decide` fires on it). -/
instance instDecidableCyclicThreeOneCellConv
    (word1 word2 : ModalityPath cyclicThreeGraph CyclicThreeMode.point CyclicThreeMode.point) :
    Decidable (CyclicThreeOneCellConv word1 word2) :=
  decideCyclicThreeOneCellConv word1 word2

/-! ## Non-vacuity smokes — the decider genuinely discriminates -/

/-- Positive witness: `s.s.s ≈ id` (the triple rotation is the identity) — a convertible pair. -/
theorem cyclicThreeConv_triple_nil :
    CyclicThreeOneCellConv cyclicThreeSSS cyclicThreeNil :=
  cyclicThreeLawHolds

/-- Negative witness: `s` is NOT convertible to `id` (a single rotation is not the identity) — via soundness,
since their residues are `one` and `zero`. -/
theorem cyclicThreeNotConv_single_nil :
    ¬ CyclicThreeOneCellConv cyclicThreeS cyclicThreeNil := by
  intro conv
  have contradiction : CyclicThreeResidue.residueOne = CyclicThreeResidue.residueZero :=
    cyclicThreeResidueOf_congr_of_conv conv
  exact CyclicThreeResidue.noConfusion contradiction

/-- Negative witness: `s.s` is NOT convertible to `id` (a double rotation is not the identity) — residues `two`
and `zero`. -/
theorem cyclicThreeNotConv_double_nil :
    ¬ CyclicThreeOneCellConv cyclicThreeSS cyclicThreeNil := by
  intro conv
  have contradiction : CyclicThreeResidue.residueTwo = CyclicThreeResidue.residueZero :=
    cyclicThreeResidueOf_congr_of_conv conv
  exact CyclicThreeResidue.noConfusion contradiction

/-- ★ Non-vacuity by the DECIDER (positive): `decide` on the convertible pair `s.s.s ≈ id` returns `true` — the
total decider actually fires and accepts. -/
theorem cyclicThreeDecide_true_on_triple :
    decide (CyclicThreeOneCellConv cyclicThreeSSS cyclicThreeNil) = true := rfl

/-- ★ Non-vacuity by the DECIDER (negative, single): `decide` on the separated pair `s ≟ id` returns `false`. -/
theorem cyclicThreeDecide_false_on_single :
    decide (CyclicThreeOneCellConv cyclicThreeS cyclicThreeNil) = false := rfl

/-- ★ Non-vacuity by the DECIDER (negative, double): `decide` on the separated pair `s.s ≟ id` returns `false` —
witnessing the mod-3 content beyond mod-2 (a double `s` is NOT the identity, unlike the involution). -/
theorem cyclicThreeDecide_false_on_double :
    decide (CyclicThreeOneCellConv cyclicThreeSS cyclicThreeNil) = false := rfl

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The walking cyclic-3 1-cell word problem `⟨s | s.s.s = id⟩` is DECIDED, zero-axiom and
non-vacuously: the `Z/3` model `cyclicThreeResidueOf` is SOUND (`cyclicThreeResidueOf_congr_of_conv`) and
COMPLETE (`cyclicThreeOneCellConv_of_residue_eq`, via the three-element `residueNF` reconstruction
`conv_toResidueNF`), and the total decider `decideCyclicThreeOneCellConv` accepts the convertible pair
`s.s.s ≈ id` (`cyclicThreeDecide_true_on_triple`) and rejects the separated pairs `s ≟ id`
(`cyclicThreeDecide_false_on_single`) and `s.s ≟ id` (`cyclicThreeDecide_false_on_double`).  Since the
2-signature is free on nothing (`cyclicThree_no_two_generators`), 2-cell equality IS this 1-cell equality.  This
closes the `WordProblemDecisionLedger` cyclic-3 gap (`fxWpLedger_cyclicThreeDecisionUnshipped`) — the SOLE
decided-family rung that had a coherent presentation and a homology read-off (`H1 = Z/3`) but no shipped
word-problem decider.  `= true`. -/
def fxCyclicThree_hasOneCellWordProblemDecided : Bool := true

end FX1Poly.Polygraph
