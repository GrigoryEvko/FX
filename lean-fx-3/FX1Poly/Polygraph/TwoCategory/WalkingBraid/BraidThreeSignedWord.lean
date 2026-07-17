import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeGarsideDecision

/-! # WalkingBraid/BraidThreeSignedWord — the SIGNED braid-group alphabet + relation (`B_3`, brick 1)

The walking braid goes GROUP: `B_3 = ⟨σ1, σ2 | σ1σ2σ1 = σ2σ1σ2⟩` with genuine inverses.  This brick ships
the SIGNED word carrier and its convertibility:

  * **The signed alphabet** `BraidSignedAtom` — four atoms `σ1, σ2, σ1⁻¹, σ2⁻¹`.  Unlike the finite-cyclic
    walkers (where `s⁻¹ = s²` is a positive power), `B_3`'s inverses are NOT expressible positively — the
    signed alphabet is essential, and the carrier is the plain free monoid `List BraidSignedAtom` (a group
    presentation is not a free category on a quiver, so the mode-indexed `ModalityPath` deliberately stays
    on the positive side; the embedding of positive words and the agreement theorem live in the decision
    brick).
  * **The signed convertibility** `BraidThreeSignedConv` — the braid relation on the positive atoms PLUS the
    FOUR cancellation axioms (`σi·σi⁻¹ ≈ ε`, `σi⁻¹·σi ≈ ε`), each front-firing and whiskered by an arbitrary
    suffix, closed under the generic `consCongr` + `refl`/`symm`/`trans` — the exact house shape of the
    positive `BraidThreeOneCellConv`, so the two-sided congruence argument carries over verbatim.
  * **The derived complement identities**, PROVED from the relation (never asserted):
      - `Δ⁻¹·Δ ≈ ε` and its `σ2σ1σ2`-representation twin (`braidSignedDeltaInvDeltaCancel`,
        `braidSignedDeltaSecondRepCancel`) — pure cancellation chains;
      - the **inverse braid relation** `σ1⁻¹σ2⁻¹σ1⁻¹ ≈ σ2⁻¹σ1⁻¹σ2⁻¹` (`braidSignedInverseBraidRel`) — pad
        with `Δ·Δ⁻¹`, fire the positive braid move in the middle, cancel;
      - the **Δ⁻¹-conjugation flips** `σ1·Δ⁻¹·R ≈ Δ⁻¹·σ2·R`, `σ2·Δ⁻¹·R ≈ Δ⁻¹·σ1·R`
        (`braidSignedFlipDeltaInvSigmaOne/Two`) — the signed mirror of the shipped
        `braidThreeDeltaConjugateSigma1/2`, the domino the negative-shift carry rides;
      - the **left-complement expansions** `σ1⁻¹·R ≈ Δ⁻¹·(σ1σ2)·R`, `σ2⁻¹·R ≈ Δ⁻¹·(σ2σ1)·R`
        (`braidSignedInvExpandSigmaOne/Two`) — `σi⁻¹ = Δ⁻¹ · (left complement of σi)`, THE identity that
        lets the signed normalizer prepend an inverse atom as one `Δ⁻¹`-shift plus two POSITIVE prepends
        through the shipped `braidPrependAtom` machinery.

## Honesty boundary

NO canonical form and NO decision in this brick — carrier + relation + the conv toolkit only.  The signed
Garside canon (`Δ`-power in `ℤ` represented Int-free) is brick 2 (`BraidThreeSignedCanon`); soundness /
completeness / the total decider / the positive-embedding agreement are brick 3
(`BraidThreeSignedGroupDecision`).

## Propext-cleanliness

The convertibility is an inductive `Prop`; every derived identity is a TERM-mode constructor chain (no match
compiler, no tactics beyond none).  Per-declaration `#assert_no_axioms` gated in the audit twin.  Free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The signed alphabet -/

/-- The four **signed atoms** of the braid group `B_3`: the two elementary crossings and their genuine
inverses.  The inverses are NOT positive powers (unlike `Z/3`'s `s⁻¹ = s²`), so the group word problem needs
this enlarged alphabet. -/
inductive BraidSignedAtom where
  /-- The crossing `σ1`. -/
  | signedSigmaOne
  /-- The crossing `σ2`. -/
  | signedSigmaTwo
  /-- The inverse crossing `σ1⁻¹`. -/
  | signedSigmaOneInv
  /-- The inverse crossing `σ2⁻¹`. -/
  | signedSigmaTwoInv

/-- The **Garside element as a signed word**: `Δ = σ1σ2σ1`. -/
def braidSignedDeltaWord : List BraidSignedAtom :=
  [.signedSigmaOne, .signedSigmaTwo, .signedSigmaOne]

/-- The **explicit inverse word of the Garside element**: `Δ⁻¹ = σ1⁻¹σ2⁻¹σ1⁻¹` (the letterwise-reversed
inverse of `σ1σ2σ1`). -/
def braidSignedDeltaInverseWord : List BraidSignedAtom :=
  [.signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv]

/-! ## The signed convertibility -/

/-- ★ The **signed braid-group convertibility** of `B_3` on `List BraidSignedAtom`: the braid / Yang–Baxter
relation on the POSITIVE atoms plus the FOUR cancellation axioms (`σ1·σ1⁻¹ ≈ ε`, `σ1⁻¹·σ1 ≈ ε`, `σ2·σ2⁻¹ ≈ ε`,
`σ2⁻¹·σ2 ≈ ε`), each front-firing whiskered by an arbitrary suffix, closed under the generic
`consCongr` + `refl`/`symm`/`trans` into the full two-sided monoid congruence — exactly the house shape of the
positive `BraidThreeOneCellConv`, extended by the group cancellations.  Two signed words are equal in `B_3`
exactly when they are `BraidThreeSignedConv`-related. -/
inductive BraidThreeSignedConv : List BraidSignedAtom → List BraidSignedAtom → Prop where
  /-- The **braid / Yang–Baxter relation** `σ1σ2σ1 ≈ σ2σ1σ2` on the positive atoms, whiskered on the right by
  an arbitrary suffix. -/
  | braidRel (rest : List BraidSignedAtom) :
      BraidThreeSignedConv
        (.signedSigmaOne :: .signedSigmaTwo :: .signedSigmaOne :: rest)
        (.signedSigmaTwo :: .signedSigmaOne :: .signedSigmaTwo :: rest)
  /-- Cancellation `σ1·σ1⁻¹ ≈ ε`, whiskered. -/
  | cancelSigmaOne (rest : List BraidSignedAtom) :
      BraidThreeSignedConv (.signedSigmaOne :: .signedSigmaOneInv :: rest) rest
  /-- Cancellation `σ1⁻¹·σ1 ≈ ε`, whiskered. -/
  | cancelSigmaOneInv (rest : List BraidSignedAtom) :
      BraidThreeSignedConv (.signedSigmaOneInv :: .signedSigmaOne :: rest) rest
  /-- Cancellation `σ2·σ2⁻¹ ≈ ε`, whiskered. -/
  | cancelSigmaTwo (rest : List BraidSignedAtom) :
      BraidThreeSignedConv (.signedSigmaTwo :: .signedSigmaTwoInv :: rest) rest
  /-- Cancellation `σ2⁻¹·σ2 ≈ ε`, whiskered. -/
  | cancelSigmaTwoInv (rest : List BraidSignedAtom) :
      BraidThreeSignedConv (.signedSigmaTwoInv :: .signedSigmaTwo :: rest) rest
  /-- Congruence under an arbitrary leading signed atom. -/
  | consCongr {atom : BraidSignedAtom} {word1 word2 : List BraidSignedAtom} :
      BraidThreeSignedConv word1 word2 →
      BraidThreeSignedConv (atom :: word1) (atom :: word2)
  /-- Reflexivity. -/
  | refl (word : List BraidSignedAtom) : BraidThreeSignedConv word word
  /-- Symmetry. -/
  | symm {word1 word2 : List BraidSignedAtom} :
      BraidThreeSignedConv word1 word2 → BraidThreeSignedConv word2 word1
  /-- Transitivity. -/
  | trans {word1 word2 word3 : List BraidSignedAtom} :
      BraidThreeSignedConv word1 word2 → BraidThreeSignedConv word2 word3 →
      BraidThreeSignedConv word1 word3

/-! ## The Δ-cancellation chains (pure cancellation, no braid content) -/

/-- **`Δ⁻¹·Δ ≈ ε`** as words: `σ1⁻¹σ2⁻¹σ1⁻¹ · σ1σ2σ1 · R ≈ R` — three nested cancellations, innermost first.
The signed readback of a completed `Δ⁻¹`-shift meeting a `Δ`-power cancels through this chain (the soundness
leg of the `Δ⁻¹`-carry). -/
theorem braidSignedDeltaInvDeltaCancel (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv ::
        .signedSigmaOne :: .signedSigmaTwo :: .signedSigmaOne :: rest) rest :=
  BraidThreeSignedConv.trans
    (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
      (BraidThreeSignedConv.cancelSigmaOneInv (.signedSigmaTwo :: .signedSigmaOne :: rest))))
    (BraidThreeSignedConv.trans
      (BraidThreeSignedConv.consCongr
        (BraidThreeSignedConv.cancelSigmaTwoInv (.signedSigmaOne :: rest)))
      (BraidThreeSignedConv.cancelSigmaOneInv rest))

/-- **`Δ·Δ⁻¹ ≈ ε` on the SECOND representations**: `σ2σ1σ2 · σ2⁻¹σ1⁻¹σ2⁻¹ · R ≈ R` — the mirror cancellation
chain, the padding block of the inverse braid relation below. -/
theorem braidSignedDeltaSecondRepCancel (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaTwo :: .signedSigmaOne :: .signedSigmaTwo ::
        .signedSigmaTwoInv :: .signedSigmaOneInv :: .signedSigmaTwoInv :: rest) rest :=
  BraidThreeSignedConv.trans
    (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
      (BraidThreeSignedConv.cancelSigmaTwo (.signedSigmaOneInv :: .signedSigmaTwoInv :: rest))))
    (BraidThreeSignedConv.trans
      (BraidThreeSignedConv.consCongr
        (BraidThreeSignedConv.cancelSigmaOne (.signedSigmaTwoInv :: rest)))
      (BraidThreeSignedConv.cancelSigmaTwo rest))

/-! ## The inverse braid relation -/

/-- ★ The **inverse braid relation** `σ1⁻¹σ2⁻¹σ1⁻¹ · R ≈ σ2⁻¹σ1⁻¹σ2⁻¹ · R` — the braid move on the inverse
atoms, DERIVED (not asserted): pad the left side with the second-representation block `σ2σ1σ2·σ2⁻¹σ1⁻¹σ2⁻¹`
(reversed `braidSignedDeltaSecondRepCancel`), rewrite the padded middle `σ2σ1σ2 → σ1σ2σ1` by the positive
braid relation reversed, and collapse the leading `σ1⁻¹σ2⁻¹σ1⁻¹·σ1σ2σ1` block by
`braidSignedDeltaInvDeltaCancel`.  The two representations of `Δ⁻¹` coincide. -/
theorem braidSignedInverseBraidRel (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv :: rest)
      (.signedSigmaTwoInv :: .signedSigmaOneInv :: .signedSigmaTwoInv :: rest) :=
  BraidThreeSignedConv.trans
    (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
      (BraidThreeSignedConv.symm (braidSignedDeltaSecondRepCancel rest)))))
    (BraidThreeSignedConv.trans
      (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
        (BraidThreeSignedConv.symm (BraidThreeSignedConv.braidRel
          (.signedSigmaTwoInv :: .signedSigmaOneInv :: .signedSigmaTwoInv :: rest))))))
      (braidSignedDeltaInvDeltaCancel
        (.signedSigmaTwoInv :: .signedSigmaOneInv :: .signedSigmaTwoInv :: rest)))

/-! ## The Δ⁻¹-conjugation flips: pushing an atom through `Δ⁻¹` swaps it -/

/-- ★ **`σ1·Δ⁻¹·R ≈ Δ⁻¹·σ2·R`** — conjugating `σ1` through `Δ⁻¹` yields `σ2` (the signed mirror of the
shipped `braidThreeDeltaConjugateSigma1`, read through the inverse).  Left side: one cancellation
(`σ1·σ1⁻¹`); right side: the inverse braid relation plus one cancellation.  This is the per-level domino of
the negative-shift carry. -/
theorem braidSignedFlipDeltaInvSigmaOne (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaOne :: .signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv :: rest)
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv :: .signedSigmaTwo :: rest) :=
  BraidThreeSignedConv.trans
    (BraidThreeSignedConv.cancelSigmaOne (.signedSigmaTwoInv :: .signedSigmaOneInv :: rest))
    (BraidThreeSignedConv.symm
      (BraidThreeSignedConv.trans
        (braidSignedInverseBraidRel (.signedSigmaTwo :: rest))
        (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
          (BraidThreeSignedConv.cancelSigmaTwoInv rest)))))

/-- ★ **`σ2·Δ⁻¹·R ≈ Δ⁻¹·σ1·R`** — conjugating `σ2` through `Δ⁻¹` yields `σ1` (the mirror flip): rewrite
`Δ⁻¹` to its second representation, cancel `σ2·σ2⁻¹`, and un-cancel `σ1⁻¹·σ1` on the other side. -/
theorem braidSignedFlipDeltaInvSigmaTwo (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaTwo :: .signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv :: rest)
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv :: .signedSigmaOne :: rest) :=
  BraidThreeSignedConv.trans
    (BraidThreeSignedConv.trans
      (BraidThreeSignedConv.consCongr (braidSignedInverseBraidRel rest))
      (BraidThreeSignedConv.cancelSigmaTwo (.signedSigmaOneInv :: .signedSigmaTwoInv :: rest)))
    (BraidThreeSignedConv.symm
      (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
        (BraidThreeSignedConv.cancelSigmaOneInv rest))))

/-! ## The left-complement expansions: `σi⁻¹ = Δ⁻¹ · (left complement of σi)` -/

/-- ★ **`σ1⁻¹·R ≈ Δ⁻¹·(σ1σ2)·R`** — the left-complement identity for `σ1`: since `Δ = (σ1σ2)·σ1`, the
inverse atom is `σ1⁻¹ = Δ⁻¹·σ1σ2`.  DERIVED by two cancellations (right-to-left: `σ1⁻¹·σ1` then
`σ2⁻¹·σ2` collapse the expansion).  This is THE identity the signed normalizer uses: prepending `σ1⁻¹` is
one `Δ⁻¹`-shift plus the two POSITIVE prepends `σ2` then `σ1`. -/
theorem braidSignedInvExpandSigmaOne (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaOneInv :: rest)
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv ::
        .signedSigmaOne :: .signedSigmaTwo :: rest) :=
  BraidThreeSignedConv.symm
    (BraidThreeSignedConv.trans
      (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
        (BraidThreeSignedConv.cancelSigmaOneInv (.signedSigmaTwo :: rest))))
      (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.cancelSigmaTwoInv rest)))

/-- ★ **`σ2⁻¹·R ≈ Δ⁻¹·(σ2σ1)·R`** — the left-complement identity for `σ2`: since `Δ ≈ (σ2σ1)·σ2`, the
inverse atom is `σ2⁻¹ = Δ⁻¹·σ2σ1`.  DERIVED through the inverse braid relation (the `Δ⁻¹` must first move to
its second representation before the cancellations reach). -/
theorem braidSignedInvExpandSigmaTwo (rest : List BraidSignedAtom) :
    BraidThreeSignedConv
      (.signedSigmaTwoInv :: rest)
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv ::
        .signedSigmaTwo :: .signedSigmaOne :: rest) :=
  BraidThreeSignedConv.symm
    (BraidThreeSignedConv.trans
      (braidSignedInverseBraidRel (.signedSigmaTwo :: .signedSigmaOne :: rest))
      (BraidThreeSignedConv.trans
        (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
          (BraidThreeSignedConv.cancelSigmaTwoInv (.signedSigmaOne :: rest))))
        (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.cancelSigmaOneInv rest))))

/-! ## Non-vacuity smokes -/

/-- Smoke: the braid law holds on signed words (at the empty suffix). -/
theorem braidSignedLawHolds :
    BraidThreeSignedConv
      [.signedSigmaOne, .signedSigmaTwo, .signedSigmaOne]
      [.signedSigmaTwo, .signedSigmaOne, .signedSigmaTwo] :=
  BraidThreeSignedConv.braidRel []

/-- Smoke: `σ1·σ1⁻¹ ≈ ε` (at the empty suffix) — the first genuine GROUP cancellation of the lane. -/
theorem braidSignedCancelHolds :
    BraidThreeSignedConv [.signedSigmaOne, .signedSigmaOneInv] [] :=
  BraidThreeSignedConv.cancelSigmaOne []

/-- Smoke: `Δ⁻¹·Δ ≈ ε` as full words (the two three-letter blocks annihilate). -/
theorem braidSignedDeltaInvDeltaWordCancel :
    BraidThreeSignedConv
      [.signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv,
       .signedSigmaOne, .signedSigmaTwo, .signedSigmaOne] [] :=
  braidSignedDeltaInvDeltaCancel []

/-! ## Marker -/

/-- **ESTABLISHED.**  The SIGNED braid-group alphabet and relation of `B_3` are shipped, zero-axiom: the
four-atom carrier `BraidSignedAtom` over plain `List` words, the convertibility `BraidThreeSignedConv`
(braid relation + FOUR cancellations + generic congruence closure), and the derived toolkit — the
`Δ`-cancellation chains, the DERIVED inverse braid relation (`braidSignedInverseBraidRel`), the
`Δ⁻¹`-conjugation flips (`braidSignedFlipDeltaInvSigmaOne/Two`), and the left-complement expansions
`σi⁻¹ ≈ Δ⁻¹·(complement)` (`braidSignedInvExpandSigmaOne/Two`) — every identity a constructor chain from the
relation, none asserted.  Canon, normalizer, decision are bricks 2/3.  `= true`. -/
def fxBraid_hasSignedWordRelation : Bool := true

end FX1Poly.Polygraph
