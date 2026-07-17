import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedCanon

/-! # WalkingBraid/BraidThreeSignedGroupDecision — the FULL braid GROUP `B_3` word problem, DECIDED

The WP-BRAID ladder tops out: the word problem of the braid GROUP `B_3 = ⟨σ1, σ2 | σ1σ2σ1 = σ2σ1σ2⟩` on
ARBITRARY SIGNED words (crossings AND their inverses) is decided, zero-axiom, via the signed Garside normal
form `Δ^m · f1 · … · fk` (`m : ℤ` represented Int-free by the brick-2 constructor split):

  * **SOUNDNESS** (`braidSignedConv_toReadback`) — every signed word is convertible to the readback of its
    canon.  The positive domino transliterates the shipped `braidPrependAtom_readback_conv` onto signed
    lists (nine definitional arms + one `braidRel` at the base; one `braidRel` per `Δ`-level); the NEGATIVE
    domino inducts on the shift with the brick-1 `Δ⁻¹`-conjugation flips as the per-level move; the inverse
    atoms expand through the brick-1 left-complement identities and ride the positive domino twice; the
    `Δ⁻¹`-move's readback is definitional except where a `Δ⁻¹` meets a `Δ`-power — exactly the
    `braidSignedDeltaInvDeltaCancel` chain.
  * **COMPLETENESS** (`braidSignedNormalizeWord_congr_of_conv`) — convertible signed words have EQUAL canons,
    with every relation arm LEMMA-CLOSED: the braid arm is the signed braid-agreement
    (`braidSignedPrependPositiveAtom_braidAgreement` — the brick-2 COMMUTATION pushes the two triples
    through the `Δ⁻¹`-shifts, flipping `aba ↔ bab` per level, down to the SHIPPED greedy agreement); each
    of the FOUR cancellation arms collapses through the signed `Δ`-factorization
    (`braidSignedPrependPositiveAtom_deltaFactorization`: greedy triple-prepend = `Δ`-prepend, the brick-2
    positive engine lifted through the same commutation) followed by `Δ⁻¹ ∘ Δ = id`.
  * **THE TOTAL DECIDER** (`decideBraidThreeGroupConv`) — compare signed canons under the manual `decEq`;
    both branches load-bearing (equal canons ⟹ convertible via the readback round-trip; distinct canons ⟹
    not convertible via completeness).
  * **THE EMBEDDING AGREEMENT** (`decideBraidThreeGroupConv_agreesWithPositive`) — on embedded POSITIVE
    words the group decider and the shipped positive decider `decideBraidThreeConv` return the SAME verdict:
    the signed canon of an embedded positive word is exactly `nonNegativeDelta` of its positive canon
    (`braidSignedNormalizeWord_ofPositiveWord`), so the group extension is CONSERVATIVE over the shipped
    positive decision — `B_3^+ ↪ B_3` detects no new positive equalities (Garside's embedding theorem,
    machine-checked on the deciders).

## Honesty notes

`B_3` is an INFINITE, non-abelian GROUP — the first rung of the walking-zoo whose group inverses are NOT
positive powers (the finite-cyclic walkers' `s⁻¹ = s²` needs no new alphabet; here the signed alphabet is
essential).  The decision is at dimension 1 (the 2-signature of the walking braid is free on nothing, so
2-cell equality is 1-cell equality).  The ZOO-BRAIDED (Ξ@symmetric-affine parametricity) tie-in is NOT
claimed here — that is an Omega-side 2-cell PROP statement, not this 1-cell group decision.

## Propext-cleanliness

Both path inductions are plain list/`Nat` structural inductions (no mode index anywhere — the signed carrier
is a bare `List`); the embedding theorem inducts on the `ModalityPath` with BOTH mode indices variable (the
concrete-index trap never arises) and splits the ATOM value, not the generator.  All matches
full-enumeration; the decider agreement is a tactic double-`cases` on the two `Decidable` values.
Per-declaration `#assert_no_axioms` gated in the audit twin.  Free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## SOUNDNESS I: the positive domino on signed lists -/

/-- The **positive domino with power** — the shipped `braidPrependAtom_readback_conv` transliterated to the
signed list carrier: prepending a positive atom commutes with the non-negative readback up to
convertibility.  Induction on the `Δ`-power with atom and factors quantified (the atom flips per level);
base: ten-way case on `atom × head`, nine arms definitional on the cons-based readback, exactly one
(`σ2·σ1σ2 = Δ`) fires `braidRel` reversed; step: one `braidRel` pushes the atom through the leading `Δ`,
then the flipped inductive hypothesis fires under the three `Δ`-conses. -/
theorem braidSignedPositiveDominoWithPower (power : Nat) :
    ∀ (atom : BraidAtom) (factors : List BraidProperSimple),
      BraidThreeSignedConv
        (braidSignedAtomOfPositiveAtom atom
          :: braidSignedReadbackCanon (.nonNegativeDelta ⟨power, factors⟩))
        (braidSignedReadbackCanon
          (.nonNegativeDelta (braidPrependAtomWithPower atom power factors))) := by
  induction power with
  | zero =>
      intro atom factors
      cases atom with
      | atomSigmaOne =>
          cases factors with
          | nil => exact BraidThreeSignedConv.refl _
          | cons headFactor rest =>
              cases headFactor with
              | properSigmaOne => exact BraidThreeSignedConv.refl _
              | properSigmaTwo => exact BraidThreeSignedConv.refl _
              | properOneTwo => exact BraidThreeSignedConv.refl _
              | properTwoOne => exact BraidThreeSignedConv.refl _
      | atomSigmaTwo =>
          cases factors with
          | nil => exact BraidThreeSignedConv.refl _
          | cons headFactor rest =>
              cases headFactor with
              | properSigmaOne => exact BraidThreeSignedConv.refl _
              | properSigmaTwo => exact BraidThreeSignedConv.refl _
              | properOneTwo =>
                  exact BraidThreeSignedConv.symm
                    (BraidThreeSignedConv.braidRel (braidSignedReadbackFactors rest))
              | properTwoOne => exact BraidThreeSignedConv.refl _
  | succ predecessor inductiveHypothesis =>
      intro atom factors
      cases atom with
      | atomSigmaOne =>
          exact BraidThreeSignedConv.trans
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.braidRel
              (braidSignedDeltaPow predecessor (braidSignedReadbackFactors factors))))
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
              (BraidThreeSignedConv.consCongr
                (inductiveHypothesis BraidAtom.atomSigmaTwo factors))))
      | atomSigmaTwo =>
          exact BraidThreeSignedConv.trans
            (BraidThreeSignedConv.symm (BraidThreeSignedConv.braidRel
              (.signedSigmaOne :: braidSignedDeltaPow predecessor
                (braidSignedReadbackFactors factors))))
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
              (BraidThreeSignedConv.consCongr
                (inductiveHypothesis BraidAtom.atomSigmaOne factors))))

/-! ## SOUNDNESS II: the `Δ⁻¹`-move's readback -/

/-- The **`Δ⁻¹` domino** — prepending the explicit inverse triple `σ1⁻¹σ2⁻¹σ1⁻¹` commutes with readback up
to convertibility.  Two of the three arms are DEFINITIONAL (crossing into or deepening the negative side is
literally the readback's `Δ⁻¹`-triple); the one with content is `Δ⁻¹` meeting a positive `Δ`-power, where
the `braidSignedDeltaInvDeltaCancel` chain annihilates the adjacent triples. -/
theorem braidSignedDeltaInvDomino (canon : BraidSignedCanon) :
    BraidThreeSignedConv
      (.signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv ::
        braidSignedReadbackCanon canon)
      (braidSignedReadbackCanon (braidSignedPrependDeltaInv canon)) := by
  cases canon with
  | nonNegativeDelta positivePart =>
      cases positivePart with
      | mk power factors =>
          cases power with
          | zero => exact BraidThreeSignedConv.refl _
          | succ predecessor =>
              exact braidSignedDeltaInvDeltaCancel
                (braidSignedDeltaPow predecessor (braidSignedReadbackFactors factors))
  | negativeDelta shiftPredecessor properFactors => exact BraidThreeSignedConv.refl _

/-! ## SOUNDNESS III: the negative domino -/

/-- The **negative domino** — prepending a positive atom commutes with the NEGATIVE readback: per
`Δ⁻¹`-level, the brick-1 conjugation flip (`σ1·Δ⁻¹ ≈ Δ⁻¹·σ2`, `σ2·Δ⁻¹ ≈ Δ⁻¹·σ1`) pushes the atom inward
under the inverse triple; the base hands the flipped atom to the positive domino at power zero and closes
with the `Δ⁻¹` domino.  Induction on the shift with the atom quantified (it flips per level). -/
theorem braidSignedNegativeDomino :
    ∀ (shiftPredecessor : Nat) (atom : BraidAtom) (properFactors : List BraidProperSimple),
      BraidThreeSignedConv
        (braidSignedAtomOfPositiveAtom atom
          :: braidSignedReadbackCanon (.negativeDelta shiftPredecessor properFactors))
        (braidSignedReadbackCanon
          (braidSignedPrependPositiveAtomWithShift atom shiftPredecessor properFactors)) := by
  intro shiftPredecessor
  induction shiftPredecessor with
  | zero =>
      intro atom properFactors
      cases atom with
      | atomSigmaOne =>
          exact BraidThreeSignedConv.trans
            (braidSignedFlipDeltaInvSigmaOne (braidSignedReadbackFactors properFactors))
            (BraidThreeSignedConv.trans
              (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
                (BraidThreeSignedConv.consCongr
                  (braidSignedPositiveDominoWithPower 0 BraidAtom.atomSigmaTwo properFactors))))
              (braidSignedDeltaInvDomino
                (.nonNegativeDelta (braidPrependAtomToFactors BraidAtom.atomSigmaTwo properFactors))))
      | atomSigmaTwo =>
          exact BraidThreeSignedConv.trans
            (braidSignedFlipDeltaInvSigmaTwo (braidSignedReadbackFactors properFactors))
            (BraidThreeSignedConv.trans
              (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
                (BraidThreeSignedConv.consCongr
                  (braidSignedPositiveDominoWithPower 0 BraidAtom.atomSigmaOne properFactors))))
              (braidSignedDeltaInvDomino
                (.nonNegativeDelta (braidPrependAtomToFactors BraidAtom.atomSigmaOne properFactors))))
  | succ shiftPredecessorPred inductiveHypothesis =>
      intro atom properFactors
      cases atom with
      | atomSigmaOne =>
          exact BraidThreeSignedConv.trans
            (braidSignedFlipDeltaInvSigmaOne
              (braidSignedReadbackCanon (.negativeDelta shiftPredecessorPred properFactors)))
            (BraidThreeSignedConv.trans
              (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
                (BraidThreeSignedConv.consCongr
                  (inductiveHypothesis BraidAtom.atomSigmaTwo properFactors))))
              (braidSignedDeltaInvDomino
                (braidSignedPrependPositiveAtomWithShift BraidAtom.atomSigmaTwo
                  shiftPredecessorPred properFactors)))
      | atomSigmaTwo =>
          exact BraidThreeSignedConv.trans
            (braidSignedFlipDeltaInvSigmaTwo
              (braidSignedReadbackCanon (.negativeDelta shiftPredecessorPred properFactors)))
            (BraidThreeSignedConv.trans
              (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
                (BraidThreeSignedConv.consCongr
                  (inductiveHypothesis BraidAtom.atomSigmaOne properFactors))))
              (braidSignedDeltaInvDomino
                (braidSignedPrependPositiveAtomWithShift BraidAtom.atomSigmaOne
                  shiftPredecessorPred properFactors)))

/-! ## SOUNDNESS IV: assembly -/

/-- The **positive-atom domino** on every signed canon (non-negative side: the positive domino; negative
side: the negative domino). -/
theorem braidSignedPositiveAtomDomino (atom : BraidAtom) (canon : BraidSignedCanon) :
    BraidThreeSignedConv
      (braidSignedAtomOfPositiveAtom atom :: braidSignedReadbackCanon canon)
      (braidSignedReadbackCanon (braidSignedPrependPositiveAtom atom canon)) := by
  cases canon with
  | nonNegativeDelta positivePart =>
      cases positivePart with
      | mk power factors => exact braidSignedPositiveDominoWithPower power atom factors
  | negativeDelta shiftPredecessor properFactors =>
      exact braidSignedNegativeDomino shiftPredecessor atom properFactors

/-- ★ The **signed transducer domino** — prepending ANY signed atom commutes with readback up to
convertibility.  Positive atoms are the positive-atom domino; inverse atoms EXPAND through the brick-1
left-complement identity (`σi⁻¹ ≈ Δ⁻¹·complement`), ride the positive-atom domino twice (once per
complement letter), and close with the `Δ⁻¹` domino. -/
theorem braidSignedPrependAtom_readback_conv (signedAtom : BraidSignedAtom)
    (canon : BraidSignedCanon) :
    BraidThreeSignedConv
      (signedAtom :: braidSignedReadbackCanon canon)
      (braidSignedReadbackCanon (braidSignedPrependAtom signedAtom canon)) := by
  cases signedAtom with
  | signedSigmaOne => exact braidSignedPositiveAtomDomino BraidAtom.atomSigmaOne canon
  | signedSigmaTwo => exact braidSignedPositiveAtomDomino BraidAtom.atomSigmaTwo canon
  | signedSigmaOneInv =>
      exact BraidThreeSignedConv.trans
        (braidSignedInvExpandSigmaOne (braidSignedReadbackCanon canon))
        (BraidThreeSignedConv.trans
          (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
              (braidSignedPositiveAtomDomino BraidAtom.atomSigmaTwo canon)))))
          (BraidThreeSignedConv.trans
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
              (BraidThreeSignedConv.consCongr
                (braidSignedPositiveAtomDomino BraidAtom.atomSigmaOne
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon)))))
            (braidSignedDeltaInvDomino
              (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon)))))
  | signedSigmaTwoInv =>
      exact BraidThreeSignedConv.trans
        (braidSignedInvExpandSigmaTwo (braidSignedReadbackCanon canon))
        (BraidThreeSignedConv.trans
          (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
              (braidSignedPositiveAtomDomino BraidAtom.atomSigmaOne canon)))))
          (BraidThreeSignedConv.trans
            (BraidThreeSignedConv.consCongr (BraidThreeSignedConv.consCongr
              (BraidThreeSignedConv.consCongr
                (braidSignedPositiveAtomDomino BraidAtom.atomSigmaTwo
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon)))))
            (braidSignedDeltaInvDomino
              (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon)))))

/-- ★ **Soundness of the signed canonical form**: every signed word is convertible to the readback of its
canon (plain list induction — the signed carrier has no mode index, so the `Nat`-length-bound recipe of the
positive side is unnecessary here). -/
theorem braidSignedConv_toReadback (word : List BraidSignedAtom) :
    BraidThreeSignedConv word (braidSignedReadbackCanon (braidSignedNormalizeWord word)) := by
  induction word with
  | nil => exact BraidThreeSignedConv.refl []
  | cons atom rest inductiveHypothesis =>
      exact BraidThreeSignedConv.trans
        (BraidThreeSignedConv.consCongr inductiveHypothesis)
        (braidSignedPrependAtom_readback_conv atom (braidSignedNormalizeWord rest))

/-- ★ **Equal canons ⟹ convertible** (the YES direction): route both words through the common readback. -/
theorem braidSignedConv_of_normalizeWord_eq {word1 word2 : List BraidSignedAtom}
    (canonsEqual : braidSignedNormalizeWord word1 = braidSignedNormalizeWord word2) :
    BraidThreeSignedConv word1 word2 := by
  have reduceFirst :
      BraidThreeSignedConv word1 (braidSignedReadbackCanon (braidSignedNormalizeWord word2)) := by
    rw [← canonsEqual]
    exact braidSignedConv_toReadback word1
  exact BraidThreeSignedConv.trans reduceFirst
    (BraidThreeSignedConv.symm (braidSignedConv_toReadback word2))

/-! ## COMPLETENESS I: the signed braid-agreement -/

/-- The braid-agreement on the NON-NEGATIVE side — `congrArg` of the SHIPPED greedy agreement (the three
positive prepends never leave the non-negative constructor). -/
theorem braidSignedPrependPositiveAtom_braidAgreementNonNegative (positivePart : BraidGarsideCanon)
    (greedyFactors : braidIsLeftGreedy positivePart.properFactors = true) :
    braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
        BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
          (.nonNegativeDelta positivePart)))
      = braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom
          BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
            (.nonNegativeDelta positivePart))) := by
  cases positivePart with
  | mk power factors =>
      exact congrArg BraidSignedCanon.nonNegativeDelta
        (braidPrependAtom_braidAgreement power factors greedyFactors)

/-- The braid-agreement on the NEGATIVE side — induction on the shift: each level pushes all three prepends
through one `Δ⁻¹` via the brick-2 COMMUTATION (three rewrites per side, flipping `aba ↔ bab`), so the goal
reduces to the SWAPPED agreement one level down; the base lands on the non-negative agreement. -/
theorem braidSignedPrependPositiveAtom_braidAgreementNegative :
    ∀ (shiftPredecessor : Nat) (properFactors : List BraidProperSimple),
      braidIsLeftGreedy properFactors = true →
      braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
          BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
            (.negativeDelta shiftPredecessor properFactors)))
        = braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom
            BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
              (.negativeDelta shiftPredecessor properFactors))) := by
  intro shiftPredecessor
  induction shiftPredecessor with
  | zero =>
      intro properFactors greedyFactors
      have leftPush :
          braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
              BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependDeltaInv
                  (.nonNegativeDelta (BraidGarsideCanon.mk 0 properFactors)))))
            = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                    (.nonNegativeDelta (BraidGarsideCanon.mk 0 properFactors))))) := by
        rw [braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne]
      have rightPush :
          braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom
              BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependDeltaInv
                  (.nonNegativeDelta (BraidGarsideCanon.mk 0 properFactors)))))
            = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                    (.nonNegativeDelta (BraidGarsideCanon.mk 0 properFactors))))) := by
        rw [braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo]
      exact leftPush.trans
        ((congrArg braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtom_braidAgreementNonNegative
            (BraidGarsideCanon.mk 0 properFactors) greedyFactors).symm).trans
          rightPush.symm)
  | succ shiftPredecessorPred inductiveHypothesis =>
      intro properFactors greedyFactors
      have leftPush :
          braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
              BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependDeltaInv (.negativeDelta shiftPredecessorPred properFactors))))
            = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                    (.negativeDelta shiftPredecessorPred properFactors)))) := by
        rw [braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne]
      have rightPush :
          braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom
              BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependDeltaInv (.negativeDelta shiftPredecessorPred properFactors))))
            = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                    (.negativeDelta shiftPredecessorPred properFactors)))) := by
        rw [braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo]
      exact leftPush.trans
        ((congrArg braidSignedPrependDeltaInv
          (inductiveHypothesis properFactors greedyFactors).symm).trans
          rightPush.symm)

/-- ★ The **signed braid-agreement** — on left-greedy signed canons the two positive triple-prepends agree
as data: `P σ1 (P σ2 (P σ1 c)) = P σ2 (P σ1 (P σ2 c))`.  The completeness crux for the braid arm. -/
theorem braidSignedPrependPositiveAtom_braidAgreement (canon : BraidSignedCanon)
    (greedyFactors : braidIsLeftGreedy (braidSignedCanonFactors canon) = true) :
    braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
        BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon))
      = braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom
          BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon)) := by
  cases canon with
  | nonNegativeDelta positivePart =>
      exact braidSignedPrependPositiveAtom_braidAgreementNonNegative positivePart greedyFactors
  | negativeDelta shiftPredecessor properFactors =>
      exact braidSignedPrependPositiveAtom_braidAgreementNegative shiftPredecessor properFactors
        greedyFactors

/-! ## COMPLETENESS II: the signed Δ-factorization -/

/-- The signed `Δ`-factorization on the NEGATIVE side — induction on the shift with the same COMMUTATION
pushes; the swap back from `bab` to `aba` per level rides the signed braid-agreement, and the collapse
`Δ⁻¹ ∘ Δ = id` is the brick-2 inverse pair. -/
theorem braidSignedPrependPositiveAtom_deltaFactorizationNegative :
    ∀ (shiftPredecessor : Nat) (properFactors : List BraidProperSimple),
      braidIsLeftGreedy properFactors = true →
      braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
          BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
            (.negativeDelta shiftPredecessor properFactors)))
        = braidSignedPrependDelta (.negativeDelta shiftPredecessor properFactors) := by
  intro shiftPredecessor
  induction shiftPredecessor with
  | zero =>
      intro properFactors greedyFactors
      have leftPush :
          braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
              BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependDeltaInv
                  (.nonNegativeDelta (BraidGarsideCanon.mk 0 properFactors)))))
            = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                    (.nonNegativeDelta (BraidGarsideCanon.mk 0 properFactors))))) := by
        rw [braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne]
      exact leftPush.trans
        (congrArg braidSignedPrependDeltaInv
          (congrArg BraidSignedCanon.nonNegativeDelta
            (braidPrependAtom_deltaFactorizationSwapped 0 properFactors greedyFactors)))
  | succ shiftPredecessorPred inductiveHypothesis =>
      intro properFactors greedyFactors
      have leftPush :
          braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
              BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                (braidSignedPrependDeltaInv (.negativeDelta shiftPredecessorPred properFactors))))
            = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
                  (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
                    (.negativeDelta shiftPredecessorPred properFactors)))) := by
        rw [braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo,
            braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne]
      exact leftPush.trans
        ((congrArg braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtom_braidAgreementNegative shiftPredecessorPred
            properFactors greedyFactors).symm).trans
          ((congrArg braidSignedPrependDeltaInv
            (inductiveHypothesis properFactors greedyFactors)).trans
            (braidSignedPrependDeltaInv_prependDelta
              (.negativeDelta shiftPredecessorPred properFactors))))

/-- ★ The **signed `Δ`-factorization** — on a left-greedy signed canon the positive triple-prepend
`σ1∘σ2∘σ1` IS the `Δ`-prepend: `P σ1 (P σ2 (P σ1 c)) = Δ·c`.  The brick-2 positive engine lifted through
the commutation; the completeness crux for the cancellation arms. -/
theorem braidSignedPrependPositiveAtom_deltaFactorization (canon : BraidSignedCanon)
    (greedyFactors : braidIsLeftGreedy (braidSignedCanonFactors canon) = true) :
    braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom
        BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon))
      = braidSignedPrependDelta canon := by
  cases canon with
  | nonNegativeDelta positivePart =>
      cases positivePart with
      | mk power factors =>
          exact congrArg BraidSignedCanon.nonNegativeDelta
            (braidPrependAtom_deltaFactorization power factors greedyFactors)
  | negativeDelta shiftPredecessor properFactors =>
      exact braidSignedPrependPositiveAtom_deltaFactorizationNegative shiftPredecessor
        properFactors greedyFactors

/-- The signed `Δ`-factorization in the SWAPPED order `σ2∘σ1∘σ2` — via the signed braid-agreement. -/
theorem braidSignedPrependPositiveAtom_deltaFactorizationSwapped (canon : BraidSignedCanon)
    (greedyFactors : braidIsLeftGreedy (braidSignedCanonFactors canon) = true) :
    braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependPositiveAtom
        BraidAtom.atomSigmaOne (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon))
      = braidSignedPrependDelta canon :=
  (braidSignedPrependPositiveAtom_braidAgreement canon greedyFactors).symm.trans
    (braidSignedPrependPositiveAtom_deltaFactorization canon greedyFactors)

/-! ## COMPLETENESS III: the congruence -/

/-- ★ **Completeness of the signed canonical form**: convertible signed words have EQUAL canons, every arm
LEMMA-CLOSED.  `braidRel` is the signed braid-agreement at the tail's (greedy) canon; each of the FOUR
cancellation arms unfolds the inverse atom to `Δ⁻¹ ∘ P ∘ P`, pushes the outer positive prepend through the
`Δ⁻¹` where needed (the commutation), collapses the resulting triple by the signed `Δ`-factorization, and
finishes with `Δ⁻¹ ∘ Δ = id`; `consCongr` is `congrArg` of the transducer; `refl`/`symm`/`trans` are the
equivalence closure.  The NO direction of the decision. -/
theorem braidSignedNormalizeWord_congr_of_conv {word1 word2 : List BraidSignedAtom}
    (conv : BraidThreeSignedConv word1 word2) :
    braidSignedNormalizeWord word1 = braidSignedNormalizeWord word2 := by
  induction conv with
  | braidRel rest =>
      exact braidSignedPrependPositiveAtom_braidAgreement (braidSignedNormalizeWord rest)
        (braidSignedNormalizeWord_greedy rest)
  | cancelSigmaOne rest =>
      exact (braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne
          (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
            (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
              (braidSignedNormalizeWord rest)))).trans
        ((congrArg braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtom_deltaFactorizationSwapped
            (braidSignedNormalizeWord rest) (braidSignedNormalizeWord_greedy rest))).trans
          (braidSignedPrependDeltaInv_prependDelta (braidSignedNormalizeWord rest)))
  | cancelSigmaOneInv rest =>
      exact (congrArg braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtom_deltaFactorization
            (braidSignedNormalizeWord rest) (braidSignedNormalizeWord_greedy rest))).trans
        (braidSignedPrependDeltaInv_prependDelta (braidSignedNormalizeWord rest))
  | cancelSigmaTwo rest =>
      exact (braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo
          (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
            (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
              (braidSignedNormalizeWord rest)))).trans
        ((congrArg braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtom_deltaFactorization
            (braidSignedNormalizeWord rest) (braidSignedNormalizeWord_greedy rest))).trans
          (braidSignedPrependDeltaInv_prependDelta (braidSignedNormalizeWord rest)))
  | cancelSigmaTwoInv rest =>
      exact (congrArg braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtom_deltaFactorizationSwapped
            (braidSignedNormalizeWord rest) (braidSignedNormalizeWord_greedy rest))).trans
        (braidSignedPrependDeltaInv_prependDelta (braidSignedNormalizeWord rest))
  | @consCongr atom innerWordOne innerWordTwo _ innerInductiveHypothesis =>
      exact congrArg (braidSignedPrependAtom atom) innerInductiveHypothesis
  | refl _ => rfl
  | symm _ innerInductiveHypothesis => exact innerInductiveHypothesis.symm
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact firstInductiveHypothesis.trans secondInductiveHypothesis

/-! ## The TOTAL decision -/

/-- ★ **Decide the full `B_3` GROUP word problem** — TOTAL, on ARBITRARY signed words.  Compare the two
words' signed Garside canons under the manual `decEq`: equal canons ⟹ convertible (the soundness
round-trip); distinct canons ⟹ not convertible (completeness).  The first walking-zoo decision of an
INFINITE group whose inverses are not positive powers. -/
def decideBraidThreeGroupConv (word1 word2 : List BraidSignedAtom) :
    Decidable (BraidThreeSignedConv word1 word2) :=
  match braidSignedCanonDecEq (braidSignedNormalizeWord word1) (braidSignedNormalizeWord word2) with
  | isTrue canonsEqual => isTrue (braidSignedConv_of_normalizeWord_eq canonsEqual)
  | isFalse canonsDiffer =>
      isFalse (fun conv => canonsDiffer (braidSignedNormalizeWord_congr_of_conv conv))

/-- The signed convertibility as a `Decidable` instance (so `decide` fires on arbitrary signed pairs). -/
instance instDecidableBraidThreeSignedConv (word1 word2 : List BraidSignedAtom) :
    Decidable (BraidThreeSignedConv word1 word2) :=
  decideBraidThreeGroupConv word1 word2

/-! ## The positive embedding and the agreement theorem -/

/-- The **embedding of positive words** into signed words: each generator becomes its positive signed atom
(mode-generic fold, mirroring `braidNormalizeWord`'s shape — the σ-match lives in the shipped
`braidAtomOfGenerator`). -/
def braidSignedWordOfPositiveWord {sourceMode targetMode : BraidThreeMode}
    (word : ModalityPath braidThreeGraph sourceMode targetMode) : List BraidSignedAtom :=
  match word with
  | .nil _ => []
  | .cons generator rest =>
      braidSignedAtomOfPositiveAtom (braidAtomOfGenerator generator)
        :: braidSignedWordOfPositiveWord rest

/-- The embedding canon, length-generalized: the canon of an embedded positive word is `nonNegativeDelta`
of its positive canon.  The recursion is the propext-free `Nat`-length-bound recipe of the shipped
reconstruction (`braidConv_toReadback_ofLength`) — a bare `induction word` is blocked by the single-object
mode index. -/
theorem braidSignedNormalizeWord_ofPositiveWord_ofLength :
    ∀ (bound : Nat)
      (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point),
      word.length = bound →
      braidSignedNormalizeWord (braidSignedWordOfPositiveWord word)
        = .nonNegativeDelta (braidNormalizeWord word) := by
  intro bound
  induction bound with
  | zero =>
      intro word wordLengthEqZero
      match word with
      | .nil _ => rfl
      | .cons _ _ => exact absurd wordLengthEqZero (by intro isZero; cases isZero)
  | succ predecessor inductiveHypothesis =>
      intro word wordLengthEqSucc
      match word with
      | .nil _ => exact absurd wordLengthEqSucc (by intro isSucc; cases isSucc)
      | .cons .sigma1 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          show braidSignedPrependAtom BraidSignedAtom.signedSigmaOne
              (braidSignedNormalizeWord (braidSignedWordOfPositiveWord rest))
            = BraidSignedCanon.nonNegativeDelta
                (braidPrependAtom BraidAtom.atomSigmaOne (braidNormalizeWord rest))
          rw [inductiveHypothesis rest restLengthEqPredecessor]
          rfl
      | .cons .sigma2 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          show braidSignedPrependAtom BraidSignedAtom.signedSigmaTwo
              (braidSignedNormalizeWord (braidSignedWordOfPositiveWord rest))
            = BraidSignedCanon.nonNegativeDelta
                (braidPrependAtom BraidAtom.atomSigmaTwo (braidNormalizeWord rest))
          rw [inductiveHypothesis rest restLengthEqPredecessor]
          rfl

/-- ★ The **canon of an embedded positive word** is exactly `nonNegativeDelta` of its positive canon — the
signed normalizer NEVER leaves the non-negative side on positive input (the length-generalized recursion at
the word's own length). -/
theorem braidSignedNormalizeWord_ofPositiveWord
    (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    braidSignedNormalizeWord (braidSignedWordOfPositiveWord word)
      = .nonNegativeDelta (braidNormalizeWord word) :=
  braidSignedNormalizeWord_ofPositiveWord_ofLength word.length word rfl

/-- Positive-word transfer, signed ⟹ positive: a signed convertibility between embedded positive words
forces positive convertibility (signed completeness + the embedding canon + `nonNegativeDelta`-injectivity +
the shipped positive round-trip). -/
theorem braidThreeConv_ofSignedConvOnPositive
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (signedConv : BraidThreeSignedConv (braidSignedWordOfPositiveWord word1)
      (braidSignedWordOfPositiveWord word2)) :
    BraidThreeOneCellConv word1 word2 := by
  have signedCanonsEqual := braidSignedNormalizeWord_congr_of_conv signedConv
  rw [braidSignedNormalizeWord_ofPositiveWord, braidSignedNormalizeWord_ofPositiveWord]
    at signedCanonsEqual
  have positiveCanonsEqual : braidNormalizeWord word1 = braidNormalizeWord word2 := by
    injection signedCanonsEqual
  exact braidThreeConv_of_normalizeWord_eq positiveCanonsEqual

/-- Positive-word transfer, positive ⟹ signed: positive convertibility embeds (shipped positive
completeness + the embedding canon + the signed round-trip). -/
theorem braidSignedConv_ofPositiveConv
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (conv : BraidThreeOneCellConv word1 word2) :
    BraidThreeSignedConv (braidSignedWordOfPositiveWord word1)
      (braidSignedWordOfPositiveWord word2) := by
  apply braidSignedConv_of_normalizeWord_eq
  rw [braidSignedNormalizeWord_ofPositiveWord, braidSignedNormalizeWord_ofPositiveWord]
  exact congrArg BraidSignedCanon.nonNegativeDelta (braidNormalizeWord_congr_of_conv conv)

/-- ★ **THE EMBEDDING AGREEMENT**: on embedded positive words, the GROUP decider returns the SAME verdict
as the shipped POSITIVE decider `decideBraidThreeConv` — for every pair of positive words.  The group
extension is conservative over the positive monoid decision: `B_3^+ ↪ B_3` creates no new positive
equalities (Garside's embedding theorem, machine-checked at the decider level). -/
theorem decideBraidThreeGroupConv_agreesWithPositive
    (word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    @decide (BraidThreeSignedConv (braidSignedWordOfPositiveWord word1)
        (braidSignedWordOfPositiveWord word2))
      (decideBraidThreeGroupConv (braidSignedWordOfPositiveWord word1)
        (braidSignedWordOfPositiveWord word2))
      = @decide (BraidThreeOneCellConv word1 word2) (decideBraidThreeConv word1 word2) := by
  cases decideBraidThreeGroupConv (braidSignedWordOfPositiveWord word1)
      (braidSignedWordOfPositiveWord word2) with
  | isTrue signedHolds =>
      cases decideBraidThreeConv word1 word2 with
      | isTrue positiveHolds => rfl
      | isFalse positiveRefutes =>
          exact absurd (braidThreeConv_ofSignedConvOnPositive signedHolds) positiveRefutes
  | isFalse signedRefutes =>
      cases decideBraidThreeConv word1 word2 with
      | isTrue positiveHolds =>
          exact absurd (braidSignedConv_ofPositiveConv positiveHolds) signedRefutes
      | isFalse positiveRefutes => rfl

/-! ## Canon value smokes (all definitional) -/

/-- Canon smoke: `σ1·σ1⁻¹` normalizes to the EMPTY canon — the cancellation is invisible to the
normalizer. -/
theorem braidSignedNormalizeWord_sigmaOneCancelPair :
    braidSignedNormalizeWord [.signedSigmaOne, .signedSigmaOneInv]
      = .nonNegativeDelta ⟨0, []⟩ := rfl

/-- Canon smoke: `σ1⁻¹·σ1` normalizes to the EMPTY canon (the other cancellation order). -/
theorem braidSignedNormalizeWord_sigmaOneInvCancelPair :
    braidSignedNormalizeWord [.signedSigmaOneInv, .signedSigmaOne]
      = .nonNegativeDelta ⟨0, []⟩ := rfl

/-- Canon smoke: `Δ⁻²` as the doubled explicit inverse word normalizes to shift 2 (stored predecessor 1)
with an empty tail — the negative carry propagates through TWO `Δ⁻¹`-levels. -/
theorem braidSignedNormalizeWord_deltaInverseSquared :
    braidSignedNormalizeWord
      [.signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv,
       .signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv]
      = .negativeDelta 1 [] := rfl

/-- Non-vacuity of the YES direction as a TERM on a GENUINELY MIXED pair: the conjugation instance
`σ1⁻¹σ2σ1 ≈ σ2σ1σ2⁻¹` (the braid relation read as a conjugation), produced by the completeness round-trip
from the definitional canon equality (both canons are `Δ⁻¹·(σ1σ2)·(σ2σ1)`). -/
theorem braidSignedConv_conjugationPair :
    BraidThreeSignedConv
      [.signedSigmaOneInv, .signedSigmaTwo, .signedSigmaOne]
      [.signedSigmaTwo, .signedSigmaOne, .signedSigmaTwoInv] :=
  braidSignedConv_of_normalizeWord_eq rfl

/-! ## Decider fires — the group decider genuinely discriminates -/

/-- ★ Decider fire (positive): `decide` ACCEPTS `σ1·σ1⁻¹ ≟ ε`. -/
theorem braidSignedGroupDecide_true_on_sigmaOneCancel :
    decide (BraidThreeSignedConv [.signedSigmaOne, .signedSigmaOneInv] []) = true := rfl

/-- ★ Decider fire (positive): `decide` ACCEPTS `σ1⁻¹·σ1 ≟ ε`. -/
theorem braidSignedGroupDecide_true_on_sigmaOneInvCancel :
    decide (BraidThreeSignedConv [.signedSigmaOneInv, .signedSigmaOne] []) = true := rfl

/-- ★ Decider fire (positive): `decide` ACCEPTS `Δ·Δ⁻¹ ≟ ε` — the six-letter word `σ1σ2σ1·σ1⁻¹σ2⁻¹σ1⁻¹`
collapses to the identity. -/
theorem braidSignedGroupDecide_true_on_deltaTimesInverse :
    decide (BraidThreeSignedConv
      [.signedSigmaOne, .signedSigmaTwo, .signedSigmaOne,
       .signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv] []) = true := rfl

/-- ★ Decider fire (positive): `decide` ACCEPTS `Δ⁻¹·Δ ≟ ε` (the other annihilation order — the negative
shift meets the positive power). -/
theorem braidSignedGroupDecide_true_on_deltaInverseTimesDelta :
    decide (BraidThreeSignedConv
      [.signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv,
       .signedSigmaOne, .signedSigmaTwo, .signedSigmaOne] []) = true := rfl

/-- ★ Decider fire (positive, conjugation): `decide` ACCEPTS `σ1⁻¹σ2σ1 ≟ σ2σ1σ2⁻¹` — the braid relation
rearranged as a conjugation, undecidable by any positive-word engine (both sides carry inverse atoms). -/
theorem braidSignedGroupDecide_true_on_conjugation :
    decide (BraidThreeSignedConv
      [.signedSigmaOneInv, .signedSigmaTwo, .signedSigmaOne]
      [.signedSigmaTwo, .signedSigmaOne, .signedSigmaTwoInv]) = true := rfl

/-- ★ Decider fire (positive, mixed 5-atom): `decide` ACCEPTS `σ1·σ1⁻¹·σ2·σ2⁻¹·σ1 ≟ σ1` — two interleaved
cancellations inside a five-letter word. -/
theorem braidSignedGroupDecide_true_on_mixedFiveAtom :
    decide (BraidThreeSignedConv
      [.signedSigmaOne, .signedSigmaOneInv, .signedSigmaTwo, .signedSigmaTwoInv, .signedSigmaOne]
      [.signedSigmaOne]) = true := rfl

/-- ★ Decider fire (positive, deep negative shift): `decide` ACCEPTS `Δ⁻² ≟ (σ2⁻¹σ1⁻¹)³` — the inverse of
the classical `(σ1σ2)³ = Δ²` center identity, both normalizations crossing shift depth 2. -/
theorem braidSignedGroupDecide_true_on_deltaInverseSquared :
    decide (BraidThreeSignedConv
      [.signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv,
       .signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv]
      [.signedSigmaTwoInv, .signedSigmaOneInv, .signedSigmaTwoInv,
       .signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOneInv]) = true := rfl

/-- ★ Decider fire (NEGATIVE control): `decide` REJECTS `σ1 ≟ σ2`. -/
theorem braidSignedGroupDecide_false_on_atoms :
    decide (BraidThreeSignedConv [.signedSigmaOne] [.signedSigmaTwo]) = false := rfl

/-- ★ Decider fire (NEGATIVE control): `decide` REJECTS `σ1 ≟ σ1⁻¹` (a crossing is not its inverse — the
canons live on OPPOSITE sides of the sign split). -/
theorem braidSignedGroupDecide_false_on_atomVersusInverse :
    decide (BraidThreeSignedConv [.signedSigmaOne] [.signedSigmaOneInv]) = false := rfl

/-- ★ Decider fire (NEGATIVE control): `decide` REJECTS `σ1σ2 ≟ σ2⁻¹σ1⁻¹` — a positive word is NOT
convertible to its inverse word (only to the identity when multiplied against it). -/
theorem braidSignedGroupDecide_false_on_wordVersusInverse :
    decide (BraidThreeSignedConv
      [.signedSigmaOne, .signedSigmaTwo]
      [.signedSigmaTwoInv, .signedSigmaOneInv]) = false := rfl

/-- ★ Decider fire (NEGATIVE, mixed 5-atom): `decide` REJECTS `σ1σ2σ1⁻¹σ2⁻¹σ1 ≟ σ1` — the commutator
`σ1σ2σ1⁻¹σ2⁻¹` is NOT trivial in `B_3` (the braid relation is not commutativity). -/
theorem braidSignedGroupDecide_false_on_commutatorFiveAtom :
    decide (BraidThreeSignedConv
      [.signedSigmaOne, .signedSigmaTwo, .signedSigmaOneInv, .signedSigmaTwoInv, .signedSigmaOne]
      [.signedSigmaOne]) = false := rfl

/-- Cross-check fire: on the embedded braid pair `σ1σ2σ1 ≟ σ2σ1σ2` the group decider accepts — one concrete
instance of the general `decideBraidThreeGroupConv_agreesWithPositive`. -/
theorem braidSignedGroupDecide_true_on_embeddedBraidPair :
    decide (BraidThreeSignedConv
      (braidSignedWordOfPositiveWord braidThreeBraidLeft)
      (braidSignedWordOfPositiveWord braidThreeBraidRight)) = true := rfl

/-! ## `#eval` decide pins (elaboration-time cross-fire of the compiled decider) -/

#eval decide (BraidThreeSignedConv [.signedSigmaOne, .signedSigmaOneInv] [])
#eval decide (BraidThreeSignedConv
  [.signedSigmaOneInv, .signedSigmaTwo, .signedSigmaOne]
  [.signedSigmaTwo, .signedSigmaOne, .signedSigmaTwoInv])
#eval decide (BraidThreeSignedConv [.signedSigmaOne] [.signedSigmaOneInv])
#eval decide (BraidThreeSignedConv
  [.signedSigmaOne, .signedSigmaTwo] [.signedSigmaTwoInv, .signedSigmaOneInv])

/-! ## Marker -/

/-- **ESTABLISHED.**  The FULL word problem of the braid GROUP `B_3` on ARBITRARY SIGNED words is DECIDED,
zero-axiom and non-vacuously, via the signed Garside normal form `Δ^m · f1 · … · fk` (`m : ℤ` Int-free):
SOUNDNESS (`braidSignedConv_toReadback` — positive/negative/`Δ⁻¹` dominoes over the brick-1 conjugation
flips and left-complement expansions), COMPLETENESS (`braidSignedNormalizeWord_congr_of_conv` — braid arm by
the signed braid-agreement through the COMMUTATION, all FOUR cancellation arms by the signed
`Δ`-factorization + `Δ⁻¹∘Δ = id`, every arm lemma-closed), the total decider `decideBraidThreeGroupConv`
(fires: both cancellation orders, `Δ·Δ⁻¹` and `Δ⁻¹·Δ`, the conjugation `σ1⁻¹σ2σ1 ≟ σ2σ1σ2⁻¹`, the mixed
five-atom pair, `Δ⁻² ≟ (σ2⁻¹σ1⁻¹)³`; rejects `σ1 ≟ σ2`, `σ1 ≟ σ1⁻¹`, word-vs-inverse, and the nontrivial
commutator), and THE EMBEDDING AGREEMENT (`decideBraidThreeGroupConv_agreesWithPositive`: on embedded
positive words the group decider coincides with the shipped `decideBraidThreeConv` — the conservative
`B_3^+ ↪ B_3` at decider level).  Honest scope: `B_3` is an INFINITE non-abelian GROUP at dimension 1 — the
first walking-zoo group rung whose inverses are NOT positive powers, so the signed alphabet is essential;
the ZOO-BRAIDED parametricity tie-in is NOT claimed (that is an Omega 2-cell PROP statement, a different
rung).  `= true`. -/
def fxBraid_hasBraidGroupDecided : Bool := true

end FX1Poly.Polygraph
