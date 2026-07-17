import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedWord

/-! # WalkingBraid/BraidThreeSignedCanon — the SIGNED Garside canonical form + carrying transducer (`B_3`, brick 2)

The canonical-form layer of the `B_3` GROUP word problem: every group element is uniquely `Δ^m · f1 · … · fk`
with `m : ℤ` and the `fi` a left-greedy tail of proper simples.  The integer power is represented INT-FREE
(the `Int.add_comm` propext hazard never enters) by a two-constructor inductive with the min-normalization
invariant STRUCTURAL:

  * **The carrier** `BraidSignedCanon` — `nonNegativeDelta positivePart` reuses the shipped positive canon
    `BraidGarsideCanon` verbatim (`Δ^k · F`, `k ≥ 0`), and `negativeDelta shiftPredecessor properFactors`
    is `Δ^-(shiftPredecessor+1) · F` — the negative constructor stores the PREDECESSOR of the shift and has
    NO positive `Δ`-power field at all, so the junk state "both a negative shift and a positive `Δ`-power"
    is unrepresentable by construction (no invariant, no normalization pass).  A greedy proper tail is never
    left-divisible by `Δ` (a would-be `Δ`-completion is exactly an illegal handoff), so nothing hides in the
    factor list either.
  * **The two primitive moves** — `braidSignedPrependDeltaInv` / `braidSignedPrependDelta` (left-multiply by
    `Δ∓1`): three-arm reindexings that are mutually inverse (`braidSignedPrependDeltaInv_prependDelta`,
    `braidSignedPrependDelta_prependDeltaInv`) and never touch the factors
    (`braidSignedCanonFactors_prependDeltaInv`).
  * **The positive-atom carry** `braidSignedPrependPositiveAtom` — on the non-negative side it IS the shipped
    `braidPrependAtom`; on the negative side `a·Δ^-(s+1)·F = Δ⁻¹·τ(a)·Δ^-s·F` recurses STRUCTURALLY on the
    bare shift `Nat` (`braidSignedPrependPositiveAtomWithShift`), flipping the atom per `Δ⁻¹`-level exactly
    like the shipped positive power carry (the `rfl` tripwire
    `braidSignedPrependPositiveAtomWithShift_succ` pins the definitional reduction).
  * **THE COMMUTATION** (`braidSignedPrependPositiveAtom_prependDeltaInv_comm`): `P_a ∘ Δ⁻¹ = Δ⁻¹ ∘ P_τ(a)`
    AS DATA on every canon, no invariant needed — the single lemma that lets brick 3 push any positive-triple
    through the `Δ⁻¹`-shifts down to the SHIPPED greedy machinery.
  * **The signed transducer + normalizer** — `braidSignedPrependAtom` prepends `σi` directly and `σi⁻¹` via
    the brick-1 left-complement identity (`σi⁻¹ = Δ⁻¹ · complement`: two positive prepends then one
    `Δ⁻¹`-shift); `braidSignedNormalizeWord` folds it over the plain list word.
  * **The greedy invariant** — the factor list of every normalizer output is left-greedy
    (`braidSignedNormalizeWord_greedy`), because every primitive preserves greediness (the `Δ`-moves don't
    touch factors, the positive carry rides the shipped preservation lemmas).
  * **The `Δ`-factorization of the positive layer** (`braidPrependAtom_deltaFactorization`): on a GREEDY
    canon, the positive triple-prepend `σ1∘σ2∘σ1` IS the `Δ`-power bump — `P σ1 (P σ2 (P σ1 ⟨p, F⟩)) =
    ⟨p+1, F⟩`.  New content about the SHIPPED transducer (the shipped braid-agreement says the two triples
    agree; this pins their common VALUE), the engine that closes all four cancellation arms in brick 3.
  * **The signed readback** — cons-only (`List.append` never appears): factor words, `Δ`-powers as positive
    triples, `Δ⁻¹`-powers as explicit `σ1⁻¹σ2⁻¹σ1⁻¹` triples.

## Propext-cleanliness

All matches full-enumeration; the canon `decEq` is manual (constructor split + componentwise, `noConfusion` /
`injection` on the cross arms); the shift carry is structural on a bare `Nat`; readback is cons-only.
Per-declaration `#assert_no_axioms` gated in the audit twin.  Free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The signed canonical-form carrier -/

/-- ★ The **signed Garside canonical form** of a `B_3` group element: `Δ^m · f1 · … · fk` with `m : ℤ`,
represented INT-FREE by constructor split on the sign.  `nonNegativeDelta ⟨k, F⟩` is `Δ^k · F` (`k ≥ 0`,
the shipped positive canon reused verbatim); `negativeDelta s F` is `Δ^-(s+1) · F` (the stored `Nat` is the
shift's PREDECESSOR, so the shift is always `≥ 1`).  The min-normalization invariant — never both a negative
shift and a positive `Δ`-power — is STRUCTURAL: the negative constructor has no positive power field.  Junk
unrepresentable, no `Int`, no normalization pass. -/
inductive BraidSignedCanon where
  /-- `Δ^k · F` for `k ≥ 0` — the shipped positive canon embedded verbatim. -/
  | nonNegativeDelta (positivePart : BraidGarsideCanon)
  /-- `Δ^-(shiftPredecessor+1) · F` — a strictly negative `Δ`-power over a proper-simple tail. -/
  | negativeDelta (shiftPredecessor : Nat) (properFactors : List BraidProperSimple)

/-- Decidable equality of signed canons — MANUAL constructor split: same-constructor arms go componentwise
through the shipped `braidGarsideCanonDecEq` / `Nat.decEq` / `braidProperFactorsDecEq`, cross arms are
`noConfusion`.  Propext-free (the polymorphic `decEq` derivation is never touched). -/
def braidSignedCanonDecEq :
    (firstCanon secondCanon : BraidSignedCanon) → Decidable (firstCanon = secondCanon)
  | .nonNegativeDelta firstPositive, .nonNegativeDelta secondPositive =>
      match braidGarsideCanonDecEq firstPositive secondPositive with
      | isTrue positivesEqual =>
          isTrue (congrArg BraidSignedCanon.nonNegativeDelta positivesEqual)
      | isFalse positivesDiffer =>
          isFalse (fun canonsEqual => by
            injection canonsEqual with positivesEqual
            exact positivesDiffer positivesEqual)
  | .nonNegativeDelta _, .negativeDelta _ _ =>
      isFalse (fun canonsEqual => BraidSignedCanon.noConfusion canonsEqual)
  | .negativeDelta _ _, .nonNegativeDelta _ =>
      isFalse (fun canonsEqual => BraidSignedCanon.noConfusion canonsEqual)
  | .negativeDelta firstShift firstFactors, .negativeDelta secondShift secondFactors =>
      match Nat.decEq firstShift secondShift, braidProperFactorsDecEq firstFactors secondFactors with
      | isTrue shiftsEqual, isTrue factorsEqual =>
          isTrue (by subst shiftsEqual; subst factorsEqual; rfl)
      | isFalse shiftsDiffer, _ =>
          isFalse (fun canonsEqual => by
            injection canonsEqual with shiftsEqual _factorsEqual
            exact shiftsDiffer shiftsEqual)
      | _, isFalse factorsDiffer =>
          isFalse (fun canonsEqual => by
            injection canonsEqual with _shiftsEqual factorsEqual
            exact factorsDiffer factorsEqual)

/-- The signed canons have decidable equality. -/
instance instDecidableEqBraidSignedCanon : DecidableEq BraidSignedCanon := braidSignedCanonDecEq

/-- The **factor list** of a signed canon (either constructor's proper-simple tail) — the carrier of the
left-greedy invariant. -/
def braidSignedCanonFactors : BraidSignedCanon → List BraidProperSimple
  | .nonNegativeDelta positivePart => positivePart.properFactors
  | .negativeDelta _ properFactors => properFactors

/-! ## The two primitive Δ-moves -/

/-- **Left-multiply by `Δ⁻¹`** — the three-arm reindexing: decrement a positive power, or (at power zero)
cross into the negative side, or deepen a negative shift.  Never touches the factors. -/
def braidSignedPrependDeltaInv : BraidSignedCanon → BraidSignedCanon
  | .nonNegativeDelta ⟨0, properFactors⟩ => .negativeDelta 0 properFactors
  | .nonNegativeDelta ⟨power + 1, properFactors⟩ => .nonNegativeDelta ⟨power, properFactors⟩
  | .negativeDelta shiftPredecessor properFactors =>
      .negativeDelta (shiftPredecessor + 1) properFactors

/-- **Left-multiply by `Δ`** — the inverse reindexing: bump a positive power, or shallow a negative shift,
or (at shift one) cross into the non-negative side. -/
def braidSignedPrependDelta : BraidSignedCanon → BraidSignedCanon
  | .nonNegativeDelta positivePart => .nonNegativeDelta (braidSuccDelta positivePart)
  | .negativeDelta 0 properFactors => .nonNegativeDelta ⟨0, properFactors⟩
  | .negativeDelta (shiftPredecessor + 1) properFactors =>
      .negativeDelta shiftPredecessor properFactors

/-- The two `Δ`-moves are mutually inverse, `Δ⁻¹ ∘ Δ = id` — the min-normalization carrier genuinely
represents the integers: no drift at the sign crossing. -/
theorem braidSignedPrependDeltaInv_prependDelta (canon : BraidSignedCanon) :
    braidSignedPrependDeltaInv (braidSignedPrependDelta canon) = canon := by
  cases canon with
  | nonNegativeDelta positivePart => cases positivePart with | mk power factors => rfl
  | negativeDelta shiftPredecessor properFactors =>
      cases shiftPredecessor with
      | zero => rfl
      | succ shiftPredecessorPred => rfl

/-- The two `Δ`-moves are mutually inverse, `Δ ∘ Δ⁻¹ = id`. -/
theorem braidSignedPrependDelta_prependDeltaInv (canon : BraidSignedCanon) :
    braidSignedPrependDelta (braidSignedPrependDeltaInv canon) = canon := by
  cases canon with
  | nonNegativeDelta positivePart =>
      cases positivePart with
      | mk power factors =>
          cases power with
          | zero => rfl
          | succ predecessor => rfl
  | negativeDelta shiftPredecessor properFactors => rfl

/-- The `Δ⁻¹`-move never touches the factor list — the greedy invariant rides through for free. -/
theorem braidSignedCanonFactors_prependDeltaInv (canon : BraidSignedCanon) :
    braidSignedCanonFactors (braidSignedPrependDeltaInv canon) = braidSignedCanonFactors canon := by
  cases canon with
  | nonNegativeDelta positivePart =>
      cases positivePart with
      | mk power factors =>
          cases power with
          | zero => rfl
          | succ predecessor => rfl
  | negativeDelta shiftPredecessor properFactors => rfl

/-! ## The positive-atom carry -/

/-- The **negative-shift carry**: prepend a positive atom to `Δ^-(shiftPredecessor+1) · F` by peeling one
`Δ⁻¹`-level at a time — `a·Δ^-(s+2)·F = Δ⁻¹·(τ(a)·Δ^-(s+1)·F)` recursively, landing at
`a·Δ⁻¹·F = Δ⁻¹·τ(a)·F` with the flipped atom handed to the SHIPPED carry table.  STRUCTURAL recursion on the
bare shift `Nat` (a recursion through the canon constructor would fall to `WellFounded.fix`; the `rfl`
tripwire below pins the definitional reduction), the exact `braidPrependAtomWithPower` recipe mirrored to
the negative side. -/
def braidSignedPrependPositiveAtomWithShift :
    BraidAtom → Nat → List BraidProperSimple → BraidSignedCanon
  | atom, 0, properFactors =>
      braidSignedPrependDeltaInv
        (.nonNegativeDelta (braidPrependAtomToFactors (braidFlipAtom atom) properFactors))
  | atom, shiftPredecessor + 1, properFactors =>
      braidSignedPrependDeltaInv
        (braidSignedPrependPositiveAtomWithShift (braidFlipAtom atom) shiftPredecessor properFactors)

/-- Definitional-reduction tripwire (the `WellFounded.fix` sentinel): peeling one `Δ⁻¹`-level off the shift
carry flips the atom and re-wraps in `Δ⁻¹` — BY `rfl`, which would fail if the carry compiled to
`WellFounded.fix`. -/
theorem braidSignedPrependPositiveAtomWithShift_succ (atom : BraidAtom) (shiftPredecessor : Nat)
    (properFactors : List BraidProperSimple) :
    braidSignedPrependPositiveAtomWithShift atom (shiftPredecessor + 1) properFactors
      = braidSignedPrependDeltaInv
          (braidSignedPrependPositiveAtomWithShift (braidFlipAtom atom) shiftPredecessor properFactors) :=
  rfl

/-- ★ **Prepend a positive atom** to a signed canon: on the non-negative side this IS the shipped
`braidPrependAtom`; on the negative side it is the shift carry. -/
def braidSignedPrependPositiveAtom (atom : BraidAtom) : BraidSignedCanon → BraidSignedCanon
  | .nonNegativeDelta positivePart => .nonNegativeDelta (braidPrependAtom atom positivePart)
  | .negativeDelta shiftPredecessor properFactors =>
      braidSignedPrependPositiveAtomWithShift atom shiftPredecessor properFactors

/-! ## THE COMMUTATION: `P_a ∘ Δ⁻¹ = Δ⁻¹ ∘ P_τ(a)` as data -/

/-- ★ **The commutation** — prepending a positive atom past a `Δ⁻¹`-shift flips the atom:
`P_a (Δ⁻¹ · c) = Δ⁻¹ · P_τ(a) (c)` AS DATA on EVERY canon (no greedy hypothesis).  Case split on the canon
(with a power split on the non-negative side and an atom split for `τ∘τ = id`); each arm is `rfl` — the
shipped positive power carry and the negative shift carry are built from the same flip, so the two routes
compute identically.  This is the single lemma that lets the completeness bricks push any positive-prepend
composite through the `Δ⁻¹`-shifts down to the SHIPPED left-greedy machinery. -/
theorem braidSignedPrependPositiveAtom_prependDeltaInv_comm (atom : BraidAtom)
    (canon : BraidSignedCanon) :
    braidSignedPrependPositiveAtom atom (braidSignedPrependDeltaInv canon)
      = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom (braidFlipAtom atom) canon) := by
  cases canon with
  | nonNegativeDelta positivePart =>
      cases positivePart with
      | mk power factors =>
          cases power with
          | zero => rfl
          | succ predecessor =>
              cases atom with
              | atomSigmaOne => rfl
              | atomSigmaTwo => rfl
  | negativeDelta shiftPredecessor properFactors => rfl

/-- The commutation, `σ1`-specialized with the flip EVALUATED (`τ(σ1) = σ2`) — the syntactic rewrite form
the completeness pushes fire. -/
theorem braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne (canon : BraidSignedCanon) :
    braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne (braidSignedPrependDeltaInv canon)
      = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon) :=
  braidSignedPrependPositiveAtom_prependDeltaInv_comm BraidAtom.atomSigmaOne canon

/-- The commutation, `σ2`-specialized with the flip EVALUATED (`τ(σ2) = σ1`). -/
theorem braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo (canon : BraidSignedCanon) :
    braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo (braidSignedPrependDeltaInv canon)
      = braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon) :=
  braidSignedPrependPositiveAtom_prependDeltaInv_comm BraidAtom.atomSigmaTwo canon

/-! ## The signed transducer and normalizer -/

/-- ★ The **signed carrying transducer** — prepend one signed atom to a signed canon.  Positive atoms carry
directly; inverse atoms ride the brick-1 left-complement identity `σi⁻¹ = Δ⁻¹ · (complement of σi)`:
`σ1⁻¹ = Δ⁻¹·σ1σ2` prepends `σ2` then `σ1` (positive!) then shifts by `Δ⁻¹`; `σ2⁻¹ = Δ⁻¹·σ2σ1` mirrors.  The
inverse atoms thus REUSE the shipped positive carry — the only genuinely new move is the `Δ⁻¹` reindexing. -/
def braidSignedPrependAtom : BraidSignedAtom → BraidSignedCanon → BraidSignedCanon
  | .signedSigmaOne, canon => braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon
  | .signedSigmaTwo, canon => braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon
  | .signedSigmaOneInv, canon =>
      braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
        (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon))
  | .signedSigmaTwoInv, canon =>
      braidSignedPrependDeltaInv (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
        (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon))

/-- ★ The **signed normalizer** — fold the signed transducer over the word (plain structural recursion on
the list; every defining equation is definitional). -/
def braidSignedNormalizeWord : List BraidSignedAtom → BraidSignedCanon
  | [] => .nonNegativeDelta ⟨0, []⟩
  | atom :: rest => braidSignedPrependAtom atom (braidSignedNormalizeWord rest)

/-- The defining equation on `[]`. -/
theorem braidSignedNormalizeWord_nil :
    braidSignedNormalizeWord [] = .nonNegativeDelta ⟨0, []⟩ := rfl

/-- The defining equation on `cons` — definitional. -/
theorem braidSignedNormalizeWord_cons (atom : BraidSignedAtom) (rest : List BraidSignedAtom) :
    braidSignedNormalizeWord (atom :: rest)
      = braidSignedPrependAtom atom (braidSignedNormalizeWord rest) := rfl

/-! ## The greedy invariant rides through every signed move -/

/-- The negative-shift carry preserves left-greediness — each level only flips the atom and reindexes the
`Δ`-power, so everything reduces to the SHIPPED carry-table preservation. -/
theorem braidSignedPrependPositiveAtomWithShift_preservesGreedy :
    ∀ (shiftPredecessor : Nat) (atom : BraidAtom) (properFactors : List BraidProperSimple),
      braidIsLeftGreedy properFactors = true →
      braidIsLeftGreedy (braidSignedCanonFactors
        (braidSignedPrependPositiveAtomWithShift atom shiftPredecessor properFactors)) = true := by
  intro shiftPredecessor
  induction shiftPredecessor with
  | zero =>
      intro atom properFactors greedyFactors
      show braidIsLeftGreedy (braidSignedCanonFactors (braidSignedPrependDeltaInv
        (.nonNegativeDelta (braidPrependAtomToFactors (braidFlipAtom atom) properFactors)))) = true
      rw [braidSignedCanonFactors_prependDeltaInv]
      exact braidPrependAtomToFactors_preservesGreedy (braidFlipAtom atom) properFactors greedyFactors
  | succ shiftPredecessorPred inductiveHypothesis =>
      intro atom properFactors greedyFactors
      show braidIsLeftGreedy (braidSignedCanonFactors (braidSignedPrependDeltaInv
        (braidSignedPrependPositiveAtomWithShift (braidFlipAtom atom) shiftPredecessorPred
          properFactors))) = true
      rw [braidSignedCanonFactors_prependDeltaInv]
      exact inductiveHypothesis (braidFlipAtom atom) properFactors greedyFactors

/-- The positive-atom prepend preserves left-greediness on every signed canon. -/
theorem braidSignedPrependPositiveAtom_preservesGreedy (atom : BraidAtom) (canon : BraidSignedCanon)
    (greedyCanon : braidIsLeftGreedy (braidSignedCanonFactors canon) = true) :
    braidIsLeftGreedy (braidSignedCanonFactors (braidSignedPrependPositiveAtom atom canon)) = true := by
  cases canon with
  | nonNegativeDelta positivePart =>
      exact braidPrependAtomWithPower_preservesGreedy positivePart.deltaPower atom
        positivePart.properFactors greedyCanon
  | negativeDelta shiftPredecessor properFactors =>
      exact braidSignedPrependPositiveAtomWithShift_preservesGreedy shiftPredecessor atom
        properFactors greedyCanon

/-- The full signed transducer preserves left-greediness (the inverse atoms compose the positive
preservation with the factor-transparent `Δ⁻¹`-move). -/
theorem braidSignedPrependAtom_preservesGreedy (signedAtom : BraidSignedAtom)
    (canon : BraidSignedCanon)
    (greedyCanon : braidIsLeftGreedy (braidSignedCanonFactors canon) = true) :
    braidIsLeftGreedy (braidSignedCanonFactors (braidSignedPrependAtom signedAtom canon)) = true := by
  cases signedAtom with
  | signedSigmaOne =>
      exact braidSignedPrependPositiveAtom_preservesGreedy BraidAtom.atomSigmaOne canon greedyCanon
  | signedSigmaTwo =>
      exact braidSignedPrependPositiveAtom_preservesGreedy BraidAtom.atomSigmaTwo canon greedyCanon
  | signedSigmaOneInv =>
      show braidIsLeftGreedy (braidSignedCanonFactors (braidSignedPrependDeltaInv
        (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne
          (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo canon)))) = true
      rw [braidSignedCanonFactors_prependDeltaInv]
      exact braidSignedPrependPositiveAtom_preservesGreedy BraidAtom.atomSigmaOne _
        (braidSignedPrependPositiveAtom_preservesGreedy BraidAtom.atomSigmaTwo canon greedyCanon)
  | signedSigmaTwoInv =>
      show braidIsLeftGreedy (braidSignedCanonFactors (braidSignedPrependDeltaInv
        (braidSignedPrependPositiveAtom BraidAtom.atomSigmaTwo
          (braidSignedPrependPositiveAtom BraidAtom.atomSigmaOne canon)))) = true
      rw [braidSignedCanonFactors_prependDeltaInv]
      exact braidSignedPrependPositiveAtom_preservesGreedy BraidAtom.atomSigmaTwo _
        (braidSignedPrependPositiveAtom_preservesGreedy BraidAtom.atomSigmaOne canon greedyCanon)

/-- ★ The **signed normalizer's invariant**: every canon it produces has a left-greedy factor list. -/
theorem braidSignedNormalizeWord_greedy (word : List BraidSignedAtom) :
    braidIsLeftGreedy (braidSignedCanonFactors (braidSignedNormalizeWord word)) = true := by
  induction word with
  | nil => rfl
  | cons atom rest inductiveHypothesis =>
      exact braidSignedPrependAtom_preservesGreedy atom (braidSignedNormalizeWord rest)
        inductiveHypothesis

/-! ## The Δ-factorization of the SHIPPED positive transducer -/

/-- ★ **The `Δ`-factorization**: on a left-greedy canon, the positive triple-prepend `σ1∘σ2∘σ1` IS the
`Δ`-power bump — `P σ1 (P σ2 (P σ1 ⟨power, factors⟩)) = ⟨power+1, factors⟩`.  NEW content about the shipped
transducer: the shipped `braidPrependAtom_braidAgreement` says the two braid-triples AGREE on greedy canons;
this lemma pins their common VALUE as exactly one `Δ`.  Induction on the power (the step pushes the three
prepends through `braidSuccDelta`, flipping `aba ↔ bab`, then swaps back via the shipped agreement); the base
is a finite leaf split on the first factor (with a second-factor split where the carry absorbs a `Δ`) —
every legal leaf closes by `rfl`, every illegal leaf by `Bool.noConfusion` on the reduced greedy
hypothesis.  This is the engine that closes all four CANCELLATION arms of the brick-3 completeness:
`σi⁻¹·σi`-collapse is `Δ⁻¹ · (Δ-bump) = id`. -/
theorem braidPrependAtom_deltaFactorization (power : Nat) :
    ∀ (factors : List BraidProperSimple), braidIsLeftGreedy factors = true →
      braidPrependAtom BraidAtom.atomSigmaOne (braidPrependAtom BraidAtom.atomSigmaTwo
          (braidPrependAtom BraidAtom.atomSigmaOne ⟨power, factors⟩))
        = ⟨power + 1, factors⟩ := by
  induction power with
  | zero =>
      intro factors greedyFactors
      cases factors with
      | nil => rfl
      | cons headFactor rest =>
          cases headFactor with
          | properSigmaOne => rfl
          | properSigmaTwo =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact Bool.noConfusion greedyFactors
                  | properSigmaTwo => rfl
                  | properOneTwo => exact Bool.noConfusion greedyFactors
                  | properTwoOne => rfl
          | properOneTwo => rfl
          | properTwoOne =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => rfl
                  | properSigmaTwo => exact Bool.noConfusion greedyFactors
                  | properOneTwo => rfl
                  | properTwoOne => exact Bool.noConfusion greedyFactors
  | succ predecessor inductiveHypothesis =>
      intro factors greedyFactors
      show braidSuccDelta (braidPrependAtom BraidAtom.atomSigmaTwo
          (braidPrependAtom BraidAtom.atomSigmaOne
            (braidPrependAtom BraidAtom.atomSigmaTwo ⟨predecessor, factors⟩)))
        = ⟨predecessor + 1 + 1, factors⟩
      exact congrArg braidSuccDelta
        ((braidPrependAtom_braidAgreement predecessor factors greedyFactors).symm.trans
          (inductiveHypothesis factors greedyFactors))

/-- The `Δ`-factorization in the SWAPPED order `σ2∘σ1∘σ2` — via the shipped agreement. -/
theorem braidPrependAtom_deltaFactorizationSwapped (power : Nat) (factors : List BraidProperSimple)
    (greedyFactors : braidIsLeftGreedy factors = true) :
    braidPrependAtom BraidAtom.atomSigmaTwo (braidPrependAtom BraidAtom.atomSigmaOne
        (braidPrependAtom BraidAtom.atomSigmaTwo ⟨power, factors⟩))
      = ⟨power + 1, factors⟩ :=
  (braidPrependAtom_braidAgreement power factors greedyFactors).symm.trans
    (braidPrependAtom_deltaFactorization power factors greedyFactors)

/-! ## The signed readback (cons-only) -/

/-- The signed atom of a positive atom (the alphabet embedding). -/
def braidSignedAtomOfPositiveAtom : BraidAtom → BraidSignedAtom
  | .atomSigmaOne => .signedSigmaOne
  | .atomSigmaTwo => .signedSigmaTwo

/-- Prepend one proper-simple factor's word onto a tail (cons-only; `List.append` never appears — the
difference-list recipe). -/
def braidSignedFactorWordOnto : BraidProperSimple → List BraidSignedAtom → List BraidSignedAtom
  | .properSigmaOne, tail => .signedSigmaOne :: tail
  | .properSigmaTwo, tail => .signedSigmaTwo :: tail
  | .properOneTwo, tail => .signedSigmaOne :: .signedSigmaTwo :: tail
  | .properTwoOne, tail => .signedSigmaTwo :: .signedSigmaOne :: tail

/-- The signed word of a factor list. -/
def braidSignedReadbackFactors : List BraidProperSimple → List BraidSignedAtom
  | [] => []
  | factor :: remainingFactors =>
      braidSignedFactorWordOnto factor (braidSignedReadbackFactors remainingFactors)

/-- Prepend `Δ^power` (each level the positive triple `σ1σ2σ1`) onto a tail. -/
def braidSignedDeltaPow : Nat → List BraidSignedAtom → List BraidSignedAtom
  | 0, tail => tail
  | power + 1, tail =>
      .signedSigmaOne :: .signedSigmaTwo :: .signedSigmaOne :: braidSignedDeltaPow power tail

/-- Prepend `Δ^-shift` (each level the EXPLICIT inverse triple `σ1⁻¹σ2⁻¹σ1⁻¹`) onto a tail. -/
def braidSignedDeltaInvPow : Nat → List BraidSignedAtom → List BraidSignedAtom
  | 0, tail => tail
  | shift + 1, tail =>
      .signedSigmaOneInv :: .signedSigmaTwoInv :: .signedSigmaOneInv ::
        braidSignedDeltaInvPow shift tail

/-- ★ The **signed readback** of a canon: `Δ^k · f1 · … · fm` on the non-negative side,
`Δ^-(s+1) · f1 · … · fm` with the explicit `σ1⁻¹σ2⁻¹σ1⁻¹` inverse triples on the negative side. -/
def braidSignedReadbackCanon : BraidSignedCanon → List BraidSignedAtom
  | .nonNegativeDelta positivePart =>
      braidSignedDeltaPow positivePart.deltaPower
        (braidSignedReadbackFactors positivePart.properFactors)
  | .negativeDelta shiftPredecessor properFactors =>
      braidSignedDeltaInvPow (shiftPredecessor + 1) (braidSignedReadbackFactors properFactors)

/-- Readback smoke: `Δ¹` reads back to the positive `Δ`-word. -/
theorem braidSignedReadbackCanon_deltaOne :
    braidSignedReadbackCanon (.nonNegativeDelta ⟨1, []⟩) = braidSignedDeltaWord := rfl

/-- Readback smoke: `Δ⁻¹` reads back to the EXPLICIT inverse word `σ1⁻¹σ2⁻¹σ1⁻¹`. -/
theorem braidSignedReadbackCanon_deltaInvOne :
    braidSignedReadbackCanon (.negativeDelta 0 []) = braidSignedDeltaInverseWord := rfl

/-! ## Canon value smokes (all definitional) -/

/-- Canon smoke: the empty word normalizes to the empty canon. -/
theorem braidSignedNormalizeWord_emptyWord :
    braidSignedNormalizeWord [] = .nonNegativeDelta ⟨0, []⟩ := rfl

/-- Canon smoke: `σ1⁻¹` normalizes to `Δ⁻¹·(σ1σ2)` — the left-complement identity REALIZED by the
transducer (the brick-1 `braidSignedInvExpandSigmaOne` as data). -/
theorem braidSignedNormalizeWord_sigmaOneInv :
    braidSignedNormalizeWord [.signedSigmaOneInv]
      = .negativeDelta 0 [BraidProperSimple.properOneTwo] := rfl

/-- Canon smoke: `σ2⁻¹` normalizes to `Δ⁻¹·(σ2σ1)` — the mirror complement. -/
theorem braidSignedNormalizeWord_sigmaTwoInv :
    braidSignedNormalizeWord [.signedSigmaTwoInv]
      = .negativeDelta 0 [BraidProperSimple.properTwoOne] := rfl

/-- Canon smoke: the explicit inverse word `σ1⁻¹σ2⁻¹σ1⁻¹` normalizes to `Δ⁻¹` with an EMPTY tail — the
three complements chain into exactly one negative shift. -/
theorem braidSignedNormalizeWord_deltaInverseWord :
    braidSignedNormalizeWord braidSignedDeltaInverseWord = .negativeDelta 0 [] := rfl

/-- Canon smoke: the positive `Δ`-word normalizes to `Δ¹` (the shipped positive behavior, reproduced by the
signed transducer through the embedding arms). -/
theorem braidSignedNormalizeWord_deltaWord :
    braidSignedNormalizeWord braidSignedDeltaWord = .nonNegativeDelta ⟨1, []⟩ := rfl

/-! ## Marker -/

/-- **ESTABLISHED.**  The SIGNED Garside canonical form of the `B_3` group is shipped, zero-axiom and
Int-free: the two-constructor carrier `BraidSignedCanon` (min-normalization STRUCTURAL — the negative
constructor stores the shift's predecessor and has no positive power field, junk unrepresentable), manual
`decEq`, the mutually-inverse `Δ`-moves, the positive-atom carry with the STRUCTURAL negative-shift
recursion, THE COMMUTATION `P_a ∘ Δ⁻¹ = Δ⁻¹ ∘ P_τ(a)` as data
(`braidSignedPrependPositiveAtom_prependDeltaInv_comm`), the signed transducer riding the brick-1
left-complement identities, the total normalizer with its left-greedy invariant
(`braidSignedNormalizeWord_greedy`), the `Δ`-factorization of the shipped positive transducer
(`braidPrependAtom_deltaFactorization`: greedy triple-prepend = `Δ`-bump), and the cons-only signed
readback.  Soundness/completeness/decision are brick 3.  `= true`. -/
def fxBraid_hasSignedGarsideCanon : Bool := true

end FX1Poly.Polygraph
