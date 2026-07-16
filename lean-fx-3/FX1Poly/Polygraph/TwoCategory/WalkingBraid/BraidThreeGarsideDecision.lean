import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeGarside

/-! # WalkingBraid/BraidThreeGarsideDecision — the FULL `B_3^+` word problem, DECIDED (left-greedy Garside NF)

The WP-BRAID-3 wall comes down: the word problem of the positive braid monoid `B_3^+ = ⟨σ1, σ2 | σ1σ2σ1 =
σ2σ1σ2⟩` on ARBITRARY words is decided, zero-axiom, via the left-greedy Garside normal form.  The complete
model is the canonical form `Δ^k · f1 · … · fm` — a Δ-power plus a left-greedy sequence of PROPER simple
elements (the four divisors of Δ strictly between `1` and `Δ`: `σ1, σ2, σ1σ2, σ2σ1`) — computed by a
rightward-carrying transducer `braidPrependAtom : BraidAtom → BraidGarsideCanon → BraidGarsideCanon` folded
over the word:

  * **The carry table** (`braidPrependAtomToFactors`, ten full-enumeration arms) — prepending an atom to the
    factor list either CONSES a new head factor, MERGES with the head into a longer simple (`σ1·σ2 = σ1σ2`,
    `σ2·σ1 = σ2σ1`), or completes the head to `Δ` (`σ1·σ2σ1 = Δ = σ2·σ1σ2`) and ABSORBS it into the Δ-power.
  * **The Δ-power carry** (`braidPrependAtomWithPower`, STRUCTURAL recursion on a bare `Nat`) — pushing an
    atom through `Δ^k` flips it at each level (`a·Δ = Δ·τ(a)` with `τ(σ1) = σ2, τ(σ2) = σ1`, the shipped
    Δ-conjugations `braidThreeDeltaConjugateSigma1/Sigma2`), the "domino" carry.
  * **SOUNDNESS** (`braidConv_toReadback`) — every word is convertible to the readback of its canonical form;
    each carry move is discharged as a braid-relation convertibility: nine of the ten table arms are
    DEFINITIONAL on the cons-based readback, exactly one (`σ2·σ1σ2 = Δ`) fires `braidRel`, and each Δ-level of
    the power carry fires `braidRel` once — the move-by-move bubble/domino assembly the wall named.
  * **COMPLETENESS** (`braidNormalizeWord_congr_of_conv`) — convertible words have EQUAL canonical form.  The
    crux: the triple-prepend composites `P σ1 ∘ P σ2 ∘ P σ1` and `P σ2 ∘ P σ1 ∘ P σ2` do NOT agree on raw
    canons (counterexample: `⟨0, [σ1, σ2]⟩`, an ILLEGAL non-greedy state, separates them as data), but they DO
    agree on LEFT-GREEDY canons (`braidPrependAtom_braidAgreement`), and the normalizer only ever produces
    those (`braidNormalizeWord_greedy`, via `braidPrependAtomToFactors_preservesGreedy`).  Left-greediness for
    `B_3` degenerates to a finite handoff table: the finishing atom of each factor must equal the starting atom
    of the next (`braidHandoffAllows`).
  * **THE TOTAL DECIDER** (`decideBraidThreeConv`) — compare canonical forms under the manual
    `braidGarsideCanonDecEq`; both branches are load-bearing (equal canons ⟹ convertible via the readback
    round-trip `braidThreeConv_of_normalizeWord_eq`, distinct canons ⟹ not convertible via completeness).

## Why this defeats the two named obstructions

The braid relation is LENGTH-PRESERVING, so no monotone word-length measure exists: the reconstruction inducts
on word STRUCTURE (through the propext-free `Nat`-length-bound recipe of `convWhiskerLeftOfLength`), with the
carry as an inner structural recursion on the Δ-power.  `B_3^+` is INFINITE (`σ1^k` all distinct), so the
model is a canonical form on words, not a finite-group residue — the `(Nat × List BraidProperSimple)` carrier
is exactly that form, and junk states (identity or Δ mid-list) are UNREPRESENTABLE by construction, so the
left-greedy invariant is needed only as a hypothesis of one lemma, never inside the decider.

## Propext-cleanliness

The normalizer fold is MODE-GENERIC exactly like `braidThreePermutationOf` (the generator is matched in
`braidAtomOfGenerator`, never inside the fold), so its `cons` equation is definitional.  Both path inductions
(`braidConv_toReadback_ofLength`, `braidNormalizeWord_greedy_ofLength`) recurse on a plain `Nat` length bound
with the word destructured in a TACTIC match.  The Δ-power carry is structural on a bare `Nat` argument (a
structure-field recursion would fall to `WellFounded.fix`; the `rfl` smoke `braidPrependAtom_succDelta` pins
this).  All matches are full-enumeration; list equality is a MONOMORPHIC per-carrier `decEq`; the illegal
handoff refutations reduce `false && x` definitionally and close by `Bool.noConfusion`.  Per-declaration
`#assert_no_axioms` gated in the audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The atoms and the proper simple elements -/

/-- The two **atoms** of `B_3^+` — the generators `σ1`, `σ2` as a bare two-element carrier (the alphabet of
the carrying transducer, decoupled from the mode-indexed `BraidThreeModality`). -/
inductive BraidAtom where
  /-- The atom `σ1`. -/
  | atomSigmaOne
  /-- The atom `σ2`. -/
  | atomSigmaTwo

/-- The **Δ-conjugation flip** `τ` on atoms: `τ(σ1) = σ2`, `τ(σ2) = σ1`.  Pushing an atom rightward through
one `Δ` flips it (`a·Δ = Δ·τ(a)`, the shipped `braidThreeDeltaConjugateSigma1/Sigma2` read right-to-left). -/
def braidFlipAtom : BraidAtom → BraidAtom
  | .atomSigmaOne => .atomSigmaTwo
  | .atomSigmaTwo => .atomSigmaOne

/-- The atom of a generating modality — the index-refining match lives HERE, not in the normalizer fold
(exactly the `applyGen` recipe of `braidThreePermutationOf`: the fold stays a non-index-refining structural
recursion, and its `cons` equation stays definitional). -/
def braidAtomOfGenerator {sourceMode middleMode : BraidThreeMode}
    (generator : BraidThreeModality sourceMode middleMode) : BraidAtom :=
  match generator with
  | .sigma1 => .atomSigmaOne
  | .sigma2 => .atomSigmaTwo

/-- Prepend an atom to a word as a leading `cons` (the word-side action of the transducer's input letter). -/
def braidConsAtom (atom : BraidAtom)
    (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  match atom with
  | .atomSigmaOne => ModalityPath.cons BraidThreeModality.sigma1 word
  | .atomSigmaTwo => ModalityPath.cons BraidThreeModality.sigma2 word

/-- The four **proper simple elements** of `B_3^+` — the divisors of the Garside element `Δ = σ1σ2σ1` strictly
between `1` and `Δ`: the atoms `σ1`, `σ2` and the two-letter simples `σ1σ2`, `σ2σ1`.  These are the admissible
FACTORS of the canonical form's tail; the identity and `Δ` are deliberately NOT representable as factors (the
identity is the empty list, Δ-factors live in the `deltaPower` field), so the junk states that would break
canonicity (`[] ≠ [identity]`, a `Δ` after a non-`Δ` factor) are unrepresentable by construction. -/
inductive BraidProperSimple where
  /-- The atom factor `σ1`. -/
  | properSigmaOne
  /-- The atom factor `σ2`. -/
  | properSigmaTwo
  /-- The two-letter factor `σ1σ2`. -/
  | properOneTwo
  /-- The two-letter factor `σ2σ1`. -/
  | properTwoOne

/-- Decidable equality of proper simples — a MANUAL full-enumeration `decEq` (sixteen cases: four
`isTrue rfl`, twelve `isFalse` via `noConfusion`), propext-free.  Copies the `threeIdxDecEq` pattern. -/
def braidProperSimpleDecEq :
    (firstFactor secondFactor : BraidProperSimple) → Decidable (firstFactor = secondFactor)
  | .properSigmaOne, .properSigmaOne => isTrue rfl
  | .properSigmaTwo, .properSigmaTwo => isTrue rfl
  | .properOneTwo, .properOneTwo => isTrue rfl
  | .properTwoOne, .properTwoOne => isTrue rfl
  | .properSigmaOne, .properSigmaTwo => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properSigmaOne, .properOneTwo => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properSigmaOne, .properTwoOne => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properSigmaTwo, .properSigmaOne => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properSigmaTwo, .properOneTwo => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properSigmaTwo, .properTwoOne => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properOneTwo, .properSigmaOne => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properOneTwo, .properSigmaTwo => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properOneTwo, .properTwoOne => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properTwoOne, .properSigmaOne => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properTwoOne, .properSigmaTwo => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)
  | .properTwoOne, .properOneTwo => isFalse (fun factorsEqual => BraidProperSimple.noConfusion factorsEqual)

/-- The proper simples have decidable equality. -/
instance instDecidableEqBraidProperSimple : DecidableEq BraidProperSimple := braidProperSimpleDecEq

/-- Decidable equality of proper-simple factor LISTS — a MONOMORPHIC recursive list `decEq` (a polymorphic
recursive list-equality lemma would pull `propext` through the match compiler; the per-carrier copy stays
clean).  Cons-only: no `List.append` appears anywhere in this file. -/
def braidProperFactorsDecEq :
    (firstFactors secondFactors : List BraidProperSimple) → Decidable (firstFactors = secondFactors)
  | [], [] => isTrue rfl
  | [], _secondHead :: _secondTail =>
      isFalse (fun listsEqual => by injection listsEqual)
  | _firstHead :: _firstTail, [] =>
      isFalse (fun listsEqual => by injection listsEqual)
  | firstHead :: firstTail, secondHead :: secondTail =>
      match braidProperSimpleDecEq firstHead secondHead,
            braidProperFactorsDecEq firstTail secondTail with
      | isTrue headsEqual, isTrue tailsEqual =>
          isTrue (by subst headsEqual; subst tailsEqual; rfl)
      | isFalse headsDiffer, _ =>
          isFalse (fun listsEqual => by
            injection listsEqual with headsEqual _tailsEqual
            exact headsDiffer headsEqual)
      | _, isFalse tailsDiffer =>
          isFalse (fun listsEqual => by
            injection listsEqual with _headsEqual tailsEqual
            exact tailsDiffer tailsEqual)

/-! ## The canonical-form carrier -/

/-- ★ The **Garside canonical form** of a positive `B_3^+` word: `Δ^deltaPower · f1 · f2 · … · fm` with the
`fi` PROPER simples.  In any left-weighted normal form the `Δ` factors cluster at the FRONT (a `Δ` after a
non-`Δ` factor violates left-weightedness, since `Δ`'s starting set is both atoms), so the `Nat` power loses
nothing; and with proper simples as the only representable factors, canonicity junk is unrepresentable.  Words
are equal in `B_3^+` iff their canons are EQUAL AS DATA (`braidNormalizeWord_congr_of_conv` +
`braidThreeConv_of_normalizeWord_eq`). -/
structure BraidGarsideCanon where
  /-- The exponent of the leading Garside-element power `Δ^k`. -/
  deltaPower : Nat
  /-- The left-greedy tail of proper simple factors. -/
  properFactors : List BraidProperSimple

/-- Bump the Δ-power by one, keeping the factors (the canon-side image of a completed `Δ` carry). -/
def braidSuccDelta (canon : BraidGarsideCanon) : BraidGarsideCanon :=
  ⟨canon.deltaPower + 1, canon.properFactors⟩

/-- Decidable equality of canons — componentwise from `Nat.decEq` and the monomorphic factor-list `decEq`
(equality by double `subst`, inequality via `congrArg` of the field projections; the audited `symThreeDecEq`
shape). -/
def braidGarsideCanonDecEq :
    (firstCanon secondCanon : BraidGarsideCanon) → Decidable (firstCanon = secondCanon)
  | ⟨firstPower, firstFactors⟩, ⟨secondPower, secondFactors⟩ =>
      match Nat.decEq firstPower secondPower,
            braidProperFactorsDecEq firstFactors secondFactors with
      | isTrue powersEqual, isTrue factorsEqual =>
          isTrue (by subst powersEqual; subst factorsEqual; rfl)
      | isFalse powersDiffer, _ =>
          isFalse (fun canonsEqual => powersDiffer (congrArg BraidGarsideCanon.deltaPower canonsEqual))
      | _, isFalse factorsDiffer =>
          isFalse (fun canonsEqual => factorsDiffer (congrArg BraidGarsideCanon.properFactors canonsEqual))

/-- The canons have decidable equality. -/
instance instDecidableEqBraidGarsideCanon : DecidableEq BraidGarsideCanon := braidGarsideCanonDecEq

/-! ## The carrying transducer: prepend one atom to a canon -/

/-- ★ The **carry table** — prepend an atom to the FACTOR LIST (the `Δ^0` case), by full enumeration on
`atom × head`: either CONS a new head factor (`σ1·σ1…`, `σ1·σ1σ2…`, `σ2·σ2…`, `σ2·σ2σ1…` — the products are
not simple), MERGE with the head into a longer simple (`σ1·σ2 = σ1σ2`, `σ2·σ1 = σ2σ1`), or complete the head
to `Δ` and ABSORB it into the power (`σ1·σ2σ1 = Δ`, `σ2·σ1σ2 = Δ`).  Ten arms, non-recursive. -/
def braidPrependAtomToFactors : BraidAtom → List BraidProperSimple → BraidGarsideCanon
  | .atomSigmaOne, [] => ⟨0, [.properSigmaOne]⟩
  | .atomSigmaOne, .properSigmaOne :: rest => ⟨0, .properSigmaOne :: .properSigmaOne :: rest⟩
  | .atomSigmaOne, .properSigmaTwo :: rest => ⟨0, .properOneTwo :: rest⟩
  | .atomSigmaOne, .properOneTwo :: rest => ⟨0, .properSigmaOne :: .properOneTwo :: rest⟩
  | .atomSigmaOne, .properTwoOne :: rest => ⟨1, rest⟩
  | .atomSigmaTwo, [] => ⟨0, [.properSigmaTwo]⟩
  | .atomSigmaTwo, .properSigmaOne :: rest => ⟨0, .properTwoOne :: rest⟩
  | .atomSigmaTwo, .properSigmaTwo :: rest => ⟨0, .properSigmaTwo :: .properSigmaTwo :: rest⟩
  | .atomSigmaTwo, .properOneTwo :: rest => ⟨1, rest⟩
  | .atomSigmaTwo, .properTwoOne :: rest => ⟨0, .properSigmaTwo :: .properTwoOne :: rest⟩

/-- ★ The **Δ-power carry** — prepend an atom to `Δ^power · factors` by pushing it through the power, FLIPPING
at each level (`a·Δ^(k+1)·F = Δ·(τ(a)·Δ^k·F)`), landing in the carry table at level zero.  STRUCTURAL
recursion on the bare `Nat` power (a recursion on a structure FIELD would fall to `WellFounded.fix` and stop
reducing; the `rfl` smoke `braidPrependAtom_succDelta` pins the definitional reduction). -/
def braidPrependAtomWithPower : BraidAtom → Nat → List BraidProperSimple → BraidGarsideCanon
  | atom, 0, factors => braidPrependAtomToFactors atom factors
  | atom, power + 1, factors => braidSuccDelta (braidPrependAtomWithPower (braidFlipAtom atom) power factors)

/-- ★ The **carrying transducer** `prependGen : Generator → Canon → Canon` of the WP-BRAID-3 wall statement —
prepend one atom to a canonical form. -/
def braidPrependAtom (atom : BraidAtom) (canon : BraidGarsideCanon) : BraidGarsideCanon :=
  braidPrependAtomWithPower atom canon.deltaPower canon.properFactors

/-- Definitional-reduction smoke (the `WellFounded.fix` tripwire): prepending past a bumped power flips the
atom and bumps outside — BY `rfl`, which would fail if the power carry compiled to `WellFounded.fix`. -/
theorem braidPrependAtom_succDelta (atom : BraidAtom) (canon : BraidGarsideCanon) :
    braidPrependAtom atom (braidSuccDelta canon)
      = braidSuccDelta (braidPrependAtom (braidFlipAtom atom) canon) := rfl

/-! ## The normalizer: fold the transducer over the word -/

/-- ★ The **normalizer** `normalizeWord : Word → Canon` — fold the carrying transducer over the word:
`nil ↦ ⟨0, []⟩`, and each leading generator prepends its atom to the tail's canon.  MODE-GENERIC exactly like
`braidThreePermutationOf` (the `cons` match binds the generator WITHOUT refining the modality index; the
σ-match lives in `braidAtomOfGenerator`), so the defining equations reduce DEFINITIONALLY. -/
def braidNormalizeWord {sourceMode targetMode : BraidThreeMode}
    (word : ModalityPath braidThreeGraph sourceMode targetMode) : BraidGarsideCanon :=
  match word with
  | .nil _ => ⟨0, []⟩
  | .cons generator rest => braidPrependAtom (braidAtomOfGenerator generator) (braidNormalizeWord rest)

/-- The defining equation on `nil` — the empty word normalizes to the empty canon. -/
theorem braidNormalizeWord_nil : braidNormalizeWord braidThreeNil = ⟨0, []⟩ := rfl

/-- The GENERIC `cons` equation — for either leading generator, prepending it carries its atom onto the tail's
canon.  Holds DEFINITIONALLY (the payoff of the mode-generic fold). -/
theorem braidNormalizeWord_cons
    (generator : BraidThreeModality BraidThreeMode.point BraidThreeMode.point)
    (rest : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    braidNormalizeWord (ModalityPath.cons generator rest)
      = braidPrependAtom (braidAtomOfGenerator generator) (braidNormalizeWord rest) := rfl

/-! ## Readback: the canonical form's word -/

/-- The word of a proper simple factor (literal conses, reusing the shipped Garside-layer words). -/
def braidProperFactorWord :
    BraidProperSimple → ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point
  | .properSigmaOne => braidThreeSigma1
  | .properSigmaTwo => braidThreeSigma2
  | .properOneTwo => braidThreeSigma1Sigma2
  | .properTwoOne => braidThreeSigma2Sigma1

/-- The word of a factor list — `[] ↦ nil`, `factor :: rest ↦ factorWord · rest`.  Because each factor word is
a concrete cons chain and `composePath` recurses on its first argument, every unfolding is definitional. -/
def braidReadbackFactors :
    List BraidProperSimple → ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point
  | [] => braidThreeNil
  | factor :: remainingFactors =>
      composePath (braidProperFactorWord factor) (braidReadbackFactors remainingFactors)

/-- The word `Δ^power · tail` — each level prepends `Δ`'s primary word `σ1σ2σ1` as literal conses. -/
def braidDeltaPowPath :
    Nat → ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point →
    ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point
  | 0, wordTail => wordTail
  | power + 1, wordTail =>
      ModalityPath.cons BraidThreeModality.sigma1
        (ModalityPath.cons BraidThreeModality.sigma2
          (ModalityPath.cons BraidThreeModality.sigma1 (braidDeltaPowPath power wordTail)))

/-- The **readback** of a canon: the word `Δ^deltaPower · f1 · … · fm`. -/
def braidReadbackCanon (canon : BraidGarsideCanon) :
    ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  braidDeltaPowPath canon.deltaPower (braidReadbackFactors canon.properFactors)

/-- Readback smoke: the canon `⟨1, []⟩` reads back to the Garside element `Δ` itself. -/
theorem braidReadbackCanon_deltaOne : braidReadbackCanon ⟨1, []⟩ = braidThreeDelta := rfl

/-! ## SOUNDNESS: every word is convertible to its canon's readback -/

/-- ★ The **domino step** — prepending an atom commutes with readback UP TO CONVERTIBILITY:
`a · readback ⟨power, factors⟩ ≈ readback (prependAtom a ⟨power, factors⟩)`.  Induction on the Δ-power with
the atom AND factors universally quantified in the motive (the atom FLIPS at each level).  Base `power = 0`:
ten-way case on `atom × head` — nine arms are DEFINITIONAL on the cons-based readback (both non-Δ merges and
the `σ1·σ2σ1 = Δ` completion land on the nose, since `Δ`'s primary word is `σ1σ2σ1`), and exactly one arm
carries braid content: `σ2·σ1σ2 = Δ` is `braidRel` reversed.  Step: one braid firing pushes the atom through
the leading `Δ` (`σ1·Δ·X ≈ Δ·σ2·X` is `braidRel` under a leading `σ1`; `σ2·Δ·X ≈ Δ·σ1·X` is `braidRel`
reversed), then the flipped inductive hypothesis fires under the three Δ-conses. -/
theorem braidPrependAtom_readback_conv (power : Nat) :
    ∀ (atom : BraidAtom) (factors : List BraidProperSimple),
      BraidThreeOneCellConv
        (braidConsAtom atom (braidReadbackCanon ⟨power, factors⟩))
        (braidReadbackCanon (braidPrependAtomWithPower atom power factors)) := by
  induction power with
  | zero =>
      intro atom factors
      cases atom with
      | atomSigmaOne =>
          cases factors with
          | nil => exact BraidThreeOneCellConv.refl _
          | cons headFactor rest =>
              cases headFactor with
              | properSigmaOne => exact BraidThreeOneCellConv.refl _
              | properSigmaTwo => exact BraidThreeOneCellConv.refl _
              | properOneTwo => exact BraidThreeOneCellConv.refl _
              | properTwoOne => exact BraidThreeOneCellConv.refl _
      | atomSigmaTwo =>
          cases factors with
          | nil => exact BraidThreeOneCellConv.refl _
          | cons headFactor rest =>
              cases headFactor with
              | properSigmaOne => exact BraidThreeOneCellConv.refl _
              | properSigmaTwo => exact BraidThreeOneCellConv.refl _
              | properOneTwo =>
                  exact BraidThreeOneCellConv.symm
                    (BraidThreeOneCellConv.braidRel (braidReadbackFactors rest))
              | properTwoOne => exact BraidThreeOneCellConv.refl _
  | succ predecessor inductiveHypothesis =>
      intro atom factors
      cases atom with
      | atomSigmaOne =>
          exact BraidThreeOneCellConv.trans
            (BraidThreeOneCellConv.consCongr (BraidThreeOneCellConv.braidRel
              (braidDeltaPowPath predecessor (braidReadbackFactors factors))))
            (BraidThreeOneCellConv.consCongr (BraidThreeOneCellConv.consCongr
              (BraidThreeOneCellConv.consCongr
                (inductiveHypothesis BraidAtom.atomSigmaTwo factors))))
      | atomSigmaTwo =>
          exact BraidThreeOneCellConv.trans
            (BraidThreeOneCellConv.symm (BraidThreeOneCellConv.braidRel
              (ModalityPath.cons BraidThreeModality.sigma1
                (braidDeltaPowPath predecessor (braidReadbackFactors factors)))))
            (BraidThreeOneCellConv.consCongr (BraidThreeOneCellConv.consCongr
              (BraidThreeOneCellConv.consCongr
                (inductiveHypothesis BraidAtom.atomSigmaOne factors))))

/-- The reconstruction, length-generalized: every word is convertible to the readback of its canon.  Recursion
on a plain `Nat` (the word length) with the word destructured in a TACTIC match and the generator matched
concretely — the propext-free `convWhiskerLeftOfLength` recipe (a bare `induction word` is blocked by the
single-object mode index; a proof-valued `def` matching `.cons .sigma1` would refine the modality index and
leak `propext`). -/
theorem braidConv_toReadback_ofLength :
    ∀ (bound : Nat)
      (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point),
      word.length = bound →
      BraidThreeOneCellConv word (braidReadbackCanon (braidNormalizeWord word)) := by
  intro bound
  induction bound with
  | zero =>
      intro word wordLengthEqZero
      match word with
      | .nil _ => exact BraidThreeOneCellConv.refl braidThreeNil
      | .cons _ _ => exact absurd wordLengthEqZero (by intro isZero; cases isZero)
  | succ predecessor inductiveHypothesis =>
      intro word wordLengthEqSucc
      match word with
      | .nil _ => exact absurd wordLengthEqSucc (by intro isSucc; cases isSucc)
      | .cons .sigma1 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          exact BraidThreeOneCellConv.trans
            (BraidThreeOneCellConv.consCongr (inductiveHypothesis rest restLengthEqPredecessor))
            (braidPrependAtom_readback_conv (braidNormalizeWord rest).deltaPower
              BraidAtom.atomSigmaOne (braidNormalizeWord rest).properFactors)
      | .cons .sigma2 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          exact BraidThreeOneCellConv.trans
            (BraidThreeOneCellConv.consCongr (inductiveHypothesis rest restLengthEqPredecessor))
            (braidPrependAtom_readback_conv (braidNormalizeWord rest).deltaPower
              BraidAtom.atomSigmaTwo (braidNormalizeWord rest).properFactors)

/-- ★ **Soundness of the canonical form**: every word is convertible to the readback of its canon (the
length-generalized reconstruction at the word's own length) — each carry move discharged as a braid-relation
convertibility, the move-by-move bubble/domino assembly the WP-BRAID-3 wall named. -/
theorem braidConv_toReadback
    (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    BraidThreeOneCellConv word (braidReadbackCanon (braidNormalizeWord word)) :=
  braidConv_toReadback_ofLength word.length word rfl

/-- ★ **Equal canons ⟹ convertible** (the YES direction of the decision): route both words through the common
readback — `word1 ≈ readback (canon word1) = readback (canon word2) ≈ word2`. -/
theorem braidThreeConv_of_normalizeWord_eq
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (canonsEqual : braidNormalizeWord word1 = braidNormalizeWord word2) :
    BraidThreeOneCellConv word1 word2 := by
  have reduceFirst : BraidThreeOneCellConv word1 (braidReadbackCanon (braidNormalizeWord word2)) := by
    rw [← canonsEqual]
    exact braidConv_toReadback word1
  exact BraidThreeOneCellConv.trans reduceFirst
    (BraidThreeOneCellConv.symm (braidConv_toReadback word2))

/-! ## The left-greedy invariant -/

/-- The **handoff table** of left-weightedness: `braidHandoffAllows first second = true` iff the FINISHING
atom of `first` equals the STARTING atom of `second` (Elrifai–Morton left-weightedness degenerates to this for
`B_3`: `first·second` is left-weighted iff `first` cannot absorb `second`'s starting atom into a longer
simple).  Finishing atoms: `σ1 ↦ σ1`, `σ2 ↦ σ2`, `σ1σ2 ↦ σ2`, `σ2σ1 ↦ σ1`; starting atoms: `σ1 ↦ σ1`,
`σ2 ↦ σ2`, `σ1σ2 ↦ σ1`, `σ2σ1 ↦ σ2`.  Sixteen full-enumeration arms. -/
def braidHandoffAllows : BraidProperSimple → BraidProperSimple → Bool
  | .properSigmaOne, .properSigmaOne => true
  | .properSigmaOne, .properSigmaTwo => false
  | .properSigmaOne, .properOneTwo => true
  | .properSigmaOne, .properTwoOne => false
  | .properSigmaTwo, .properSigmaOne => false
  | .properSigmaTwo, .properSigmaTwo => true
  | .properSigmaTwo, .properOneTwo => false
  | .properSigmaTwo, .properTwoOne => true
  | .properOneTwo, .properSigmaOne => false
  | .properOneTwo, .properSigmaTwo => true
  | .properOneTwo, .properOneTwo => false
  | .properOneTwo, .properTwoOne => true
  | .properTwoOne, .properSigmaOne => true
  | .properTwoOne, .properSigmaTwo => false
  | .properTwoOne, .properOneTwo => true
  | .properTwoOne, .properTwoOne => false

/-- The **left-greedy predicate** on factor lists: every adjacent handoff is legal.  The normalizer only ever
produces greedy factor lists (`braidNormalizeWord_greedy`), and the braid-agreement lemma needs exactly this
hypothesis — the raw-carrier agreement is FALSE (`⟨0, [σ1, σ2]⟩`, an illegal handoff state, separates the two
triple-prepend composites as data). -/
def braidIsLeftGreedy : List BraidProperSimple → Bool
  | [] => true
  | _onlyFactor :: [] => true
  | firstFactor :: secondFactor :: rest =>
      braidHandoffAllows firstFactor secondFactor && braidIsLeftGreedy (secondFactor :: rest)

/-- The carry table PRESERVES left-greediness.  Full enumeration on `atom × head` (with a further split on the
second factor where the head merges or absorbs): the four no-merge conses create exactly the four LEGAL
handoffs (goal collapses definitionally through `true && x`); both non-Δ merges preserve the head's finishing
atom (`σ1·σ2 = σ1σ2` finishes like `σ2`, `σ2·σ1 = σ2σ1` finishes like `σ1`), so the new head accepts exactly
the successors the old head accepted; Δ-absorptions drop the head, and the tail of a greedy list is greedy.
Illegal-handoff hypotheses reduce to `false = true` (`false && x` computes) and close by `Bool.noConfusion`. -/
theorem braidPrependAtomToFactors_preservesGreedy :
    ∀ (atom : BraidAtom) (factors : List BraidProperSimple),
      braidIsLeftGreedy factors = true →
      braidIsLeftGreedy (braidPrependAtomToFactors atom factors).properFactors = true := by
  intro atom factors greedyFactors
  cases atom with
  | atomSigmaOne =>
      cases factors with
      | nil => rfl
      | cons headFactor rest =>
          cases headFactor with
          | properSigmaOne => exact greedyFactors
          | properSigmaTwo =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact Bool.noConfusion greedyFactors
                  | properSigmaTwo => exact greedyFactors
                  | properOneTwo => exact Bool.noConfusion greedyFactors
                  | properTwoOne => exact greedyFactors
          | properOneTwo => exact greedyFactors
          | properTwoOne =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact greedyFactors
                  | properSigmaTwo => exact Bool.noConfusion greedyFactors
                  | properOneTwo => exact greedyFactors
                  | properTwoOne => exact Bool.noConfusion greedyFactors
  | atomSigmaTwo =>
      cases factors with
      | nil => rfl
      | cons headFactor rest =>
          cases headFactor with
          | properSigmaOne =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact greedyFactors
                  | properSigmaTwo => exact Bool.noConfusion greedyFactors
                  | properOneTwo => exact greedyFactors
                  | properTwoOne => exact Bool.noConfusion greedyFactors
          | properSigmaTwo => exact greedyFactors
          | properOneTwo =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact Bool.noConfusion greedyFactors
                  | properSigmaTwo => exact greedyFactors
                  | properOneTwo => exact Bool.noConfusion greedyFactors
                  | properTwoOne => exact greedyFactors
          | properTwoOne => exact greedyFactors

/-- The Δ-power carry preserves left-greediness — the power recursion leaves the factor list untouched (each
level only flips the atom), so everything reduces to the carry table.  The motive quantifies the atom (it
flips per level). -/
theorem braidPrependAtomWithPower_preservesGreedy :
    ∀ (power : Nat) (atom : BraidAtom) (factors : List BraidProperSimple),
      braidIsLeftGreedy factors = true →
      braidIsLeftGreedy (braidPrependAtomWithPower atom power factors).properFactors = true := by
  intro power
  induction power with
  | zero =>
      intro atom factors greedyFactors
      exact braidPrependAtomToFactors_preservesGreedy atom factors greedyFactors
  | succ predecessor inductiveHypothesis =>
      intro atom factors greedyFactors
      exact inductiveHypothesis (braidFlipAtom atom) factors greedyFactors

/-- The greedy invariant of the normalizer, length-generalized (the same `Nat`-length-bound recipe as the
reconstruction). -/
theorem braidNormalizeWord_greedy_ofLength :
    ∀ (bound : Nat)
      (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point),
      word.length = bound →
      braidIsLeftGreedy (braidNormalizeWord word).properFactors = true := by
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
          exact braidPrependAtomWithPower_preservesGreedy (braidNormalizeWord rest).deltaPower
            BraidAtom.atomSigmaOne (braidNormalizeWord rest).properFactors
            (inductiveHypothesis rest restLengthEqPredecessor)
      | .cons .sigma2 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj wordLengthEqSucc
          exact braidPrependAtomWithPower_preservesGreedy (braidNormalizeWord rest).deltaPower
            BraidAtom.atomSigmaTwo (braidNormalizeWord rest).properFactors
            (inductiveHypothesis rest restLengthEqPredecessor)

/-- ★ The **normalizer's invariant**: every canon the normalizer produces has a left-greedy factor list. -/
theorem braidNormalizeWord_greedy
    (word : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    braidIsLeftGreedy (braidNormalizeWord word).properFactors = true :=
  braidNormalizeWord_greedy_ofLength word.length word rfl

/-! ## COMPLETENESS: the braid relation is invisible to the normalizer -/

/-- ★ The **braid-agreement lemma** — the completeness crux: on LEFT-GREEDY canons, the two triple-prepend
composites agree AS DATA: `P σ1 (P σ2 (P σ1 c)) = P σ2 (P σ1 (P σ2 c))`.  This is FALSE on raw canons
(`⟨0, [σ1, σ2]⟩` yields `⟨1, [σ1, σ2]⟩` vs `⟨1, [σ1σ2]⟩`), and the greedy hypothesis kills exactly the
offending states.  Induction on the Δ-power: the step is `congrArg braidSuccDelta` of the flipped-and-swapped
inductive hypothesis (the composite `τ³ = τ` swaps the two sides), and the base is a finite leaf split on the
first two factors — every legal leaf closes by `rfl` (both composites reduce through the carry table to the
same canon), every illegal leaf by `Bool.noConfusion` on the reduced hypothesis. -/
theorem braidPrependAtom_braidAgreement (power : Nat) :
    ∀ (factors : List BraidProperSimple), braidIsLeftGreedy factors = true →
      braidPrependAtom BraidAtom.atomSigmaOne (braidPrependAtom BraidAtom.atomSigmaTwo
          (braidPrependAtom BraidAtom.atomSigmaOne ⟨power, factors⟩))
        = braidPrependAtom BraidAtom.atomSigmaTwo (braidPrependAtom BraidAtom.atomSigmaOne
          (braidPrependAtom BraidAtom.atomSigmaTwo ⟨power, factors⟩)) := by
  induction power with
  | zero =>
      intro factors greedyFactors
      cases factors with
      | nil => rfl
      | cons headFactor rest =>
          cases headFactor with
          | properSigmaOne =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => rfl
                  | properSigmaTwo => exact Bool.noConfusion greedyFactors
                  | properOneTwo => rfl
                  | properTwoOne => exact Bool.noConfusion greedyFactors
          | properSigmaTwo =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact Bool.noConfusion greedyFactors
                  | properSigmaTwo => rfl
                  | properOneTwo => exact Bool.noConfusion greedyFactors
                  | properTwoOne => rfl
          | properOneTwo =>
              cases rest with
              | nil => rfl
              | cons secondFactor tail =>
                  cases secondFactor with
                  | properSigmaOne => exact Bool.noConfusion greedyFactors
                  | properSigmaTwo => rfl
                  | properOneTwo => exact Bool.noConfusion greedyFactors
                  | properTwoOne => rfl
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
      exact congrArg braidSuccDelta ((inductiveHypothesis factors greedyFactors).symm)

/-- ★ **Completeness of the canonical form**: braid-convertible words have EQUAL canons.  By induction on the
convertibility: `braidRel` is the braid-agreement lemma at the tail's canon (which IS left-greedy by the
normalizer's invariant); the generic `cons`-congruence is `congrArg` of the transducer via the definitional
`cons` equation; `refl`/`symm`/`trans` are the equivalence closure.  This is the NO direction of the decision:
distinct canons ⟹ not convertible.  Mirrors `braidThreePermutationOf_congr_of_conv` — but unlike the `S_3`
invariant, the canon is COMPLETE (`braidThreeConv_of_normalizeWord_eq` is its converse). -/
theorem braidNormalizeWord_congr_of_conv
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (conv : BraidThreeOneCellConv word1 word2) :
    braidNormalizeWord word1 = braidNormalizeWord word2 := by
  induction conv with
  | braidRel rest =>
      exact braidPrependAtom_braidAgreement (braidNormalizeWord rest).deltaPower
        (braidNormalizeWord rest).properFactors (braidNormalizeWord_greedy rest)
  | @consCongr generator innerWordOne innerWordTwo _ innerInductiveHypothesis =>
      exact congrArg (braidPrependAtom (braidAtomOfGenerator generator)) innerInductiveHypothesis
  | refl _ => rfl
  | symm _ innerInductiveHypothesis => exact innerInductiveHypothesis.symm
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact firstInductiveHypothesis.trans secondInductiveHypothesis

/-! ## The TOTAL decision -/

/-- ★ **Decide the full `B_3^+` word problem** — TOTAL, on ARBITRARY words.  Compare the two words' Garside
canons under the manual `decEq`: equal canons ⟹ convertible (soundness round-trip
`braidThreeConv_of_normalizeWord_eq`); distinct canons ⟹ not convertible (completeness
`braidNormalizeWord_congr_of_conv` would force them equal).  Both branches discharged — the WP-BRAID-3 wall's
statement is met. -/
def decideBraidThreeConv
    (word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    Decidable (BraidThreeOneCellConv word1 word2) :=
  match braidGarsideCanonDecEq (braidNormalizeWord word1) (braidNormalizeWord word2) with
  | isTrue canonsEqual => isTrue (braidThreeConv_of_normalizeWord_eq canonsEqual)
  | isFalse canonsDiffer =>
      isFalse (fun conv => canonsDiffer (braidNormalizeWord_congr_of_conv conv))

/-- The full braid convertibility as a `Decidable` instance (so `decide` fires on arbitrary word pairs). -/
instance instDecidableBraidThreeConv
    (word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    Decidable (BraidThreeOneCellConv word1 word2) :=
  decideBraidThreeConv word1 word2

/-! ## Smoke words -/

/-- The length-2 word `σ1σ1` — the seed's non-injectivity witness (its `S_3` permutation is the identity, yet
it is NOT convertible to `nil`; the Garside decider separates them). -/
def braidThreeSigma1Sigma1 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma1 braidThreeSigma1

/-- The length-4 word `σ1σ1σ2σ1` = `σ1·(σ1σ2σ1)` — the carried pair's left side. -/
def braidThreeCarriedLeft : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma1 braidThreeBraidLeft

/-- The length-4 word `σ1σ2σ1σ2` = `σ1·(σ2σ1σ2)` — the carried pair's right side (normalizing it pushes an
atom through the Δ produced by its tail: the flip carry actually fires). -/
def braidThreeCarriedRight : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma1 braidThreeBraidRight

/-- The length-6 word `(σ1σ2)³` — equal to `Δ²` in `B_3^+` (the classical presentation of the center's
generator), the double-carry smoke. -/
def braidThreeSigmaOneTwoCubed : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  composePath braidThreeSigma1Sigma2 (composePath braidThreeSigma1Sigma2 braidThreeSigma1Sigma2)

/-! ## Canon value smokes (all definitional) -/

/-- Canon smoke: `σ1σ2σ1` normalizes to `Δ¹` with no proper tail. -/
theorem braidNormalizeWord_braidLeft : braidNormalizeWord braidThreeBraidLeft = ⟨1, []⟩ := rfl

/-- Canon smoke: `σ2σ1σ2` normalizes to the SAME canon `Δ¹` — the braid relation is invisible to the
normalizer on its defining instance. -/
theorem braidNormalizeWord_braidRight : braidNormalizeWord braidThreeBraidRight = ⟨1, []⟩ := rfl

/-- Canon smoke: `σ1σ1σ2σ1 = σ1·Δ` normalizes to `⟨1, [σ2]⟩` — the atom FLIPS through the Δ (`σ1·Δ = Δ·σ2`),
the carry genuinely fires. -/
theorem braidNormalizeWord_carriedLeft :
    braidNormalizeWord braidThreeCarriedLeft = ⟨1, [BraidProperSimple.properSigmaTwo]⟩ := rfl

/-- Canon smoke: `σ1σ2σ1σ2 = Δ·σ2` normalizes to the SAME `⟨1, [σ2]⟩`. -/
theorem braidNormalizeWord_carriedRight :
    braidNormalizeWord braidThreeCarriedRight = ⟨1, [BraidProperSimple.properSigmaTwo]⟩ := rfl

/-- Canon smoke: `(σ1σ2)³` normalizes to `Δ²` — the carries propagate through TWO Δ levels. -/
theorem braidNormalizeWord_sigmaOneTwoCubed :
    braidNormalizeWord braidThreeSigmaOneTwoCubed = ⟨2, []⟩ := rfl

/-- Canon smoke: `Δ² = σ1σ2σ1σ1σ2σ1` normalizes to `⟨2, []⟩` as well. -/
theorem braidNormalizeWord_deltaSquared :
    braidNormalizeWord braidThreeDeltaSquared = ⟨2, []⟩ := rfl

/-- Non-vacuity of the YES direction as a TERM: the carried pair's convertibility witness, produced by the
completeness round-trip from the definitional canon equality. -/
theorem braidThreeConv_carriedPair :
    BraidThreeOneCellConv braidThreeCarriedLeft braidThreeCarriedRight :=
  braidThreeConv_of_normalizeWord_eq rfl

/-! ## Decider smokes — the total decider genuinely discriminates -/

/-- ★ Decider smoke (positive): `decide` ACCEPTS the braid pair `σ1σ2σ1 ≟ σ2σ1σ2`. -/
theorem braidThreeGarsideDecide_true_on_braidPair :
    decide (BraidThreeOneCellConv braidThreeBraidLeft braidThreeBraidRight) = true := rfl

/-- ★ Decider smoke (positive, carried): `decide` ACCEPTS `σ1σ1σ2σ1 ≟ σ1σ2σ1σ2` — a pair whose agreement
needs an atom carried THROUGH a Δ power (the flip actually fires in both normalizations). -/
theorem braidThreeGarsideDecide_true_on_carriedPair :
    decide (BraidThreeOneCellConv braidThreeCarriedLeft braidThreeCarriedRight) = true := rfl

/-- ★ Decider smoke (positive, double carry): `decide` ACCEPTS `(σ1σ2)³ ≟ Δ²` — carries propagate through two
Δ levels on the left word. -/
theorem braidThreeGarsideDecide_true_on_doubleCarry :
    decide (BraidThreeOneCellConv braidThreeSigmaOneTwoCubed braidThreeDeltaSquared) = true := rfl

/-- ★ Decider smoke (negative): `decide` REJECTS `σ1 ≟ σ2` (canons `⟨0, [σ1]⟩` vs `⟨0, [σ2]⟩`). -/
theorem braidThreeGarsideDecide_false_on_atoms :
    decide (BraidThreeOneCellConv braidThreeSigma1 braidThreeSigma2) = false := rfl

/-- ★ Decider smoke (negative): `decide` REJECTS `σ1σ2 ≟ σ2σ1` (canons `⟨0, [σ1σ2]⟩` vs `⟨0, [σ2σ1]⟩`). -/
theorem braidThreeGarsideDecide_false_on_twoLetters :
    decide (BraidThreeOneCellConv braidThreeSigma1Sigma2 braidThreeSigma2Sigma1) = false := rfl

/-- ★ Decider smoke (negative, length-separated): `decide` REJECTS `σ1 ≟ σ1σ1` (canons `⟨0, [σ1]⟩` vs
`⟨0, [σ1, σ1]⟩` — the braid relation preserves length, so no relation chain connects them). -/
theorem braidThreeGarsideDecide_false_on_lengthSeparated :
    decide (BraidThreeOneCellConv braidThreeSigma1 braidThreeSigma1Sigma1) = false := rfl

/-- ★ Decider smoke (negative, the seed's honesty witness KILLED): `decide` REJECTS `σ1σ1 ≟ nil` — the exact
pair on which the `S_3` permutation invariant is blind (`braidThreePermutationOf_sigma1Sigma1_eq_nil`), now
separated by the complete Garside canon (`⟨0, [σ1, σ1]⟩` vs `⟨0, []⟩`). -/
theorem braidThreeGarsideDecide_false_on_sigmaSquaredNil :
    decide (BraidThreeOneCellConv braidThreeSigma1Sigma1 braidThreeNil) = false := rfl

/-! ## Cross-check against the shipped simple-stratum decider -/

/-- Cross-check (negative leg): on the simple-stratum pair `σ1σ2 ≟ σ2σ1`, the shipped permutation-based
simple-stratum decider and the new Garside decider agree (both reject). -/
theorem braidThreeGarsideDecide_agreesWithSimpleStratum_twoLetters :
    @decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleSigmaOneTwo)
        (simpleWord SimpleThree.simpleSigmaTwoOne))
      (decideBraidThreeSimpleConv SimpleThree.simpleSigmaOneTwo SimpleThree.simpleSigmaTwoOne)
    = @decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleSigmaOneTwo)
        (simpleWord SimpleThree.simpleSigmaTwoOne))
      (decideBraidThreeConv (simpleWord SimpleThree.simpleSigmaOneTwo)
        (simpleWord SimpleThree.simpleSigmaTwoOne)) := rfl

/-- Cross-check (positive leg): on the simple-stratum pair `Δ ≟ Δ`, the two deciders agree (both accept). -/
theorem braidThreeGarsideDecide_agreesWithSimpleStratum_delta :
    @decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleDelta)
        (simpleWord SimpleThree.simpleDelta))
      (decideBraidThreeSimpleConv SimpleThree.simpleDelta SimpleThree.simpleDelta)
    = @decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleDelta)
        (simpleWord SimpleThree.simpleDelta))
      (decideBraidThreeConv (simpleWord SimpleThree.simpleDelta)
        (simpleWord SimpleThree.simpleDelta)) := rfl

/-! ## Marker -/

/-- **ESTABLISHED.**  The FULL word problem of the positive braid monoid `B_3^+` on ARBITRARY words is
DECIDED, zero-axiom and non-vacuously, via the left-greedy Garside normal form: the carrying transducer
`braidPrependAtom` over `BraidGarsideCanon = Δ-power × proper-simple tail`, the total normalizer
`braidNormalizeWord`, SOUNDNESS (`braidConv_toReadback` — every carry move a braid-relation convertibility),
COMPLETENESS (`braidNormalizeWord_congr_of_conv`, via the left-greedy braid-agreement
`braidPrependAtom_braidAgreement` + the invariant `braidNormalizeWord_greedy`), and the total decider
`decideBraidThreeConv` — which accepts `σ1σ2σ1 ≟ σ2σ1σ2`, the carried pair `σ1σ1σ2σ1 ≟ σ1σ2σ1σ2`, and the
double-carry pair `(σ1σ2)³ ≟ Δ²`, and rejects `σ1 ≟ σ2`, `σ1σ2 ≟ σ2σ1`, the length-separated `σ1 ≟ σ1σ1`, and
the permutation-blind `σ1σ1 ≟ nil`.  This discharges the STATEMENT of the WP-BRAID-3 wall
(`fxBraid_hasFullWordProblemDecided`, owner flag untouched here — the orchestrator flips it after
verification).  `= true`. -/
def fxBraid_hasGarsideNormalFormDecision : Bool := true

end FX1Poly.Polygraph
