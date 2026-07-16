import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreePermutation

/-! # WalkingBraid/BraidThreeGarside — the Garside Δ-element + simple-stratum decision layer of `B_3^+`

The **Garside** half of the walking positive braid `B_3^+ = ⟨σ1, σ2 | σ1σ2σ1 = σ2σ1σ2⟩`.  Brick-1
(`BraidThreeSeed` / `BraidThreePermutation`) shipped the SIGNATURE and the SOUND-but-not-injective `S_3`
underlying-permutation invariant.  This brick ships the structural machinery of the Garside monoid at the
`ModalityPath` 1-cell level, all as bounded convertibility derivations, plus a genuine BOUNDED DECISION on the
simple stratum:

  * **Whiskering** — the two one-sided congruence closures of `BraidThreeOneCellConv` under composition
    (`convWhiskerLeft`, `convWhiskerRight`) and their two-sided combination (`convComposeCongr`).  The
    reusable substrate: `BraidThreeOneCellConv` respects `composePath` on both flanks, so a local braid move
    lifts under an arbitrary prefix and suffix.
  * **The Garside element Δ** — `braidThreeDelta := σ1σ2σ1` with its second representation `σ2σ1σ2` and the
    conversion between them (`braidThreeLawHolds`), the fundamental "half-twist" `Δ`.
  * **Δ-conjugation** — `Δ·σ1 ≈ σ2·Δ` and `Δ·σ2 ≈ σ1·Δ` (`braidThreeDeltaConjugateSigma1/Sigma2`): conjugation
    by Δ swaps the two atoms.  These are the exact word identities that make Δ the Garside element.
  * **Δ² is central** — `Δ²·σ1 ≈ σ1·Δ²` and `Δ²·σ2 ≈ σ2·Δ²` (`braidThreeDeltaSquaredCentralSigma1/Sigma2`):
    the double half-twist commutes with every atom, so it generates the center of `B_3` (composing the two
    conjugations through the whiskering engine).
  * **Simple-element divisibility of Δ** — the six simple elements (divisors of Δ, in bijection with `S_3`)
    each LEFT-divide Δ (`braidThreeDelta_leftDivisibleBy_*`), and both atoms also RIGHT-divide Δ
    (`braidThreeDelta_rightDivisibleBy_sigmaOne/Two`).  Δ is the least common multiple of the atoms.
  * **The simple stratum, DECIDED** — the six simple words inject into `S_3` (`simplePerm_injective`, via a
    retraction `simpleOfPerm`, upgrading the seed's non-injective map to "the `S_3` invariant is COMPLETE on
    the simple stratum"), giving a TOTAL `Decidable (BraidThreeOneCellConv (simpleWord _) (simpleWord _))`
    (`decideBraidThreeSimpleConv`).

## The honesty boundary — the FULL word problem, WALLED here, CAME DOWN in `BraidThreeGarsideDecision`

The full left-greedy Garside normal form for ARBITRARY words is NOT shipped in THIS file — its hard half (a
rightward carrying transducer whose conv-reconstruction discharges each carry move as a braid-relation
convertibility, the move-by-move "bubble/domino" assembly) exceeded this brick, for the reasons this section
originally recorded: the braid relation `σ1σ2σ1 = σ2σ1σ2` is LENGTH-PRESERVING (no monotone word-length
measure), and `B_3^+` is INFINITE (`σ1^k` all distinct), so the complete model is a canonical form on words,
not a finite-group residue.  That BOUNDED ENGINEERING wall was closed by WP-BRAID-3
(`BraidThreeGarsideDecision.lean`): `braidPrependAtom` / `braidNormalizeWord` / `decideBraidThreeConv`, sound
+ complete + total, zero-axiom.  Both `fxBraid_hasFullWordProblemDecided` (below) and the seed marker
`fxBraidThree_hasWordProblemDecided` are now `true`.

## Propext-cleanliness

The whiskering folds keep the generator MODE-GENERIC (left whisker recurses on a `Nat` LENGTH bound with the
generator matched in a TACTIC `match`, exactly the `WalkingCyclicThree` reconstruction recipe; right whisker
inducts on the convertibility, where `composePath` reduces definitionally because the leading conses are
concrete).  All `SymThree` / `ThreeIdx` matches are full-enumeration; the simple-stratum retraction is a total
nine-arm match on `(img0, img1)`; the decision routes through the existing `symThreeDecEq`.  Per-declaration
`#assert_no_axioms` gated in the audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## Whiskering: `BraidThreeOneCellConv` is a congruence for `composePath` on both flanks -/

/-- **Right whiskering** — post-composing both sides of a convertibility by an arbitrary suffix preserves it:
`word1 ≈ word2 ⟹ word1·suffix ≈ word2·suffix`.  By induction on the convertibility derivation; the `braidRel`
case re-fires the braid law with the suffix folded into its whiskered remainder (`braidRel (rest·suffix)`),
which lands DEFINITIONALLY because `composePath` recurses on its first argument and the braid word's leading
three conses are concrete. -/
theorem convWhiskerRight
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (conv : BraidThreeOneCellConv word1 word2)
    (suffixWord : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    BraidThreeOneCellConv (composePath word1 suffixWord) (composePath word2 suffixWord) := by
  induction conv with
  | braidRel rest => exact BraidThreeOneCellConv.braidRel (composePath rest suffixWord)
  | consCongr _ ih => exact BraidThreeOneCellConv.consCongr ih
  | refl word => exact BraidThreeOneCellConv.refl (composePath word suffixWord)
  | symm _ ih => exact BraidThreeOneCellConv.symm ih
  | trans _ _ ih1 ih2 => exact BraidThreeOneCellConv.trans ih1 ih2

/-- **Left whiskering, length-generalized** — pre-composing both sides of a convertibility by a prefix of a
GIVEN length preserves it.  The recursion is on a plain `Nat` (the prefix length `bound`), destructuring the
prefix in a TACTIC `match` with the generator matched concretely (`.cons .sigma1` / `.cons .sigma2`): a
proof-valued `def` recursing on the prefix path directly would refine the modality index and leak `propext`,
so this mirrors the `WalkingCyclicThree` reconstruction's propext-free Nat-bound recipe (the single-object mode
also blocks a bare `induction` on the prefix, whose target index is not a variable). -/
theorem convWhiskerLeftOfLength :
    ∀ (bound : Nat)
      (prefixWord : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point),
      prefixWord.length = bound →
      ∀ {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point},
        BraidThreeOneCellConv word1 word2 →
        BraidThreeOneCellConv (composePath prefixWord word1) (composePath prefixWord word2) := by
  intro bound
  induction bound with
  | zero =>
      intro prefixWord prefixLengthEqZero word1 word2 conv
      match prefixWord with
      | .nil _ => exact conv
      | .cons _ _ => exact absurd prefixLengthEqZero (by intro isZero; cases isZero)
  | succ predecessor inductiveHypothesis =>
      intro prefixWord prefixLengthEqSucc word1 word2 conv
      match prefixWord with
      | .nil _ => exact absurd prefixLengthEqSucc (by intro isSucc; cases isSucc)
      | .cons .sigma1 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj prefixLengthEqSucc
          exact BraidThreeOneCellConv.consCongr (inductiveHypothesis rest restLengthEqPredecessor conv)
      | .cons .sigma2 rest =>
          have restLengthEqPredecessor : rest.length = predecessor := Nat.succ.inj prefixLengthEqSucc
          exact BraidThreeOneCellConv.consCongr (inductiveHypothesis rest restLengthEqPredecessor conv)

/-- **Left whiskering** — pre-composing both sides of a convertibility by an arbitrary prefix preserves it:
`word1 ≈ word2 ⟹ prefix·word1 ≈ prefix·word2` (the length-generalized `convWhiskerLeftOfLength` at the
prefix's own length). -/
theorem convWhiskerLeft
    (prefixWord : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point)
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (conv : BraidThreeOneCellConv word1 word2) :
    BraidThreeOneCellConv (composePath prefixWord word1) (composePath prefixWord word2) :=
  convWhiskerLeftOfLength prefixWord.length prefixWord rfl conv

/-- **Two-sided whiskering** — `composePath` is a congruence in BOTH arguments: `word1 ≈ word2` and
`suffix1 ≈ suffix2` give `word1·suffix1 ≈ word2·suffix2`.  The monoid-congruence property in one step (right
whisker on the left factor, then left whisker on the right factor). -/
theorem convComposeCongr
    {word1 word2 suffix1 suffix2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (convWords : BraidThreeOneCellConv word1 word2)
    (convSuffixes : BraidThreeOneCellConv suffix1 suffix2) :
    BraidThreeOneCellConv (composePath word1 suffix1) (composePath word2 suffix2) :=
  BraidThreeOneCellConv.trans (convWhiskerRight convWords suffix1) (convWhiskerLeft word2 convSuffixes)

/-! ## The Garside element Δ and its two representations -/

/-- ★ The **Garside element** `Δ = σ1σ2σ1` of `B_3^+` — the fundamental half-twist, taken with its `braidLeft`
representation as the primary word.  Every simple element divides it (below), and it is the least common
multiple of the two atoms. -/
def braidThreeDelta : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  braidThreeBraidLeft

/-- Smoke: Δ is the length-3 1-cell. -/
theorem braidThreeDelta_length : braidThreeDelta.length = 3 := rfl

/-- ★ Δ's **second representation** `Δ ≈ σ2σ1σ2` — the braid relation itself, exhibiting the half-twist's two
canonical words (the defining feature of the Garside element in `B_3^+`). -/
theorem braidThreeDelta_rightRepresentation :
    BraidThreeOneCellConv braidThreeDelta braidThreeBraidRight :=
  braidThreeLawHolds

/-! ## The two two-letter simple words (the middle stratum of the divisor lattice) -/

/-- The two-letter simple `σ1σ2` — a divisor of Δ (the `⟨2,0,1⟩` permutation). -/
def braidThreeSigma1Sigma2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma1 braidThreeSigma2

/-- The two-letter simple `σ2σ1` — a divisor of Δ (the `⟨1,2,0⟩` permutation). -/
def braidThreeSigma2Sigma1 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  ModalityPath.cons BraidThreeModality.sigma2 braidThreeSigma1

/-! ## Δ-conjugation: conjugating by Δ swaps the two atoms -/

/-- ★ **Δ-conjugation of `σ1`**: `Δ·σ1 ≈ σ2·Δ`.  Both sides are the length-4 word `σ2σ1σ2σ1`: the LHS is
`(σ1σ2σ1)·σ1` and the RHS is `σ2·(σ1σ2σ1)`, and the braid relation whiskered by the trailing `σ1`
(`braidRel σ1`) IS this convertibility on the nose (`σ1σ2σ1·σ1 ≈ σ2σ1σ2·σ1`, and `σ2σ1σ2·σ1 = σ2·(σ1σ2σ1)`
definitionally).  Conjugating the first atom by Δ yields the second. -/
theorem braidThreeDeltaConjugateSigma1 :
    BraidThreeOneCellConv
      (composePath braidThreeDelta braidThreeSigma1)
      (composePath braidThreeSigma2 braidThreeDelta) :=
  BraidThreeOneCellConv.braidRel braidThreeSigma1

/-- ★ **Δ-conjugation of `σ2`**: `Δ·σ2 ≈ σ1·Δ`.  The braid relation fired under a leading `σ1` and reversed:
`σ1·(σ1σ2σ1) ≈ σ1·(σ2σ1σ2)` reads, after regrouping, as `σ1·Δ ≈ Δ·σ2` (LHS `σ1σ1σ2σ1 = σ1·(σ1σ2σ1)`, RHS
`σ1σ2σ1σ2 = (σ1σ2σ1)·σ2`), so its symmetric form is `Δ·σ2 ≈ σ1·Δ`.  Conjugating the second atom by Δ yields
the first — together with `braidThreeDeltaConjugateSigma1` this is the swap that makes Δ the Garside element. -/
theorem braidThreeDeltaConjugateSigma2 :
    BraidThreeOneCellConv
      (composePath braidThreeDelta braidThreeSigma2)
      (composePath braidThreeSigma1 braidThreeDelta) :=
  BraidThreeOneCellConv.consCongr (BraidThreeOneCellConv.braidRel braidThreeNil).symm

/-! ## Δ² is central: the double half-twist commutes with every atom -/

/-- The **double half-twist** `Δ² = σ1σ2σ1σ1σ2σ1` — the generator of the center of `B_3` (proved central on
the atoms just below). -/
def braidThreeDeltaSquared : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point :=
  composePath braidThreeDelta braidThreeDelta

/-- Smoke: Δ² is the length-6 1-cell. -/
theorem braidThreeDeltaSquared_length : braidThreeDeltaSquared.length = 6 := rfl

/-- ★ **Δ² commutes with `σ1`**: `Δ²·σ1 ≈ σ1·Δ²`.  Compose the two Δ-conjugations through the whiskering
engine: `Δ·(Δ·σ1) ≈ Δ·(σ2·Δ)` (left-whisker `braidThreeDeltaConjugateSigma1` by Δ) then `(Δ·σ2)·Δ ≈ (σ1·Δ)·Δ`
(right-whisker `braidThreeDeltaConjugateSigma2` by Δ); the associativity regroupings are definitional because
Δ is a concrete word. -/
theorem braidThreeDeltaSquaredCentralSigma1 :
    BraidThreeOneCellConv
      (composePath braidThreeDeltaSquared braidThreeSigma1)
      (composePath braidThreeSigma1 braidThreeDeltaSquared) :=
  BraidThreeOneCellConv.trans
    (convWhiskerLeft braidThreeDelta braidThreeDeltaConjugateSigma1)
    (convWhiskerRight braidThreeDeltaConjugateSigma2 braidThreeDelta)

/-- ★ **Δ² commutes with `σ2`**: `Δ²·σ2 ≈ σ2·Δ²`.  The mirror of `braidThreeDeltaSquaredCentralSigma1`:
`Δ·(Δ·σ2) ≈ Δ·(σ1·Δ)` (left-whisker `braidThreeDeltaConjugateSigma2` by Δ) then `(Δ·σ1)·Δ ≈ (σ2·Δ)·Δ`
(right-whisker `braidThreeDeltaConjugateSigma1` by Δ).  With the `σ1` case this establishes that Δ² commutes
with every generator, hence lies in the center of `B_3`. -/
theorem braidThreeDeltaSquaredCentralSigma2 :
    BraidThreeOneCellConv
      (composePath braidThreeDeltaSquared braidThreeSigma2)
      (composePath braidThreeSigma2 braidThreeDeltaSquared) :=
  BraidThreeOneCellConv.trans
    (convWhiskerLeft braidThreeDelta braidThreeDeltaConjugateSigma2)
    (convWhiskerRight braidThreeDeltaConjugateSigma1 braidThreeDelta)

/-! ## Simple-element divisibility of Δ: the divisor lattice -/

/-- Δ is left-divisible by the identity: `Δ ≈ e·Δ` (complement Δ).  Definitional (`composePath` erases the
empty prefix). -/
theorem braidThreeDelta_leftDivisibleBy_identity :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeNil braidThreeDelta) :=
  BraidThreeOneCellConv.refl braidThreeDelta

/-- Δ is left-divisible by `σ1`: `Δ = σ1·(σ2σ1)` (complement `σ2σ1`).  Definitional (the primary `σ1σ2σ1`
representation splits after its first letter). -/
theorem braidThreeDelta_leftDivisibleBy_sigmaOne :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeSigma1 braidThreeSigma2Sigma1) :=
  BraidThreeOneCellConv.refl braidThreeDelta

/-- Δ is left-divisible by `σ2`: `Δ ≈ σ2·(σ1σ2)` (complement `σ1σ2`).  Via the braid relation — the RHS is Δ's
second representation `σ2σ1σ2`. -/
theorem braidThreeDelta_leftDivisibleBy_sigmaTwo :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeSigma2 braidThreeSigma1Sigma2) :=
  braidThreeLawHolds

/-- Δ is left-divisible by `σ1σ2`: `Δ = (σ1σ2)·σ1` (complement `σ1`).  Definitional. -/
theorem braidThreeDelta_leftDivisibleBy_sigmaOneTwo :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeSigma1Sigma2 braidThreeSigma1) :=
  BraidThreeOneCellConv.refl braidThreeDelta

/-- Δ is left-divisible by `σ2σ1`: `Δ ≈ (σ2σ1)·σ2` (complement `σ2`).  Via the braid relation — the RHS is Δ's
second representation `σ2σ1σ2`. -/
theorem braidThreeDelta_leftDivisibleBy_sigmaTwoOne :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeSigma2Sigma1 braidThreeSigma2) :=
  braidThreeLawHolds

/-- Δ is left-divisible by Δ itself: `Δ ≈ Δ·e` (complement e).  Definitional (`composePath` erases the empty
suffix on a concrete word). -/
theorem braidThreeDelta_leftDivisibleBy_delta :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeDelta braidThreeNil) :=
  BraidThreeOneCellConv.refl braidThreeDelta

/-- ★ Δ is RIGHT-divisible by `σ1`: `Δ = (σ1σ2)·σ1` (complement `σ1σ2` on the left).  Together with the left
divisibility, the atom `σ1` divides Δ on both flanks — Δ is balanced, the Garside signature. -/
theorem braidThreeDelta_rightDivisibleBy_sigmaOne :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeSigma1Sigma2 braidThreeSigma1) :=
  BraidThreeOneCellConv.refl braidThreeDelta

/-- ★ Δ is RIGHT-divisible by `σ2`: `Δ ≈ (σ2σ1)·σ2` (complement `σ2σ1` on the left).  The RHS is Δ's second
representation `σ2σ1σ2`; the atom `σ2` divides Δ on both flanks. -/
theorem braidThreeDelta_rightDivisibleBy_sigmaTwo :
    BraidThreeOneCellConv braidThreeDelta (composePath braidThreeSigma2Sigma1 braidThreeSigma2) :=
  braidThreeLawHolds

/-! ## The simple stratum, in bijection with `S_3` -/

/-- The six **simple elements** of `B_3^+` — the divisors of the Garside element Δ, in bijection with `S_3`.
Each is a positive braid word in which no atom repeats a descent; together they are the "permutation braids"
(the left-greedy normal-form factors of WP-BRAID-3). -/
inductive SimpleThree where
  /-- The identity simple `e` (empty word). -/
  | simpleIdentity
  /-- The atom `σ1`. -/
  | simpleSigmaOne
  /-- The atom `σ2`. -/
  | simpleSigmaTwo
  /-- The two-letter simple `σ1σ2`. -/
  | simpleSigmaOneTwo
  /-- The two-letter simple `σ2σ1`. -/
  | simpleSigmaTwoOne
  /-- The Garside element `Δ = σ1σ2σ1`. -/
  | simpleDelta

/-- The canonical positive-braid word of each simple element (the divisor's chosen representative). -/
def simpleWord :
    SimpleThree → ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point
  | .simpleIdentity => braidThreeNil
  | .simpleSigmaOne => braidThreeSigma1
  | .simpleSigmaTwo => braidThreeSigma2
  | .simpleSigmaOneTwo => braidThreeSigma1Sigma2
  | .simpleSigmaTwoOne => braidThreeSigma2Sigma1
  | .simpleDelta => braidThreeDelta

/-- The **underlying permutation of a simple element** — its `S_3` image under the seed's permutation fold.
The six values are the six distinct permutations `⟨0,1,2⟩, ⟨1,0,2⟩, ⟨0,2,1⟩, ⟨2,0,1⟩, ⟨1,2,0⟩, ⟨2,1,0⟩` — the
whole of `S_3` (`simplePerm_injective` below), so the seed's non-injective braid-permutation map becomes a
BIJECTION when restricted to the simple stratum. -/
def simplePerm (simple : SimpleThree) : SymThree :=
  braidThreePermutationOf (simpleWord simple)

/-- Image smoke: `simplePerm e = ⟨0,1,2⟩` (identity). -/
theorem simplePerm_simpleIdentity :
    simplePerm SimpleThree.simpleIdentity = ⟨ThreeIdx.i0, ThreeIdx.i1, ThreeIdx.i2⟩ := rfl

/-- Image smoke: `simplePerm σ1 = ⟨1,0,2⟩`. -/
theorem simplePerm_simpleSigmaOne :
    simplePerm SimpleThree.simpleSigmaOne = ⟨ThreeIdx.i1, ThreeIdx.i0, ThreeIdx.i2⟩ := rfl

/-- Image smoke: `simplePerm σ2 = ⟨0,2,1⟩`. -/
theorem simplePerm_simpleSigmaTwo :
    simplePerm SimpleThree.simpleSigmaTwo = ⟨ThreeIdx.i0, ThreeIdx.i2, ThreeIdx.i1⟩ := rfl

/-- Image smoke: `simplePerm σ1σ2 = ⟨2,0,1⟩`. -/
theorem simplePerm_simpleSigmaOneTwo :
    simplePerm SimpleThree.simpleSigmaOneTwo = ⟨ThreeIdx.i2, ThreeIdx.i0, ThreeIdx.i1⟩ := rfl

/-- Image smoke: `simplePerm σ2σ1 = ⟨1,2,0⟩`. -/
theorem simplePerm_simpleSigmaTwoOne :
    simplePerm SimpleThree.simpleSigmaTwoOne = ⟨ThreeIdx.i1, ThreeIdx.i2, ThreeIdx.i0⟩ := rfl

/-- Image smoke: `simplePerm Δ = ⟨2,1,0⟩` (the reversal). -/
theorem simplePerm_simpleDelta :
    simplePerm SimpleThree.simpleDelta = ⟨ThreeIdx.i2, ThreeIdx.i1, ThreeIdx.i0⟩ := rfl

/-- The **retraction** `S_3 → SimpleThree` recovering a simple from its permutation image: the six simple
images have pairwise-distinct `(img0, img1)` prefixes, so a total nine-arm match on `(img0, img1)` inverts
`simplePerm` (the three "diagonal" pairs `(i,i)`, never permutation images, fall through to `simpleIdentity`).
This left inverse (`simpleOfPerm_simplePerm`) is what proves the injectivity. -/
def simpleOfPerm (permutation : SymThree) : SimpleThree :=
  match permutation.img0, permutation.img1 with
  | ThreeIdx.i0, ThreeIdx.i0 => SimpleThree.simpleIdentity
  | ThreeIdx.i0, ThreeIdx.i1 => SimpleThree.simpleIdentity
  | ThreeIdx.i0, ThreeIdx.i2 => SimpleThree.simpleSigmaTwo
  | ThreeIdx.i1, ThreeIdx.i0 => SimpleThree.simpleSigmaOne
  | ThreeIdx.i1, ThreeIdx.i1 => SimpleThree.simpleIdentity
  | ThreeIdx.i1, ThreeIdx.i2 => SimpleThree.simpleSigmaTwoOne
  | ThreeIdx.i2, ThreeIdx.i0 => SimpleThree.simpleSigmaOneTwo
  | ThreeIdx.i2, ThreeIdx.i1 => SimpleThree.simpleDelta
  | ThreeIdx.i2, ThreeIdx.i2 => SimpleThree.simpleIdentity

/-- ★ `simpleOfPerm` is a LEFT INVERSE of `simplePerm` — each of the six simples is recovered from its `S_3`
image (a six-case reduction, each definitional). -/
theorem simpleOfPerm_simplePerm (simple : SimpleThree) :
    simpleOfPerm (simplePerm simple) = simple := by
  cases simple with
  | simpleIdentity => rfl
  | simpleSigmaOne => rfl
  | simpleSigmaTwo => rfl
  | simpleSigmaOneTwo => rfl
  | simpleSigmaTwoOne => rfl
  | simpleDelta => rfl

/-- ★ **The `S_3` invariant is COMPLETE on the simple stratum**: `simplePerm` is INJECTIVE — distinct simple
elements have distinct permutations (immediate from the left inverse `simpleOfPerm_simplePerm`).  This upgrades
the seed's honest non-injectivity (`braidThreePermutationOf_sigma1Sigma1_eq_nil`): the permutation map fails to
be injective on all of `B_3^+`, but it IS injective on the six divisors of Δ — the simple stratum. -/
theorem simplePerm_injective {simpleOne simpleTwo : SimpleThree}
    (permutationsEqual : simplePerm simpleOne = simplePerm simpleTwo) : simpleOne = simpleTwo :=
  (simpleOfPerm_simplePerm simpleOne).symm.trans
    ((congrArg simpleOfPerm permutationsEqual).trans (simpleOfPerm_simplePerm simpleTwo))

/-! ## The simple-stratum word problem, DECIDED -/

/-- Equal simples give convertible words (reflexivity after substituting the equality). -/
theorem braidThreeSimpleConv_of_eq {simpleOne simpleTwo : SimpleThree}
    (simplesEqual : simpleOne = simpleTwo) :
    BraidThreeOneCellConv (simpleWord simpleOne) (simpleWord simpleTwo) := by
  subst simplesEqual
  exact BraidThreeOneCellConv.refl (simpleWord simpleOne)

/-- ★ **Decide convertibility on the simple stratum** — TOTAL.  Compare the two simples' `S_3` permutations:
equal permutations ⟹ equal simples (`simplePerm_injective`) ⟹ equal words ⟹ convertible; distinct
permutations ⟹ NOT convertible (seed SOUNDNESS `braidThreePermutationOf_congr_of_conv` would force the
permutations equal).  Both branches discharged — the word problem RESTRICTED TO THE SIX SIMPLE WORDS is
genuinely decided (the reachable bounded decision; the full-word decider is WP-BRAID-3). -/
def decideBraidThreeSimpleConv (simpleOne simpleTwo : SimpleThree) :
    Decidable (BraidThreeOneCellConv (simpleWord simpleOne) (simpleWord simpleTwo)) :=
  match symThreeDecEq (simplePerm simpleOne) (simplePerm simpleTwo) with
  | isTrue permutationsEqual =>
      isTrue (braidThreeSimpleConv_of_eq (simplePerm_injective permutationsEqual))
  | isFalse permutationsDiffer =>
      isFalse (fun conv => permutationsDiffer (braidThreePermutationOf_congr_of_conv conv))

/-- The simple-stratum convertibility as a `Decidable` instance (so `decide` fires on it). -/
instance instDecidableBraidThreeSimpleConv (simpleOne simpleTwo : SimpleThree) :
    Decidable (BraidThreeOneCellConv (simpleWord simpleOne) (simpleWord simpleTwo)) :=
  decideBraidThreeSimpleConv simpleOne simpleTwo

/-! ## Non-vacuity — the simple-stratum decider genuinely discriminates -/

/-- Non-vacuity by the DECIDER (positive, reflexive): `decide` accepts `Δ ≟ Δ`. -/
theorem braidThreeSimpleDecide_true_on_delta :
    decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleDelta)
      (simpleWord SimpleThree.simpleDelta)) = true := rfl

/-- ★ Non-vacuity by the DECIDER (negative): `decide` REJECTS `σ1 ≟ σ2` — the two atoms are distinct simples
(permutations `⟨1,0,2⟩` vs `⟨0,2,1⟩`), so their words are not braid-convertible. -/
theorem braidThreeSimpleDecide_false_on_atoms :
    decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleSigmaOne)
      (simpleWord SimpleThree.simpleSigmaTwo)) = false := rfl

/-- ★ Non-vacuity by the DECIDER (negative): `decide` REJECTS `σ1σ2 ≟ σ2σ1` — distinct two-letter simples
(permutations `⟨2,0,1⟩` vs `⟨1,2,0⟩`).  The braid word problem separates the two length-2 simples even though
`B_3^+` is non-commutative in a subtle way — the simple stratum sees it. -/
theorem braidThreeSimpleDecide_false_on_twoLetters :
    decide (BraidThreeOneCellConv (simpleWord SimpleThree.simpleSigmaOneTwo)
      (simpleWord SimpleThree.simpleSigmaTwoOne)) = false := rfl

/-! ## Markers -/

/-- **ESTABLISHED.**  The Garside Δ-layer of the walking positive braid `B_3^+` is shipped, zero-axiom: the
Garside element `braidThreeDelta = σ1σ2σ1` with its second representation (`braidThreeDelta_rightRepresentation`),
the Δ-conjugations swapping the atoms (`braidThreeDeltaConjugateSigma1/Sigma2`), the centrality of Δ²
(`braidThreeDeltaSquaredCentralSigma1/Sigma2`, via the whiskering engine `convWhiskerLeft`/`convWhiskerRight`),
and the divisor lattice (`braidThreeDelta_leftDivisibleBy_*`, plus atom right-divisibility).  `= true`. -/
def fxBraid_hasGarsideDeltaLayer : Bool := true

/-- **ESTABLISHED.**  The word problem of `B_3^+` RESTRICTED TO THE SIMPLE STRATUM (the six divisors of Δ) is
DECIDED, zero-axiom and non-vacuously: `simplePerm` is INJECTIVE (`simplePerm_injective`, the `S_3` invariant
is complete on the simples, via the retraction `simpleOfPerm`), giving the total decider
`decideBraidThreeSimpleConv` — which accepts `Δ ≟ Δ` (`braidThreeSimpleDecide_true_on_delta`) and rejects
`σ1 ≟ σ2` (`braidThreeSimpleDecide_false_on_atoms`) and `σ1σ2 ≟ σ2σ1`
(`braidThreeSimpleDecide_false_on_twoLetters`).  `= true`. -/
def fxBraid_hasSimpleStratumConvDecided : Bool := true

/-- **ESTABLISHED — the WP-BRAID-3 WALL CAME DOWN (`BraidThreeGarsideDecision.lean`).**  The FULL word
problem of `B_3^+` on ARBITRARY words IS decided, exactly along the route this wall named: the
rightward-carrying transducer is `braidPrependAtom : BraidAtom → BraidGarsideCanon → BraidGarsideCanon`
over `BraidGarsideCanon := ⟨deltaPower : Nat, properFactors : List BraidProperSimple⟩`; SOUNDNESS
(`braidConv_toReadback`) discharges each carry move as a braid-relation convertibility (nine of the ten
table arms definitional, one fires `braidRel`, each Δ-level of the power carry fires `braidRel` once —
the move-by-move bubble/domino assembly); COMPLETENESS (`braidNormalizeWord_congr_of_conv`) rides the
LEFT-GREEDY invariant (`braidNormalizeWord_greedy`) through the agreement crux
`braidPrependAtom_braidAgreement` — the two obstructions this docstring recorded were met exactly as
predicted: no monotone length measure (the reconstruction inducts on word structure via a `Nat` length
bound), infinite `B_3^+` (the model is the canonical form, not a residue).  Total decider
`decideBraidThreeConv` via the manual canon `DecidableEq`.  `= true`. -/
def fxBraid_hasFullWordProblemDecided : Bool := true

end FX1Poly.Polygraph
