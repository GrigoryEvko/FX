import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSeed

/-! # WalkingBraid/BraidThreePermutation — the `S_3` underlying-permutation model + SOUNDNESS

The soundness half of the walking positive braid `B_3^+`: the underlying-permutation map
`braidThreePermutationOf : (word in σ1, σ2) → S_3` sending each elementary crossing to its transposition, and
the SOUNDNESS theorem `braidThreePermutationOf_congr_of_conv` — braid-convertible words have EQUAL underlying
permutation.  This is the permutation-invariant NO-direction: distinct permutations ⟹ not convertible.

## The model — `S_3` as a one-line word of three indices

`ThreeIdx` is the strand-slot type `{0, 1, 2}`; `SymThree` is a one-line permutation `⟨img0, img1, img2⟩`.  The
crossing `σi` acts as the elementary transposition `s_i` on the one-line word: `σ1` swaps slots 0,1; `σ2` swaps
slots 1,2.  `braidThreePermutationOf` folds a word into its permutation (leftmost generator applied outermost).

## Why the braid-relation image is EVEN CLEANER than cyclic-3's

The `S_3` witness `braidThreeApplyGenBraidRelation` — `σ1∘σ2∘σ1 = σ2∘σ1∘σ2` on any `SymThree` — reduces both
sides of a generic `⟨a,b,c⟩` to `⟨c,b,a⟩` by pure slot-shuffling.  It is content-AGNOSTIC (one `mk` case, no
per-value enumeration), unlike cyclic-3's residue-shift which needed a three-case split.

## ★ Critical honesty boundary — SOUNDNESS ONLY (see the marker)

The permutation map is **NOT injective** on `B_3^+`: e.g. `permutationOf (σ1.σ1) = symThreeIdentity =
permutationOf nil`, yet `σ1.σ1` is NOT convertible to `nil` (the positive braid monoid has NO `σi² = 1`
relation).  So brick-1 delivers the SOUNDNESS direction only.  The reverse (completeness / decision) needs
Garside normal form and is WP-BRAID-2/3.  This inverts the cyclic-3 relationship: cyclic-3's length-mod-3 map
happened to be complete; the braid's permutation map is a genuine INVARIANT ONLY.

## Propext-cleanliness

`braidThreePermutationOf` is DATA-valued (returns `SymThree : Type`) and folds via `casesOn` on the top
constructor and the generator (concrete `point → point`, no index refinement that would leak) — clean.  All
matches are full-enumeration; `DecidableEq` is manual via `noConfusion`; the negatives route through soundness
+ field projection + `noConfusion`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The three strand-slots and their decidable equality -/

/-- The three strand-slots `{0, 1, 2}` of the braid on three strands. -/
inductive ThreeIdx where
  /-- Slot 0. -/
  | i0
  /-- Slot 1. -/
  | i1
  /-- Slot 2. -/
  | i2

/-- Decidable equality of strand-slots — a MANUAL full-enumeration `decEq` (nine cases: three `isTrue rfl`,
six `isFalse` via `noConfusion`), propext-free.  Copies the cyclic-3 residue `decEq` pattern. -/
def threeIdxDecEq : (firstIdx secondIdx : ThreeIdx) → Decidable (firstIdx = secondIdx)
  | .i0, .i0 => isTrue rfl
  | .i1, .i1 => isTrue rfl
  | .i2, .i2 => isTrue rfl
  | .i0, .i1 => isFalse (fun idxEqual => ThreeIdx.noConfusion idxEqual)
  | .i0, .i2 => isFalse (fun idxEqual => ThreeIdx.noConfusion idxEqual)
  | .i1, .i0 => isFalse (fun idxEqual => ThreeIdx.noConfusion idxEqual)
  | .i1, .i2 => isFalse (fun idxEqual => ThreeIdx.noConfusion idxEqual)
  | .i2, .i0 => isFalse (fun idxEqual => ThreeIdx.noConfusion idxEqual)
  | .i2, .i1 => isFalse (fun idxEqual => ThreeIdx.noConfusion idxEqual)

/-- The strand-slots have decidable equality. -/
instance instDecidableEqThreeIdx : DecidableEq ThreeIdx := threeIdxDecEq

/-! ## `S_3` as a one-line permutation of three slots -/

/-- A **permutation of three slots** in one-line notation: `img0`, `img1`, `img2` are the images of slots
0, 1, 2.  The soundness target `S_3` (six elements when the images are a permutation; the map only ever
produces permutations). -/
structure SymThree where
  /-- The image of slot 0. -/
  img0 : ThreeIdx
  /-- The image of slot 1. -/
  img1 : ThreeIdx
  /-- The image of slot 2. -/
  img2 : ThreeIdx

/-- The identity permutation `⟨0, 1, 2⟩`. -/
def symThreeIdentity : SymThree := ⟨ThreeIdx.i0, ThreeIdx.i1, ThreeIdx.i2⟩

/-- Decidable equality of `S_3` — built COMPONENTWISE from `threeIdxDecEq` (manual, not `deriving`, to stay
provably propext-clean): three-field agreement gives equality (via `subst`), any field disagreement gives
inequality (via `congrArg` of the field projection). -/
def symThreeDecEq : (firstSym secondSym : SymThree) → Decidable (firstSym = secondSym)
  | ⟨firstImg0, firstImg1, firstImg2⟩, ⟨secondImg0, secondImg1, secondImg2⟩ =>
    match threeIdxDecEq firstImg0 secondImg0,
          threeIdxDecEq firstImg1 secondImg1,
          threeIdxDecEq firstImg2 secondImg2 with
    | isTrue img0Equal, isTrue img1Equal, isTrue img2Equal =>
        isTrue (by subst img0Equal; subst img1Equal; subst img2Equal; rfl)
    | isFalse img0Differ, _, _ =>
        isFalse (fun symsEqual => img0Differ (congrArg SymThree.img0 symsEqual))
    | _, isFalse img1Differ, _ =>
        isFalse (fun symsEqual => img1Differ (congrArg SymThree.img1 symsEqual))
    | _, _, isFalse img2Differ =>
        isFalse (fun symsEqual => img2Differ (congrArg SymThree.img2 symsEqual))

/-- `S_3` has decidable equality. -/
instance instDecidableEqSymThree : DecidableEq SymThree := symThreeDecEq

/-! ## The action of a crossing: `σi` as the transposition `s_i` -/

/-- The action of a generating crossing on a one-line permutation: `σ1` swaps slots 0,1
(`⟨a,b,c⟩ ↦ ⟨b,a,c⟩`); `σ2` swaps slots 1,2 (`⟨a,b,c⟩ ↦ ⟨a,c,b⟩`).  The elementary transposition `s_i` acting
on the one-line word.  Kept GENERIC over the modes (matching the generator pins them to `point`) so the
`braidThreePermutationOf` fold below can hand it the middle-mode-existential generator that a `cons` exposes —
this is what keeps the fold a NON-index-refining structural recursion (see its docstring). -/
def applyGen {sourceMode middleMode : BraidThreeMode}
    (generator : BraidThreeModality sourceMode middleMode) (permutation : SymThree) : SymThree :=
  match generator, permutation with
  | .sigma1, ⟨slot0, slot1, slot2⟩ => ⟨slot1, slot0, slot2⟩
  | .sigma2, ⟨slot0, slot1, slot2⟩ => ⟨slot0, slot2, slot1⟩

/-! ## The underlying-permutation map -/

/-- ★ The **underlying-permutation map** of the walking braid: fold a word in `σ1, σ2` into its `S_3`
permutation — `nil ↦ identity`, and each leading generator `applyGen`s its transposition onto the tail's
permutation.  DATA-valued structural recursion, kept GENERIC over source/target modes so the `cons` match binds
the generator WITHOUT refining the modality index (exactly like `ModalityPath.length`); the index-refinement is
pushed into `applyGen`.  This is the reason the defining equations reduce DEFINITIONALLY — a mode-specialised
fold that pattern-matched `σ1`/`σ2` inside the `cons` would defeat structural-recursion detection and reduce to
nothing (an opaque `WellFounded.fix`). -/
def braidThreePermutationOf {sourceMode targetMode : BraidThreeMode}
    (word : ModalityPath braidThreeGraph sourceMode targetMode) : SymThree :=
  match word with
  | .nil _ => symThreeIdentity
  | .cons generator rest => applyGen generator (braidThreePermutationOf rest)

/-- The defining equation on `nil` — the identity word has the identity permutation. -/
theorem braidThreePermutationOf_nil :
    braidThreePermutationOf braidThreeNil = symThreeIdentity := rfl

/-- The defining equation on a leading `σ1`. -/
theorem braidThreePermutationOf_consSigma1
    (rest : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    braidThreePermutationOf (ModalityPath.cons BraidThreeModality.sigma1 rest)
      = applyGen BraidThreeModality.sigma1 (braidThreePermutationOf rest) := rfl

/-- The defining equation on a leading `σ2`. -/
theorem braidThreePermutationOf_consSigma2
    (rest : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    braidThreePermutationOf (ModalityPath.cons BraidThreeModality.sigma2 rest)
      = applyGen BraidThreeModality.sigma2 (braidThreePermutationOf rest) := rfl

/-- The GENERIC `cons` equation — for either leading generator, prepending it `applyGen`s onto the tail's
permutation.  Holds DEFINITIONALLY (the generic fold's `cons` arm), the payoff of keeping the fold mode-generic. -/
theorem braidThreePermutationOf_cons
    (generator : BraidThreeModality BraidThreeMode.point BraidThreeMode.point)
    (rest : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point) :
    braidThreePermutationOf (ModalityPath.cons generator rest)
      = applyGen generator (braidThreePermutationOf rest) := rfl

/-- Smoke: `permutationOf (σ1.σ2.σ1) = ⟨2, 1, 0⟩` — the braid word `braidLeft` realizes the reversal `(0 2)`. -/
theorem braidThreePermutationOf_braidLeft :
    braidThreePermutationOf braidThreeBraidLeft = ⟨ThreeIdx.i2, ThreeIdx.i1, ThreeIdx.i0⟩ := rfl

/-- Smoke: `permutationOf (σ2.σ1.σ2) = ⟨2, 1, 0⟩` — the other braid word `braidRight` realizes the SAME
reversal `(0 2)` (the braid move's two sides have equal underlying permutation). -/
theorem braidThreePermutationOf_braidRight :
    braidThreePermutationOf braidThreeBraidRight = ⟨ThreeIdx.i2, ThreeIdx.i1, ThreeIdx.i0⟩ := rfl

/-! ## The braid-relation image — the `S_3` witness -/

/-- ★ The **braid-relation image** (the `S_3` witness): `σ1∘σ2∘σ1 = σ2∘σ1∘σ2` as an equality of actions on any
one-line permutation.  Both sides reduce a generic `⟨a,b,c⟩` to `⟨c,b,a⟩` by pure slot-shuffling — content
AGNOSTIC, so a single `mk` case closes it (cleaner than cyclic-3's per-value split). -/
theorem braidThreeApplyGenBraidRelation (permutation : SymThree) :
    applyGen BraidThreeModality.sigma1
        (applyGen BraidThreeModality.sigma2 (applyGen BraidThreeModality.sigma1 permutation))
      = applyGen BraidThreeModality.sigma2
        (applyGen BraidThreeModality.sigma1 (applyGen BraidThreeModality.sigma2 permutation)) := by
  cases permutation with
  | mk slot0 slot1 slot2 => rfl

/-! ## SOUNDNESS: convertible braid words have equal underlying permutation -/

/-- ★ **Soundness of the `S_3` model**: braid-convertible words have EQUAL underlying permutation.  By induction
on the convertibility: the braid law `braidRel` is exactly `σ1∘σ2∘σ1 = σ2∘σ1∘σ2`
(`braidThreeApplyGenBraidRelation`), the generic `cons`-congruence applies the same generator to both sides
(`congrArg (applyGen generator)`, via the generic `cons` equation), and `refl`/`symm`/`trans` are the
equivalence closure.  This is the NO-direction of the (undecided-here) word problem: distinct permutation ⟹ not
convertible.  Mirrors `cyclicThreeResidueOf_congr_of_conv`. -/
theorem braidThreePermutationOf_congr_of_conv
    {word1 word2 : ModalityPath braidThreeGraph BraidThreeMode.point BraidThreeMode.point}
    (conv : BraidThreeOneCellConv word1 word2) :
    braidThreePermutationOf word1 = braidThreePermutationOf word2 := by
  induction conv with
  | braidRel rest => exact braidThreeApplyGenBraidRelation (braidThreePermutationOf rest)
  | consCongr _ ih =>
      rw [braidThreePermutationOf_cons, braidThreePermutationOf_cons, ih]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Non-vacuity — the model genuinely discriminates -/

/-- Positive witness: `σ1.σ2.σ1 ≈ σ2.σ1.σ2` (the braid move is a convertible pair). -/
theorem braidThreeConv_braidLeft_braidRight :
    BraidThreeOneCellConv braidThreeBraidLeft braidThreeBraidRight :=
  braidThreeLawHolds

/-- Negative witness: `σ1` is NOT convertible to `σ2` (the two crossings are distinct 1-cells) — via soundness,
since their permutations `⟨1,0,2⟩` and `⟨0,2,1⟩` differ in slot 0. -/
theorem braidThreeNotConv_sigma1_sigma2 :
    ¬ BraidThreeOneCellConv braidThreeSigma1 braidThreeSigma2 := by
  intro conv
  have permutationsEqual :
      braidThreePermutationOf braidThreeSigma1 = braidThreePermutationOf braidThreeSigma2 :=
    braidThreePermutationOf_congr_of_conv conv
  have img0Equal : ThreeIdx.i1 = ThreeIdx.i0 := congrArg SymThree.img0 permutationsEqual
  exact ThreeIdx.noConfusion img0Equal

/-- Negative witness: `σ1` is NOT convertible to the identity `nil` (a single crossing is not trivial) — via
soundness, since their permutations `⟨1,0,2⟩` and `⟨0,1,2⟩` differ in slot 0. -/
theorem braidThreeNotConv_sigma1_nil :
    ¬ BraidThreeOneCellConv braidThreeSigma1 braidThreeNil := by
  intro conv
  have permutationsEqual :
      braidThreePermutationOf braidThreeSigma1 = braidThreePermutationOf braidThreeNil :=
    braidThreePermutationOf_congr_of_conv conv
  have img0Equal : ThreeIdx.i1 = ThreeIdx.i0 := congrArg SymThree.img0 permutationsEqual
  exact ThreeIdx.noConfusion img0Equal

/-! ## The honesty boundary, witnessed: the permutation map is NOT injective -/

/-- ★ The **non-injectivity witness** pinning the soundness-only boundary: `permutationOf (σ1.σ1) =
permutationOf nil = identity`, even though `σ1.σ1` is NOT braid-convertible to `nil` (`B_3^+` has no `σi² = 1`).
So the `S_3` model is a genuine INVARIANT, not a decision procedure — completeness needs Garside normal form
(WP-BRAID-2/3).  This inverts cyclic-3, whose length-mod-3 map happened to be complete. -/
theorem braidThreePermutationOf_sigma1Sigma1_eq_nil :
    braidThreePermutationOf (ModalityPath.cons BraidThreeModality.sigma1 braidThreeSigma1)
      = braidThreePermutationOf braidThreeNil := rfl

/-! ## Markers -/

/-- **ESTABLISHED.**  The walking positive braid `B_3^+ = ⟨σ1, σ2 | σ1σ2σ1 = σ2σ1σ2⟩` has its SIGNATURE and an
`S_3` underlying-permutation model with SOUNDNESS (`braidThreePermutationOf_congr_of_conv`: braid-convertible
words have equal permutation), zero-axiom and non-vacuously (positive `braidThreeLawHolds`; negatives
`braidThreeNotConv_sigma1_sigma2`, `braidThreeNotConv_sigma1_nil`).  `= true`. -/
def fxBraidThree_hasPermutationSoundness : Bool := true

/-- Rules-named alias of `fxBraidThree_hasPermutationSoundness` — brick-1 ships the braid signature (fixed
minimal `n = 3`, the two `σ` generators + the braid relation as a conv generator), the permutation-underlying
map, and the soundness theorem.  `= true`. -/
def fxBraid_hasSignatureAndPermutationSoundness : Bool := true

/-- **NOT ESTABLISHED (brick boundary).**  The braid WORD PROBLEM is NOT decided here: the permutation map is
sound but NOT injective (`braidThreePermutationOf_sigma1Sigma1_eq_nil`), so it is an invariant only.  A total
decider needs Garside normal form and is WP-BRAID-2/3.  This rung therefore does NOT enter the
`WordProblemDecisionLedger` "decided" enumeration — it belongs to the Garside-walled bucket.  `= false`. -/
def fxBraidThree_hasWordProblemDecided : Bool := false

end FX1Poly.Polygraph
