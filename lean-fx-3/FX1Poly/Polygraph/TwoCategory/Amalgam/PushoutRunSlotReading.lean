import FX1Poly.Polygraph.TwoCategory.Amalgam.RealLawDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeVcompCase
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvertRoundTrip

/-! # Polygraph/TwoCategory/Amalgam/PushoutRunSlotReading — the WALL-FREE gap-slot substrate: the flat wall/gap
layout with wall-free gap payloads, and word-level PARSING UNIQUENESS (WP-AMALG r30, Brick A)

The r20 ceiling ledger holds #2043's LAST wall at the vcomp payload zip = the JAM-A per-gap descent.  The r30
attack dissolves that descent through the WALL-FREE READING: every pushout 2-cell is read into a flat wall/gap
layout whose per-gap payloads have WALL-FREE boundaries — so each gap payload descends to the monad component by
the SHIPPED cell converse (`wallFreeCellInvert` + its backward round-trip) and the per-gap comparison is the
SHIPPED reconstructed word problem, never a fresh descent.  This file ships the substrate:

  * **`GapSlot`** — a gap slot: a wall-free-boundary parallel pair with its payload cell.
  * **`interleaveRuns` / `flatSlotsDom` / `flatSlotsCod` / `flatSlotsCell`** — the flat wall/gap layout: gap
    payloads interleaved with single inert `s`-walls, right-nested so every boundary composes DEFINITIONALLY.
  * **the length coordinate** — a wall-free pushout run is DETERMINED by its length
    (`wallFreeRun_eq_of_length`), so gap geometry is a `Nat`-list.
  * **★ PARSING UNIQUENESS** (`flatBoundary_slots_aligned`) — two slot decompositions assembling the same
    pushout 1-cell have EQUAL gap boundaries, pointwise.  The word-level parse (`runsWord_parse_unique`) makes
    the alignment of two readings of parallel cells — the exact alignment the vcomp seam consumes — a THEOREM,
    killing the r19 "common-refinement re-slice" obstruction: gap geometry is boundary-determined.
  * **`segmentRuns` / `interleave_segmentRuns`** — the run segmentation of a pushout 1-cell and its round-trip
    (via `pushoutPathWord_injective`), feeding the reader's `id` arm.

Raw Lean 4 + Init.  STRUCTURAL throughout (nested list/path inductions, no well-founded recursion).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The wall-free gap slot -/

/-- ★ **A wall-free gap slot** — one gap of a flat wall/gap layout: a parallel pair of WALL-FREE pushout
1-cells and the gap's payload cell between them.  Wall-freeness is carried as data, so every gap payload
descends to the monad component by the shipped `wallFreeCellInvert`. -/
structure GapSlot : Type where
  /-- The gap's domain run. -/
  gapDom : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode
  /-- The gap's codomain run. -/
  gapCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode
  /-- The domain run is wall-free (pure component 2). -/
  domWallFree : pathWallFree gapDom
  /-- The codomain run is wall-free (pure component 2). -/
  codWallFree : pathWallFree gapCod
  /-- The gap's payload cell. -/
  payload : RawTwoCellExpr involutionMonadPushout.toModeSignature gapDom gapCod

/-! ## The flat wall/gap layout -/

/-- The **run interleave** — the pushout 1-cell `run₀ · s · run₁ · s · … · runₙ` (single `s`-walls between
consecutive runs, right-nested so composition is definitional). -/
def interleaveRuns (headRun : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) →
    ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode
  | [] => headRun
  | nextRun :: restRuns => composePath headRun (composePath monadPushSPath (interleaveRuns nextRun restRuns))

/-- The **domain boundary** of a slot layout — the interleave of the slots' domain runs. -/
def flatSlotsDom (headSlot : GapSlot) (tailSlots : List GapSlot) :
    ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  interleaveRuns headSlot.gapDom (tailSlots.map GapSlot.gapDom)

/-- The **codomain boundary** of a slot layout — the interleave of the slots' codomain runs. -/
def flatSlotsCod (headSlot : GapSlot) (tailSlots : List GapSlot) :
    ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  interleaveRuns headSlot.gapCod (tailSlots.map GapSlot.gapCod)

/-- ★ **The flat wall/gap layout CELL** — the gap payloads horizontally interleaved with inert single
`s`-walls: `payload₀ ⊠ id s ⊠ payload₁ ⊠ … ⊠ payloadₙ`, right-nested.  Every boundary composes definitionally
with `flatSlotsDom` / `flatSlotsCod`. -/
def flatSlotsCell (headSlot : GapSlot) :
    (tailSlots : List GapSlot) →
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (flatSlotsDom headSlot tailSlots) (flatSlotsCod headSlot tailSlots)
  | [] => headSlot.payload
  | nextSlot :: restSlots =>
      RawTwoCellExpr.hcomp headSlot.payload
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
          (flatSlotsCell nextSlot restSlots))

/-! ## The word coordinates of wall-free runs and interleaves -/

/-- The pure-`t` word of a given length. -/
def tRunWord : Nat → List (Fin involutionMonadPushout.modalityGenerators.length)
  | 0 => []
  | count + 1 => tLetter :: tRunWord count

/-- The word of an interleave, computed from the runs' LENGTHS: `t^n₀ · s · t^n₁ · s · …`. -/
def runsWord (headLength : Nat) : List Nat → List (Fin involutionMonadPushout.modalityGenerators.length)
  | [] => tRunWord headLength
  | nextLength :: restLengths => tRunWord headLength ++ (sLetter :: runsWord nextLength restLengths)

/-- A wall-free letter IS the `t`-letter (`letterTag = false` forces the index off component 1, and the
two-letter alphabet pins it). -/
theorem wallFreeLetter_eq_tLetter
    (letter : Fin involutionMonadPushout.modalityGenerators.length)
    (wallFree : letterTag involutionMonadSplit letter = false) : letter = tLetter :=
  match letter, wallFree with
  | ⟨0, _⟩, wallFree => Bool.noConfusion wallFree
  | ⟨1, _⟩, _ => rfl
  | ⟨index + 2, isLt⟩, _ =>
      absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)) (Nat.not_lt_zero index)

/-- The boundary word of a wall-free pushout 1-cell is the pure-`t` word of its length. -/
theorem pushoutPathWord_wallFree :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pathWallFree path → pushoutPathWord path = tRunWord path.length
  | _, _, .nil _, _ => rfl
  | _, _, .cons letter rest, wallFree => by
    show letter.val :: pushoutPathWord rest = tLetter :: tRunWord rest.length
    rw [wallFreeLetter_eq_tLetter letter.val wallFree.1, pushoutPathWord_wallFree rest wallFree.2]

/-- ★ **A wall-free pushout run is DETERMINED by its length** — via `pushoutPathWord_injective` off the
pure-`t` word characterization. -/
theorem wallFreeRun_eq_of_length
    (runA runB : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (wallFreeA : pathWallFree runA) (wallFreeB : pathWallFree runB)
    (lengthsEqual : runA.length = runB.length) : runA = runB :=
  pushoutPathWord_injective runA runB
    ((pushoutPathWord_wallFree runA wallFreeA).trans
      (lengthsEqual ▸ (pushoutPathWord_wallFree runB wallFreeB).symm))

/-- The word of a composite pushout 1-cell is the concatenation of the words (cons-structural). -/
theorem pushoutPathWord_composePathHom :
    {modeA modeB modeC : Fin involutionMonadPushout.modeCount} →
    (first : ModalityPath involutionMonadPushout.toModeGraph modeA modeB) →
    (second : ModalityPath involutionMonadPushout.toModeGraph modeB modeC) →
    pushoutPathWord (composePath first second) = pushoutPathWord first ++ pushoutPathWord second
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons letter rest, second =>
      congrArg (letter.val :: ·) (pushoutPathWord_composePathHom rest second)

/-- The word of a wall-free-run interleave is `runsWord` of the runs' lengths.  The wall-freeness of every run
is threaded from a slot list. -/
theorem pushoutPathWord_flatDom (headSlot : GapSlot) :
    (tailSlots : List GapSlot) →
    pushoutPathWord (flatSlotsDom headSlot tailSlots)
      = runsWord headSlot.gapDom.length (tailSlots.map (fun slot => slot.gapDom.length))
  | [] => pushoutPathWord_wallFree headSlot.gapDom headSlot.domWallFree
  | nextSlot :: restSlots => by
    show pushoutPathWord
        (composePath headSlot.gapDom (composePath monadPushSPath (flatSlotsDom nextSlot restSlots)))
      = tRunWord headSlot.gapDom.length
          ++ (sLetter :: runsWord nextSlot.gapDom.length (restSlots.map (fun slot => slot.gapDom.length)))
    rw [pushoutPathWord_composePathHom headSlot.gapDom
        (composePath monadPushSPath (flatSlotsDom nextSlot restSlots)),
      pushoutPathWord_wallFree headSlot.gapDom headSlot.domWallFree]
    show tRunWord headSlot.gapDom.length ++ (sLetter :: pushoutPathWord (flatSlotsDom nextSlot restSlots))
      = tRunWord headSlot.gapDom.length
          ++ (sLetter :: runsWord nextSlot.gapDom.length (restSlots.map (fun slot => slot.gapDom.length)))
    rw [pushoutPathWord_flatDom nextSlot restSlots]

/-- The codomain twin of `pushoutPathWord_flatDom`. -/
theorem pushoutPathWord_flatCod (headSlot : GapSlot) :
    (tailSlots : List GapSlot) →
    pushoutPathWord (flatSlotsCod headSlot tailSlots)
      = runsWord headSlot.gapCod.length (tailSlots.map (fun slot => slot.gapCod.length))
  | [] => pushoutPathWord_wallFree headSlot.gapCod headSlot.codWallFree
  | nextSlot :: restSlots => by
    show pushoutPathWord
        (composePath headSlot.gapCod (composePath monadPushSPath (flatSlotsCod nextSlot restSlots)))
      = tRunWord headSlot.gapCod.length
          ++ (sLetter :: runsWord nextSlot.gapCod.length (restSlots.map (fun slot => slot.gapCod.length)))
    rw [pushoutPathWord_composePathHom headSlot.gapCod
        (composePath monadPushSPath (flatSlotsCod nextSlot restSlots)),
      pushoutPathWord_wallFree headSlot.gapCod headSlot.codWallFree]
    show tRunWord headSlot.gapCod.length ++ (sLetter :: pushoutPathWord (flatSlotsCod nextSlot restSlots))
      = tRunWord headSlot.gapCod.length
          ++ (sLetter :: runsWord nextSlot.gapCod.length (restSlots.map (fun slot => slot.gapCod.length)))
    rw [pushoutPathWord_flatCod nextSlot restSlots]

/-! ## Word-level parsing uniqueness -/

/-- The two letters differ: `s` is not `t`. -/
theorem sLetter_ne_tLetter : sLetter = tLetter → False :=
  fun equal => Nat.noConfusion (congrArg Fin.val equal)

/-- `runsWord` at head length zero and an empty list is the empty word (`rfl`). -/
theorem runsWord_zero_nil : runsWord 0 [] = [] := rfl

/-- `runsWord` at head length zero and a cons list starts with the `s`-wall (`rfl`). -/
theorem runsWord_zero_cons (nextLength : Nat) (restLengths : List Nat) :
    runsWord 0 (nextLength :: restLengths) = sLetter :: runsWord nextLength restLengths := rfl

/-- `runsWord` peels a `t` off a positive head length regardless of the list (cases; `rfl`). -/
theorem runsWord_succPeel (headLength : Nat) :
    (restLengths : List Nat) →
    runsWord (headLength + 1) restLengths = tLetter :: runsWord headLength restLengths
  | [] => rfl
  | _ :: _ => rfl

/-- ★★ **PARSING UNIQUENESS at the word level** — a `runsWord` presentation is unique: equal interleave words
force equal head lengths and equal run-length lists.  Nested structural induction: OUTER on the run-length list
(the wall count), INNER on the head length (the head run); every case first normalizes the word equation to
constructor form by the three peel equations. -/
theorem runsWord_parse_unique :
    (restLengths restLengths' : List Nat) → (headLength headLength' : Nat) →
    runsWord headLength restLengths = runsWord headLength' restLengths' →
    headLength = headLength' ∧ restLengths = restLengths' := by
  intro restLengths
  induction restLengths with
  | nil =>
    intro restLengths' headLength
    induction headLength with
    | zero =>
      intro headLength' equalWords
      cases restLengths' with
      | nil =>
        cases headLength' with
        | zero => exact ⟨rfl, rfl⟩
        | succ headLength' =>
          rw [runsWord_zero_nil, runsWord_succPeel headLength' []] at equalWords
          exact Nat.noConfusion (congrArg List.length equalWords)
      | cons nextLength' restLengths' =>
        cases headLength' with
        | zero =>
          rw [runsWord_zero_nil, runsWord_zero_cons nextLength' restLengths'] at equalWords
          exact Nat.noConfusion (congrArg List.length equalWords)
        | succ headLength' =>
          rw [runsWord_zero_nil, runsWord_succPeel headLength' (nextLength' :: restLengths')] at equalWords
          exact Nat.noConfusion (congrArg List.length equalWords)
    | succ headLength innerIH =>
      intro headLength' equalWords
      rw [runsWord_succPeel headLength []] at equalWords
      cases headLength' with
      | zero =>
        cases restLengths' with
        | nil =>
          rw [runsWord_zero_nil] at equalWords
          exact Nat.noConfusion (congrArg List.length equalWords)
        | cons nextLength' restLengths' =>
          rw [runsWord_zero_cons nextLength' restLengths'] at equalWords
          injection equalWords with headLetterEq _
          exact absurd headLetterEq.symm sLetter_ne_tLetter
      | succ headLength' =>
        rw [runsWord_succPeel headLength' restLengths'] at equalWords
        injection equalWords with _ tailWordEq
        obtain ⟨headEq, restEq⟩ := innerIH headLength' tailWordEq
        exact ⟨congrArg Nat.succ headEq, restEq⟩
  | cons nextLength restLengths outerIH =>
    intro restLengths' headLength
    induction headLength with
    | zero =>
      intro headLength' equalWords
      rw [runsWord_zero_cons nextLength restLengths] at equalWords
      cases headLength' with
      | zero =>
        cases restLengths' with
        | nil =>
          rw [runsWord_zero_nil] at equalWords
          exact Nat.noConfusion (congrArg List.length equalWords)
        | cons nextLength' restLengths' =>
          rw [runsWord_zero_cons nextLength' restLengths'] at equalWords
          injection equalWords with _ tailWordEq
          obtain ⟨nextEq, restEq⟩ := outerIH restLengths' nextLength nextLength' tailWordEq
          exact ⟨rfl, by rw [nextEq, restEq]⟩
      | succ headLength' =>
        rw [runsWord_succPeel headLength' restLengths'] at equalWords
        injection equalWords with headLetterEq _
        exact absurd headLetterEq sLetter_ne_tLetter
    | succ headLength innerIH =>
      intro headLength' equalWords
      rw [runsWord_succPeel headLength (nextLength :: restLengths)] at equalWords
      cases headLength' with
      | zero =>
        cases restLengths' with
        | nil =>
          rw [runsWord_zero_nil] at equalWords
          exact Nat.noConfusion (congrArg List.length equalWords)
        | cons nextLength' restLengths' =>
          rw [runsWord_zero_cons nextLength' restLengths'] at equalWords
          injection equalWords with headLetterEq _
          exact absurd headLetterEq.symm sLetter_ne_tLetter
      | succ headLength' =>
        rw [runsWord_succPeel headLength' restLengths'] at equalWords
        injection equalWords with _ tailWordEq
        obtain ⟨headEq, restEq⟩ := innerIH headLength' tailWordEq
        exact ⟨congrArg Nat.succ headEq, restEq⟩

/-! ## The slot alignment: gap geometry is boundary-determined -/

/-- Pointwise alignment of two slot lists off their length lists: equal gap-boundary length lists force equal
gap-boundary PATH lists (wall-free runs are length-determined).  Stated for a cod-side list against a dom-side
list — the exact zip the vcomp seam consumes. -/
theorem slotRuns_aligned_of_lengths :
    (upTail loTail : List GapSlot) →
    upTail.map (fun slot => slot.gapCod.length) = loTail.map (fun slot => slot.gapDom.length) →
    upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom
  | [], [], _ => rfl
  | [], _ :: _, hmap => Nat.noConfusion (congrArg List.length hmap)
  | _ :: _, [], hmap => Nat.noConfusion (congrArg List.length hmap)
  | upSlot :: upRest, loSlot :: loRest, hmap => by
    injection hmap with headLenEq tailMapEq
    show upSlot.gapCod :: upRest.map GapSlot.gapCod = loSlot.gapDom :: loRest.map GapSlot.gapDom
    rw [wallFreeRun_eq_of_length upSlot.gapCod loSlot.gapDom upSlot.codWallFree loSlot.domWallFree headLenEq,
      slotRuns_aligned_of_lengths upRest loRest tailMapEq]

/-- ★★★ **PARSING UNIQUENESS — the slot boundaries are ALIGNED by the assembled 1-cell.**  If the codomain
boundary of one slot layout equals the domain boundary of another (the shared middle of a vertical composite),
then the head runs agree and the tail runs agree POINTWISE.  This is the boundary-determined-geometry theorem
the vcomp zip consumes: two readings meeting at a shared 1-cell automatically share their gap skeleton. -/
theorem flatBoundary_slots_aligned (upHead loHead : GapSlot) (upTail loTail : List GapSlot)
    (middleEq : flatSlotsCod upHead upTail = flatSlotsDom loHead loTail) :
    upHead.gapCod = loHead.gapDom ∧ upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom := by
  have wordEq := congrArg pushoutPathWord middleEq
  rw [pushoutPathWord_flatCod upHead upTail, pushoutPathWord_flatDom loHead loTail] at wordEq
  obtain ⟨headLenEq, tailLensEq⟩ :=
    runsWord_parse_unique (upTail.map (fun slot => slot.gapCod.length))
      (loTail.map (fun slot => slot.gapDom.length)) upHead.gapCod.length loHead.gapDom.length wordEq
  exact ⟨wallFreeRun_eq_of_length upHead.gapCod loHead.gapDom upHead.codWallFree loHead.domWallFree headLenEq,
    slotRuns_aligned_of_lengths upTail loTail tailLensEq⟩

/-! ## The segmentation and its round-trip -/

/-- **The run segmentation** — read a pushout 1-cell into its wall-free runs: an `s`-letter (component tag
`true`) closes the current head run; a `t`-letter (tag `false`) extends it with the anchored `t`-generator.
Head-first, so the `s`-cons and `t`-cons equations are DEFINITIONAL. -/
def segmentRuns : {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode →
    ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode
      × List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
  | _, _, .nil _ => (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode, [])
  | _, _, .cons letter rest =>
      bif letterTag involutionMonadSplit letter.val then
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode,
          (segmentRuns rest).1 :: (segmentRuns rest).2)
      else
        (ModalityPath.cons monadPushTModality (segmentRuns rest).1, (segmentRuns rest).2)

/-- All-runs wall-freeness of the segmentation, as a structural predicate on the tail list. -/
inductive AllRunsWallFree :
    List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) → Prop where
  | nil : AllRunsWallFree []
  | cons (run : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
      (rest : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) :
      pathWallFree run → AllRunsWallFree rest → AllRunsWallFree (run :: rest)

/-- The segmentation's runs are all wall-free (head + tail list). -/
theorem segmentRuns_allWallFree :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pathWallFree (segmentRuns path).1 ∧ AllRunsWallFree (segmentRuns path).2
  | _, _, .nil _ => ⟨True.intro, AllRunsWallFree.nil⟩
  | _, _, .cons letter rest =>
    match letter with
    | ⟨⟨0, _⟩, _⟩ =>
      ⟨True.intro,
        AllRunsWallFree.cons _ _ (segmentRuns_allWallFree rest).1 (segmentRuns_allWallFree rest).2⟩
    | ⟨⟨1, _⟩, _⟩ =>
      ⟨⟨rfl, (segmentRuns_allWallFree rest).1⟩, (segmentRuns_allWallFree rest).2⟩
    | ⟨⟨index + 2, isLtBig⟩, _⟩ =>
      absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLtBig)) (Nat.not_lt_zero index)

/-- The segmentation's word round-trip: `runsWord` of the segmented lengths is the path's own word.  Structural
on the path; letters are cased by the two-letter alphabet so the component `bif` reduces definitionally. -/
theorem runsWord_segmentRuns :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    runsWord (segmentRuns path).1.length ((segmentRuns path).2.map ModalityPath.length)
      = pushoutPathWord path
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest =>
    match letter with
    | ⟨⟨0, _⟩, _⟩ => congrArg (sLetter :: ·) (runsWord_segmentRuns rest)
    | ⟨⟨1, _⟩, _⟩ =>
      (runsWord_succPeel (segmentRuns rest).1.length
          ((segmentRuns rest).2.map ModalityPath.length)).trans
        (congrArg (tLetter :: ·) (runsWord_segmentRuns rest))
    | ⟨⟨index + 2, isLtBig⟩, _⟩ =>
      absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLtBig)) (Nat.not_lt_zero index)

/-- The word of a wall-free-run interleave, threaded from a wall-freeness list (the segmentation variant of
`pushoutPathWord_flatDom`, over bare run lists). -/
theorem pushoutPathWord_interleaveRuns
    (headRun : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (headWallFree : pathWallFree headRun) :
    (restRuns : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) →
    AllRunsWallFree restRuns →
    pushoutPathWord (interleaveRuns headRun restRuns)
      = runsWord headRun.length (restRuns.map ModalityPath.length)
  | [], _ => pushoutPathWord_wallFree headRun headWallFree
  | nextRun :: restRuns, AllRunsWallFree.cons _ _ nextWallFree restWallFree => by
    show pushoutPathWord (composePath headRun (composePath monadPushSPath (interleaveRuns nextRun restRuns)))
      = tRunWord headRun.length ++ (sLetter :: runsWord nextRun.length (restRuns.map ModalityPath.length))
    rw [pushoutPathWord_composePathHom headRun (composePath monadPushSPath (interleaveRuns nextRun restRuns)),
      pushoutPathWord_wallFree headRun headWallFree]
    show tRunWord headRun.length ++ (sLetter :: pushoutPathWord (interleaveRuns nextRun restRuns))
      = tRunWord headRun.length ++ (sLetter :: runsWord nextRun.length (restRuns.map ModalityPath.length))
    rw [pushoutPathWord_interleaveRuns nextRun nextWallFree restRuns restWallFree]

/-- ★★ **The segmentation ROUND-TRIP** — interleaving the segmented runs reassembles the 1-cell
(`pushoutPathWord_injective` off the word round-trip). -/
theorem interleave_segmentRuns
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    interleaveRuns (segmentRuns path).1 (segmentRuns path).2 = path :=
  pushoutPathWord_injective _ path
    ((pushoutPathWord_interleaveRuns (segmentRuns path).1 (segmentRuns_allWallFree path).1
        (segmentRuns path).2 (segmentRuns_allWallFree path).2).trans
      (runsWord_segmentRuns path))

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the wall-free gap-slot substrate SHIPS (WP-AMALG r30, Brick A).**  `= true`.  The
wall-free gap slot (`GapSlot` — payloads descend to the monad component by the shipped `wallFreeCellInvert`),
the flat wall/gap layout (`interleaveRuns` / `flatSlotsDom` / `flatSlotsCod` / `flatSlotsCell`, right-nested
definitional boundaries), the length coordinate (`wallFreeRun_eq_of_length` — a gap's geometry is one `Nat`),
word-level PARSING UNIQUENESS (`runsWord_parse_unique` / `flatBoundary_slots_aligned` — gap geometry is
boundary-determined, so two readings meeting at a shared 1-cell share their gap skeleton: the r19 vcomp
"common-refinement re-slice" obstruction dissolves at this representation), and the segmentation round-trip
(`segmentRuns` / `interleave_segmentRuns`).  Substrate only — the reader, the zip, and the decider are the
successor bricks; NO master flips here.  `= true`. -/
def fxAmalg_hasRunSlotSubstrate : Bool := true

end FX1Poly.Polygraph.Amalgam
