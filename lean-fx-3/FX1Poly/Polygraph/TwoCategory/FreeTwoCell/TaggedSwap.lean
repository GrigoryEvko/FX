import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpinePathChain

/-! # TaggedSwap — occurrence-tagged atomic swaps + the tag-count class invariant

The Mazurkiewicz occurrence-tracking route distinguishes the members of a trace class by
WHICH seed occurrence sits where: atoms carry an occurrence tag, swaps transpose tagged atoms
(mutating the whisker contexts exactly as the untagged swap does), and the tag order becomes
the coordinate the determination rung reads a class member off from.  This file ships the
tagged data layer and its two projection invariants:

  * `TaggedSpineAtom` — an occurrence tag paired with a spine atom;
  * `untagSpineAtoms` / `spineTagList` — the two cons-only projections (atoms, tags);
  * `tagSpineAtomsFrom` — the seed tagging (consecutive tags from a start), with the
    round-trip `untagSpineAtoms_tagSpineAtomsFrom`;
  * `TaggedSpineAtomSwap` — the tagged adjacent transposition (the untagged swap's context
    algebra verbatim, tags riding along), with `TaggedTraceEquiv` its reflexive-symmetric-
    transitive-cons closure;
  * `TaggedSpineAtomSwap.untagged` / `TaggedTraceEquiv.untagged` — the atom projection is
    ctor-for-ctor: tagged rewriting IS the shipped atomic rewriting below the tags;
  * `natCount` + `natCount_transpose` — the hand-rolled occurrence counter on tag lists (a
    `cond`/`Nat.beq` fold; the transposition case is one `Nat.add_left_comm`);
  * ★ `TaggedSpineAtomSwap.preservesTagCount` / `TaggedTraceEquiv.preservesTagCount` — tag
    COUNTS are a class invariant: a member's tags are always a rearrangement of the seed's
    (the finite skeleton the enumeration bound and the dup-freedom rungs stand on).

The path-level chain invariant transfers to tagged traces for free through `untagged` and
the shipped `AtomicTraceEquiv.pathChainedTransfer`.  The next rung is determination: a
CHAINED tagged trace is determined by its tag order.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The tagged atom + the two projections -/

/-- A spine atom carrying its occurrence tag (its identity as a seed occurrence, stable
across swaps). -/
structure TaggedSpineAtom (signature : ModeSignature)
    (sourceMode targetMode : signature.graph.Mode) where
  /-- The occurrence tag — which seed occurrence this atom is. -/
  occurrenceTag : Nat
  /-- The atom itself (whisker contexts mutate as it swaps; the tag does not). -/
  atom : SpineAtom signature sourceMode targetMode

/-- Forget the tags (cons-only recursion). -/
def untagSpineAtoms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    List (TaggedSpineAtom signature sourceMode targetMode) →
    List (SpineAtom signature sourceMode targetMode)
  | [] => []
  | taggedAtom :: rest => taggedAtom.atom :: untagSpineAtoms rest

/-- Project the tag order (cons-only recursion). -/
def spineTagList {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    List (TaggedSpineAtom signature sourceMode targetMode) → List Nat
  | [] => []
  | taggedAtom :: rest => taggedAtom.occurrenceTag :: spineTagList rest

/-- Tag a seed trace with consecutive occurrence tags from a start value. -/
def tagSpineAtomsFrom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    Nat → List (SpineAtom signature sourceMode targetMode) →
    List (TaggedSpineAtom signature sourceMode targetMode)
  | _, [] => []
  | startTag, atom :: rest => ⟨startTag, atom⟩ :: tagSpineAtomsFrom (Nat.succ startTag) rest

/-- Tagging then untagging is the identity — the seed tagging loses no atoms. -/
theorem untagSpineAtoms_tagSpineAtomsFrom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    ∀ (startTag : Nat), untagSpineAtoms (tagSpineAtomsFrom startTag atoms) = atoms := by
  induction atoms with
  | nil => intro _; rfl
  | cons atom rest innerHypothesis =>
      intro startTag
      exact congrArg (List.cons atom) (innerHypothesis (Nat.succ startTag))

/-! ## The tagged swap + its closure -/

/-- **The tagged adjacent transposition**: the shipped `SpineAtomSwap` context algebra
verbatim — the left atom's right context tracks the right generator's state
(`gLow ↝ gMid`), the right atom's left context tracks the left generator's state
(`fHigh ↝ fMid`) — with the occurrence tags riding along their atoms. -/
inductive TaggedSpineAtomSwap (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (TaggedSpineAtom signature overallSource overallTarget) →
    List (TaggedSpineAtom signature overallSource overallTarget) → Prop where
  /-- Transpose two adjacent horizontally-independent tagged generator atoms. -/
  | swap {swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode : signature.graph.Mode}
      {oneCellFMid oneCellFHigh : ModalityPath signature.graph swapSourceMode swapMiddleLeft}
      {oneCellGLow oneCellGMid : ModalityPath signature.graph swapMiddleRight swapTargetMode}
      (generatorLeft : signature.twoCell oneCellFMid oneCellFHigh)
      (generatorRight : signature.twoCell oneCellGLow oneCellGMid)
      (leftTag rightTag : Nat)
      (leftAcc : ModalityPath signature.graph overallSource swapSourceMode)
      (inertPath : ModalityPath signature.graph swapMiddleLeft swapMiddleRight)
      (rightAcc : ModalityPath signature.graph swapTargetMode overallTarget)
      (rest : List (TaggedSpineAtom signature overallSource overallTarget)) :
      TaggedSpineAtomSwap signature
        (⟨leftTag, ⟨_, _, leftAcc, _, _, generatorLeft,
            composePath (composePath inertPath oneCellGLow) rightAcc⟩⟩ ::
          ⟨rightTag, ⟨_, _, composePath (composePath leftAcc oneCellFHigh) inertPath, _, _,
            generatorRight, rightAcc⟩⟩ :: rest)
        (⟨rightTag, ⟨_, _, composePath (composePath leftAcc oneCellFMid) inertPath, _, _,
            generatorRight, rightAcc⟩⟩ ::
          ⟨leftTag, ⟨_, _, leftAcc, _, _, generatorLeft,
            composePath (composePath inertPath oneCellGMid) rightAcc⟩⟩ :: rest)

/-- **The tagged trace equivalence** — the reflexive-symmetric-transitive closure of the
tagged swap, plus the head-cons congruence, mirroring `AtomicTraceEquiv`. -/
inductive TaggedTraceEquiv (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (TaggedSpineAtom signature overallSource overallTarget) →
    List (TaggedSpineAtom signature overallSource overallTarget) → Prop where
  /-- A single tagged adjacent swap. -/
  | ofSwap {firstList secondList :
      List (TaggedSpineAtom signature overallSource overallTarget)} :
      TaggedSpineAtomSwap signature firstList secondList →
      TaggedTraceEquiv signature firstList secondList
  /-- Reflexivity. -/
  | refl (taggedList : List (TaggedSpineAtom signature overallSource overallTarget)) :
      TaggedTraceEquiv signature taggedList taggedList
  /-- Symmetry. -/
  | symm {firstList secondList :
      List (TaggedSpineAtom signature overallSource overallTarget)} :
      TaggedTraceEquiv signature firstList secondList →
      TaggedTraceEquiv signature secondList firstList
  /-- Transitivity. -/
  | trans {firstList secondList thirdList :
      List (TaggedSpineAtom signature overallSource overallTarget)} :
      TaggedTraceEquiv signature firstList secondList →
      TaggedTraceEquiv signature secondList thirdList →
      TaggedTraceEquiv signature firstList thirdList
  /-- A head tagged atom passes through (independent prefix). -/
  | consCongr (taggedAtom : TaggedSpineAtom signature overallSource overallTarget)
      {firstList secondList :
        List (TaggedSpineAtom signature overallSource overallTarget)} :
      TaggedTraceEquiv signature firstList secondList →
      TaggedTraceEquiv signature (taggedAtom :: firstList) (taggedAtom :: secondList)

/-! ## The atom projection is ctor-for-ctor -/

/-- Untagging a tagged swap yields the shipped atomic swap — the context algebra is
verbatim, so the projected lists ARE the untagged constructor's shapes. -/
theorem TaggedSpineAtomSwap.untagged {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (taggedStep : TaggedSpineAtomSwap signature firstList secondList) :
    SpineAtomSwap signature (untagSpineAtoms firstList) (untagSpineAtoms secondList) := by
  cases taggedStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftTag rightTag
      leftAcc inertPath rightAcc rest =>
      exact SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath rightAcc
        (untagSpineAtoms rest)

/-- Untagging a tagged trace equivalence yields the shipped atomic trace equivalence —
closure operators map one-to-one. -/
theorem TaggedTraceEquiv.untagged {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (taggedEquiv : TaggedTraceEquiv signature firstList secondList) :
    AtomicTraceEquiv signature (untagSpineAtoms firstList) (untagSpineAtoms secondList) := by
  induction taggedEquiv with
  | ofSwap taggedStep => exact AtomicTraceEquiv.ofSwap taggedStep.untagged
  | refl taggedList => exact AtomicTraceEquiv.refl (untagSpineAtoms taggedList)
  | symm _ innerHypothesis => exact AtomicTraceEquiv.symm innerHypothesis
  | trans _ _ firstHypothesis secondHypothesis =>
      exact AtomicTraceEquiv.trans firstHypothesis secondHypothesis
  | consCongr taggedAtom _ innerHypothesis =>
      exact AtomicTraceEquiv.consCongr taggedAtom.atom innerHypothesis

/-! ## The tag-count invariant -/

/-- Count the occurrences of a tag in a tag list (a `cond`/`Nat.beq` fold — hand-rolled so
every proof below is structural). -/
def natCount (target : Nat) : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.add (cond (Nat.beq head target) 1 0) (natCount target tail)

/-- Counting is blind to an adjacent transposition — one `Nat.add_left_comm`. -/
theorem natCount_transpose (target firstTag secondTag : Nat) (tags : List Nat) :
    natCount target (firstTag :: secondTag :: tags)
      = natCount target (secondTag :: firstTag :: tags) := by
  dsimp only [natCount]
  exact Nat.add_left_comm (cond (Nat.beq firstTag target) 1 0)
    (cond (Nat.beq secondTag target) 1 0) (natCount target tags)

/-- One tagged swap preserves every tag count. -/
theorem TaggedSpineAtomSwap.preservesTagCount {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (taggedStep : TaggedSpineAtomSwap signature firstList secondList) (target : Nat) :
    natCount target (spineTagList firstList) = natCount target (spineTagList secondList) := by
  cases taggedStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftTag rightTag
      leftAcc inertPath rightAcc rest =>
      exact natCount_transpose target leftTag rightTag (spineTagList rest)

/-- ★ **Tag counts are a class invariant**: every member of a tagged trace class carries a
rearrangement of the seed's tags — no occurrence is created, dropped, or relabeled. -/
theorem TaggedTraceEquiv.preservesTagCount {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (taggedEquiv : TaggedTraceEquiv signature firstList secondList) (target : Nat) :
    natCount target (spineTagList firstList) = natCount target (spineTagList secondList) := by
  induction taggedEquiv with
  | ofSwap taggedStep => exact taggedStep.preservesTagCount target
  | refl _ => rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr taggedAtom _ innerHypothesis =>
      exact congrArg
        (Nat.add (cond (Nat.beq taggedAtom.occurrenceTag target) 1 0)) innerHypothesis

/-! ## The tagging lift -/

/-- Cons inversion for the untag projection: a tagged list projecting to a cons splits as a
tagged head over a tail projecting to the tail (the head atom pinned by structure eta). -/
theorem untagSpineAtoms_cons_inversion {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {taggedList : List (TaggedSpineAtom signature sourceMode targetMode)}
    {headAtom : SpineAtom signature sourceMode targetMode}
    {tailAtoms : List (SpineAtom signature sourceMode targetMode)}
    (projectsToCons : untagSpineAtoms taggedList = headAtom :: tailAtoms) :
    ∃ (headTag : Nat)
      (taggedRest : List (TaggedSpineAtom signature sourceMode targetMode)),
      taggedList = ⟨headTag, headAtom⟩ :: taggedRest
        ∧ untagSpineAtoms taggedRest = tailAtoms := by
  cases taggedList with
  | nil => exact nomatch projectsToCons
  | cons taggedHead taggedRest =>
      injection projectsToCons with headEq tailEq
      exact ⟨taggedHead.occurrenceTag, taggedRest, by rw [← headEq], tailEq⟩

/-- ★ **The tagging lift**: an atomic trace equivalence lifts along ANY tagging of either
side — the tagged closure covers the untagged one over every tagging.  Both directions ride
together through the symmetric closure; the tagging stays universally quantified in the
conclusion so the swap and cons arms can invert it against their list shapes. -/
theorem AtomicTraceEquiv.liftTagged {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtoms secondAtoms : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstAtoms secondAtoms) :
    (∀ (firstTagged : List (TaggedSpineAtom signature overallSource overallTarget)),
        untagSpineAtoms firstTagged = firstAtoms →
        ∃ (secondTagged : List (TaggedSpineAtom signature overallSource overallTarget)),
          untagSpineAtoms secondTagged = secondAtoms
            ∧ TaggedTraceEquiv signature firstTagged secondTagged)
      ∧ (∀ (secondTagged : List (TaggedSpineAtom signature overallSource overallTarget)),
        untagSpineAtoms secondTagged = secondAtoms →
        ∃ (firstTagged : List (TaggedSpineAtom signature overallSource overallTarget)),
          untagSpineAtoms firstTagged = firstAtoms
            ∧ TaggedTraceEquiv signature firstTagged secondTagged) := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
          oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc
          inertPath rightAcc rest =>
          constructor
          · intro firstTagged untagEq
            obtain ⟨leftTag, taggedTail, taggedShape, tailProjects⟩ :=
              untagSpineAtoms_cons_inversion untagEq
            obtain ⟨rightTag, taggedRest, tailShape, restProjects⟩ :=
              untagSpineAtoms_cons_inversion tailProjects
            subst taggedShape
            subst tailShape
            refine ⟨_, ?_, TaggedTraceEquiv.ofSwap
              (TaggedSpineAtomSwap.swap generatorLeft generatorRight leftTag rightTag
                leftAcc inertPath rightAcc taggedRest)⟩
            dsimp only [untagSpineAtoms]
            rw [restProjects]
          · intro secondTagged untagEq
            obtain ⟨movedTag, taggedTail, taggedShape, tailProjects⟩ :=
              untagSpineAtoms_cons_inversion untagEq
            obtain ⟨stayedTag, taggedRest, tailShape, restProjects⟩ :=
              untagSpineAtoms_cons_inversion tailProjects
            subst taggedShape
            subst tailShape
            refine ⟨_, ?_, TaggedTraceEquiv.ofSwap
              (TaggedSpineAtomSwap.swap generatorLeft generatorRight stayedTag movedTag
                leftAcc inertPath rightAcc taggedRest)⟩
            dsimp only [untagSpineAtoms]
            rw [restProjects]
  | refl _ =>
      exact ⟨fun tagged untagEq => ⟨tagged, untagEq, TaggedTraceEquiv.refl tagged⟩,
        fun tagged untagEq => ⟨tagged, untagEq, TaggedTraceEquiv.refl tagged⟩⟩
  | symm _ innerHypothesis =>
      refine ⟨fun tagged untagEq => ?forward, fun tagged untagEq => ?backward⟩
      case forward =>
          obtain ⟨liftedTagged, liftedProjects, liftedEquiv⟩ :=
            innerHypothesis.2 tagged untagEq
          exact ⟨liftedTagged, liftedProjects, liftedEquiv.symm⟩
      case backward =>
          obtain ⟨liftedTagged, liftedProjects, liftedEquiv⟩ :=
            innerHypothesis.1 tagged untagEq
          exact ⟨liftedTagged, liftedProjects, liftedEquiv.symm⟩
  | trans _ _ firstHypothesis secondHypothesis =>
      refine ⟨fun tagged untagEq => ?forward, fun tagged untagEq => ?backward⟩
      case forward =>
          obtain ⟨middleTagged, middleProjects, firstLeg⟩ :=
            firstHypothesis.1 tagged untagEq
          obtain ⟨finalTagged, finalProjects, secondLeg⟩ :=
            secondHypothesis.1 middleTagged middleProjects
          exact ⟨finalTagged, finalProjects, firstLeg.trans secondLeg⟩
      case backward =>
          obtain ⟨middleTagged, middleProjects, secondLeg⟩ :=
            secondHypothesis.2 tagged untagEq
          obtain ⟨startTagged, startProjects, firstLeg⟩ :=
            firstHypothesis.2 middleTagged middleProjects
          exact ⟨startTagged, startProjects, firstLeg.trans secondLeg⟩
  | consCongr atom _ innerHypothesis =>
      refine ⟨fun tagged untagEq => ?forward, fun tagged untagEq => ?backward⟩
      case forward =>
          obtain ⟨headTag, taggedRest, taggedShape, restProjects⟩ :=
            untagSpineAtoms_cons_inversion untagEq
          obtain ⟨liftedRest, liftedProjects, liftedEquiv⟩ :=
            innerHypothesis.1 taggedRest restProjects
          subst taggedShape
          exact ⟨⟨headTag, atom⟩ :: liftedRest,
            congrArg (List.cons atom) liftedProjects,
            TaggedTraceEquiv.consCongr ⟨headTag, atom⟩ liftedEquiv⟩
      case backward =>
          obtain ⟨headTag, taggedRest, taggedShape, restProjects⟩ :=
            untagSpineAtoms_cons_inversion untagEq
          obtain ⟨liftedRest, liftedProjects, liftedEquiv⟩ :=
            innerHypothesis.2 taggedRest restProjects
          subst taggedShape
          exact ⟨⟨headTag, atom⟩ :: liftedRest,
            congrArg (List.cons atom) liftedProjects,
            TaggedTraceEquiv.consCongr ⟨headTag, atom⟩ liftedEquiv⟩

/-! ## Chaining transfers to tagged traces for free -/

/-- The path-level chain invariant holds across a tagged trace class, through the atom
projection and the shipped untagged transfer. -/
theorem TaggedTraceEquiv.pathChainedTransfer {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (TaggedSpineAtom signature overallSource overallTarget)}
    (taggedEquiv : TaggedTraceEquiv signature firstList secondList)
    (boundaryPath : ModalityPath signature.graph overallSource overallTarget) :
    (SpinePathChained boundaryPath (untagSpineAtoms firstList)
        → SpinePathChained boundaryPath (untagSpineAtoms secondList))
      ∧ (SpinePathChained boundaryPath (untagSpineAtoms secondList)
        → SpinePathChained boundaryPath (untagSpineAtoms firstList)) :=
  taggedEquiv.untagged.pathChainedTransfer boundaryPath

end FX1Poly.Polygraph
