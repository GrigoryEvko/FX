import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingInterfaceTransfer

/-! # MatchingFoldRename — fold-rename equivariance of the empty-base event fold (MODE3-D)

The relative run's trace is the pointwise `sigma` pair-rename of the canonical run's trace
(`spineJoinEvents_ofRelativeWireSim`), so the VIEW-leg segment transfer must move empty-base
fold connectivity between a trace and its rename.  This file ships that equivariance: for an
INJECTIVE rename, the empty-base fold's component view is invariant under the pointwise
pair-rename —

* `renamedJoinEventPath_ofCanonicalPath` / `renamedFoldConnected_ofCanonicalFold` — the easy
  direction (no injectivity): canonical path steps map forward (empty-base steps are
  equalities, event steps by map membership introduction) and reassemble;
* `canonicalFoldConnected_ofRenamedPath` / `canonicalFoldConnected_ofRenamedFold` — the hard
  direction: a preimage-tracking walk over the renamed path.  Empty-base steps over `[]` force
  node equality, so the walk never leaves the rename's image; each renamed event decomposes
  through map membership into a canonical event whose endpoints injectivity pins to the
  tracked preimage;
* ★ `componentView_applyJoinEvents_ofRename` — the Bool-level equivariance, both directions
  glued.

The rename shape `(events.map (fun event => (sigma event.1, sigma event.2)))` is EXACTLY the
D3 trace-correspondence shape, so the D5 instantiation composes with
`spineJoinEvents_ofRelativeWireSim` with no reshaping.  Raw Lean 4 + Init; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (core map/membership lemmas leak propext) -/

private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

/-- Map membership elimination: a member of a mapped list is the image of a member. -/
private theorem memberOfMapExists {Element ResultElement : Type}
    (mapper : Element → ResultElement) :
    (elements : List Element) → (mapped : ResultElement) →
    mapped ∈ List.map mapper elements →
    ∃ element : Element, element ∈ elements ∧ mapper element = mapped := by
  intro elements
  induction elements with
  | nil =>
      intro mapped absurdMembership
      cases absurdMembership
  | cons headElement restElements restExists =>
      intro mapped membership
      cases membership with
      | head => exact ⟨headElement, List.Mem.head restElements, rfl⟩
      | tail _ restMembership =>
          obtain ⟨element, elementListed, mapsTo⟩ := restExists mapped restMembership
          exact ⟨element, List.Mem.tail headElement elementListed, mapsTo⟩

/-- Map membership introduction: the image of a member is a member of the mapped list. -/
private theorem memberOfMapIntro {Element ResultElement : Type}
    (mapper : Element → ResultElement) (elements : List Element) (element : Element)
    (elementListed : element ∈ elements) :
    mapper element ∈ List.map mapper elements := by
  induction elementListed with
  | head restElements => exact List.Mem.head (List.map mapper restElements)
  | tail headElement _ restMapped => exact List.Mem.tail (mapper headElement) restMapped

/-! ## The easy direction: canonical connectivity maps forward -/

/-- A canonical empty-base path maps forward along the rename: empty-base steps are node
equalities (so their images are trivially base-connected), event steps land in the renamed
trace by map membership introduction.  No injectivity needed. -/
theorem renamedJoinEventPath_ofCanonicalPath (sigma : Nat → Nat)
    (events : List (Nat × Nat)) (firstNode lastNode : Nat)
    (path : JoinEventPath events [] firstNode lastNode) :
    JoinEventPath (events.map (fun event => (sigma event.1, sigma event.2))) []
      (sigma firstNode) (sigma lastNode) := by
  induction path with
  | refl node => exact JoinEventPath.refl (sigma node)
  | cons stepFirst stepMiddle stepLast headStep _ renamedRest =>
      refine JoinEventPath.cons (sigma stepFirst) (sigma stepMiddle) (sigma stepLast)
        ?_ renamedRest
      cases headStep with
      | ofBase baseConnected =>
          rw [nodesEqual_ofEmptyBaseConnected stepFirst stepMiddle baseConnected]
          exact JoinEventStep.ofBase (sigma stepMiddle) (sigma stepMiddle)
            (isSameComponent_self [] (sigma stepMiddle))
      | ofEvent eventListed =>
          exact JoinEventStep.ofEvent (sigma stepFirst) (sigma stepMiddle)
            (memberOfMapIntro (fun event => (sigma event.1, sigma event.2)) events
              (stepFirst, stepMiddle) eventListed)
      | ofEventFlipped eventListed =>
          exact JoinEventStep.ofEventFlipped (sigma stepFirst) (sigma stepMiddle)
            (memberOfMapIntro (fun event => (sigma event.1, sigma event.2)) events
              (stepMiddle, stepFirst) eventListed)

/-- Canonical empty-base fold connectivity maps forward along the rename (decompose, map the
path, reassemble). -/
theorem renamedFoldConnected_ofCanonicalFold (sigma : Nat → Nat)
    (events : List (Nat × Nat)) (probeOne probeTwo : Nat)
    (canonicalConnected :
      isSameComponent (applyJoinEvents events []) probeOne probeTwo = true) :
    isSameComponent
        (applyJoinEvents (events.map (fun event => (sigma event.1, sigma event.2))) [])
        (sigma probeOne) (sigma probeTwo) = true :=
  isSameComponent_applyJoinEvents_ofPath
    (events.map (fun event => (sigma event.1, sigma event.2))) [] True.intro
    (sigma probeOne) (sigma probeTwo)
    (renamedJoinEventPath_ofCanonicalPath sigma events probeOne probeTwo
      (joinEventPath_ofFold events [] True.intro probeOne probeTwo canonicalConnected))

/-! ## The hard direction: the preimage-tracking walk -/

/-- **The preimage-tracking walk** — a renamed empty-base path never leaves the rename's
image: empty-base steps over `[]` are node equalities, and each renamed event decomposes
through map membership into a canonical event whose endpoint injectivity pins to the tracked
preimage.  The walk threads the accumulated canonical connectivity from a start node to the
current preimage and closes against the last node's preimage at the path's end. -/
theorem canonicalFoldConnected_ofRenamedPath (sigma : Nat → Nat)
    (isInjective : ∀ idOne idTwo : Nat, sigma idOne = sigma idTwo → idOne = idTwo)
    (events : List (Nat × Nat)) (currentNode lastNode : Nat)
    (path : JoinEventPath (events.map (fun event => (sigma event.1, sigma event.2))) []
      currentNode lastNode) :
    ∀ startNode currentPreimage : Nat, sigma currentPreimage = currentNode →
      isSameComponent (applyJoinEvents events []) startNode currentPreimage = true →
      ∀ lastPreimage : Nat, sigma lastPreimage = lastNode →
      isSameComponent (applyJoinEvents events []) startNode lastPreimage = true := by
  induction path with
  | refl node =>
      intro startNode currentPreimage currentMaps accumulated lastPreimage lastMaps
      exact isInjective currentPreimage lastPreimage (currentMaps.trans lastMaps.symm)
        ▸ accumulated
  | cons stepFirst stepMiddle stepLast headStep _ transferRest =>
      intro startNode currentPreimage currentMaps accumulated lastPreimage lastMaps
      cases headStep with
      | ofBase baseConnected =>
          exact transferRest startNode currentPreimage
            (currentMaps.trans
              (nodesEqual_ofEmptyBaseConnected stepFirst stepMiddle baseConnected))
            accumulated lastPreimage lastMaps
      | ofEvent eventListed =>
          obtain ⟨eventPair, eventInCanonical, eventMaps⟩ :=
            memberOfMapExists (fun event => (sigma event.1, sigma event.2)) events
              (stepFirst, stepMiddle) eventListed
          have firstComponent : sigma eventPair.1 = stepFirst :=
            congrArg Prod.fst eventMaps
          have secondComponent : sigma eventPair.2 = stepMiddle :=
            congrArg Prod.snd eventMaps
          have pinnedPreimage : currentPreimage = eventPair.1 :=
            isInjective currentPreimage eventPair.1
              (currentMaps.trans firstComponent.symm)
          have extendedAccumulated :
              isSameComponent (applyJoinEvents events []) startNode eventPair.2 = true :=
            isSameComponent_trans (applyJoinEvents events [])
              startNode eventPair.1 eventPair.2
              (pinnedPreimage ▸ accumulated)
              (isSameComponent_applyJoinEvents_ofMem events [] True.intro
                eventPair.1 eventPair.2 eventInCanonical)
          exact transferRest startNode eventPair.2 secondComponent extendedAccumulated
            lastPreimage lastMaps
      | ofEventFlipped eventListed =>
          obtain ⟨eventPair, eventInCanonical, eventMaps⟩ :=
            memberOfMapExists (fun event => (sigma event.1, sigma event.2)) events
              (stepMiddle, stepFirst) eventListed
          have firstComponent : sigma eventPair.1 = stepMiddle :=
            congrArg Prod.fst eventMaps
          have secondComponent : sigma eventPair.2 = stepFirst :=
            congrArg Prod.snd eventMaps
          have pinnedPreimage : currentPreimage = eventPair.2 :=
            isInjective currentPreimage eventPair.2
              (currentMaps.trans secondComponent.symm)
          have extendedAccumulated :
              isSameComponent (applyJoinEvents events []) startNode eventPair.1 = true :=
            isSameComponent_trans (applyJoinEvents events [])
              startNode eventPair.2 eventPair.1
              (pinnedPreimage ▸ accumulated)
              (isSameComponent_flip (applyJoinEvents events []) eventPair.1 eventPair.2
                (isSameComponent_applyJoinEvents_ofMem events [] True.intro
                  eventPair.1 eventPair.2 eventInCanonical))
          exact transferRest startNode eventPair.1 firstComponent extendedAccumulated
            lastPreimage lastMaps

/-- Renamed empty-base fold connectivity between image probes reflects back to the canonical
fold (decompose the renamed fold, walk with the trivial initial segment). -/
theorem canonicalFoldConnected_ofRenamedFold (sigma : Nat → Nat)
    (isInjective : ∀ idOne idTwo : Nat, sigma idOne = sigma idTwo → idOne = idTwo)
    (events : List (Nat × Nat)) (probeOne probeTwo : Nat)
    (renamedConnected :
      isSameComponent
        (applyJoinEvents (events.map (fun event => (sigma event.1, sigma event.2))) [])
        (sigma probeOne) (sigma probeTwo) = true) :
    isSameComponent (applyJoinEvents events []) probeOne probeTwo = true :=
  canonicalFoldConnected_ofRenamedPath sigma isInjective events
    (sigma probeOne) (sigma probeTwo)
    (joinEventPath_ofFold (events.map (fun event => (sigma event.1, sigma event.2))) []
      True.intro (sigma probeOne) (sigma probeTwo) renamedConnected)
    probeOne probeOne rfl (isSameComponent_self (applyJoinEvents events []) probeOne)
    probeTwo rfl

/-! ## The equivariance -/

/-- ★ **Fold-rename equivariance** — for an injective rename, the empty-base event fold's
component view at image probes IS the canonical fold's component view at the preimages. -/
theorem componentView_applyJoinEvents_ofRename (sigma : Nat → Nat)
    (isInjective : ∀ idOne idTwo : Nat, sigma idOne = sigma idTwo → idOne = idTwo)
    (events : List (Nat × Nat)) (probeOne probeTwo : Nat) :
    isSameComponent
        (applyJoinEvents (events.map (fun event => (sigma event.1, sigma event.2))) [])
        (sigma probeOne) (sigma probeTwo)
      = isSameComponent (applyJoinEvents events []) probeOne probeTwo :=
  boolEqOfImpliesBoth _ _
    (canonicalFoldConnected_ofRenamedFold sigma isInjective events probeOne probeTwo)
    (renamedFoldConnected_ofCanonicalFold sigma events probeOne probeTwo)

/-! ## Honesty marker -/

/-- **Honesty marker — fold-rename equivariance of the empty-base event fold is SHIPPED,
both directions** (`componentView_applyJoinEvents_ofRename`): for an injective rename the
renamed trace's empty-base component view at image probes equals the canonical trace's view
at the preimages, in the exact D3 trace-correspondence rename shape.  NOT yet shipped: the
D5 `Corresponds` instantiation — the concrete segment-transfer discharge combining this
equivariance with canonical extract equality and fold-support rigidity.  `= true`. -/
def fxMode_hasFoldRenameEquivariance : Bool := true

end FX1Poly.Polygraph
