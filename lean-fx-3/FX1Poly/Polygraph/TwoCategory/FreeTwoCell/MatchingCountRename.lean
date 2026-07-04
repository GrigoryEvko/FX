import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # MatchingCountRename — count rename invariance of the join-event fold (MODE3-D)

The LOOP leg of the interface gluing must compare loop counts of a canonical trace and its
pointwise `sigma` pair-rename (the D3 correspondence shape).  The loop count only reads the
component VIEW at fold time, so it transports along any rename whose image-view corresponds:

* `countJoinEventLoops_ofRenameCorrespondence` — the invariant induction: over two bases whose
  views correspond through `sigma` (renamed view at image probes = canonical view), the renamed
  trace's count equals the canonical trace's count.  The join preserves the correspondence
  through the flat-disjunction characterization `isSameComponent_unionFindJoin`, whose five
  atoms are all pure image pairs;
* ★ `countJoinEventLoops_ofRename` — the empty-base corollary for an INJECTIVE rename: the
  empty view relates a node only to itself, and injectivity makes that correspond through
  `sigma` — so a renamed trace closes exactly as many loops as the canonical trace.

With `spineJoinEvents_ofRelativeWireSim` this pins the relative run's canonical-loop content;
the remaining LOOP-leg work is the mid-links excess (the exchange decomposition) and the
mid-node view agreement.  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

/-! ## The image-view correspondence survives a join -/

/-- One join at an image pair preserves the image-view correspondence: read both sides off the
flat-disjunction characterization — every atom is an image pair, so the correspondence rewrites
all five. -/
private theorem viewCorrespondence_unionFindJoin (sigma : Nat → Nat)
    (baseRenamed baseCanonical : List (Nat × Nat))
    (forestRenamed : isUnionFindForest baseRenamed)
    (forestCanonical : isUnionFindForest baseCanonical)
    (viewsCorrespond : ∀ probeOne probeTwo : Nat,
      isSameComponent baseRenamed (sigma probeOne) (sigma probeTwo)
        = isSameComponent baseCanonical probeOne probeTwo)
    (joinLeft joinRight probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin baseRenamed (sigma joinLeft) (sigma joinRight))
        (sigma probeOne) (sigma probeTwo)
      = isSameComponent (unionFindJoin baseCanonical joinLeft joinRight) probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin baseRenamed forestRenamed (sigma joinLeft)
      (sigma joinRight) (sigma probeOne) (sigma probeTwo),
    isSameComponent_unionFindJoin baseCanonical forestCanonical joinLeft joinRight
      probeOne probeTwo,
    viewsCorrespond probeOne probeTwo, viewsCorrespond joinLeft probeOne,
    viewsCorrespond joinRight probeTwo, viewsCorrespond joinLeft probeTwo,
    viewsCorrespond probeOne joinRight]

/-! ## Count transport along a view correspondence -/

/-- The loop count transports along an image-view correspondence: each event's test reads only
the view at an image pair, and the correspondence survives every join. -/
theorem countJoinEventLoops_ofRenameCorrespondence (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) → (baseRenamed baseCanonical : List (Nat × Nat)) →
    isUnionFindForest baseRenamed → isUnionFindForest baseCanonical →
    (∀ probeOne probeTwo : Nat,
      isSameComponent baseRenamed (sigma probeOne) (sigma probeTwo)
        = isSameComponent baseCanonical probeOne probeTwo) →
    countJoinEventLoops (events.map (fun event => (sigma event.1, sigma event.2))) baseRenamed
      = countJoinEventLoops events baseCanonical
  | [], _, _, _, _, _ => rfl
  | (firstNode, secondNode) :: restEvents, baseRenamed, baseCanonical, forestRenamed,
      forestCanonical, viewsCorrespond => by
      show (isSameComponent baseRenamed (sigma firstNode) (sigma secondNode)).toNat
            + countJoinEventLoops
                (restEvents.map (fun event => (sigma event.1, sigma event.2)))
                (unionFindJoin baseRenamed (sigma firstNode) (sigma secondNode))
          = (isSameComponent baseCanonical firstNode secondNode).toNat
              + countJoinEventLoops restEvents (unionFindJoin baseCanonical firstNode secondNode)
      rw [viewsCorrespond firstNode secondNode,
        countJoinEventLoops_ofRenameCorrespondence sigma restEvents
          (unionFindJoin baseRenamed (sigma firstNode) (sigma secondNode))
          (unionFindJoin baseCanonical firstNode secondNode)
          (isUnionFindForest_unionFindJoin baseRenamed (sigma firstNode) (sigma secondNode)
            forestRenamed)
          (isUnionFindForest_unionFindJoin baseCanonical firstNode secondNode forestCanonical)
          (fun probeOne probeTwo => viewCorrespondence_unionFindJoin sigma
            baseRenamed baseCanonical forestRenamed forestCanonical viewsCorrespond
            firstNode secondNode probeOne probeTwo)]

/-- ★ **Count rename invariance over the empty base**: an injective pointwise pair-rename closes
exactly as many loops as the original trace.  The empty view relates a node only to itself, and
injectivity carries that through `sigma`. -/
theorem countJoinEventLoops_ofRename (sigma : Nat → Nat)
    (isInjective : ∀ nodeOne nodeTwo : Nat, sigma nodeOne = sigma nodeTwo → nodeOne = nodeTwo)
    (events : List (Nat × Nat)) :
    countJoinEventLoops (events.map (fun event => (sigma event.1, sigma event.2))) []
      = countJoinEventLoops events [] :=
  countJoinEventLoops_ofRenameCorrespondence sigma events [] [] True.intro True.intro
    (fun probeOne probeTwo => by
      show (sigma probeOne == sigma probeTwo) = (probeOne == probeTwo)
      apply boolEqOfImpliesBoth
      · intro imagesBeq
        cases isInjective probeOne probeTwo (of_decide_eq_true imagesBeq)
        exact decide_eq_true rfl
      · intro nodesBeq
        cases of_decide_eq_true nodesBeq
        exact decide_eq_true rfl)

/-- **Honesty marker — count rename invariance of the join-event fold is PROVED.**  Shipped: the
correspondence-transport induction (`countJoinEventLoops_ofRenameCorrespondence`) and the
injective empty-base invariance (`countJoinEventLoops_ofRename`).  NOT yet shipped: the LOOP
leg's mid-links excess decomposition (the links-as-events exchange) and the mid-node view
agreement between the two renamed folds. -/
def fxMode_hasCountRenameInvariance : Bool := true

end FX1Poly.Polygraph
