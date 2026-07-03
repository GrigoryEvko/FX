import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # MatchingJoinEventPath — the alternating-path characterization of the event fold (MODE3-D)

The interface-gluing VIEW leg needs a DECOMPOSITION of composite connectivity that the shipped
fold universal property cannot express: `isSameComponent_applyJoinEvents_lift`'s target must be
another LINKS LIST, but the gluing argument needs to eliminate a fold-connectivity fact into an
ALTERNATING CHAIN of base-connectivity segments and trace events — an abstract relation, not a
link list.  This file ships that characterization:

* `JoinEventStep` / `JoinEventPath` — one chain step is base-view connectivity or one trace
  event (either orientation); a path is a finite chain of steps.  With the equivalence kit
  (`joinEventStep_symm`, `joinEventPath_append`, `joinEventPath_symm`) the path relation is the
  equivalence closure of (base view ∪ trace pairs);
* `isSameComponent_applyJoinEvents_ofPath` — ASSEMBLY: every path folds into fold connectivity
  (base steps by monotone extension, event steps by completeness, composition by root-equality
  transitivity);
* ★ `joinEventPath_ofFold` — DECOMPOSITION: fold connectivity yields a path.  Structural
  recursion on the trace; each peeled head join is eliminated through the flat-disjunction
  characterization `isSameComponent_unionFindJoin` (forest-conditioned), whose two mixed
  disjuncts become explicit three-step paths through the head event.

Why this is the load-bearing gluing engine: in the composite run the second-half events touch
only the sigma-image zones (ports below the mid fresh base, fresh block above it) while the
mid-state links touch only identifiers below the base — so a path between boundary probes
factors through interface ports, each second-half segment is a boundary-to-boundary canonical
connectivity fact (where extract equality bites), and the chain transfers between two
extract-equal second halves.  That locality argument is the NEXT brick; this file is its
substrate.  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The chain relation -/

/-- One step of the interpolation chain over a trace and a base link list: base-view
connectivity, or one trace event in either orientation. -/
inductive JoinEventStep (events links : List (Nat × Nat)) : Nat → Nat → Prop where
  /-- The two nodes are already connected in the base links. -/
  | ofBase (firstNode secondNode : Nat)
      (baseConnected : isSameComponent links firstNode secondNode = true) :
      JoinEventStep events links firstNode secondNode
  /-- The two nodes are one trace event, in trace orientation. -/
  | ofEvent (firstNode secondNode : Nat)
      (eventListed : (firstNode, secondNode) ∈ events) :
      JoinEventStep events links firstNode secondNode
  /-- The two nodes are one trace event, against trace orientation. -/
  | ofEventFlipped (firstNode secondNode : Nat)
      (eventListed : (secondNode, firstNode) ∈ events) :
      JoinEventStep events links firstNode secondNode

/-- A finite chain of interpolation steps — the equivalence closure of
(base view ∪ trace pairs), in path form. -/
inductive JoinEventPath (events links : List (Nat × Nat)) : Nat → Nat → Prop where
  /-- The empty chain. -/
  | refl (node : Nat) : JoinEventPath events links node node
  /-- One step followed by a chain. -/
  | cons (firstNode middleNode lastNode : Nat)
      (headStep : JoinEventStep events links firstNode middleNode)
      (restPath : JoinEventPath events links middleNode lastNode) :
      JoinEventPath events links firstNode lastNode

/-- A single step is a path. -/
theorem joinEventPath_ofStep (events links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (step : JoinEventStep events links firstNode secondNode) :
    JoinEventPath events links firstNode secondNode :=
  JoinEventPath.cons firstNode secondNode secondNode step (JoinEventPath.refl secondNode)

/-- Steps reverse: base steps by view symmetry, event steps by switching orientation. -/
theorem joinEventStep_symm (events links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (step : JoinEventStep events links firstNode secondNode) :
    JoinEventStep events links secondNode firstNode := by
  cases step with
  | ofBase baseConnected =>
      exact JoinEventStep.ofBase secondNode firstNode
        (isSameComponent_flip links firstNode secondNode baseConnected)
  | ofEvent eventListed =>
      exact JoinEventStep.ofEventFlipped secondNode firstNode eventListed
  | ofEventFlipped eventListed =>
      exact JoinEventStep.ofEvent secondNode firstNode eventListed

/-- Paths concatenate. -/
theorem joinEventPath_append (events links : List (Nat × Nat))
    (firstNode middleNode lastNode : Nat)
    (frontPath : JoinEventPath events links firstNode middleNode)
    (backPath : JoinEventPath events links middleNode lastNode) :
    JoinEventPath events links firstNode lastNode := by
  revert backPath
  induction frontPath with
  | refl _ => exact fun backPath => backPath
  | cons stepFirst stepMiddle _ headStep _ appendRest =>
      exact fun backPath =>
        JoinEventPath.cons stepFirst stepMiddle lastNode headStep (appendRest backPath)

/-- Paths reverse (step-wise symmetry spliced through concatenation). -/
theorem joinEventPath_symm (events links : List (Nat × Nat)) (firstNode lastNode : Nat)
    (path : JoinEventPath events links firstNode lastNode) :
    JoinEventPath events links lastNode firstNode := by
  induction path with
  | refl node => exact JoinEventPath.refl node
  | cons stepFirst stepMiddle stepLast headStep _ reversedRest =>
      exact joinEventPath_append events links stepLast stepMiddle stepFirst reversedRest
        (joinEventPath_ofStep events links stepMiddle stepFirst
          (joinEventStep_symm events links stepFirst stepMiddle headStep))

/-! ## Assembly: paths fold into fold connectivity -/

/-- **Assembly** — every interpolation path is realized by the event fold: base steps by
monotone extension, event steps by completeness, composition by root-equality transitivity. -/
theorem isSameComponent_applyJoinEvents_ofPath (events links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstNode lastNode : Nat)
    (path : JoinEventPath events links firstNode lastNode) :
    isSameComponent (applyJoinEvents events links) firstNode lastNode = true := by
  induction path with
  | refl node => exact isSameComponent_self (applyJoinEvents events links) node
  | cons stepFirst stepMiddle stepLast headStep _ foldRest =>
      apply isSameComponent_trans (applyJoinEvents events links) stepFirst stepMiddle stepLast
        _ foldRest
      cases headStep with
      | ofBase baseConnected =>
          exact isSameComponent_applyJoinEvents_ofBase events links forest
            stepFirst stepMiddle baseConnected
      | ofEvent eventListed =>
          exact isSameComponent_applyJoinEvents_ofMem events links forest
            stepFirst stepMiddle eventListed
      | ofEventFlipped eventListed =>
          exact isSameComponent_flip (applyJoinEvents events links) stepMiddle stepFirst
            (isSameComponent_applyJoinEvents_ofMem events links forest
              stepMiddle stepFirst eventListed)

/-! ## Decomposition: fold connectivity yields a path -/

/-- One step over the head-joined base becomes a path over the plain base with the head event
available: the flat-disjunction characterization of the join turns each mixed disjunct into an
explicit three-step chain through the head event. -/
theorem joinEventPath_ofJoinStep (headFirst headSecond : Nat)
    (restEvents links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstNode secondNode : Nat)
    (step : JoinEventStep restEvents (unionFindJoin links headFirst headSecond)
      firstNode secondNode) :
    JoinEventPath ((headFirst, headSecond) :: restEvents) links firstNode secondNode := by
  cases step with
  | ofEvent eventListed =>
      exact joinEventPath_ofStep _ links firstNode secondNode
        (JoinEventStep.ofEvent firstNode secondNode
          (List.Mem.tail (headFirst, headSecond) eventListed))
  | ofEventFlipped eventListed =>
      exact joinEventPath_ofStep _ links firstNode secondNode
        (JoinEventStep.ofEventFlipped firstNode secondNode
          (List.Mem.tail (headFirst, headSecond) eventListed))
  | ofBase baseConnected =>
      rw [isSameComponent_unionFindJoin links forest headFirst headSecond
        firstNode secondNode] at baseConnected
      cases hplainView : isSameComponent links firstNode secondNode with
      | true =>
          exact joinEventPath_ofStep _ links firstNode secondNode
            (JoinEventStep.ofBase firstNode secondNode hplainView)
      | false =>
          rw [hplainView] at baseConnected
          cases hheadToProbes : isSameComponent links headFirst firstNode
              && isSameComponent links headSecond secondNode with
          | true =>
              cases hheadFirstProbe : isSameComponent links headFirst firstNode with
              | false =>
                  rw [hheadFirstProbe] at hheadToProbes
                  exact Bool.noConfusion hheadToProbes
              | true =>
                  rw [hheadFirstProbe] at hheadToProbes
                  exact JoinEventPath.cons firstNode headFirst secondNode
                    (JoinEventStep.ofBase firstNode headFirst
                      (isSameComponent_flip links headFirst firstNode hheadFirstProbe))
                    (JoinEventPath.cons headFirst headSecond secondNode
                      (JoinEventStep.ofEvent headFirst headSecond (List.Mem.head restEvents))
                      (joinEventPath_ofStep _ links headSecond secondNode
                        (JoinEventStep.ofBase headSecond secondNode hheadToProbes)))
          | false =>
              rw [hheadToProbes] at baseConnected
              cases hheadFirstLast : isSameComponent links headFirst secondNode with
              | false =>
                  rw [hheadFirstLast] at baseConnected
                  exact Bool.noConfusion baseConnected
              | true =>
                  rw [hheadFirstLast] at baseConnected
                  exact JoinEventPath.cons firstNode headSecond secondNode
                    (JoinEventStep.ofBase firstNode headSecond baseConnected)
                    (JoinEventPath.cons headSecond headFirst secondNode
                      (JoinEventStep.ofEventFlipped headSecond headFirst
                        (List.Mem.head restEvents))
                      (joinEventPath_ofStep _ links headFirst secondNode
                        (JoinEventStep.ofBase headFirst secondNode hheadFirstLast)))

/-- A whole path over the head-joined base becomes a path over the plain base with the head
event available (step-wise translation spliced through concatenation). -/
theorem joinEventPath_ofJoinedBasePath (headFirst headSecond : Nat)
    (restEvents links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstNode lastNode : Nat)
    (joinedPath : JoinEventPath restEvents (unionFindJoin links headFirst headSecond)
      firstNode lastNode) :
    JoinEventPath ((headFirst, headSecond) :: restEvents) links firstNode lastNode := by
  induction joinedPath with
  | refl node => exact JoinEventPath.refl node
  | cons stepFirst stepMiddle stepLast headStep _ liftedRest =>
      exact joinEventPath_append ((headFirst, headSecond) :: restEvents) links
        stepFirst stepMiddle stepLast
        (joinEventPath_ofJoinStep headFirst headSecond restEvents links forest
          stepFirst stepMiddle headStep)
        liftedRest

/-- ★ **Decomposition — fold connectivity yields an interpolation path.**  Structural recursion
on the trace: the empty trace's fold IS the base view (one base step); a head event peels off
through the join-step translation, with the forest invariant threaded through the join. -/
theorem joinEventPath_ofFold :
    (events links : List (Nat × Nat)) → isUnionFindForest links →
    (firstNode lastNode : Nat) →
    isSameComponent (applyJoinEvents events links) firstNode lastNode = true →
    JoinEventPath events links firstNode lastNode
  | [], links, _, firstNode, lastNode, foldConnected =>
      joinEventPath_ofStep [] links firstNode lastNode
        (JoinEventStep.ofBase firstNode lastNode foldConnected)
  | (headFirst, headSecond) :: restEvents, links, forest, firstNode, lastNode,
      foldConnected =>
      joinEventPath_ofJoinedBasePath headFirst headSecond restEvents links forest
        firstNode lastNode
        (joinEventPath_ofFold restEvents (unionFindJoin links headFirst headSecond)
          (isUnionFindForest_unionFindJoin links headFirst headSecond forest)
          firstNode lastNode foldConnected)

/-! ## Honesty marker -/

/-- **Honesty marker — the alternating-path characterization of the event fold is SHIPPED,
both directions.**  Fold connectivity = existence of a finite chain of base-view segments and
trace events (`joinEventPath_ofFold` / `isSameComponent_applyJoinEvents_ofPath`), with the
equivalence kit (reverse, concatenate).  NOT yet shipped: the LOCALITY grouping — factoring a
path between boundary probes into maximal same-kind segments whose switch nodes are interface
ports (the zone-discipline argument), and the extract-equality transfer of the second-half
segments.  `= true`. -/
def fxMode_hasJoinEventPathCharacterization : Bool := true

end FX1Poly.Polygraph
