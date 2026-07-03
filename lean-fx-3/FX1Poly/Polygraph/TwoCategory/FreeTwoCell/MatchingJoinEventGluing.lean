import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # MatchingJoinEventGluing — mutually CONNECTED traces fold to equal views (MODE3-D)

The interface-gluing VIEW leg compares two event-trace folds over one mid-state link list.
The shipped exchange layer already answers this for MEM-equivalent traces
(`componentView_applyJoinEvents_ofMemEquiv` — reorderings), but the vcompRight gluing compares
two DIFFERENT traces (the canonical traces of two parallel disciplined spines, renamed into
the composite): their event pairs are not literally shared — extract equality only makes each
trace's pairs CONNECTED in the other's fold.

This file weakens the exchange hypothesis to that semantic form:

* ★ `componentView_applyJoinEvents_ofCrossConnected` — if every event pair of each trace is
  same-component in the OTHER trace's fold (over the same base links), the two folds have
  pointwise-EQUAL same-component views.  Each direction is one application of the fold's
  universal property (`isSameComponent_applyJoinEvents_lift`) with the other fold itself as
  the target view: the target contains the base (`_ofBase`) and relates the pairs (the
  cross-connectivity hypothesis) — no chain combinatorics, no new inductives.

HONESTY CORRECTION (post-scout): the cross-connectivity hypothesis is NOT dischargeable from
extract equality at ALL probes — extract equality constrains connectivity only at BOUNDARY
indices (`matchingSameComponent_eq_diagramView`), and a zigzag spine (cup;cap;cap) has the same
extract as a plain cap while its trace joins fresh wires the plain cap's fold never touches.
The live VIEW-leg route is therefore the alternating-path interpolation
(`MatchingJoinEventPath`): decompose composite connectivity into base/trace segments, transfer
the second-half segments through the boundary view, reassemble.  This engine remains a correct
general fold lemma.  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Boolean extensionality from mutual implication (private copy — the exchange file's helper
is file-private). -/
private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

/-- ★ **The gluing engine — mutually connected traces act identically on the partition.**
When every event pair of each trace is same-component in the OTHER trace's fold over the same
base links, the two folds' same-component views agree pointwise.  Strictly weaker hypothesis
than mem-equivalence: the pairs need only be CONNECTED by the other fold, not listed in it —
the form extract equality can discharge across two different canonical traces. -/
theorem componentView_applyJoinEvents_ofCrossConnected
    (eventsOne eventsTwo : List (Nat × Nat)) (links : List (Nat × Nat))
    (forest : isUnionFindForest links)
    (oneConnectedInTwo : ∀ firstNode secondNode : Nat, (firstNode, secondNode) ∈ eventsOne →
      isSameComponent (applyJoinEvents eventsTwo links) firstNode secondNode = true)
    (twoConnectedInOne : ∀ firstNode secondNode : Nat, (firstNode, secondNode) ∈ eventsTwo →
      isSameComponent (applyJoinEvents eventsOne links) firstNode secondNode = true)
    (probeOne probeTwo : Nat) :
    isSameComponent (applyJoinEvents eventsOne links) probeOne probeTwo
      = isSameComponent (applyJoinEvents eventsTwo links) probeOne probeTwo := by
  apply boolEqOfImpliesBoth
  · intro inFoldOne
    exact isSameComponent_applyJoinEvents_lift eventsOne links
      (applyJoinEvents eventsTwo links) forest
      (fun nodeOne nodeTwo base =>
        isSameComponent_applyJoinEvents_ofBase eventsTwo links forest nodeOne nodeTwo base)
      oneConnectedInTwo probeOne probeTwo inFoldOne
  · intro inFoldTwo
    exact isSameComponent_applyJoinEvents_lift eventsTwo links
      (applyJoinEvents eventsOne links) forest
      (fun nodeOne nodeTwo base =>
        isSameComponent_applyJoinEvents_ofBase eventsOne links forest nodeOne nodeTwo base)
      twoConnectedInOne probeOne probeTwo inFoldTwo

/-! ## Honesty marker -/

/-- **Honesty marker — the cross-connected gluing engine is SHIPPED, but it is NOT the VIEW
leg's route.**  The theorem is correct as stated, but its mutual-connectivity hypothesis is
not dischargeable from extract equality (which constrains only BOUNDARY connectivity — the
zigzag counterexample above), so the interface gluing goes through the alternating-path
interpolation in `MatchingJoinEventPath` instead.  Kept as a general fold lemma.  `= true`. -/
def fxMode_hasComponentViewCrossConnectedGluing : Bool := true

end FX1Poly.Polygraph
