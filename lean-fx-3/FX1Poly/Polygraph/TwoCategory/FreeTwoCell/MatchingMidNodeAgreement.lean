import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCanonicalPairs

/-! # MatchingMidNodeAgreement — the two renamed folds agree below the fresh base (MODE3-D)

The LOOP leg's remaining view input: the mid links' nodes all sit below the fresh base, and
at BELOW-BASE pairs the two renamed traces' empty-base folds have EQUAL component views —
even though their interior fresh zones differ.  Case analysis per probe:

* a probe touched by NEITHER renamed trace is rigid in both folds
  (`nodesEqual_ofFoldConnectedToUntouched`): connectivity forces equality, and equal probes
  agree by reflexivity;
* a probe touched by EITHER trace is a rename image, and a below-base image pins its
  preimage into the port zone (`freshImageAtOrAbove` else the image sits at or above the
  base) — so both probes are PORT images, where the fold-rename equivariance
  (`componentView_applyJoinEvents_ofRename`) reduces both folds to the canonical folds, and
  the connectivity-view simulation agrees at port positions (the range-prefix boundary
  reads).

★ `belowBaseFoldView_agrees_ofViewSim` is the discharger for the restricted count
congruence's view hypothesis (`countJoinEventLoops_congrOnNodeSet` at the below-base set).
Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

private theorem natBeqSelf (node : Nat) : (node == node) = true := decide_eq_true rfl

private theorem boolOrEqTrue_ofLeft (leftFlag rightFlag : Bool) (leftTrue : leftFlag = true) :
    (leftFlag || rightFlag) = true := by
  rw [leftTrue]
  rfl

private theorem boolOrEqTrue_ofRight (leftFlag rightFlag : Bool)
    (rightTrue : rightFlag = true) : (leftFlag || rightFlag) = true := by
  rw [rightTrue]
  cases leftFlag with
  | true => rfl
  | false => rfl

private theorem notTrue_ofFalse : (flag : Bool) → flag = false → ¬ flag = true
  | _, rfl => fun impossible => Bool.noConfusion impossible

private theorem memberConsCases {Element : Type} (candidate headElement : Element)
    (restElements : List Element) (membership : candidate ∈ headElement :: restElements) :
    candidate = headElement ∨ candidate ∈ restElements := by
  cases membership with
  | head => exact Or.inl rfl
  | tail _ restMembership => exact Or.inr restMembership

/-! ## The appearance scan -/

/-- Whether a node appears in a join-event trace (either component of any event). -/
private def nodeAppearsInJoinEvents : List (Nat × Nat) → Nat → Bool
  | [], _ => false
  | event :: restEvents, node =>
      (event.1 == node) || ((event.2 == node) || nodeAppearsInJoinEvents restEvents node)

/-- Every event's nodes appear in their own trace — the rigidity node-set closure. -/
private theorem nodeAppears_closesOwnEvents :
    (events : List (Nat × Nat)) → ∀ pair ∈ events,
      nodeAppearsInJoinEvents events pair.1 = true
        ∧ nodeAppearsInJoinEvents events pair.2 = true
  | [] => fun _ membership => nomatch membership
  | headEvent :: restEvents => fun pair membership => by
      cases memberConsCases pair headEvent restEvents membership with
      | inl pairEqual =>
          rw [pairEqual]
          exact ⟨boolOrEqTrue_ofLeft _ _ (natBeqSelf headEvent.1),
            boolOrEqTrue_ofRight _ _ (boolOrEqTrue_ofLeft _ _ (natBeqSelf headEvent.2))⟩
      | inr restMembership =>
          have restClosed := nodeAppears_closesOwnEvents restEvents pair restMembership
          exact ⟨boolOrEqTrue_ofRight _ _ (boolOrEqTrue_ofRight _ _ restClosed.1),
            boolOrEqTrue_ofRight _ _ (boolOrEqTrue_ofRight _ _ restClosed.2)⟩

/-- A node appearing in a renamed trace is a rename image. -/
private theorem renamedAppearsPreimage (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) → (node : Nat) →
    nodeAppearsInJoinEvents
      (events.map (fun event => (sigma event.1, sigma event.2))) node = true →
    ∃ preimage : Nat, sigma preimage = node
  | [], _, appears => nomatch appears
  | headEvent :: restEvents, node, appears => by
      cases firstTest : sigma headEvent.1 == node with
      | true => exact ⟨headEvent.1, of_decide_eq_true firstTest⟩
      | false =>
          cases secondTest : sigma headEvent.2 == node with
          | true => exact ⟨headEvent.2, of_decide_eq_true secondTest⟩
          | false =>
              have shaped : ((sigma headEvent.1 == node)
                  || ((sigma headEvent.2 == node)
                    || nodeAppearsInJoinEvents
                      (restEvents.map (fun event => (sigma event.1, sigma event.2)))
                      node)) = true := appears
              rw [firstTest, secondTest] at shaped
              have restAppears : nodeAppearsInJoinEvents
                  (restEvents.map (fun event => (sigma event.1, sigma event.2))) node
                  = true := shaped
              exact renamedAppearsPreimage sigma restEvents node restAppears

/-! ## The below-base port pinning -/

/-- A below-base rename image pins its preimage into the port zone. -/
private theorem portPreimage_ofImageBelow (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase) (preimage : Nat)
    (imageBelow : relativeWireMap wires freshBase preimage < freshBase) :
    preimage < wires.length := by
  cases Nat.lt_or_ge preimage wires.length with
  | inl inPortZone => exact inPortZone
  | inr inFreshZone =>
      exact absurd
        (Nat.lt_of_le_of_lt (discipline.freshImageAtOrAbove preimage inFreshZone) imageBelow)
        (Nat.lt_irrefl freshBase)

/-- A below-base node touched by either renamed trace is the image of a PORT index. -/
private theorem portWitness_ofTouchedBelow (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (eventsA eventsB : List (Nat × Nat)) (node : Nat) (nodeBelow : node < freshBase)
    (touched : (nodeAppearsInJoinEvents (eventsA.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) node
        || nodeAppearsInJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) node) = true) :
    ∃ port : Nat, port < wires.length ∧ relativeWireMap wires freshBase port = node := by
  have witnessOfPreimage : (∃ preimage : Nat,
      relativeWireMap wires freshBase preimage = node) →
      ∃ port : Nat, port < wires.length ∧ relativeWireMap wires freshBase port = node := by
    intro preimageWitness
    obtain ⟨preimage, preimageMaps⟩ := preimageWitness
    have imageBelow : relativeWireMap wires freshBase preimage < freshBase := by
      rw [preimageMaps]
      exact nodeBelow
    exact ⟨preimage,
      portPreimage_ofImageBelow wires freshBase discipline preimage imageBelow,
      preimageMaps⟩
  cases touchedA : nodeAppearsInJoinEvents (eventsA.map (fun event =>
      (relativeWireMap wires freshBase event.1,
        relativeWireMap wires freshBase event.2))) node with
  | true =>
      exact witnessOfPreimage
        (renamedAppearsPreimage (relativeWireMap wires freshBase) eventsA node touchedA)
  | false =>
      rw [touchedA] at touched
      have touchedB : nodeAppearsInJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) node = true := touched
      exact witnessOfPreimage
        (renamedAppearsPreimage (relativeWireMap wires freshBase) eventsB node touchedB)

/-! ## The port view agreement -/

/-- The two canonical folds' views agree at BOTTOM-PORT pairs: the view simulation read at
the two port positions, with the range-prefix boundary reads and links read-offs rewritten. -/
private theorem portView_agrees_ofViewSim (bottomCount : Nat) (stateA stateB : WireState)
    (eventsA eventsB : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (viewSim : MatchingConnectivityViewSim bottomCount stateA stateB)
    (portOne portTwo : Nat)
    (oneBelow : portOne < bottomCount) (twoBelow : portTwo < bottomCount) :
    isSameComponent (applyJoinEvents eventsA []) portOne portTwo
      = isSameComponent (applyJoinEvents eventsB []) portOne portTwo := by
  obtain ⟨onePosition, oneBound, oneReadA, oneReadB⟩ :=
    canonicalBoundaryPair_ofBottomPort bottomCount stateA stateB portOne oneBelow
  obtain ⟨twoPosition, twoBound, twoReadA, twoReadB⟩ :=
    canonicalBoundaryPair_ofBottomPort bottomCount stateA stateB portTwo twoBelow
  have oneBoundB : onePosition < bottomCount + stateB.openWires.length := by
    rw [← viewSim.lengthEq]
    exact oneBound
  have twoBoundB : twoPosition < bottomCount + stateB.openWires.length := by
    rw [← viewSim.lengthEq]
    exact twoBound
  have viewShaped : isSameComponent stateA.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateA) onePosition)
        (natListGetAt (matchingBoundaryNodes bottomCount stateA) twoPosition)
      = isSameComponent stateB.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateB) onePosition)
        (natListGetAt (matchingBoundaryNodes bottomCount stateB) twoPosition) :=
    viewSim.viewAgrees onePosition twoPosition oneBoundB twoBoundB
  rw [oneReadA, twoReadA, oneReadB, twoReadB, linksA, linksB] at viewShaped
  exact viewShaped

/-! ## The below-base view agreement -/

/-- ★ **The two renamed folds' views agree at every below-base pair.**  A probe untouched by
both renamed traces is rigid in both folds; a touched below-base probe is a port image, where
the rename equivariance reduces both folds to the canonical folds and the view simulation
closes at the port positions. -/
theorem belowBaseFoldView_agrees_ofViewSim (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (bottomCount : Nat) (midTracks : wires.length = bottomCount)
    (stateA stateB : WireState) (eventsA eventsB : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (viewSim : MatchingConnectivityViewSim bottomCount stateA stateB)
    (probeOne probeTwo : Nat)
    (oneBelow : probeOne < freshBase) (twoBelow : probeTwo < freshBase) :
    isSameComponent (applyJoinEvents (eventsA.map (fun event =>
        (relativeWireMap wires freshBase event.1,
          relativeWireMap wires freshBase event.2))) [])
      probeOne probeTwo
      = isSameComponent (applyJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) [])
        probeOne probeTwo := by
  cases oneTouched : (nodeAppearsInJoinEvents (eventsA.map (fun event =>
      (relativeWireMap wires freshBase event.1,
        relativeWireMap wires freshBase event.2))) probeOne
    || nodeAppearsInJoinEvents (eventsB.map (fun event =>
      (relativeWireMap wires freshBase event.1,
        relativeWireMap wires freshBase event.2))) probeOne) with
  | false =>
      have untouchedA : nodeAppearsInJoinEvents (eventsA.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) probeOne = false := by
        cases scanA : nodeAppearsInJoinEvents (eventsA.map (fun event =>
            (relativeWireMap wires freshBase event.1,
              relativeWireMap wires freshBase event.2))) probeOne with
        | false => rfl
        | true =>
            rw [scanA] at oneTouched
            exact Bool.noConfusion oneTouched
      have untouchedB : nodeAppearsInJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) probeOne = false := by
        cases scanB : nodeAppearsInJoinEvents (eventsB.map (fun event =>
            (relativeWireMap wires freshBase event.1,
              relativeWireMap wires freshBase event.2))) probeOne with
        | false => rfl
        | true =>
            rw [scanB, untouchedA] at oneTouched
            exact Bool.noConfusion oneTouched
      apply boolEqOfImpliesBoth
      · intro connectedA
        cases nodesEqual_ofUntouchedFoldConnected
            (fun node => nodeAppearsInJoinEvents (eventsA.map (fun event =>
              (relativeWireMap wires freshBase event.1,
                relativeWireMap wires freshBase event.2))) node = true)
            (eventsA.map (fun event =>
              (relativeWireMap wires freshBase event.1,
                relativeWireMap wires freshBase event.2)))
            (nodeAppears_closesOwnEvents _)
            probeOne probeTwo (notTrue_ofFalse _ untouchedA) connectedA
        show (unionFindRootOf (applyJoinEvents (eventsB.map (fun event =>
            (relativeWireMap wires freshBase event.1,
              relativeWireMap wires freshBase event.2))) []) probeOne
          == unionFindRootOf (applyJoinEvents (eventsB.map (fun event =>
            (relativeWireMap wires freshBase event.1,
              relativeWireMap wires freshBase event.2))) []) probeOne) = true
        exact natBeqSelf _
      · intro connectedB
        cases nodesEqual_ofUntouchedFoldConnected
            (fun node => nodeAppearsInJoinEvents (eventsB.map (fun event =>
              (relativeWireMap wires freshBase event.1,
                relativeWireMap wires freshBase event.2))) node = true)
            (eventsB.map (fun event =>
              (relativeWireMap wires freshBase event.1,
                relativeWireMap wires freshBase event.2)))
            (nodeAppears_closesOwnEvents _)
            probeOne probeTwo (notTrue_ofFalse _ untouchedB) connectedB
        show (unionFindRootOf (applyJoinEvents (eventsA.map (fun event =>
            (relativeWireMap wires freshBase event.1,
              relativeWireMap wires freshBase event.2))) []) probeOne
          == unionFindRootOf (applyJoinEvents (eventsA.map (fun event =>
            (relativeWireMap wires freshBase event.1,
              relativeWireMap wires freshBase event.2))) []) probeOne) = true
        exact natBeqSelf _
  | true =>
      obtain ⟨portOne, portOneBelow, portOneMaps⟩ :=
        portWitness_ofTouchedBelow wires freshBase discipline eventsA eventsB probeOne
          oneBelow oneTouched
      cases twoTouched : (nodeAppearsInJoinEvents (eventsA.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) probeTwo
        || nodeAppearsInJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1,
            relativeWireMap wires freshBase event.2))) probeTwo) with
      | false =>
          have untouchedA : nodeAppearsInJoinEvents (eventsA.map (fun event =>
              (relativeWireMap wires freshBase event.1,
                relativeWireMap wires freshBase event.2))) probeTwo = false := by
            cases scanA : nodeAppearsInJoinEvents (eventsA.map (fun event =>
                (relativeWireMap wires freshBase event.1,
                  relativeWireMap wires freshBase event.2))) probeTwo with
            | false => rfl
            | true =>
                rw [scanA] at twoTouched
                exact Bool.noConfusion twoTouched
          have untouchedB : nodeAppearsInJoinEvents (eventsB.map (fun event =>
              (relativeWireMap wires freshBase event.1,
                relativeWireMap wires freshBase event.2))) probeTwo = false := by
            cases scanB : nodeAppearsInJoinEvents (eventsB.map (fun event =>
                (relativeWireMap wires freshBase event.1,
                  relativeWireMap wires freshBase event.2))) probeTwo with
            | false => rfl
            | true =>
                rw [scanB, untouchedA] at twoTouched
                exact Bool.noConfusion twoTouched
          apply boolEqOfImpliesBoth
          · intro connectedA
            cases nodesEqual_ofFoldConnectedToUntouched
                (fun node => nodeAppearsInJoinEvents (eventsA.map (fun event =>
                  (relativeWireMap wires freshBase event.1,
                    relativeWireMap wires freshBase event.2))) node = true)
                (eventsA.map (fun event =>
                  (relativeWireMap wires freshBase event.1,
                    relativeWireMap wires freshBase event.2)))
                (nodeAppears_closesOwnEvents _)
                probeOne probeTwo (notTrue_ofFalse _ untouchedA) connectedA
            show (unionFindRootOf (applyJoinEvents (eventsB.map (fun event =>
                (relativeWireMap wires freshBase event.1,
                  relativeWireMap wires freshBase event.2))) []) probeOne
              == unionFindRootOf (applyJoinEvents (eventsB.map (fun event =>
                (relativeWireMap wires freshBase event.1,
                  relativeWireMap wires freshBase event.2))) []) probeOne) = true
            exact natBeqSelf _
          · intro connectedB
            cases nodesEqual_ofFoldConnectedToUntouched
                (fun node => nodeAppearsInJoinEvents (eventsB.map (fun event =>
                  (relativeWireMap wires freshBase event.1,
                    relativeWireMap wires freshBase event.2))) node = true)
                (eventsB.map (fun event =>
                  (relativeWireMap wires freshBase event.1,
                    relativeWireMap wires freshBase event.2)))
                (nodeAppears_closesOwnEvents _)
                probeOne probeTwo (notTrue_ofFalse _ untouchedB) connectedB
            show (unionFindRootOf (applyJoinEvents (eventsA.map (fun event =>
                (relativeWireMap wires freshBase event.1,
                  relativeWireMap wires freshBase event.2))) []) probeOne
              == unionFindRootOf (applyJoinEvents (eventsA.map (fun event =>
                (relativeWireMap wires freshBase event.1,
                  relativeWireMap wires freshBase event.2))) []) probeOne) = true
            exact natBeqSelf _
      | true =>
          obtain ⟨portTwo, portTwoBelow, portTwoMaps⟩ :=
            portWitness_ofTouchedBelow wires freshBase discipline eventsA eventsB probeTwo
              twoBelow twoTouched
          rw [← portOneMaps, ← portTwoMaps,
            componentView_applyJoinEvents_ofRename (relativeWireMap wires freshBase)
              discipline.isInjective eventsA portOne portTwo,
            componentView_applyJoinEvents_ofRename (relativeWireMap wires freshBase)
              discipline.isInjective eventsB portOne portTwo]
          exact portView_agrees_ofViewSim bottomCount stateA stateB eventsA eventsB
            linksA linksB viewSim portOne portTwo
            (midTracks ▸ portOneBelow) (midTracks ▸ portTwoBelow)

/-- **Honesty marker — the below-base view agreement of the two renamed folds is PROVED.**
Combined with the restricted count congruence this pins the mid edges' count over either
renamed fold; NOT yet shipped: the final loop-increment equality glue. -/
def fxMode_hasBelowBaseFoldViewAgreement : Bool := true

end FX1Poly.Polygraph
