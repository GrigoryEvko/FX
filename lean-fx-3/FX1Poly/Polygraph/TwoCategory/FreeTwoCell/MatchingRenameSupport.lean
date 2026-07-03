import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventCongruence

/-! # mode-3 keystone — the rename-support kit for the sigma-witness assembly

Every leg of the sigma witness is now banked (trace reification/faithfulness, sigma-equivariance,
block exchange, cross-order trace congruence); the final assembly composes them at the two-core
setup.  This file ships the three support pieces that composition consumes:

  * ★ `componentView_ofFreshRename` — the BASE correspondence: a rename that fixes every id below
    a bound, keeps at-or-above ids at-or-above, and is injective, preserves the same-component
    view on any link list whose entries are below the bound.  Old probes have old roots
    (`unionFindRootOf_lt_of_fresh`), fresh probes are their own roots
    (`unionFindRootOf_eq_self_ofFresh`) — so mixed pairs test false on both sides and fresh
    pairs reduce to id equality, transported by injectivity.  This discharges the
    sigma-equivariance fold's base hypothesis at `shared.links` for `blockRotate`.
  * `spineJoinEvents_valuesBounded` — every event value of a fresh run's trace lies below the
    run's OUTPUT counter (cup legs below the bumped counter, cap reads below the unchanged one,
    freshness threaded).  This is what localizes each block's trace inside its own id block, so
    the per-zone rotation/shift agreement lemmas apply pointwise.
  * `listMapPairCongr_onMembers` / `listMapPairEqSelf_onMembers` / `listMapPairCompose` — the
    pointwise map surgery converting the congruence's `freshShiftAbove` renames into the single
    `blockRotate` witness (agree-on-members, undo-on-members, compose).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Membership plumbing (private copy — the exchange file's helpers are private there) -/

private theorem pairMemAppendCases :
    (leftList rightList : List (Nat × Nat)) → (event : Nat × Nat) →
    event ∈ leftList ++ rightList → event ∈ leftList ∨ event ∈ rightList
  | [], _, _, membership => Or.inr membership
  | headEvent :: restLeft, rightList, event, membership => by
      cases membership with
      | head => exact Or.inl (List.Mem.head restLeft)
      | tail _ tailMembership =>
          cases pairMemAppendCases restLeft rightList event tailMembership with
          | inl inLeft => exact Or.inl (List.Mem.tail headEvent inLeft)
          | inr inRight => exact Or.inr inRight

/-! ## The base correspondence: a fresh rename is invisible to the component view -/

/-- ★ **A fresh rename preserves the same-component view** — the sigma-equivariance fold's BASE
correspondence.  On a link list whose entries all lie below `bound`, any rename that fixes ids
below `bound`, keeps at-or-above ids at-or-above, and is injective satisfies
`view (sigma p) (sigma q) = view p q` for ALL probes: below/below is fixed pointwise, mixed pairs
test `false` on both sides (an old probe's root is old — `unionFindRootOf_lt_of_fresh` — while an
at-or-above probe is its own root — `unionFindRootOf_eq_self_ofFresh`), and above/above reduces to
bare id equality, transported by injectivity. -/
theorem componentView_ofFreshRename (sigma : Nat → Nat) (bound : Nat)
    (links : List (Nat × Nat))
    (boundedEntries : ∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound)
    (fixesBelow : ∀ identifier, identifier < bound → sigma identifier = identifier)
    (mapsAboveWithin : ∀ identifier, bound ≤ identifier → bound ≤ sigma identifier)
    (isInjective : ∀ idOne idTwo : Nat, sigma idOne = sigma idTwo → idOne = idTwo)
    (probeOne probeTwo : Nat) :
    isSameComponent links (sigma probeOne) (sigma probeTwo)
      = isSameComponent links probeOne probeTwo := by
  have boundedChildren : ∀ edge ∈ links, edge.1 < bound :=
    fun edge edgeIn => (boundedEntries edge edgeIn).1
  have boundedParents : ∀ edge ∈ links, edge.2 < bound :=
    fun edge edgeIn => (boundedEntries edge edgeIn).2
  cases Nat.lt_or_ge probeOne bound with
  | inl belowOne =>
      cases Nat.lt_or_ge probeTwo bound with
      | inl belowTwo => rw [fixesBelow probeOne belowOne, fixesBelow probeTwo belowTwo]
      | inr atOrAboveTwo =>
          rw [fixesBelow probeOne belowOne]
          show (unionFindRootOf links probeOne == unionFindRootOf links (sigma probeTwo))
              = (unionFindRootOf links probeOne == unionFindRootOf links probeTwo)
          rw [unionFindRootOf_eq_self_ofFresh bound links boundedChildren (sigma probeTwo)
              (mapsAboveWithin probeTwo atOrAboveTwo),
            unionFindRootOf_eq_self_ofFresh bound links boundedChildren probeTwo atOrAboveTwo]
          have rootBelow := unionFindRootOf_lt_of_fresh links bound boundedParents
            probeOne belowOne
          have leftFalse : (unionFindRootOf links probeOne == sigma probeTwo) = false :=
            decide_eq_false (fun rootEqSigma => Nat.lt_irrefl (sigma probeTwo)
              (Nat.lt_of_lt_of_le (rootEqSigma ▸ rootBelow)
                (mapsAboveWithin probeTwo atOrAboveTwo)))
          have rightFalse : (unionFindRootOf links probeOne == probeTwo) = false :=
            decide_eq_false (fun rootEqProbe => Nat.lt_irrefl probeTwo
              (Nat.lt_of_lt_of_le (rootEqProbe ▸ rootBelow) atOrAboveTwo))
          rw [leftFalse, rightFalse]
  | inr atOrAboveOne =>
      cases Nat.lt_or_ge probeTwo bound with
      | inl belowTwo =>
          rw [fixesBelow probeTwo belowTwo]
          show (unionFindRootOf links (sigma probeOne) == unionFindRootOf links probeTwo)
              = (unionFindRootOf links probeOne == unionFindRootOf links probeTwo)
          rw [unionFindRootOf_eq_self_ofFresh bound links boundedChildren (sigma probeOne)
              (mapsAboveWithin probeOne atOrAboveOne),
            unionFindRootOf_eq_self_ofFresh bound links boundedChildren probeOne atOrAboveOne]
          have rootBelow := unionFindRootOf_lt_of_fresh links bound boundedParents
            probeTwo belowTwo
          have leftFalse : (sigma probeOne == unionFindRootOf links probeTwo) = false :=
            decide_eq_false (fun sigmaEqRoot => Nat.lt_irrefl (sigma probeOne)
              (Nat.lt_of_lt_of_le (sigmaEqRoot.symm ▸ rootBelow)
                (mapsAboveWithin probeOne atOrAboveOne)))
          have rightFalse : (probeOne == unionFindRootOf links probeTwo) = false :=
            decide_eq_false (fun probeEqRoot => Nat.lt_irrefl probeOne
              (Nat.lt_of_lt_of_le (probeEqRoot.symm ▸ rootBelow) atOrAboveOne))
          rw [leftFalse, rightFalse]
      | inr atOrAboveTwo =>
          show (unionFindRootOf links (sigma probeOne) == unionFindRootOf links (sigma probeTwo))
              = (unionFindRootOf links probeOne == unionFindRootOf links probeTwo)
          rw [unionFindRootOf_eq_self_ofFresh bound links boundedChildren (sigma probeOne)
              (mapsAboveWithin probeOne atOrAboveOne),
            unionFindRootOf_eq_self_ofFresh bound links boundedChildren (sigma probeTwo)
              (mapsAboveWithin probeTwo atOrAboveTwo),
            unionFindRootOf_eq_self_ofFresh bound links boundedChildren probeOne atOrAboveOne,
            unionFindRootOf_eq_self_ofFresh bound links boundedChildren probeTwo atOrAboveTwo]
          cases probesEq : probeOne == probeTwo with
          | true =>
              rw [of_decide_eq_true probesEq,
                show (sigma probeTwo == sigma probeTwo) = true from decide_eq_true rfl]
          | false =>
              exact decide_eq_false (fun sigmaEq =>
                of_decide_eq_false probesEq (isInjective probeOne probeTwo sigmaEq))

/-! ## Trace value bounds: every event value lies below the run's output counter

The counter monotonicity `processSpine_nextFresh_le` is already banked in
`MatchingSwapRenameable`; the bounds below thread it per atom. -/

/-- One atom's event values lie below its output counter: a cup's fresh legs sit below the bumped
counter, a cap's reads are fresh-bounded open wires (`natListGetAt_lt`), a box emits nothing.
Literal-arity case tree so the events matcher reduces. -/
theorem stepAtomJoinEvents_valuesBounded {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (fresh : WireStateFresh state) (nfPos : 0 < state.nextFresh)
    (firstNode secondNode : Nat)
    (membership : (firstNode, secondNode) ∈ stepAtomJoinEvents state atom) :
    firstNode < (stepAtom state atom).nextFresh
      ∧ secondNode < (stepAtom state atom).nextFresh := by
  cases hdom : atom.generatorDom.length with
  | zero =>
      cases hcod : atom.generatorCod.length with
      | zero =>
          unfold stepAtomJoinEvents at membership
          rw [hdom, hcod] at membership
          cases membership
      | succ codPred =>
          cases codPred with
          | zero =>
              unfold stepAtomJoinEvents at membership
              rw [hdom, hcod] at membership
              cases membership
          | succ codPredPred =>
              cases codPredPred with
              | zero =>
                  rw [stepAtom_ofCupArity state atom hdom hcod, stepCup_nextFresh]
                  rw [stepAtomJoinEvents_ofCupArity state atom hdom hcod] at membership
                  cases membership with
                  | head =>
                      exact ⟨Nat.succ_le_succ (Nat.le_succ state.nextFresh),
                        Nat.le_refl (state.nextFresh + 2)⟩
                  | tail _ impossible => cases impossible
              | succ _ =>
                  unfold stepAtomJoinEvents at membership
                  rw [hdom, hcod] at membership
                  cases membership
  | succ domPred =>
      cases domPred with
      | zero =>
          unfold stepAtomJoinEvents at membership
          rw [hdom] at membership
          cases membership
      | succ domPredPred =>
          cases domPredPred with
          | zero =>
              cases hcod : atom.generatorCod.length with
              | zero =>
                  rw [stepAtom_ofCapArity state atom hdom hcod, stepCap_nextFresh]
                  rw [stepAtomJoinEvents_ofCapArity state atom hdom hcod] at membership
                  cases membership with
                  | head =>
                      exact ⟨natListGetAt_lt state.nextFresh nfPos state.openWires
                          atom.leftContext.length fresh.1,
                        natListGetAt_lt state.nextFresh nfPos state.openWires
                          (atom.leftContext.length + 1) fresh.1⟩
                  | tail _ impossible => cases impossible
              | succ _ =>
                  unfold stepAtomJoinEvents at membership
                  rw [hdom, hcod] at membership
                  cases membership
          | succ _ =>
              unfold stepAtomJoinEvents at membership
              rw [hdom] at membership
              cases membership

/-- ★ **A fresh run's trace values lie below the run's output counter** — the localization that
keeps each block's events inside its own id block (freshness threaded step by step). -/
theorem spineJoinEvents_valuesBounded {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    WireStateFresh state → 0 < state.nextFresh →
    ∀ firstNode secondNode : Nat, (firstNode, secondNode) ∈ spineJoinEvents atoms state →
    firstNode < (processSpine state atoms).nextFresh
      ∧ secondNode < (processSpine state atoms).nextFresh
  | [], _, _, _, _, _, membership => by cases membership
  | atom :: restAtoms, state, fresh, nfPos, firstNode, secondNode, membership => by
      cases pairMemAppendCases (stepAtomJoinEvents state atom)
          (spineJoinEvents restAtoms (stepAtom state atom)) (firstNode, secondNode)
          membership with
      | inl inAtomEvents =>
          have atomBound := stepAtomJoinEvents_valuesBounded state atom fresh nfPos
            firstNode secondNode inAtomEvents
          exact ⟨Nat.lt_of_lt_of_le atomBound.1
              (processSpine_nextFresh_le restAtoms (stepAtom state atom)),
            Nat.lt_of_lt_of_le atomBound.2
              (processSpine_nextFresh_le restAtoms (stepAtom state atom))⟩
      | inr inRestEvents =>
          exact spineJoinEvents_valuesBounded restAtoms (stepAtom state atom)
            (stepAtom_wireStateFresh state atom fresh nfPos)
            (Nat.lt_of_lt_of_le nfPos (stepAtom_nextFresh_le state atom))
            firstNode secondNode inRestEvents

/-- Cell-granularity trace value bound (the fold over the cell's spine block). -/
theorem runMatchingCell_joinEvents_valuesBounded {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fresh : WireStateFresh state) (nfPos : 0 < state.nextFresh) :
    ∀ firstNode secondNode : Nat,
    (firstNode, secondNode) ∈ spineJoinEvents (cell.spineDiff leftAcc rightAcc []) state →
    firstNode < (runMatchingCell state leftAcc rightAcc cell).nextFresh
      ∧ secondNode < (runMatchingCell state leftAcc rightAcc cell).nextFresh :=
  spineJoinEvents_valuesBounded (cell.spineDiff leftAcc rightAcc []) state fresh nfPos

/-! ## Pointwise map surgery on event lists -/

/-- Two pair-renames that agree on every member produce the same mapped list. -/
theorem listMapPairCongr_onMembers (sigmaOne sigmaTwo : Nat → Nat) :
    (events : List (Nat × Nat)) →
    (∀ firstNode secondNode : Nat, (firstNode, secondNode) ∈ events →
      sigmaOne firstNode = sigmaTwo firstNode ∧ sigmaOne secondNode = sigmaTwo secondNode) →
    events.map (fun event => (sigmaOne event.1, sigmaOne event.2))
      = events.map (fun event => (sigmaTwo event.1, sigmaTwo event.2))
  | [], _ => rfl
  | (firstNode, secondNode) :: restEvents, agreesOnMembers => by
      show (sigmaOne firstNode, sigmaOne secondNode)
            :: restEvents.map (fun event => (sigmaOne event.1, sigmaOne event.2))
          = (sigmaTwo firstNode, sigmaTwo secondNode)
            :: restEvents.map (fun event => (sigmaTwo event.1, sigmaTwo event.2))
      rw [(agreesOnMembers firstNode secondNode (List.Mem.head restEvents)).1,
        (agreesOnMembers firstNode secondNode (List.Mem.head restEvents)).2,
        listMapPairCongr_onMembers sigmaOne sigmaTwo restEvents
          (fun innerFirst innerSecond innerMembership => agreesOnMembers innerFirst innerSecond
            (List.Mem.tail (firstNode, secondNode) innerMembership))]

/-- A pair-rename that fixes every member leaves the list unchanged. -/
theorem listMapPairEqSelf_onMembers (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) →
    (∀ firstNode secondNode : Nat, (firstNode, secondNode) ∈ events →
      sigma firstNode = firstNode ∧ sigma secondNode = secondNode) →
    events.map (fun event => (sigma event.1, sigma event.2)) = events
  | [], _ => rfl
  | (firstNode, secondNode) :: restEvents, fixesMembers => by
      show (sigma firstNode, sigma secondNode)
            :: restEvents.map (fun event => (sigma event.1, sigma event.2))
          = (firstNode, secondNode) :: restEvents
      rw [(fixesMembers firstNode secondNode (List.Mem.head restEvents)).1,
        (fixesMembers firstNode secondNode (List.Mem.head restEvents)).2,
        listMapPairEqSelf_onMembers sigma restEvents
          (fun innerFirst innerSecond innerMembership => fixesMembers innerFirst innerSecond
            (List.Mem.tail (firstNode, secondNode) innerMembership))]

/-- Two pair-renames compose pointwise. -/
theorem listMapPairCompose (sigmaOuter sigmaInner : Nat → Nat) :
    (events : List (Nat × Nat)) →
    (events.map (fun event => (sigmaInner event.1, sigmaInner event.2))).map
        (fun event => (sigmaOuter event.1, sigmaOuter event.2))
      = events.map (fun event => (sigmaOuter (sigmaInner event.1),
          sigmaOuter (sigmaInner event.2)))
  | [] => rfl
  | (firstNode, secondNode) :: restEvents =>
      congrArg ((sigmaOuter (sigmaInner firstNode), sigmaOuter (sigmaInner secondNode)) :: ·)
        (listMapPairCompose sigmaOuter sigmaInner restEvents)

/-! ## Honesty marker -/

/-- **Honesty marker — the rename-support kit for the sigma-witness assembly is PROVED.**  The
base correspondence (`componentView_ofFreshRename`: a below-bound-fixing, above-bound-keeping,
injective rename is invisible to the component view on fresh-bounded links), the trace value
bounds (`spineJoinEvents_valuesBounded` and its run corollary: every event value lies below the
run's output counter), and the pointwise map surgery
(`listMapPairCongr_onMembers`/`listMapPairEqSelf_onMembers`/`listMapPairCompose`) that converts
the trace congruence's per-block `freshShiftAbove` renames into the single `blockRotate` witness.
NOT yet covered: the final composition itself — instantiating the trace congruence per block at
the two-core setup, exchanging the blocks, and bundling `MatchingComponentSim`.  `= true`. -/
def fxMode_hasMatchingRenameSupportKit : Bool := true

end FX1Poly.Polygraph
