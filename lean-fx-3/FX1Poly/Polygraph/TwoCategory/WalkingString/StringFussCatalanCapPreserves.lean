import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanNonCrossing

/-! # WalkingString — the CAP freshness leg + the honest CAP-orient / capPin wall (FC-3b, CAP side)

The CUP legs of the joint fold invariant are CLOSED: orientation (`stringOrientationDiscipline_stepCup`), freshness
(`StringWireStateFresh_stepCup`), forest (`stringUnionFindForest_stepCup`), non-crossing (`stringNonCrossing_stepCup`).
This file ships the CAP leg that closes UNCONDITIONALLY — freshness preservation across a cap — and localizes the
remaining CAP obligations (the orientation survivor P4, non-crossing preservation, and `capPin`) to their exact shape.

## What closes here

  * ★ `StringWireStateFresh_stepCap` — a cap preserves freshness: it removes two open wires (still members of the old
    frontier) and, in the join branch, adds the single edge `(rootLeft, rootRight)` whose endpoints are roots of two
    EXISTING (below-`nextFresh`) wires — hence below `nextFresh` (`stringUnionFindRootOf_lt_of_linksBelow`); the fresh
    counter is unchanged.  So the fold's freshness invariant survives every cap.

The cap analog of `natListInsertAt_mem` — `natListRemoveTwoAt_mem` (a survivor of a two-drop is an old member) — is the
list plumbing this needs, re-derived structurally over the shared `natListRemoveTwoAt`.

## The honest wall (the CAP orientation survivor P4 + `capPin`)

The CAP case of the ORIENTATION discipline is the genuinely-new "planar survivor" P4: after a cap merges two DISTINCT
arcs meeting at the window `(p, p+1)`, the two survivors read a CUP word ONLY because the arcs were NON-crossing
(`StringNonCrossing`).  Its zero-axiom re-derivation over the bare `WireState` — the join-branch component surgery
plus the planarity nesting argument (the string port of the shipped `arcNonCrossing_stepCapArc` /
`ArcNonCrossingCapMain`) — is a multi-round arc, as is `capPin` (the label-fold boundary tracking that a cap window
reads its `generatorDom` cap word).  Both are named precisely in the honesty markers; `fxString_hasNoLoopsTheorem`
stays `false`, HONESTLY, with the CUP side + the CAP freshness leg + the forest/fuel/non-crossing infrastructure all
SHIPPED and the residual localized to exactly the CAP orient survivor + `capPin`.

Raw Lean 4 + Init; the freshness preservation is a branch split with the shared root-below-bound lemma, the list
plumbing is structural recursion.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cap survivor is an old member -/

/-- An in-range `natListGetAt` read is a genuine list member (re-declared privately). -/
private theorem natListGetAtMemCAP : (wires : List Nat) → (index : Nat) → index < wires.length →
    natListGetAt wires index ∈ wires
  | [], index, hindex => absurd hindex (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, hindex => List.Mem.tail _ (natListGetAtMemCAP rest index (Nat.lt_of_succ_lt_succ hindex))

/-- ★ **A survivor of a two-drop is an old member.**  Every wire remaining after `natListRemoveTwoAt` at `position`
was already in the list.  Structural recursion mirroring `natListRemoveTwoAt`'s arms (the recursive arm keeps `head ::
second :: rest` explicit so the two-element discriminant reduces, following the shipped `listGetAtD_removeTwoAt`). -/
private theorem natListRemoveTwoAt_mem : (wires : List Nat) → (position : Nat) → (value : Nat) →
    value ∈ natListRemoveTwoAt wires position → value ∈ wires
  | [], _, _, memberOfEmpty => memberOfEmpty
  | [_], 0, _, memberOfSingle => memberOfSingle
  | _ :: _ :: _, 0, _, memberOfRest => List.Mem.tail _ (List.Mem.tail _ memberOfRest)
  | [_], _ + 1, _, memberOfSingle => memberOfSingle
  | head :: second :: rest, position + 1, value, memberOfCons => by
      have memberForm : value ∈ head :: natListRemoveTwoAt (second :: rest) position := memberOfCons
      cases memberForm with
      | head => exact List.Mem.head _
      | tail _ memberOfRest =>
          exact List.Mem.tail _ (natListRemoveTwoAt_mem (second :: rest) position value memberOfRest)

/-! ## ★ Freshness is preserved by a CAP step -/

/-- ★★ **Freshness is preserved by a CAP step.**  `stepCap` removes the two window wires (survivors are old members,
still `< nextFresh` by `natListRemoveTwoAt_mem` + the old freshness) and leaves `nextFresh` unchanged; its links are
either the old links (loop branch) or the old links plus one edge `(rootLeft, rootRight)` whose endpoints are the
roots of the two window wires — both roots of EXISTING (`< nextFresh`) wires, hence `< nextFresh`
(`stringUnionFindRootOf_lt_of_linksBelow`).  So the new state is again `StringWireStateFresh`.  The CAP leg of the
joint invariant's freshness component, DISCHARGED. -/
theorem StringWireStateFresh_stepCap (state : WireState) (position : Nat)
    (windowInRange : position + 1 < state.openWires.length) (fresh : StringWireStateFresh state) :
    StringWireStateFresh (stepCap state position) := by
  have parentsBounded := StringWireStateFresh_parentsBelow fresh
  have leftBelow : natListGetAt state.openWires position < state.nextFresh :=
    fresh.openBelow _ (natListGetAtMemCAP state.openWires position (Nat.lt_of_succ_lt windowInRange))
  have rightBelow : natListGetAt state.openWires (position + 1) < state.nextFresh :=
    fresh.openBelow _ (natListGetAtMemCAP state.openWires (position + 1) windowInRange)
  have rootLeftBelow : unionFindRootOf state.links (natListGetAt state.openWires position) < state.nextFresh :=
    stringUnionFindRootOf_lt_of_linksBelow state.nextFresh state.links parentsBounded _ leftBelow
  have rootRightBelow : unionFindRootOf state.links (natListGetAt state.openWires (position + 1)) < state.nextFresh :=
    stringUnionFindRootOf_lt_of_linksBelow state.nextFresh state.links parentsBounded _ rightBelow
  have nfEq : (stepCap state position).nextFresh = state.nextFresh := by
    dsimp only [stepCap]; split <;> rfl
  have owEq : (stepCap state position).openWires = natListRemoveTwoAt state.openWires position := by
    dsimp only [stepCap]; split <;> rfl
  refine ⟨fun wire memberOfNew => ?_, fun edge memberOfNew => ?_⟩
  · rw [nfEq]
    rw [owEq] at memberOfNew
    exact fresh.openBelow wire (natListRemoveTwoAt_mem state.openWires position wire memberOfNew)
  · rw [nfEq]
    show edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh
    dsimp only [stepCap] at memberOfNew
    split at memberOfNew
    · exact fresh.linksBelow edge memberOfNew
    · have joinForm : unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1))
          = (if unionFindRootOf state.links (natListGetAt state.openWires position)
                == unionFindRootOf state.links (natListGetAt state.openWires (position + 1)) then state.links
              else (unionFindRootOf state.links (natListGetAt state.openWires position),
                    unionFindRootOf state.links (natListGetAt state.openWires (position + 1))) :: state.links) := rfl
      rw [joinForm] at memberOfNew
      split at memberOfNew
      · exact fresh.linksBelow edge memberOfNew
      · cases memberOfNew with
        | head => exact ⟨rootLeftBelow, rootRightBelow⟩
        | tail _ memberOfOld => exact fresh.linksBelow edge memberOfOld

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the CAP freshness leg of the joint fold invariant is CLOSED.**  `StringWireStateFresh_stepCap`
proves freshness survives every cap: the survivors are old members (`natListRemoveTwoAt_mem`), the fresh counter is
unchanged, and the join branch's single new edge has both endpoints roots of existing below-`nextFresh` wires (so
below `nextFresh`, via `stringUnionFindRootOf_lt_of_linksBelow`).  Together with the shipped CUP freshness
(`StringWireStateFresh_stepCup`), forest (`stringUnionFindForest_stepCup` / `_stepCap`), and CUP non-crossing /
orientation legs, the joint invariant's freshness + forest components are preserved by BOTH cup and cap.  All
UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxString_hasCapFreshnessPreservation : Bool := true

/-- **OPEN (honest, LOCALIZED) — the CAP orientation survivor P4 + `capPin` stay a multi-round arc.**  (Marker named
as the POSITIVE capability, matching the sibling `…Preservation := true` convention: `false` = not-yet-established.)
With the CUP
side CLOSED (orientation + non-crossing + freshness + forest) and the CAP freshness + forest legs shipped, the
no-loops flip owes exactly the CAP side of the ORIENTATION discipline and `capPin`:

  * **CAP orient survivor (P4)** — after `stepCap` merges the two DISTINCT arcs meeting at the window `(p, p+1)`, the
    two survivors read a CUP word.  The proof: the window labels are a cap word (a cap fires on its `generatorDom`),
    so by the CHIRALITY refutation the window is distinct-component (`stringDisciplinedCap_windowDistinct`); the join
    merges the two survivor components, and — crucially — the two survivors NEST by planarity (`StringNonCrossing`,
    now preserved across cups by `stringNonCrossing_stepCup`), so the exposed pair reads a cup word.  This is the
    string port of the shipped `arcNonCrossing_stepCapArc` / `ArcNonCrossingCapMain`; its zero-axiom re-derivation
    over the bare `WireState` (the join-branch component surgery + the survivor-nesting read) is the genuinely-new
    multi-round work, together with the CAP non-crossing preservation (`StringNonCrossing (stepCap …)`).
  * **`capPin`** — the label companion fold `advanceLabels` tracks the intermediate 1-cell, so a cap's window equals
    its `generatorDom` cap word (in range, a non-cup word).  This is the string port of `ArcBoundaryTracking`,
    label-valued.

So `fxString_hasNoLoopsTheorem` (in `StringFussCatalan`) STAYS `false`, HONESTLY, with the frontier moved to exactly
the CAP orient survivor P4 + CAP non-crossing preservation + `capPin`: everything ELSE the flip needs — the discipline,
the chirality refutation, the seed, the forest + fuel normalization, the CUP orientation + non-crossing + freshness
legs, and the CAP freshness + forest legs — is SHIPPED zero-axiom.  `= false`. -/
def fxString_hasCapOrientSurvivorPreservation : Bool := false

end FX1Poly.Polygraph
