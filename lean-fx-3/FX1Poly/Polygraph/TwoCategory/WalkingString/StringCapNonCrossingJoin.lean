import FX1Poly.Polygraph.TwoCategory.WalkingString.StringBoundaryCensus

/-! # WalkingString — the JOIN-branch CAP non-crossing consumer (FC-5, P2)

The LOOP-branch cap non-crossing (`stringNonCrossing_stepCap_loopBranch`, in `StringFussCatalanCapNonCrossing`) is
CLOSED.  Its JOIN-branch dual — a cap that FUSES two distinct arcs preserves planarity — is the FC-5 P2 residual, the
string port of the shipped `arcNonCrossing_stepCapArc` (`ArcNonCrossingCapMain`).  This file CLOSES it by CONSUMING the
FC-5 P1 boundary census (`StringBoundaryCensus`, `stringBoundaryCensus_fromCell`) shipped in `StringBoundaryCensus`.

## The uniform argument (both branches at once)

`stepCap`'s link update is ALWAYS the direct `unionFindJoin state.links leftWire rightWire`
(`stepCap_links_eq_unionFindJoin`, covering the loop branch as a no-op join), and every surviving open wire reads its
old wire under `capRemap` (`stringStepCap_read_oldIndex`, strictly monotone).  So a candidate post-cap interleaving
`lowA < lowB < highA < highB` backmaps to four OLD open-wire indices `a < b < c < d` (each strictly OFF the two-slot
window `{position, position+1}`, `capRemap_offWindow`), whose two arcs `(a,c)`, `(b,d)` are same-component in the
JOINED links.  The join membership DISPATCHES each arc three ways
(`sameComponent_unionFindJoin_dispatch`, over the byte-identical forest via `stringForest_toUnionFindForest`):

  * BASE — the arc was already same-component in the OLD links;
  * LEG — one endpoint reaches the LEFT window wire (`position`), the other the RIGHT (`position+1`);
  * SWAP — the mirror.

Of the nine combos, the FOUR where BOTH arcs are non-free (leg/swap × leg/swap) are refuted by the CENSUS: both arcs'
endpoints then reach the LEFT window wire, so `openSlot position` shares a component with three distinct boundary ends
— impossible.  The FIVE surviving combos each EXHIBIT an OLD crossing quadruple (chosen from the six indices
`{a,b,c,d, position, position+1}` by an off-window position split), which the OLD non-crossing forbids.

Raw Lean 4 + Init; the dispatch is shipped, the census is shipped, the position splits are additive `Nat` arithmetic
on `capRemap`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## `capRemap` lands strictly off the two-slot window -/

/-- ★ **Every `capRemap` image is strictly OFF the window `{position, position+1}`.**  A new index below the window maps
to itself (`< position`); at/above the window maps `+2` (`≥ position + 2`).  Neither hits `position` or `position+1` —
the two consumed window slots that `stepCap` removed. -/
theorem capRemap_offWindow (position index : Nat) :
    capRemap position index < position ∨ position + 2 ≤ capRemap position index := by
  show (if index < position then index else index + 2) < position
    ∨ position + 2 ≤ (if index < position then index else index + 2)
  cases Nat.decLt index position with
  | isTrue below => rw [if_pos below]; exact Or.inl below
  | isFalse notBelow =>
      rw [if_neg notBelow]
      exact Or.inr (Nat.add_le_add_right (Nat.le_of_not_lt notBelow) 2)

/-- `position ≠ index` whenever `index` is off the window. -/
private theorem positionNeOffWindow (position index : Nat)
    (offWindow : index < position ∨ position + 2 ≤ index) : position ≠ index := by
  cases offWindow with
  | inl below => exact (Nat.ne_of_lt below).symm
  | inr above =>
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) above)

/-- `position < index` whenever `position + 2 ≤ index`. -/
private theorem positionLtOfAbove (position index : Nat) (above : position + 2 ≤ index) :
    position < index :=
  Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) above

/-- `position + 1 < index` whenever `position + 2 ≤ index`. -/
private theorem positionSuccLtOfAbove (position index : Nat) (above : position + 2 ≤ index) :
    position + 1 < index :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) above

/-! ## The census refutation over three open slots -/

/-- ★ **A census hub violation over three OPEN slots.**  If a hub open slot shares a union-find component with two
other distinct valid open slots, that is three distinct boundary end tokens on one component — forbidden by
`StringBoundaryCensus`.  This is the exact fact the four "both arcs non-free" cap-join combos violate (both arcs' legs
reach the LEFT window slot). -/
private theorem stringNonCrossingCensusRefute (seedBoundary : Nat) (state : WireState)
    (census : StringBoundaryCensus seedBoundary state) (hub leftIdx rightIdx : Nat)
    (hubLt : hub < state.openWires.length) (leftLt : leftIdx < state.openWires.length)
    (rightLt : rightIdx < state.openWires.length)
    (hubNeLeft : hub ≠ leftIdx) (hubNeRight : hub ≠ rightIdx) (leftNeRight : leftIdx ≠ rightIdx)
    (hubReachesLeft : isSameComponent state.links (natListGetAt state.openWires hub)
        (natListGetAt state.openWires leftIdx) = true)
    (hubReachesRight : isSameComponent state.links (natListGetAt state.openWires hub)
        (natListGetAt state.openWires rightIdx) = true) : False :=
  census (ArcEndToken.openSlot hub) (ArcEndToken.openSlot leftIdx) (ArcEndToken.openSlot rightIdx)
    hubLt leftLt rightLt
    (fun slotsEqual => hubNeLeft (ArcEndToken.openSlot.inj slotsEqual))
    (fun slotsEqual => hubNeRight (ArcEndToken.openSlot.inj slotsEqual))
    (fun slotsEqual => leftNeRight (ArcEndToken.openSlot.inj slotsEqual))
    hubReachesLeft hubReachesRight

/-! ## ★★ The JOIN-branch (uniform) CAP non-crossing preservation -/

/-- ★★ **A CAP step preserves the non-crossing (planarity) invariant.**  Consuming the FC-5 P1 boundary census, a cap
step carries `StringNonCrossing` forward.  UNIFORM over both branches: `stepCap`'s links are always the direct
`unionFindJoin`, so the join dispatch handles the loop branch (no-op join) and the join branch alike.  Every candidate
post-cap interleaving backmaps under `capRemap` to four old indices `a < b < c < d` off the window; the join membership
dispatches each arc into base/leg/swap; the four both-non-free combos are census violations, and the five surviving
combos each exhibit an old crossing the old non-crossing forbids.  Zero-axiom.  (Together with the shipped
`stringNonCrossing_stepCap_loopBranch`, this is the FULL cap non-crossing preservation.) -/
theorem stringNonCrossing_stepCap (seedBoundary : Nat) (state : WireState) (position : Nat)
    (forest : stringIsUnionFindForest state.links)
    (capInRange : position + 2 ≤ state.openWires.length)
    (oldCensus : StringBoundaryCensus seedBoundary state)
    (oldNonCrossing : StringNonCrossing state) :
    StringNonCrossing (stepCap state position) := by
  intro lowA lowB highA highB lowALtLowB lowBLtHighA highALtHighB highBLt sameA sameB
  have sharedForest : isUnionFindForest state.links :=
    stringForest_toUnionFindForest state.links forest
  have windowInRange : position + 1 < state.openWires.length := Nat.lt_of_succ_le capInRange
  have positionLt : position < state.openWires.length := Nat.lt_of_succ_lt windowInRange
  -- new-index ranges (from the interleaving)
  have highBLtNew : highB < (stepCap state position).openWires.length := highBLt
  have highALtNew : highA < (stepCap state position).openWires.length :=
    Nat.lt_trans highALtHighB highBLtNew
  have lowBLtNew : lowB < (stepCap state position).openWires.length :=
    Nat.lt_trans lowBLtHighA highALtNew
  have lowALtNew : lowA < (stepCap state position).openWires.length :=
    Nat.lt_trans lowALtLowB lowBLtNew
  -- backmap reads + old-range facts (the four old indices are `capRemap position lowA/lowB/highA/highB`)
  obtain ⟨readA, aLt⟩ := stringStepCap_read_oldIndex state position lowA windowInRange lowALtNew
  obtain ⟨readB, bLt⟩ := stringStepCap_read_oldIndex state position lowB windowInRange lowBLtNew
  obtain ⟨readC, cLt⟩ := stringStepCap_read_oldIndex state position highA windowInRange highALtNew
  obtain ⟨readD, dLt⟩ := stringStepCap_read_oldIndex state position highB windowInRange highBLtNew
  have aLtb : capRemap position lowA < capRemap position lowB :=
    capRemap_strictMono position lowA lowB lowALtLowB
  have bLtc : capRemap position lowB < capRemap position highA :=
    capRemap_strictMono position lowB highA lowBLtHighA
  have cLtd : capRemap position highA < capRemap position highB :=
    capRemap_strictMono position highA highB highALtHighB
  have offA : capRemap position lowA < position ∨ position + 2 ≤ capRemap position lowA :=
    capRemap_offWindow position lowA
  have offB : capRemap position lowB < position ∨ position + 2 ≤ capRemap position lowB :=
    capRemap_offWindow position lowB
  have offC : capRemap position highA < position ∨ position + 2 ≤ capRemap position highA :=
    capRemap_offWindow position highA
  have offD : capRemap position highB < position ∨ position + 2 ≤ capRemap position highB :=
    capRemap_offWindow position highB
  -- rewrite the two arcs onto the joined old links
  have linksEq : (stepCap state position).links
      = unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) :=
    stepCap_links_eq_unionFindJoin state position
  rw [linksEq, readA, readC] at sameA
  rw [linksEq, readB, readD] at sameB
  -- the join dispatch on each arc
  have dispatchA := sameComponent_unionFindJoin_dispatch state.links sharedForest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (natListGetAt state.openWires (capRemap position lowA))
    (natListGetAt state.openWires (capRemap position highA)) sameA
  have dispatchB := sameComponent_unionFindJoin_dispatch state.links sharedForest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (natListGetAt state.openWires (capRemap position lowB))
    (natListGetAt state.openWires (capRemap position highB)) sameB
  -- distinctness of the window slot vs the four backmapped indices
  have posNeA : position ≠ capRemap position lowA :=
    positionNeOffWindow position (capRemap position lowA) offA
  have posNeB : position ≠ capRemap position lowB :=
    positionNeOffWindow position (capRemap position lowB) offB
  have posNeC : position ≠ capRemap position highA :=
    positionNeOffWindow position (capRemap position highA) offC
  have posNeD : position ≠ capRemap position highB :=
    positionNeOffWindow position (capRemap position highB) offD
  rcases dispatchA with baseA | ⟨legAleft, legAright⟩ | ⟨swapAleft, swapAright⟩
  · rcases dispatchB with baseB | ⟨legBleft, legBright⟩ | ⟨swapBleft, swapBright⟩
    · -- (base, base): direct old crossing a < b < c < d
      exact oldNonCrossing (capRemap position lowA) (capRemap position lowB)
        (capRemap position highA) (capRemap position highB) aLtb bLtc cLtd dLt baseA baseB
    · -- (base, leg): arc (a,c) free; b→L, d→R
      rcases offC with cBelow | cAbove
      · -- c below window: crossing (a, b, c, position)
        exact oldNonCrossing (capRemap position lowA) (capRemap position lowB)
          (capRemap position highA) position aLtb bLtc cBelow positionLt
          baseA (isSameComponent_flip state.links _ _ legBleft)
      · rcases offA with aBelow | aAbove
        · -- a below window: crossing (a, position+1, c, d)
          exact oldNonCrossing (capRemap position lowA) (position + 1)
            (capRemap position highA) (capRemap position highB)
            (Nat.lt_succ_of_lt aBelow)
            (positionSuccLtOfAbove position (capRemap position highA) cAbove) cLtd dLt
            baseA legBright
        · -- a above window: crossing (position, position+1, b, d)
          exact oldNonCrossing position (position + 1) (capRemap position lowB)
            (capRemap position highB) (Nat.lt_succ_self position)
            (Nat.lt_trans (positionSuccLtOfAbove position (capRemap position lowA) aAbove) aLtb)
            (Nat.lt_trans bLtc cLtd) dLt legBleft legBright
    · -- (base, swap): arc (a,c) free; d→L, b→R
      rcases offC with cBelow | cAbove
      · -- c below window: crossing (a, b, c, position+1)
        exact oldNonCrossing (capRemap position lowA) (capRemap position lowB)
          (capRemap position highA) (position + 1) aLtb bLtc
          (Nat.lt_succ_of_lt cBelow) windowInRange baseA swapBright
      · rcases offA with aBelow | aAbove
        · -- a below window: crossing (a, position, c, d)
          exact oldNonCrossing (capRemap position lowA) position
            (capRemap position highA) (capRemap position highB) aBelow
            (positionLtOfAbove position (capRemap position highA) cAbove) cLtd dLt baseA swapBleft
        · -- a above window: crossing (position+1, a, b, c)
          exact oldNonCrossing (position + 1) (capRemap position lowA)
            (capRemap position lowB) (capRemap position highA)
            (positionSuccLtOfAbove position (capRemap position lowA) aAbove) aLtb bLtc cLt
            (isSameComponent_flip state.links _ _ swapBright) baseA
  · rcases dispatchB with baseB | ⟨legBleft, legBright⟩ | ⟨swapBleft, swapBright⟩
    · -- (leg, base): a→L, c→R; arc (b,d) free
      rcases offB with bBelow | bAbove
      · rcases offD with dBelow | dAbove
        · -- b, d below window: crossing (b, c, d, position+1)
          exact oldNonCrossing (capRemap position lowB) (capRemap position highA)
            (capRemap position highB) (position + 1) bLtc cLtd
            (Nat.lt_succ_of_lt dBelow) windowInRange baseB
            (isSameComponent_flip state.links _ _ legAright)
        · -- b below, d above: crossing (a, b, position, d)
          exact oldNonCrossing (capRemap position lowA) (capRemap position lowB) position
            (capRemap position highB) aLtb bBelow
            (positionLtOfAbove position (capRemap position highB) dAbove) dLt
            (isSameComponent_flip state.links _ _ legAleft) baseB
      · -- b above window: crossing (position+1, b, c, d)
        exact oldNonCrossing (position + 1) (capRemap position lowB)
          (capRemap position highA) (capRemap position highB)
          (positionSuccLtOfAbove position (capRemap position lowB) bAbove) bLtc cLtd dLt
          legAright baseB
    · -- (leg, leg): both arcs reach the LEFT window slot — census violation
      exact stringNonCrossingCensusRefute seedBoundary state oldCensus position
        (capRemap position lowA) (capRemap position lowB)
        positionLt aLt bLt posNeA posNeB (Nat.ne_of_lt aLtb) legAleft legBleft
    · -- (leg, swap): a→L and d→L — census violation
      exact stringNonCrossingCensusRefute seedBoundary state oldCensus position
        (capRemap position lowA) (capRemap position highB)
        positionLt aLt dLt posNeA posNeD (Nat.ne_of_lt (Nat.lt_trans aLtb (Nat.lt_trans bLtc cLtd)))
        legAleft swapBleft
  · rcases dispatchB with baseB | ⟨legBleft, legBright⟩ | ⟨swapBleft, swapBright⟩
    · -- (swap, base): c→L, a→R; arc (b,d) free
      rcases offB with bBelow | bAbove
      · rcases offD with dBelow | dAbove
        · -- b, d below window: crossing (b, c, d, position)
          exact oldNonCrossing (capRemap position lowB) (capRemap position highA)
            (capRemap position highB) position bLtc cLtd dBelow positionLt
            baseB (isSameComponent_flip state.links _ _ swapAleft)
        · -- b below, d above: crossing (a, b, position+1, d)
          exact oldNonCrossing (capRemap position lowA) (capRemap position lowB) (position + 1)
            (capRemap position highB) aLtb (Nat.lt_succ_of_lt bBelow)
            (positionSuccLtOfAbove position (capRemap position highB) dAbove) dLt swapAright baseB
      · -- b above window: crossing (position, b, c, d)
        exact oldNonCrossing position (capRemap position lowB)
          (capRemap position highA) (capRemap position highB)
          (positionLtOfAbove position (capRemap position lowB) bAbove) bLtc cLtd dLt swapAleft baseB
    · -- (swap, leg): c→L and b→L — census violation
      exact stringNonCrossingCensusRefute seedBoundary state oldCensus position
        (capRemap position highA) (capRemap position lowB)
        positionLt cLt bLt posNeC posNeB (Nat.ne_of_lt bLtc).symm swapAleft legBleft
    · -- (swap, swap): c→L and d→L — census violation
      exact stringNonCrossingCensusRefute seedBoundary state oldCensus position
        (capRemap position highA) (capRemap position highB)
        positionLt cLt dLt posNeC posNeD (Nat.ne_of_lt cLtd) swapAleft swapBleft

/-! ## Honesty marker (flip) -/

/-- **★ ESTABLISHED — the JOIN-branch CAP non-crossing consumer is CLOSED (FC-5, P2).**  `stringNonCrossing_stepCap`
proves `StringNonCrossing (stepCap state position)` from the OLD non-crossing, CONSUMING the FC-5 P1 boundary census
(`StringBoundaryCensus`).  The proof is UNIFORM over both cap branches (`stepCap`'s links are always the direct
`unionFindJoin`), backmaps the candidate interleaving under `capRemap` to four off-window old indices, dispatches each
arc's join membership (`sameComponent_unionFindJoin_dispatch`), refutes the four both-non-free combos by the census
(three boundary ends on the left window slot's component), and exhibits an old crossing for each of the five surviving
combos.  Zero-axiom.  This is exactly the survivor combo analysis the shipped
`fxString_hasCapNonCrossingJoinBranch` docstring bequeathed — the string port of `ArcNonCrossingCapMain`.  `= true`. -/
def fxString_hasCapNonCrossingJoinConsumer : Bool := true

end FX1Poly.Polygraph
