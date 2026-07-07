import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # PureCapSurvivorUnlinked — brick (2a) of the pure-cap survivor readoff (Piece II tail)

The survivor re-ranking needs, for a pure-CAP block run from the canonical seed, that every
SURVIVING open wire is `ArcNodeUnlinked` — it sits in no recorded union-find edge, so its
component is the singleton `{itself}`.  A cap either closes a loop (links unchanged) or joins the
two ADJACENT read wires it then removes; the joined pair leaves the open-wire list, so no
surviving wire is ever an endpoint of the new edge.  The one thing that could break this is a
value COLLISION — a surviving wire whose id equals one of the two consumed reads — and the shipped
open-wire distinctness invariant (`WireListDistinct`) forbids exactly that: distinct positions
carry distinct ids, so the two removed reads never reappear among the survivors.

The fold is COUPLED: it threads
  * `WireListDistinct openWires` (shipped preservation `stepCap_wireListDistinct`),
  * `openWires.length = boundaryLength` (shipped `stepAtom_openWires_tracksBoundary` off the
    `SpineBoundaryChained` chain — this pins each cap's consumed window IN RANGE), and
  * the new invariant `∀ w ∈ openWires, ArcNodeUnlinked links w`,
and re-establishes all three across each `stepCap`.  No freshness / positivity needed: caps
allocate nothing and the argument is purely combinatorial.

Raw Lean 4 + Init; structural / `AllCapArity` recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat / membership plumbing -/

/-- A strict `<` yields `≠` (hand-rolled; the core cancellation lemmas leak `propext`). -/
private theorem posNe {smaller larger : Nat} (strict : smaller < larger) : smaller ≠ larger :=
  fun wereEqual => absurd (wereEqual ▸ strict) (Nat.lt_irrefl larger)

/-- A member of a `Nat` list is the positional read at some in-range index — the converse of
`natListGetAt_mem_inRange`, structural on the list. -/
theorem mem_imp_getAt {target : Nat} :
    (wires : List Nat) → target ∈ wires →
    ∃ index, index < wires.length ∧ natListGetAt wires index = target
  | [], membership => nomatch membership
  | _ :: rest, membership => by
      cases membership with
      | head => exact ⟨0, Nat.succ_pos rest.length, rfl⟩
      | tail _ tailMem =>
          obtain ⟨index, indexLt, indexEq⟩ := mem_imp_getAt rest tailMem
          exact ⟨index + 1, Nat.succ_lt_succ indexLt, indexEq⟩

/-- Two DISTINCT in-range positions of a positionally-distinct list carry distinct reads. -/
theorem distinctReadNe (wires : List Nat) (distinct : WireListDistinct wires)
    (firstPos secondPos : Nat) (firstLt : firstPos < wires.length)
    (secondLt : secondPos < wires.length) (posNeq : firstPos ≠ secondPos) :
    natListGetAt wires firstPos ≠ natListGetAt wires secondPos := by
  cases Nat.lt_or_ge firstPos secondPos with
  | inl firstLtSecond => exact distinct firstPos secondPos firstLtSecond secondLt
  | inr secondLeFirst =>
      have secondLtFirst : secondPos < firstPos :=
        Nat.lt_of_le_of_ne secondLeFirst (fun secondEqFirst => posNeq secondEqFirst.symm)
      exact fun readsEqual => distinct secondPos firstPos secondLtFirst firstLt readsEqual.symm

/-- ★ **The two consumed reads never reappear among the survivors.**  Given open-wire
distinctness and an in-range removal window, every surviving wire's id differs from BOTH read
ids at the removal window — because it sits at a position other than the two removed ones, and
distinct positions carry distinct ids. -/
theorem ne_reads_of_mem_natListRemoveTwoAt (wires : List Nat) (position : Nat)
    (inRange : position + 2 ≤ wires.length) (distinct : WireListDistinct wires)
    (survivor : Nat) (survivorMem : survivor ∈ natListRemoveTwoAt wires position) :
    natListGetAt wires position ≠ survivor ∧ natListGetAt wires (position + 1) ≠ survivor := by
  obtain ⟨survivorIndex, survivorIndexLt, survivorRead⟩ :=
    mem_imp_getAt (natListRemoveTwoAt wires position) survivorMem
  have removedLength : (natListRemoveTwoAt wires position).length + 2 = wires.length :=
    natListRemoveTwoAt_length wires position inRange
  have positionLt : position < wires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) inRange
  have positionSuccLt : position + 1 < wires.length :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) position) inRange
  obtain ⟨originalPos, originalPosLt, posNeOriginal, succNeOriginal, originalRead⟩ :
      ∃ originalPos, originalPos < wires.length ∧ position ≠ originalPos
        ∧ position + 1 ≠ originalPos ∧ natListGetAt wires originalPos = survivor := by
    cases Nat.lt_or_ge survivorIndex position with
    | inl below =>
        refine ⟨survivorIndex, Nat.lt_trans below positionLt, (posNe below).symm,
          (posNe (Nat.lt_trans below (Nat.lt_succ_self position))).symm, ?_⟩
        exact (natListGetAt_natListRemoveTwoAt_below wires position survivorIndex below).symm.trans
          survivorRead
    | inr atOrAbove =>
        obtain ⟨offset, offsetEq⟩ := Nat.le.dest atOrAbove
        have survivorReadShifted :
            natListGetAt (natListRemoveTwoAt wires position) (position + offset) = survivor :=
          offsetEq.symm ▸ survivorRead
        have originalRead : natListGetAt wires (position + offset + 2) = survivor :=
          (natListGetAt_natListRemoveTwoAt_pastPair wires position offset inRange).symm.trans
            survivorReadShifted
        have shiftedIndexLt : position + offset < (natListRemoveTwoAt wires position).length :=
          offsetEq.symm ▸ survivorIndexLt
        have originalPosLt : position + offset + 2 < wires.length :=
          removedLength ▸ Nat.add_lt_add_right shiftedIndexLt 2
        have posLtOriginal : position < position + offset + 2 :=
          Nat.lt_of_le_of_lt (Nat.le_add_right position offset)
            (Nat.lt_add_of_pos_right (by decide))
        have succLtOriginal : position + 1 < position + offset + 2 :=
          Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.le_add_right position offset))
            (Nat.lt_succ_self (position + offset + 1))
        exact ⟨position + offset + 2, originalPosLt, posNe posLtOriginal, posNe succLtOriginal,
          originalRead⟩
  refine ⟨?_, ?_⟩
  · rw [← originalRead]
    exact distinctReadNe wires distinct position originalPos positionLt originalPosLt posNeOriginal
  · rw [← originalRead]
    exact distinctReadNe wires distinct (position + 1) originalPos positionSuccLt originalPosLt
      succNeOriginal

/-! ## The per-step preservation -/

/-- ★ **A cap step keeps every surviving open wire unlinked.**  The loop branch leaves the links
untouched; the join branch adds the edge connecting the two consumed reads, and every surviving
wire misses both (`ne_reads_of_mem_natListRemoveTwoAt`), so `arcNodeUnlinked_unionFindJoin`
preserves its unlinkedness. -/
theorem stepCap_allUnlinked (state : WireState) (position : Nat)
    (inRange : position + 2 ≤ state.openWires.length)
    (distinct : WireListDistinct state.openWires)
    (allUnlinked : ∀ w ∈ state.openWires, ArcNodeUnlinked state.links w) :
    ∀ w ∈ (stepCap state position).openWires,
      ArcNodeUnlinked (stepCap state position).links w := by
  intro survivor survivorMem
  rw [stepCap_openWires] at survivorMem
  have survivorInOrig : survivor ∈ state.openWires :=
    mem_natListRemoveTwoAt state.openWires position survivor survivorMem
  have survivorUnlinkedOld : ArcNodeUnlinked state.links survivor := allUnlinked survivor survivorInOrig
  rw [stepCap_links]
  by_cases sameComp : isSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) = true
  · rw [if_pos sameComp]; exact survivorUnlinkedOld
  · rw [if_neg sameComp]
    obtain ⟨leftMiss, rightMiss⟩ := ne_reads_of_mem_natListRemoveTwoAt state.openWires position
      inRange distinct survivor survivorMem
    exact arcNodeUnlinked_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) survivorUnlinkedOld leftMiss rightMiss

/-! ## The coupled fold -/

/-- ★ **A pure-cap block keeps every open wire unlinked** — coupled fold threading
`WireListDistinct` + `openWires.length = boundaryLength` (via `SpineBoundaryChained`) + the
unlinked invariant across each `stepCap`.  By induction on the `AllCapArity` witness. -/
theorem processSpine_allUnlinked_ofAllCapArity {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atoms : List (SpineAtom signature sourceMode targetMode)) (pureCap : AllCapArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    WireListDistinct state.openWires →
    (∀ w ∈ state.openWires, ArcNodeUnlinked state.links w) →
    ∀ w ∈ (processSpine state atoms).openWires,
      ArcNodeUnlinked (processSpine state atoms).links w := by
  induction pureCap with
  | nil => intro state _ _ _ _ allUnlinked; exact allUnlinked
  | cons hasCapDomArity hasCapCodArity _restAllCap restIH =>
      rename_i headAtom rest
      intro state boundaryLength lengthEq chained distinct allUnlinked
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have arity : AtomHasCupOrCapArity headAtom := Or.inr ⟨hasCapDomArity, hasCapCodArity⟩
      have entryTracks : state.openWires.length = headAtom.domBoundaryLength :=
        lengthEq.trans headFires.symm
      have inRange : headAtom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryTracks]
        dsimp only [SpineAtom.domBoundaryLength]
        rw [hasCapDomArity]
        exact Nat.le_add_right (headAtom.leftContext.length + 2) headAtom.rightContext.length
      have stepEq : stepAtom state headAtom = stepCap state headAtom.leftContext.length :=
        stepAtom_ofCapArity state headAtom hasCapDomArity hasCapCodArity
      have newLength : (stepAtom state headAtom).openWires.length = headAtom.codBoundaryLength :=
        stepAtom_openWires_tracksBoundary state headAtom arity entryTracks
      have newDistinct : WireListDistinct (stepAtom state headAtom).openWires := by
        rw [stepEq]; exact stepCap_wireListDistinct state headAtom.leftContext.length distinct
      have newAllUnlinked : ∀ w ∈ (stepAtom state headAtom).openWires,
          ArcNodeUnlinked (stepAtom state headAtom).links w := by
        rw [stepEq]
        exact stepCap_allUnlinked state headAtom.leftContext.length inRange distinct allUnlinked
      show ∀ w ∈ (processSpine (stepAtom state headAtom) rest).openWires,
        ArcNodeUnlinked (processSpine (stepAtom state headAtom) rest).links w
      exact restIH (stepAtom state headAtom) headAtom.codBoundaryLength newLength tailChained
        newDistinct newAllUnlinked

/-- ★ **From the canonical seed, a pure-cap block keeps every open wire unlinked.**  The seed's
open wires are the range (`WireListDistinct` + length `bottomCount`), its links are empty (every
node trivially unlinked), and `SpineBoundaryChained bottomCount atoms` pins the caps in range.
Every SURVIVING open wire of a pure-cap matching is therefore its own singleton component — the
connectivity seed of the through-strand survivor re-ranking. -/
theorem processSpine_openWires_unlinked_ofAllCapArity_seed {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) (pureCap : AllCapArity atoms)
    (chained : SpineBoundaryChained bottomCount atoms) :
    ∀ w ∈ (processSpine (canonicalMatchingSeed bottomCount) atoms).openWires,
      ArcNodeUnlinked (processSpine (canonicalMatchingSeed bottomCount) atoms).links w :=
  processSpine_allUnlinked_ofAllCapArity atoms pureCap (canonicalMatchingSeed bottomCount)
    bottomCount (canonicalMatchingSeed_wireCount bottomCount) chained
    (canonicalMatchingSeed_wireListDistinct bottomCount)
    (fun _ _ _edge edgeMem => nomatch edgeMem)

/-! ## Honesty marker -/

/-- **Honesty marker — the pure-cap survivor unlinked invariant (2a) is SHIPPED.**  Every
surviving open wire of a pure-cap block run from the canonical seed is `ArcNodeUnlinked` — a
singleton component — proven by a coupled fold pairing the shipped `WireListDistinct` invariant
with unlinked-preservation across each in-range `stepCap`.  This is the connectivity seed of the
survivor readoff (2b): a survivor bottom port shares no component with any other bottom port, so
its partner scan front-fails.  `= true`. -/
def fxMode_hasPureCapSurvivorUnlinked : Bool := true

end FX1Poly.Polygraph
