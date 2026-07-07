import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # mode-3 keystone — the VALLEY PROGRESS lemma (the claimed last wall, dissolved STRUCTURALLY)

A prior verdict claimed the valley-normalization driver's "an innermost cup-cap partner pair exists"
premise reduces to reading WHICH cup realizes a boundary arch off the arc structure — the
`arcCupReselection_exists` / head-window readoff that `ArcCupHeadWindowUniversalRefuted` REFUTED (R1c).

★ **That is a CONFLATION.**  The valley normalization needs no arc readoff at all.  It needs only
STRUCTURAL SPINE ADJACENCY, decidable by inspecting two adjacent atoms' cup/cap tags directly.  This file
ships the purely combinatorial fact the driver actually rests on:

  * a spine (list of atoms, each classified as a `cup` — a creation, boundary source-width 0 — or a `cap`)
    that is NOT a cap-block-then-cup-block VALLEY necessarily contains an adjacent `cup`-immediately-then-`cap`
    subsequence (`hasAdjacentCupThenCap_of_not_valley`), witnessed CONCRETELY as a list split
    `spine = capPrefix ++ cupAtom :: capAtom :: suffixRest` (`hasAdjacentCupThenCap_split`).

The proof is the "first-cup" structural argument (§task): let `j` be the FIRST cup; for the spine to have
no cup-then-cap every atom from `j` on must be a cup — a VALLEY.  Contrapositive: a non-valley spine has an
adjacent cup-then-cap.  No arc, no window, no re-selection: a `List`-structural induction on a `Bool` tag.

The located adjacent pair then feeds the SHIPPED straightening/commute moves (see
`SaturatedZigZagStraightening.lean`), classified by the two atoms' whisker windows:

  * `AdjacentCupCapKind.zigZagSharedLeg` (windows share exactly one leg, `|cupLeft − capLeft| = 1`)
    → `zigzagStraightensInVcompContext` / `whiskeredZigZagCollapses` (straighten, generator count −2);
  * `AdjacentCupCapKind.disjointWindows` (windows do not touch, `|cupLeft − capLeft| ≥ 2`)
    → `saturatedGodementExchange` / `snakeCommutesPastDisjointThenStraightens` (commute, then straighten);
  * `AdjacentCupCapKind.orientationExcludedBothLegs` (`cupLeft = capLeft`) — the cap sitting on BOTH fresh
    cup legs; orientation-excluded in the walking adjunction (the unit cup makes an `[R, L]` pair, the counit
    cap wants an `[L, R]` pair, so a cap cannot consume both wires a single cup just created).

Raw Lean 4 + Init; the valley predicate is a `Bool` fold, the progress lemma a structural induction, the
witness split a cons-`List.cons_append` rebuild (all `rfl`).  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The abstract valley predicate over a cup/cap-tagged list

Everything below is parametric in a tag `isCup : α → Bool` (an atom is a `cup` iff `isCup` fires, a `cap`
otherwise).  The genuine content — the first-cup progress argument — is a fact about the tag list alone; the
spine specialization (`SpineAtom.isCupAtom`) is a one-line instantiation. -/

/-- Every remaining atom is a cup: the "cup-block" tail check. -/
def allCups {α : Type u} (isCup : α → Bool) : List α → Bool
  | [] => true
  | atom :: rest => isCup atom && allCups isCup rest

/-- **The VALLEY predicate.**  A tag list is a `cap`-block-then-`cup`-block valley: a run of caps, then a run
of cups.  Decided by walking the caps and, at the first cup, demanding everything after be a cup too. -/
def isCapThenCupValley {α : Type u} (isCup : α → Bool) : List α → Bool
  | [] => true
  | atom :: rest =>
    match isCup atom with
    | true => allCups isCup rest
    | false => isCapThenCupValley isCup rest

/-- **The adjacency witness.**  There is a position in the list where a `cup` (`isCup = true`) is immediately
followed by a `cap` (`isCup = false`) — the "cup-then-cap" the valley-normalizer straightens or commutes.  An
inductive witness (not a `Nat` index) so it carries a concrete list split without `List.get?`/`getElem`. -/
inductive HasAdjacentCupThenCap {α : Type u} (isCup : α → Bool) : List α → Prop where
  /-- The pair is at the FRONT: a cup then a cap. -/
  | here {cupAtom capAtom : α} (isCupHead : isCup cupAtom = true) (isCapNext : isCup capAtom = false)
      (rest : List α) : HasAdjacentCupThenCap isCup (cupAtom :: capAtom :: rest)
  /-- The pair is FURTHER IN: skip one leading atom. -/
  | there (atom : α) {rest : List α} (tail : HasAdjacentCupThenCap isCup rest) :
      HasAdjacentCupThenCap isCup (atom :: rest)

/-! ## The first-cup progress argument -/

/-- **Cup-headed non-cup-block has an adjacent cup-then-cap.**  If some tail is NOT all cups
(`allCups isCup rest = false`) then, placed after ANY cup head, it exhibits an adjacent cup-then-cap.  This is
the inductive heart of the first-cup argument: scan the tail for the first cap; the atom just before it is a
cup (either the head, or a cup we recursed through).  The head is quantified INSIDE the list induction so the
recursion can re-seat it on the intervening cup. -/
theorem hasAdjacentCupThenCap_of_cup_of_not_allCups {α : Type u} (isCup : α → Bool) :
    ∀ {rest : List α}, allCups isCup rest = false →
      ∀ {cupHead : α}, isCup cupHead = true → HasAdjacentCupThenCap isCup (cupHead :: rest)
  | [], tailNotAllCups, _, _ => by
      dsimp only [allCups] at tailNotAllCups
      exact Bool.noConfusion tailNotAllCups
  | nextAtom :: rest, tailNotAllCups, cupHead, isCupHead => by
      dsimp only [allCups] at tailNotAllCups
      cases isCupNext : isCup nextAtom with
      | false => exact HasAdjacentCupThenCap.here isCupHead isCupNext rest
      | true =>
          rw [isCupNext, Bool.true_and] at tailNotAllCups
          exact HasAdjacentCupThenCap.there cupHead
            (hasAdjacentCupThenCap_of_cup_of_not_allCups isCup tailNotAllCups isCupNext)

/-- ★★ **THE VALLEY PROGRESS LEMMA — the claimed last wall, dissolved.**  A tag list that is NOT a
`cap`-block-then-`cup`-block valley contains an adjacent `cup`-immediately-then-`cap`.  Contrapositive of the
first-cup argument: walking the leading caps, the first cup must (for a valley) be followed by only cups; if
the valley check fails there, the tail is not all cups, so `hasAdjacentCupThenCap_of_cup_of_not_allCups`
locates the pair.  No arc-structure readoff — a `List`/`Bool` structural induction. -/
theorem hasAdjacentCupThenCap_of_not_valley {α : Type u} (isCup : α → Bool) :
    ∀ {tags : List α}, isCapThenCupValley isCup tags = false → HasAdjacentCupThenCap isCup tags
  | [], notValley => by
      dsimp only [isCapThenCupValley] at notValley
      exact Bool.noConfusion notValley
  | atom :: rest, notValley => by
      dsimp only [isCapThenCupValley] at notValley
      cases isCupHead : isCup atom with
      | true =>
          rw [isCupHead] at notValley
          exact hasAdjacentCupThenCap_of_cup_of_not_allCups isCup notValley isCupHead
      | false =>
          rw [isCupHead] at notValley
          exact HasAdjacentCupThenCap.there atom
            (hasAdjacentCupThenCap_of_not_valley isCup notValley)

/-- **The witness is a concrete list split.**  Any `HasAdjacentCupThenCap` unfolds to
`tags = capPrefix ++ cupAtom :: capAtom :: suffixRest` with `cupAtom` a cup and `capAtom` a cap — exactly the
decomposition the assemble phase whiskers the straighten/commute move into.  Built by cons-rebuild
(`List.cons_append` is `rfl`), so it stays propext-free. -/
theorem hasAdjacentCupThenCap_split {α : Type u} (isCup : α → Bool) :
    ∀ {tags : List α}, HasAdjacentCupThenCap isCup tags →
      ∃ (capPrefix : List α) (cupAtom capAtom : α) (suffixRest : List α),
        tags = capPrefix ++ cupAtom :: capAtom :: suffixRest ∧
          isCup cupAtom = true ∧ isCup capAtom = false
  | _, HasAdjacentCupThenCap.here (cupAtom := cupAtom) (capAtom := capAtom) isCupHead isCapNext rest =>
      ⟨[], cupAtom, capAtom, rest, rfl, isCupHead, isCapNext⟩
  | _, HasAdjacentCupThenCap.there atom tail =>
      match hasAdjacentCupThenCap_split isCup tail with
      | ⟨capPrefix, cupAtom, capAtom, suffixRest, splitEq, isCupCup, isCapCap⟩ =>
          ⟨atom :: capPrefix, cupAtom, capAtom, suffixRest, congrArg (atom :: ·) splitEq,
            isCupCup, isCapCap⟩

/-! ## The spine specialization — cup/cap by boundary source width -/

/-- An atom is a `cup` when its generator's SOURCE 1-cell is empty (width 0): a creation, the unit
`id ⟹ …` shape.  Everything else (caps, and any other generator) reads as a `cap`-side atom. -/
def SpineAtom.isCupAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : Bool :=
  match atom.generatorDom.length with
  | 0 => true
  | _ + 1 => false

/-- **Spine valley progress (specialization).**  A spine that is not a cap-block-then-cup-block valley (by
`SpineAtom.isCupAtom`) contains an adjacent cup-then-cap atom pair — the driver's "innermost partner pair
exists" premise, discharged with NO arc/window readoff. -/
theorem hasAdjacentCupThenCap_of_not_valley_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {spine : List (SpineAtom signature sourceMode targetMode)}
    (notValley : isCapThenCupValley SpineAtom.isCupAtom spine = false) :
    HasAdjacentCupThenCap SpineAtom.isCupAtom spine :=
  hasAdjacentCupThenCap_of_not_valley SpineAtom.isCupAtom notValley

/-! ## Classifying the located pair — which shipped move it feeds -/

/-- Truncated-subtraction absolute difference `|leftLen − rightLen|` (one summand is `0`). -/
def natWindowDistance (leftLen rightLen : Nat) : Nat := (leftLen - rightLen) + (rightLen - leftLen)

/-- The three kinds an adjacent cup-then-cap pair can take, read off the two atoms' whisker windows. -/
inductive AdjacentCupCapKind where
  /-- `cupLeft = capLeft`: the cap sits on BOTH fresh cup legs — orientation-excluded in the walking
  adjunction (unit cup makes an `[R, L]` pair, counit cap wants an `[L, R]` pair). -/
  | orientationExcludedBothLegs
  /-- `|cupLeft − capLeft| = 1`: windows share exactly one leg — a ZIG-ZAG.  Feeds
  `zigzagStraightensInVcompContext` / `whiskeredZigZagCollapses`. -/
  | zigZagSharedLeg
  /-- `|cupLeft − capLeft| ≥ 2`: windows do not touch — DISJOINT.  Feeds `saturatedGodementExchange` /
  `snakeCommutesPastDisjointThenStraightens`. -/
  | disjointWindows
  deriving DecidableEq

/-- **Classify** an adjacent cup-then-cap pair by the offset between the two atoms' left-context widths. -/
def classifyAdjacentCupCap (cupLeftLen capLeftLen : Nat) : AdjacentCupCapKind :=
  match natWindowDistance cupLeftLen capLeftLen with
  | 0 => AdjacentCupCapKind.orientationExcludedBothLegs
  | 1 => AdjacentCupCapKind.zigZagSharedLeg
  | _ + 2 => AdjacentCupCapKind.disjointWindows

/-- The spine-level classifier: read the two adjacent atoms' left-context widths. -/
def classifyAdjacentAtoms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (cupAtom capAtom : SpineAtom signature sourceMode targetMode) : AdjacentCupCapKind :=
  classifyAdjacentCupCap cupAtom.leftContext.length capAtom.leftContext.length

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the valley-normalization "innermost partner pair exists" premise is STRUCTURAL, not an
arc readoff (the claimed last wall was a conflation).**  `hasAdjacentCupThenCap_of_not_valley` proves, by the
first-cup `List`/`Bool` induction, that any non-valley spine has an adjacent cup-then-cap, located concretely
(`hasAdjacentCupThenCap_split`) as `capPrefix ++ cupAtom :: capAtom :: suffixRest`.  This BYPASSES the
R1c-REFUTED `arcCupReselection_exists`: no cup is read off any boundary arch, no window is re-selected — the
pair is found by inspecting adjacent tags.  The located pair is classified (`classifyAdjacentAtoms`) into
ZIG-ZAG → `zigzagStraightensInVcompContext`, DISJOINT → `snakeCommutesPastDisjointThenStraightens`, or the
orientation-excluded both-legs case.  What this marker does NOT itself close: the terminating WF induction
that iterates locate → (straighten | commute) to a pure valley (the assemble phase wires the shipped moves
onto these splits).  `= true`. -/
def fxMode_hasSpineValleyProgress : Bool := true

end FX1Poly.Polygraph
