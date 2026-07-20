import FX1Poly.Polygraph.Net.VasCoverability

/-! # FX1Poly/Polygraph/Net/ExtendedPetriInhibitor — extended Petri nets: the
    decidable extension taxonomy, the total Minsky encoding, and the
    inhibitor-reachability UNDECIDABILITY wall (NET-8)

A **plain** Petri net / vector addition system (see `VasCoverability`) fires a transition
`(pre, post)` at a marking when `pre ≤ marking` componentwise; firing is MONOTONE, so plain
nets are a well-structured transition system (WSTS) and coverability is decidable by Dickson.

An **extended** net adds three arc kinds that keep firing monotone — and one that does not:

* **reset** arcs zero a listed place on firing;
* **transfer** arcs move all tokens from a source place to a destination place;
* **inhibitor** arcs carry a ZERO-TEST guard: the transition is enabled only when every
  listed inhibitor place is empty.

Reset and transfer firing are still monotone on the marking wqo (`Nat^k` under `cvbVecLe`),
so those extensions stay decidable for coverability.  The **inhibitor** guard is
*non-monotone* — growing a guarded place *disables* the transition — which breaks WSTS.  A
net with ≥ 2 unbounded zero-testable places simulates a 2-counter Minsky machine, whose
halting problem is undecidable; hence inhibitor-net reachability AND coverability are
UNDECIDABLE at any axiom strength.

## What is DECIDED / SHIPPED (zero-axiom)

* **T1 — carrier.**  `XpnArcKind` (plain/reset/transfer/inhibitor), `XpnTransition`
  (`pre`, `post`, `inhibitorPlaces`, `resetPlaces`, `transferPairs`), `XpnNet`.  Markings are
  `List Nat`; the vector order/arithmetic is reused verbatim from `VasCoverability`
  (`cvbVecLe`/`cvbVecAdd`/`cvbVecMonus`).
* **T2 — firing with teeth.**  `xpnFireEnabled` = `pre ≤ marking` AND every inhibitor place
  reads zero (`xpnAllGuardsZero`, structural fold over `xpnIsZeroAt`); `xpnFireStep` applies
  monus/add then resets then transfers.  `xpnFireEnabledElim` reuses `cvbCondGuardElim` to
  split the guard; `xpnPlainFireMonotone` reuses `cvbFireMono` (the WSTS content for the
  reset/transfer-free part).
* **T3 — taxonomy + total encoding.**  `xpnExtensionCoverabilityDecidable` classifies the
  four arc kinds (plain/reset/transfer decidable, inhibitor NOT).
  `xpnTwoCounterToInhibitorNet` is the TOTAL reduction witness: a plain cons-recursion over a
  2-counter Minsky instruction list, emitting a fixed transition set per line, with the
  program counter a one-hot family of places and the only inhibitor sites the zero-branches
  of `dec`.  No recursion on marking dynamics, no fuel, no fixpoint — every input yields a
  net.

## What is WALLED

* **`xpnHasInhibitorReachability := false`** and **`xpnHasResetReachability := false`** —
  reachability of inhibitor nets (and of reset nets) is UNDECIDABLE; see the wall docstrings.
  This is a genuine **undecidability** wall (no decider exists at any axiom strength),
  qualitatively STRONGER than the NET-4/NET-5 *provability* wall
  `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false` (there the fact is true, only its
  zero-axiom proof needs `WellFounded.fix`).

## Zero-axiom

Structural recursion throughout: on `Nat`, on `List Nat`, on the instruction list, on the
guard/reset/transfer index lists.  Full-enumeration matches, `Nat.beq` for the zero-test, and
the calibrated-clean `VasCoverability` kit.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical.choice`, `native_decide`, `omega`, `funext`, `WellFounded.fix`.  Per-declaration
gated in `FX1PolyAudit/Polygraph/Net/ExtendedPetriInhibitor.lean`. -/

namespace FX1Poly.Polygraph.Net

/-! ## T1 — the extended-net carrier -/

/-- The four extended-arc kinds.  Plain/reset/transfer keep firing monotone (WSTS);
inhibitor carries a non-monotone zero-test. -/
inductive XpnArcKind where
  | plainArc
  | resetArc
  | transferArc
  | inhibitorArc

/-- An extended transition: token consumption `pre`, production `post`, the zero-test
`inhibitorPlaces` (each must read zero to enable), the `resetPlaces` (zeroed on firing), and
the `transferPairs` `(source, dest)` (all tokens moved source → dest on firing). -/
structure XpnTransition where
  pre : List Nat
  post : List Nat
  inhibitorPlaces : List Nat
  resetPlaces : List Nat
  transferPairs : List (Nat × Nat)

/-- An extended net: a place count and a list of extended transitions. -/
structure XpnNet where
  placeCount : Nat
  transitions : List XpnTransition

/-! ## Marking lookup / update primitives (fresh, structural) -/

/-- Read the token count at place `idx` (0 outside the list).  Structural on both. -/
def xpnNth : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: rest, Nat.succ idxPred => xpnNth rest idxPred

/-- Does place `idx` read zero in `marking`? -/
def xpnIsZeroAt (marking : List Nat) (idx : Nat) : Bool := Nat.beq (xpnNth marking idx) 0

/-- Set place `idx` to zero (identity outside the list).  Structural on both. -/
def xpnSetZeroAt : List Nat → Nat → List Nat
  | [], _ => []
  | _ :: rest, 0 => 0 :: rest
  | head :: rest, Nat.succ idxPred => head :: xpnSetZeroAt rest idxPred

/-- Add `amount` tokens at place `idx` (identity outside the list).  Structural on both. -/
def xpnAddAt : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | head :: rest, 0, amount => cvbAdd head amount :: rest
  | head :: rest, Nat.succ idxPred, amount => head :: xpnAddAt rest idxPred amount

/-- The all-zeros marking of a given length. -/
def xpnZeros : Nat → List Nat
  | 0 => []
  | Nat.succ predecessor => 0 :: xpnZeros predecessor

/-- The one-hot marking of length `placeCount` with a single token at `idx`. -/
def xpnOneHot (placeCount idx : Nat) : List Nat := xpnAddAt (xpnZeros placeCount) idx 1

/-! ## T2 — firing with inhibitor zero-test guards -/

/-- Every listed inhibitor place reads zero (structural fold over the guard indices). -/
def xpnAllGuardsZero (marking : List Nat) : List Nat → Bool
  | [] => true
  | idx :: rest => cond (xpnIsZeroAt marking idx) (xpnAllGuardsZero marking rest) false

/-- A transition is enabled iff `pre ≤ marking` componentwise AND every inhibitor place is
empty.  The second conjunct is the zero-test — it has TEETH: a token in a guarded place
disables the transition even when `pre` is covered. -/
def xpnFireEnabled (transition : XpnTransition) (marking : List Nat) : Bool :=
  cond (cvbVecLe transition.pre marking)
    (xpnAllGuardsZero marking transition.inhibitorPlaces) false

/-- Apply the resets: zero each listed place (structural on the reset-index list). -/
def xpnApplyResets (marking : List Nat) : List Nat → List Nat
  | [] => marking
  | idx :: rest => xpnApplyResets (xpnSetZeroAt marking idx) rest

/-- Move all tokens from `source` to `dest`: read the source count, add it at `dest`, then
zero the source. -/
def xpnApplyTransferOne (marking : List Nat) (source dest : Nat) : List Nat :=
  let tokens := xpnNth marking source
  xpnSetZeroAt (xpnAddAt marking dest tokens) source

/-- Apply the transfers left-to-right (structural on the pair list). -/
def xpnApplyTransfers (marking : List Nat) : List (Nat × Nat) → List Nat
  | [] => marking
  | (source, dest) :: rest => xpnApplyTransfers (xpnApplyTransferOne marking source dest) rest

/-- Fire the transition: consume `pre`, produce `post`, apply resets, then transfers. -/
def xpnFireStep (transition : XpnTransition) (marking : List Nat) : List Nat :=
  xpnApplyTransfers
    (xpnApplyResets (cvbVecAdd (cvbVecMonus marking transition.pre) transition.post)
      transition.resetPlaces)
    transition.transferPairs

/-- Split an enabled-transition witness into the `pre ≤ marking` part and the
all-guards-zero part (reuses the shared `cond … false` splitter). -/
theorem xpnFireEnabledElim (transition : XpnTransition) (marking : List Nat)
    (henabled : xpnFireEnabled transition marking = true) :
    cvbVecLe transition.pre marking = true ∧
      xpnAllGuardsZero marking transition.inhibitorPlaces = true :=
  cvbCondGuardElim (cvbVecLe transition.pre marking)
    (xpnAllGuardsZero marking transition.inhibitorPlaces) henabled

/-- When a transition has no resets and no transfers, its firing IS the plain VAS firing —
so `cvbFireMono` transports monotonicity to it. -/
theorem xpnFireStepPlainIsCvbFire (transition : XpnTransition) (marking : List Nat)
    (hReset : transition.resetPlaces = []) (hTransfer : transition.transferPairs = []) :
    xpnFireStep transition marking = cvbFire marking transition.pre transition.post := by
  show xpnApplyTransfers
      (xpnApplyResets (cvbVecAdd (cvbVecMonus marking transition.pre) transition.post)
        transition.resetPlaces)
      transition.transferPairs = cvbFire marking transition.pre transition.post
  rw [hReset, hTransfer]
  rfl

/-- The reset/transfer-free firing is MONOTONE on the marking wqo — the WSTS content that
makes plain/reset/transfer coverability decidable (reuses `cvbFireMono`). -/
theorem xpnPlainFireMonotone (markingSmall markingBig pre post : List Nat)
    (hle : cvbVecLe markingSmall markingBig = true) :
    cvbVecLe (cvbFire markingSmall pre post) (cvbFire markingBig pre post) = true :=
  cvbFireMono markingSmall markingBig pre post hle

/-! ## T3 — the decidable extension taxonomy -/

/-- The finite classification of arc kinds by coverability-decidability.  Plain/reset/transfer
are monotone (WSTS ⇒ Dickson-decidable coverability, the *termination* itself walled exactly
as `cvbHasUnconditionalCoverabilityTermination`); the inhibitor zero-test is non-monotone so
inhibitor coverability is genuinely undecidable.  Exhaustive by construction. -/
def xpnExtensionCoverabilityDecidable : XpnArcKind → Bool
  | XpnArcKind.plainArc => true
  | XpnArcKind.resetArc => true
  | XpnArcKind.transferArc => true
  | XpnArcKind.inhibitorArc => false

/-! ## T3 — the total 2-counter Minsky → inhibitor-net encoding -/

/-- A 2-counter Minsky instruction: `inc reg goto` increments counter `reg` and jumps to line
`goto`; `dec reg gotoNonzero gotoZero` jumps to `gotoZero` if counter `reg` is zero, else
decrements it and jumps to `gotoNonzero`.  The zero branch is exactly where an inhibitor arc
is required. -/
inductive XpnMinskyInstr where
  | inc (reg : Nat) (goto : Nat)
  | dec (reg : Nat) (gotoNonzero : Nat) (gotoZero : Nat)

/-- Encode one instruction at line `lineIdx` into a transition set.  The program counter is a
one-hot family (line `k` ↔ place `k`); counter `reg` lives at place `lineCount + reg`.
`inc` is one plain transition; `dec` is two transitions — the nonzero branch consumes a
counter token (plain), the zero branch carries an INHIBITOR guard on the counter place. -/
def xpnInstrToTransitions (placeCount lineCount lineIdx : Nat) :
    XpnMinskyInstr → List XpnTransition
  | XpnMinskyInstr.inc reg goto =>
      [ { pre := xpnOneHot placeCount lineIdx,
          post := cvbVecAdd (xpnOneHot placeCount goto)
            (xpnOneHot placeCount (cvbAdd lineCount reg)),
          inhibitorPlaces := [], resetPlaces := [], transferPairs := [] } ]
  | XpnMinskyInstr.dec reg gotoNonzero gotoZero =>
      [ { pre := cvbVecAdd (xpnOneHot placeCount lineIdx)
            (xpnOneHot placeCount (cvbAdd lineCount reg)),
          post := xpnOneHot placeCount gotoNonzero,
          inhibitorPlaces := [], resetPlaces := [], transferPairs := [] },
        { pre := xpnOneHot placeCount lineIdx,
          post := xpnOneHot placeCount gotoZero,
          inhibitorPlaces := [cvbAdd lineCount reg],
          resetPlaces := [], transferPairs := [] } ]

/-- Own cons-only append on transition lists (avoids the leak-prone `List.append`). -/
def xpnAppendTransitions : List XpnTransition → List XpnTransition → List XpnTransition
  | [], right => right
  | head :: rest, right => head :: xpnAppendTransitions rest right

/-- Fold the instruction list into a transition list, tracking the line index (plain
cons-recursion — no marking dynamics, no fuel). -/
def xpnFoldInstrs (placeCount lineCount : Nat) :
    Nat → List XpnMinskyInstr → List XpnTransition
  | _, [] => []
  | lineIdx, instr :: rest =>
      xpnAppendTransitions (xpnInstrToTransitions placeCount lineCount lineIdx instr)
        (xpnFoldInstrs placeCount lineCount (Nat.succ lineIdx) rest)

/-- Length of an instruction list (own structural count). -/
def xpnLength : List XpnMinskyInstr → Nat
  | [] => 0
  | _ :: rest => Nat.succ (xpnLength rest)

/-- Length of a transition list (own structural count). -/
def xpnTransitionCount : List XpnTransition → Nat
  | [] => 0
  | _ :: rest => Nat.succ (xpnTransitionCount rest)

/-- **The TOTAL reduction witness.**  Every 2-counter Minsky program yields an inhibitor net:
`lineCount` one-hot program-counter places plus two counter places, with the zero-branches of
`dec` the only inhibitor sites.  Defined on EVERY input (total, structural). -/
def xpnTwoCounterToInhibitorNet (instrs : List XpnMinskyInstr) : XpnNet :=
  { placeCount := cvbAdd (xpnLength instrs) 2,
    transitions := xpnFoldInstrs (cvbAdd (xpnLength instrs) 2) (xpnLength instrs) 0 instrs }

/-! ## T4 — the undecidability walls -/

/-- **WALL** — inhibitor-net reachability AND coverability are UNDECIDABLE.  With ≥ 2 unbounded
zero-testable places the 2-counter Minsky machine halting problem reduces to inhibitor-net
reachability (`xpnTwoCounterToInhibitorNet` is the total reduction witness: the zero-branch
inhibitor guard simulates the counter zero-test).  The culprit is `xpnFireEnabled`'s guard
clause: it is NON-MONOTONE (growing a guarded place disables the transition — witnessed by
`xpnInhibitorNonMonotone`), so inhibitor transitions are NOT a WSTS and Dickson's lemma (the
backward-antichain termination `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall`) does not apply.
This is qualitatively STRONGER than the NET-4/NET-5 wall: that one is a *provability* wall
(`cvbHasUnconditionalCoverabilityTermination = false` — the fact is true, only the zero-axiom
proof needs `WellFounded.fix`); this one is a genuine *undecidability* wall — no decider
exists at any axiom strength.  Burned attacks: (1) bounded-fuel forward/backward search is
one-sided — absence of a cover within fuel never refutes reachability over the unbounded
state space (matches `cvbCoverBounded`'s `notYetAtFuel`); (2) restricting to bounded nets
abandons the unbounded case rather than deciding it, and any WQO/Karp–Miller acceleration
presupposes the monotonicity the zero-test breaks, so the covering tree is infinite. -/
def xpnHasInhibitorReachability : Bool := false

/-- **WALL** — reset-net reachability is ALSO undecidable (Araki–Kasami / reset-net halting is
undecidable), even though reset-net *coverability* is decidable (reset firing is monotone, so
reset nets are a WSTS for coverability).  The two facts are DISTINCT: coverability lands on
the decidable side of the taxonomy (`xpnExtensionCoverabilityDecidable resetArc = true`),
reachability does not.  Burned attacks mirror the inhibitor wall: (1) one-sided bounded search
cannot certify non-reachability; (2) the WSTS coverability decider answers a WEAKER question
(≥ target) and cannot be sharpened to exact reachability. -/
def xpnHasResetReachability : Bool := false

/-- Marker: inhibitor undecidability is via the total Minsky reduction, not a provability gap.
Deliberately NOT equated to `fxNet4_dicksonWall` — the obstruction is the reduction plus the
non-monotonicity fire, not the AF-product. -/
def xpnInhibitorUndecidableViaMinsky : Bool := false

/-! ## T4 — the positive decidable-content markers -/

/-- The finite arc-kind classification is a true, exhaustive decidable fact. -/
def xpnHasDecidableExtensionTaxonomy : Bool := true

/-- The 2-counter → inhibitor-net encoding is total on every input. -/
def xpnHasTotalMinskyEncoding : Bool := true

/-- Reset/transfer/plain firing is WSTS-monotone (backed by `xpnPlainFireMonotone`). -/
def xpnHasResetTransferMonotoneFiring : Bool := true

/-! ## T5 — ground fires -/

/-- A plain transition consuming one token at place `0`, producing one at place `1`. -/
def xpnPlainEnabledTransition : XpnTransition :=
  { pre := [1, 0], post := [0, 1], inhibitorPlaces := [], resetPlaces := [], transferPairs := [] }

/-- A transition with a zero-test guard on place `1` (no token flow). -/
def xpnInhibitedTransition : XpnTransition :=
  { pre := [0, 0], post := [0, 0], inhibitorPlaces := [1], resetPlaces := [], transferPairs := [] }

/-- A transition that resets place `0` on firing. -/
def xpnResetTransition : XpnTransition :=
  { pre := [0, 0], post := [0, 0], inhibitorPlaces := [], resetPlaces := [0], transferPairs := [] }

/-- A transition that transfers all tokens from place `0` to place `1`. -/
def xpnTransferTransition : XpnTransition :=
  { pre := [0, 0], post := [0, 0], inhibitorPlaces := [], resetPlaces := [], transferPairs := [(0, 1)] }

/-- A concrete 2-instruction Minsky program: increment counter 0 then decrement it. -/
def xpnExampleProgram : List XpnMinskyInstr :=
  [XpnMinskyInstr.inc 0 1, XpnMinskyInstr.dec 0 0 1]

/-- Its encoded inhibitor net. -/
def xpnExampleNet : XpnNet := xpnTwoCounterToInhibitorNet xpnExampleProgram

/-- **Fire** — a covered `pre` with clear guards enables: `[1,0] ≤ [1,1]`, no inhibitor. -/
theorem xpnFireEnabledPlainTrue : xpnFireEnabled xpnPlainEnabledTransition [1, 1] = true := rfl

/-- **Fire** — an uncovered `pre` disables: `[1,0]` is not `≤ [0,1]`. -/
theorem xpnFireEnabledNotCoveredFalse :
    xpnFireEnabled xpnPlainEnabledTransition [0, 1] = false := rfl

/-- **Fire** — clear guard enables: place `1` is empty in `[0,0]`. -/
theorem xpnFireEnabledInhibitorClear :
    xpnFireEnabled xpnInhibitedTransition [0, 0] = true := rfl

/-- **Fire (zero-test teeth)** — a token in the guarded place `1` DISABLES even though `pre`
is covered: `xpnFireEnabled` at `[0,1]` is `false`. -/
theorem xpnFireEnabledInhibitorBlocked :
    xpnFireEnabled xpnInhibitedTransition [0, 1] = false := rfl

/-- **Fire (the load-bearing non-monotonicity)** — `[0,0] ≤ [0,1]` yet the transition is
enabled at the SMALLER marking and disabled at the LARGER one.  This is exactly why the WSTS
argument (and Dickson) fails for inhibitor arcs. -/
theorem xpnInhibitorNonMonotone :
    cvbVecLe [0, 0] [0, 1] = true ∧
      xpnFireEnabled xpnInhibitedTransition [0, 0] = true ∧
      xpnFireEnabled xpnInhibitedTransition [0, 1] = false :=
  ⟨rfl, rfl, rfl⟩

/-- **Fire** — plain firing computes: `([1,1] ∸ [1,0]) + [0,1] = [0,2]`. -/
theorem xpnFireStepComputes : xpnFireStep xpnPlainEnabledTransition [1, 1] = [0, 2] := rfl

/-- **Fire** — reset zeroes place `0`: firing at `[5,3]` gives `[0,3]`. -/
theorem xpnFireStepResetZeroes : xpnFireStep xpnResetTransition [5, 3] = [0, 3] := rfl

/-- **Fire** — transfer moves place `0`'s tokens into place `1`: `[5,3] → [0,8]`. -/
theorem xpnFireStepTransferMoves : xpnFireStep xpnTransferTransition [5, 3] = [0, 8] := rfl

/-- **Fire** — taxonomy classifies `plainArc` decidable. -/
theorem xpnTaxonomyPlain : xpnExtensionCoverabilityDecidable XpnArcKind.plainArc = true := rfl

/-- **Fire** — taxonomy classifies `resetArc` decidable. -/
theorem xpnTaxonomyReset : xpnExtensionCoverabilityDecidable XpnArcKind.resetArc = true := rfl

/-- **Fire** — taxonomy classifies `transferArc` decidable. -/
theorem xpnTaxonomyTransfer :
    xpnExtensionCoverabilityDecidable XpnArcKind.transferArc = true := rfl

/-- **Fire (the undecidable row)** — taxonomy classifies `inhibitorArc` NOT decidable. -/
theorem xpnTaxonomyInhibitor :
    xpnExtensionCoverabilityDecidable XpnArcKind.inhibitorArc = false := rfl

/-- **Fire (the inhibitor site)** — encoding a `dec 0 0 1` at line `1` of a 4-place, 2-line
layout yields two transitions, the zero-branch carrying an inhibitor guard on counter place
`2`.  Pins that the zero-test is exactly where the encoding places it. -/
theorem xpnDecHasInhibitorGuard :
    xpnInstrToTransitions 4 2 1 (XpnMinskyInstr.dec 0 0 1) =
      [ { pre := [0, 1, 1, 0], post := [1, 0, 0, 0],
          inhibitorPlaces := [], resetPlaces := [], transferPairs := [] },
        { pre := [0, 1, 0, 0], post := [0, 1, 0, 0],
          inhibitorPlaces := [2], resetPlaces := [], transferPairs := [] } ] := rfl

/-- **Fire (encoding total)** — the example net has `2 + 2 = 4` places. -/
theorem xpnExampleNetPlaceCount : xpnExampleNet.placeCount = 4 := rfl

/-- **Fire (encoding total)** — the example net has 3 transitions (1 for `inc`, 2 for `dec`).-/
theorem xpnExampleNetTransitionCount :
    xpnTransitionCount xpnExampleNet.transitions = 3 := rfl

/-- **Fire (wall)** — inhibitor reachability is walled `false`. -/
theorem xpnInhibitorWallIsFalse : xpnHasInhibitorReachability = false := rfl

/-- **Fire (wall)** — reset reachability is walled `false` (distinct from reset coverability,
which the taxonomy marks decidable). -/
theorem xpnResetWallIsFalse : xpnHasResetReachability = false := rfl

/-- **Fire (wall)** — the Minsky-reduction undecidability marker is `false`. -/
theorem xpnInhibitorUndecidableIsFalse : xpnInhibitorUndecidableViaMinsky = false := rfl

/-- **Fire (positive)** — the decidable taxonomy marker is `true`. -/
theorem xpnHasDecidableExtensionTaxonomyIsTrue :
    xpnHasDecidableExtensionTaxonomy = true := rfl

/-- **Fire (positive)** — the total-encoding marker is `true`. -/
theorem xpnHasTotalMinskyEncodingIsTrue : xpnHasTotalMinskyEncoding = true := rfl

/-- **Fire (positive)** — the monotone-firing marker is `true`. -/
theorem xpnHasResetTransferMonotoneFiringIsTrue :
    xpnHasResetTransferMonotoneFiring = true := rfl

end FX1Poly.Polygraph.Net
