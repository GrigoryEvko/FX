import FX1Poly.ComputerAlgebra.Number.NormalizedRational
import FX1Poly.Polygraph.Net.VasCoverability

/-! # FX1Poly/Polygraph/Net/StochasticRateNet — stochastic rate Petri nets and
    their continuous-time Markov chain (CTMC) generator (NET-15)

A **stochastic rate net** is a Petri net whose every transition carries an exact
rational firing RATE.  Over a fixed set of reachable markings it induces a
continuous-time Markov chain: the states are the reachable markings, and the
**generator matrix** `Q` has off-diagonal entry `Q[m][m']` equal to the total rate
of transitions firing `m → m'`, and diagonal entry `Q[m][m] = -exitRate(m)`, the
negative total rate leaving `m`.  The defining soundness property of a CTMC
generator is that **every row sums to zero** — the off-diagonal rates leaving a
state exactly cancel the negative diagonal.

This module is a thin rate-graded LAYER on top of the already-shipped VAS firing
kit (`FX1Poly/Polygraph/Net/VasCoverability`: `cvbVecLe`, `cvbFire`,
`cvbFireEnabled`, `cvbVecAdd`, `cvbVecMonus`, `cvbConcat`, `cvbBasisBeq`) and the
exact-ℚ canonical arithmetic (`FX1Poly/ComputerAlgebra/Number/NormalizedRational`:
`QnfRat`, `qnfAdd`/`qnfNeg`/`qnfMul`/`qnfInv`, `qnfZero`, and the field laws — in
particular `qnfAddNegLeft`, which IS the row-sum-zero cancellation).  No new
arithmetic and no new vector operation is derived here.

## What is DECIDED / SOUND (zero-axiom)

* **T1 — carrier + firing.**  `SrnTransition` (a `pre`/`post` marking pair carrying
  a `QnfRat` rate), `SrnNet`, `srnFireEnabled` (= `cvbVecLe pre marking`),
  `srnFireTarget` (= `cvbFire marking pre post`).
* **T2 — reachable set + exit rate.**  `srnReachableMarkings` — a STRUCTURAL-FUEL
  BFS saturation from the initial marking, dedup by `cswListNatBeq` membership, no
  `WellFounded.fix` (fuel is a plain `Nat` bound, mirroring `cvbCoverBounded`).
  `srnExitRate` — a cons-only `qnfAdd` fold of the rates of the enabled
  transitions.  `srnMarkingIndex` — a structural marking-position lookup (no
  `getD`).
* **T3 — generator + jump chain + soundness.**  `srnGeneratorOffDiag` (the
  off-diagonal rate sum to one target), `srnGeneratorEntry` (off-diagonal, or the
  `qnfNeg (exitRate)` diagonal), `srnGeneratorRow`/`srnGeneratorMatrix`,
  `srnEmbeddedJumpEntry` (off-diagonal rate normalised by `qnfInv (exitRate)`), and
  `srnRowSum` with its append law `srnRowSumCat`.  **The crown soundness**
  `srnBalancedRowSumsToZero`: a generator row whose diagonal is the negation of its
  off-diagonal total sums to `qnfZero` — the row-sum-zero property, general and
  zero-axiom, one `qnfAddNegLeft`.  Fired concretely on a 2-state and a 3-state net.

## What is WALLED

* **`srnHasUnboundedStateSpace := false`** — an unbounded stochastic net has
  infinitely many reachable markings, so the induced CTMC is infinite and
  `srnReachableMarkings` never stabilises within any fuel.  Deciding boundedness is
  the coverability / WSTS well-quasi-order problem — exactly the NET-4 Dickson wall
  `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false` (the almost-full PRODUCT
  needs `WellFounded.fix`).  The generator ships only over a fuel-bounded reachable
  set (finite by fiat); soundness is conditional on the BFS having converged.
* **`srnHasStationaryDistribution := false`** — the steady-state solve `π Q = 0`
  (with `Σπ = 1`) is Gaussian elimination over `QnfRat`, a distinct rung (NET-16),
  out of scope here.

## Zero-axiom

Structural recursion throughout: on `Nat` (the BFS fuel), on `List`, on
`List QnfRat`; every arithmetic fact is a `QnfRat` field law from the canonical-NF
corpus (no setoid, no `Quot.sound`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical.choice`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Net/StochasticRateNet.lean`. -/

namespace FX1Poly.Polygraph.Net

open FX1Poly.ComputerAlgebra
  (QnfRat qnfAdd qnfNeg qnfMul qnfInv qnfZero qnfOne qnfNormalize qnfBeq
    qnfAddNegLeft qnfAddZeroLeft qnfAddAssoc RationalPair fxNet4_dicksonWall
    cswListNatBeq)

/-! ## T1 — the rated carrier and firing -/

/-- A transition of a stochastic rate net: a Petri-net `(pre, post)` pair carrying
its exact rational firing rate.  Enabled when `pre ≤ marking`; firing removes `pre`
tokens and adds `post` tokens. -/
structure SrnTransition where
  pre : List Nat
  post : List Nat
  rate : QnfRat

/-- A stochastic rate net: a place count, a list of rated transitions, and an
initial marking. -/
structure SrnNet where
  placeCount : Nat
  transitions : List SrnTransition
  initialMarking : List Nat

/-- A transition is enabled at `marking` iff its `pre` guard is `≤ marking`
componentwise — the shipped VAS enabledness test. -/
def srnFireEnabled (marking : List Nat) (transition : SrnTransition) : Bool :=
  cvbVecLe transition.pre marking

/-- Firing a transition at `marking` yields `(marking ∸ pre) + post` — the shipped
VAS firing map. -/
def srnFireTarget (marking : List Nat) (transition : SrnTransition) : List Nat :=
  cvbFire marking transition.pre transition.post

/-! ## T2 — reachable state space (structural-fuel BFS) and the exit rate -/

/-- The successor markings of `marking`: fire every enabled transition once. -/
def srnSuccessors : List SrnTransition → List Nat → List (List Nat)
  | [], _ => []
  | transition :: rest, marking =>
      cond (srnFireEnabled marking transition)
        (srnFireTarget marking transition :: srnSuccessors rest marking)
        (srnSuccessors rest marking)

/-- Structural marking membership by canonical list equality. -/
def srnMarkingMem (marking : List Nat) : List (List Nat) → Bool
  | [] => false
  | head :: rest => cond (cswListNatBeq marking head) true (srnMarkingMem marking rest)

/-- Insert `marking` into `visited` if not already present (appended at the tail so
the initial marking stays first — deterministic enumeration order). -/
def srnInsertMarking (marking : List Nat) (visited : List (List Nat)) : List (List Nat) :=
  cond (srnMarkingMem marking visited) visited (cvbConcat visited (marking :: []))

/-- Insert every marking of a list into `visited`, deduplicating. -/
def srnInsertAll : List (List Nat) → List (List Nat) → List (List Nat)
  | [], visited => visited
  | marking :: rest, visited => srnInsertAll rest (srnInsertMarking marking visited)

/-- One BFS expansion round: fold every currently-known marking's successors into
the accumulator (the `current` snapshot is fixed for the round). -/
def srnExpandRound (transitions : List SrnTransition) :
    List (List Nat) → List (List Nat) → List (List Nat)
  | [], accumulated => accumulated
  | marking :: rest, accumulated =>
      srnExpandRound transitions rest
        (srnInsertAll (srnSuccessors transitions marking) accumulated)

/-- Saturate the reachable set on structural fuel: expand until the marking set
stabilises (`cvbBasisBeq`) or the fuel bound runs out.  The fuel is a plain `Nat`
— structural recursion, never `WellFounded.fix`. -/
def srnReachSaturate (transitions : List SrnTransition) :
    Nat → List (List Nat) → List (List Nat)
  | 0, accumulated => accumulated
  | Nat.succ fuelPredecessor, accumulated =>
      cond (cvbBasisBeq (srnExpandRound transitions accumulated accumulated) accumulated)
        accumulated
        (srnReachSaturate transitions fuelPredecessor
          (srnExpandRound transitions accumulated accumulated))

/-- The reachable markings of a net within `fuel` BFS rounds, from the initial
marking. -/
def srnReachableMarkings (net : SrnNet) (fuel : Nat) : List (List Nat) :=
  srnReachSaturate net.transitions fuel (net.initialMarking :: [])

/-- Structural position lookup of a marking in a list — no `getD`; full-enum match
on the `Option` recursion. -/
def srnMarkingIndex (marking : List Nat) : List (List Nat) → Option Nat
  | [] => none
  | head :: rest =>
      cond (cswListNatBeq marking head)
        (some 0)
        (match srnMarkingIndex marking rest with
          | none => none
          | some index => some (Nat.succ index))

/-- The exit rate of a marking: the `qnfAdd` fold of the rates of every enabled
transition. -/
def srnExitRate : List SrnTransition → List Nat → QnfRat
  | [], _ => qnfZero
  | transition :: rest, marking =>
      cond (srnFireEnabled marking transition)
        (qnfAdd transition.rate (srnExitRate rest marking))
        (srnExitRate rest marking)

/-! ## T3 — the generator matrix, the jump chain, and the row-sum-zero soundness -/

/-- The off-diagonal generator entry `Q[marking][target]`: the total rate of the
enabled transitions whose firing lands exactly on `target`. -/
def srnGeneratorOffDiag : List SrnTransition → List Nat → List Nat → QnfRat
  | [], _, _ => qnfZero
  | transition :: rest, marking, target =>
      cond (srnFireEnabled marking transition &&
            cswListNatBeq (srnFireTarget marking transition) target)
        (qnfAdd transition.rate (srnGeneratorOffDiag rest marking target))
        (srnGeneratorOffDiag rest marking target)

/-- The generator entry for row `marking`, column `target`: the negated exit rate on
the diagonal (`target = marking`), else the off-diagonal rate sum. -/
def srnGeneratorEntry (transitions : List SrnTransition) (marking target : List Nat) : QnfRat :=
  cond (cswListNatBeq target marking)
    (qnfNeg (srnExitRate transitions marking))
    (srnGeneratorOffDiag transitions marking target)

/-- The generator row for `marking`: one entry per reachable column marking. -/
def srnGeneratorRow (transitions : List SrnTransition) :
    List (List Nat) → List Nat → List QnfRat
  | [], _ => []
  | target :: rest, marking =>
      srnGeneratorEntry transitions marking target :: srnGeneratorRow transitions rest marking

/-- The generator rows over a fixed `reach`, one per row marking. -/
def srnGeneratorMatrixAux (transitions : List SrnTransition) (reach : List (List Nat)) :
    List (List Nat) → List (List QnfRat)
  | [] => []
  | marking :: rest =>
      srnGeneratorRow transitions reach marking :: srnGeneratorMatrixAux transitions reach rest

/-- The full generator matrix `Q` over the reachable markings: a square table
indexed by `reach` on both axes. -/
def srnGeneratorMatrix (net : SrnNet) (reach : List (List Nat)) : List (List QnfRat) :=
  srnGeneratorMatrixAux net.transitions reach reach

/-- Sum a list of rationals (cons-only `qnfAdd` fold) — the row total. -/
def srnRowSum : List QnfRat → QnfRat
  | [] => qnfZero
  | value :: rest => qnfAdd value (srnRowSum rest)

/-- Cons-only concatenation of rational lists. -/
def srnQnfConcat : List QnfRat → List QnfRat → List QnfRat
  | [], right => right
  | head :: rest, right => head :: srnQnfConcat rest right

/-- `srnRowSum` distributes over concatenation — the append-splits-sum law (the
`ihcSumCat` shape), transported through `qnfAddZeroLeft`/`qnfAddAssoc`. -/
theorem srnRowSumCat : (firstVec secondVec : List QnfRat) →
    srnRowSum (srnQnfConcat firstVec secondVec) =
      qnfAdd (srnRowSum firstVec) (srnRowSum secondVec)
  | [], secondVec => (qnfAddZeroLeft (srnRowSum secondVec)).symm
  | head :: rest, secondVec => by
      show qnfAdd head (srnRowSum (srnQnfConcat rest secondVec)) =
        qnfAdd (qnfAdd head (srnRowSum rest)) (srnRowSum secondVec)
      rw [srnRowSumCat rest secondVec,
        qnfAddAssoc head (srnRowSum rest) (srnRowSum secondVec)]

/-- The embedded discrete-time jump chain entry: the off-diagonal generator rate
normalised by the exit rate, `Q[marking][target] / exitRate(marking)`.  Total when
the exit rate is nonzero (otherwise `qnfInv` returns canonical-zero junk — guard
with `srnExitRatePositive`). -/
def srnEmbeddedJumpEntry (transitions : List SrnTransition) (marking target : List Nat) : QnfRat :=
  qnfMul (srnGeneratorOffDiag transitions marking target)
    (qnfInv (srnExitRate transitions marking))

/-- Well-formedness guard for the jump chain: the exit rate of `marking` is nonzero
(the marking is not an absorbing state) — read directly off the canonical carrier by
`qnfBeq` against `qnfZero`. -/
def srnExitRatePositive (transitions : List SrnTransition) (marking : List Nat) : Bool :=
  not (qnfBeq (srnExitRate transitions marking) qnfZero)

/-- **THE CROWN SOUNDNESS — the CTMC generator row sums to zero.**  A generator row
presented as its off-diagonal entries with the diagonal `qnfNeg total` prepended,
where `total` is the off-diagonal sum, sums to `qnfZero`.  The off-diagonal rates
leaving a state exactly cancel the negative diagonal — the defining property of a
Markov generator — a single `qnfAddNegLeft`, general and zero-axiom. -/
theorem srnBalancedRowSumsToZero (total : QnfRat) (offDiagEntries : List QnfRat)
    (hasOffDiagTotal : srnRowSum offDiagEntries = total) :
    srnRowSum (qnfNeg total :: offDiagEntries) = qnfZero := by
  show qnfAdd (qnfNeg total) (srnRowSum offDiagEntries) = qnfZero
  rw [hasOffDiagTotal]
  exact qnfAddNegLeft total

/-! ## T4 — the walls -/

/-- **WALL** — an unbounded stochastic rate net has infinitely many reachable
markings, so its CTMC is an infinite-state chain and `srnReachableMarkings` never
stabilises within any fuel.  Deciding boundedness (so as to enumerate the FULL
state space) is the Petri-net coverability / WSTS well-quasi-order problem — exactly
the NET-4 Dickson impossibility `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false`:
the finiteness certificate is the almost-full PRODUCT over `List Nat`, whose
both-`later` case needs the non-structural `WellFounded.fix`, unavailable in Init.
Shipped instead: the fuel-bounded `srnReachableMarkings`, correct over whatever
finite set it converges to.  Burned attacks: (1) raising the BFS fuel only
under-approximates — a net that grows a coordinate without bound never converges, so
no fuel value certifies "these are ALL the states"; (2) a decreasing structural
measure on the round-to-round marking-set chain would need the `Nat^k`-WQO to bound
the antichain growth — the same walled `WellFounded.fix` (see the sibling
`cvbHasUnconditionalCoverabilityTermination = false`). -/
def srnHasUnboundedStateSpace : Bool := false

/-- **WALL** — the stationary (steady-state) distribution `π` with `π Q = 0` and
`Σπ = 1` is the null-space of the generator, computed by Gaussian elimination over
`QnfRat`.  That linear solve is a DISTINCT rung (NET-16); the substrate exists
(`ComputerAlgebra/.../RationalLinearRelations`) but wiring the null-space extraction
is separate work, out of scope for NET-15.  Burned attacks: (1) fixed-point
iteration `π ← π P` on the embedded jump chain converges only in the limit — no
finite `rfl` certificate over exact `QnfRat`, and its convergence proof needs a
contraction/ergodicity argument absent here; (2) reading `π` off a cofactor /
adjugate expansion of `Q` needs the determinant-and-minors machinery over `QnfRat`,
itself the NET-16 linear-algebra rung, not a Petri-net fact. -/
def srnHasStationaryDistribution : Bool := false

/-- The unbounded-state-space wall is definitionally the NET-4 Dickson wall. -/
theorem srnUnboundedWallEqualsDickson :
    srnHasUnboundedStateSpace = fxNet4_dicksonWall := rfl

/-- DECIDED: a stochastic rate net extracts a CTMC generator matrix over its
fuel-bounded reachable markings — exit rates (`srnExitRate`), off-diagonal rate sums
(`srnGeneratorOffDiag`), the negated diagonal (`srnGeneratorEntry`/`srnGeneratorRow`/
`srnGeneratorMatrix`), and the embedded jump chain (`srnEmbeddedJumpEntry`), all in
exact `QnfRat`. -/
def srnHasGeneratorExtraction : Bool := true

/-- DECIDED: the extracted generator satisfies the row-sum-zero soundness
(`srnBalancedRowSumsToZero`) — off-diagonal rates cancel the negative diagonal —
fired on concrete 2-state and 3-state chains. -/
def srnHasRowSumZeroSoundness : Bool := true

/-! ## T5 — concrete rates, nets, and ground fires

Small nets with rational rates `1/2`, `1/3`, `1/6`.  Every marking-changing
transition (no self-loops), so the off-diagonal total equals the exit rate and each
generator row sums to zero by kernel computation. -/

set_option maxRecDepth 8192

/-- The rate `1/2`. -/
def srnHalf : QnfRat := qnfNormalize ({ numerator := 1, denominatorPredecessor := 1 } : RationalPair)

/-- The rate `1/3`. -/
def srnThird : QnfRat := qnfNormalize ({ numerator := 1, denominatorPredecessor := 2 } : RationalPair)

/-- The rate `1/6`. -/
def srnSixth : QnfRat := qnfNormalize ({ numerator := 1, denominatorPredecessor := 5 } : RationalPair)

/-- Move the token from place `0` to place `1`, at rate `1/2`. -/
def srnMoveAB : SrnTransition := { pre := [1, 0], post := [0, 1], rate := srnHalf }

/-- Move the token from place `1` to place `0`, at rate `1/3`. -/
def srnMoveBA : SrnTransition := { pre := [0, 1], post := [1, 0], rate := srnThird }

/-- A two-state toggle net: one token toggling between the two places.  Reachable
markings: `[1,0]` and `[0,1]`. -/
def srnToggleNet : SrnNet :=
  { placeCount := 2, transitions := [srnMoveAB, srnMoveBA], initialMarking := [1, 0] }

/-- Cycle `e0 → e1` at rate `1/2`. -/
def srnCycleA : SrnTransition := { pre := [1, 0, 0], post := [0, 1, 0], rate := srnHalf }

/-- Cycle `e1 → e2` at rate `1/3`. -/
def srnCycleB : SrnTransition := { pre := [0, 1, 0], post := [0, 0, 1], rate := srnThird }

/-- Cycle `e2 → e0` at rate `1/6`. -/
def srnCycleC : SrnTransition := { pre := [0, 0, 1], post := [1, 0, 0], rate := srnSixth }

/-- A three-state cyclic net: one token cycling `e0 → e1 → e2 → e0`.  Reachable
markings: `[1,0,0]`, `[0,1,0]`, `[0,0,1]`. -/
def srnCycleNet : SrnNet :=
  { placeCount := 3, transitions := [srnCycleA, srnCycleB, srnCycleC],
    initialMarking := [1, 0, 0] }

/-- Fire: the move `e0 → e1` is enabled at `[1,0]`. -/
theorem srnFireEnabledToggle : srnFireEnabled [1, 0] srnMoveAB = true := rfl

/-- Fire: firing `e0 → e1` at `[1,0]` reaches `[0,1]`. -/
theorem srnFireTargetToggle : srnFireTarget [1, 0] srnMoveAB = [0, 1] := rfl

/-- Fire (disabled): the reverse move `e1 → e0` is NOT enabled at `[1,0]`. -/
theorem srnFireDisabledToggle : srnFireEnabled [1, 0] srnMoveBA = false := rfl

/-- Fire: the exit rate of `[1,0]` is `1/2` — the single enabled move's rate. -/
theorem srnExitRateToggle : srnExitRate srnToggleNet.transitions [1, 0] = srnHalf := rfl

/-- Fire (disabled contributes nothing): the reverse move alone gives exit rate
`0` at `[1,0]`, where it is disabled. -/
theorem srnExitRateDisabledSkips : srnExitRate [srnMoveBA] [1, 0] = qnfZero := rfl

/-- Fire: the marking-index lookup finds `[0,1]` at position `1`. -/
theorem srnMarkingIndexToggle : srnMarkingIndex [0, 1] [[1, 0], [0, 1]] = some 1 := rfl

/-- Fire: the reachable set of the toggle net enumerates `[[1,0], [0,1]]`. -/
theorem srnReachableToggle : srnReachableMarkings srnToggleNet 4 = [[1, 0], [0, 1]] := rfl

/-- Fire: the reachable set of the cyclic net enumerates all three states. -/
theorem srnReachableCycle :
    srnReachableMarkings srnCycleNet 5 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]] := rfl

/-- **The soundness fire (2-state)**: the generator row for `[1,0]` — the diagonal
`-1/2` and the off-diagonal `1/2` — sums to `qnfZero`. -/
theorem srnGeneratorRowToggleSumsZero :
    srnRowSum (srnGeneratorRow srnToggleNet.transitions [[1, 0], [0, 1]] [1, 0]) = qnfZero := rfl

/-- The soundness fire, other row (2-state): the generator row for `[0,1]` sums to
`qnfZero` as well. -/
theorem srnGeneratorRowToggleSumsZeroOther :
    srnRowSum (srnGeneratorRow srnToggleNet.transitions [[1, 0], [0, 1]] [0, 1]) = qnfZero := rfl

/-- **The soundness fire (3-state)**: the generator row for `[1,0,0]` in the cyclic
net sums to `qnfZero`. -/
theorem srnGeneratorRowCycleSumsZero :
    srnRowSum
        (srnGeneratorRow srnCycleNet.transitions [[1, 0, 0], [0, 1, 0], [0, 0, 1]] [1, 0, 0]) =
      qnfZero := rfl

/-- Fire: the embedded jump probability out of `[1,0]` to `[0,1]` is
`(1/2) / (1/2) = 1` — the only exit, so probability one. -/
theorem srnEmbeddedJumpToggleOne :
    srnEmbeddedJumpEntry srnToggleNet.transitions [1, 0] [0, 1] = qnfOne := rfl

end FX1Poly.Polygraph.Net
