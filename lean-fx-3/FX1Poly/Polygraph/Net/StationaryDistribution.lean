import FX1Poly.Polygraph.Net.StochasticRateNet

/-!
# Exact stationary distributions of finite CTMCs (`stn` prefix)

Given the NET-15 stochastic-rate-net generator matrix `Q` over the fuel-bounded
reachable markings (exact `QnfRat` throughout), this module solves the steady-state
balance equations `π Q = 0` with `Σ π = 1` by exact rational Gaussian elimination.

The pipeline is entirely structural / structural-fuel (no `WellFounded.fix`, no
`Nat`-order lemmas in proofs):

* `stnTranspose` turns the row-indexed `Q` into the column-indexed `Qᵀ` (fuel = the
  width of the first row);
* `stnNullSpaceSystem` pins the first coordinate (`π₀ = 1`) and keeps the remaining
  balance rows, forming a nonsingular augmented system;
* `stnForward` is the forward elimination (structural on a `Nat` fuel = row count):
  scale the head row by `qnfInv` of its pivot, clear the pivot column from every
  remaining row by a `qnfMul`/`qnfAdd` combination, recurse;
* `stnBack` is the back-substitution (structural on the row list);
* `stnNormalise` rescales the null vector by the reciprocal of its `qnfAdd`-fold so
  the entries sum to `qnfOne`.

The crown soundness is the COLUMN-side balance: for the computed `π`, the exact
rational dot product against EACH column of `Q` is `qnfZero` — this is `π Q = 0`
per coordinate, distinct from NET-15's ROW-side `srnBalancedRowSumsToZero`.

Everything is fired on the concrete NET-15 toggle net (`π = [2/5, 3/5]`) and the
three-state cyclic net (`π = [2/11, 3/11, 6/11]`, proportional to the exit-rate
reciprocals) by kernel `rfl`.  Zero-axiom: no `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `funext`, `WellFounded.fix`, `omega`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FX1Poly.Polygraph.Net

open FX1Poly.ComputerAlgebra

/-! ## T1 — the matrix and vector algebra (own cons-only list ops) -/

/-- A rational matrix: a list of rational rows. -/
abbrev StnMatrix : Type := List (List QnfRat)

/-- Read the entry at position `index` of a rational vector; out-of-range is the
canonical zero. -/
def stnGet : Nat → List QnfRat → QnfRat
  | _, [] => qnfZero
  | 0, value :: _ => value
  | Nat.succ index, _ :: rest => stnGet index rest

/-- Scale every entry of a vector by `factor` — cons-only `qnfMul` map. -/
def stnScale (factor : QnfRat) : List QnfRat → List QnfRat
  | [] => []
  | value :: rest => qnfMul factor value :: stnScale factor rest

/-- The elimination combination `target + factor · pivot`, entrywise — cons-only
`qnfAdd`-of-`qnfMul` over the two aligned rows. -/
def stnAxpy (factor : QnfRat) : List QnfRat → List QnfRat → List QnfRat
  | [], target => target
  | _, [] => []
  | pivotHead :: pivotRest, targetHead :: targetRest =>
      qnfAdd targetHead (qnfMul factor pivotHead) ::
        stnAxpy factor pivotRest targetRest

/-- Clear column `column` from every row using a pivot row whose entry at `column`
is one: `row := row - row[column] · pivot`. -/
def stnClearRows (column : Nat) (pivot : List QnfRat) : StnMatrix → StnMatrix
  | [] => []
  | row :: rest =>
      stnAxpy (qnfNeg (stnGet column row)) pivot row ::
        stnClearRows column pivot rest

/-- Extract column `column` of a matrix as a vector — cons-only. -/
def stnColumn (column : Nat) : StnMatrix → List QnfRat
  | [] => []
  | row :: rest => stnGet column row :: stnColumn column rest

/-- The exact rational dot product of two aligned vectors — cons-only
`qnfAdd`-of-`qnfMul` fold. -/
def stnVecDot : List QnfRat → List QnfRat → QnfRat
  | [], _ => qnfZero
  | _, [] => qnfZero
  | leftHead :: leftRest, rightHead :: rightRest =>
      qnfAdd (qnfMul leftHead rightHead) (stnVecDot leftRest rightRest)

/-- Matrix times vector `M · x`: each row dotted with `x` — cons-only. -/
def stnMatVec : StnMatrix → List QnfRat → List QnfRat
  | [], _ => []
  | row :: rest, vector => stnVecDot row vector :: stnMatVec rest vector

/-- Take the first `count` entries of a vector — own structural definition. -/
def stnTake : Nat → List QnfRat → List QnfRat
  | 0, _ => []
  | _, [] => []
  | Nat.succ count, value :: rest => value :: stnTake count rest

/-- Drop the first `count` entries of a vector — own structural definition. -/
def stnDrop : Nat → List QnfRat → List QnfRat
  | 0, values => values
  | _, [] => []
  | Nat.succ count, _ :: rest => stnDrop count rest

/-- The first entry of every row (the leading column) — cons-only. -/
def stnHeads : StnMatrix → List QnfRat
  | [] => []
  | row :: rest => stnGet 0 row :: stnHeads rest

/-- Drop the leading column from every row — cons-only. -/
def stnTails : StnMatrix → StnMatrix
  | [] => []
  | row :: rest => stnDrop 1 row :: stnTails rest

/-- Column-cons transpose driven by a structural fuel = the matrix width. -/
def stnTransposeAux : Nat → StnMatrix → StnMatrix
  | 0, _ => []
  | Nat.succ fuel, rows => stnHeads rows :: stnTransposeAux fuel (stnTails rows)

/-- The width of a matrix — the length of its first row. -/
def stnFirstRowLength : StnMatrix → Nat
  | [] => 0
  | row :: _ => row.length

/-- Transpose a rational matrix; `π Q = 0` is equivalent to `Qᵀ πᵀ = 0`. -/
def stnTranspose (rows : StnMatrix) : StnMatrix :=
  stnTransposeAux (stnFirstRowLength rows) rows

/-- Append a single entry to the tail of a vector — cons-only. -/
def stnSnoc : List QnfRat → QnfRat → List QnfRat
  | [], value => [value]
  | head :: rest, value => head :: stnSnoc rest value

/-- The all-zero vector of a given length. -/
def stnZeros : Nat → List QnfRat
  | 0 => []
  | Nat.succ predecessor => qnfZero :: stnZeros predecessor

/-- The all-one vector of a given length. -/
def stnOnes : Nat → List QnfRat
  | 0 => []
  | Nat.succ predecessor => qnfOne :: stnOnes predecessor

/-! ## T2 — the augmented balance system and structural-fuel Gaussian elimination -/

/-- The pin row `[1, 0, …, 0 | 1]` of the augmented system — fixes `π₀ = 1`,
replacing one (linearly dependent) balance row so the system becomes nonsingular. -/
def stnPinRow (dimension : Nat) : List QnfRat :=
  stnSnoc (qnfOne :: stnZeros (dimension - 1)) qnfOne

/-- Append a zero right-hand side to every balance row — cons-only. -/
def stnMapAppendZero : StnMatrix → StnMatrix
  | [] => []
  | row :: rest => stnSnoc row qnfZero :: stnMapAppendZero rest

/-- The augmented null-space system for `Qᵀ`: the pin row `π₀ = 1` on top, then
the remaining transposed balance rows with a zero right-hand side. -/
def stnNullSpaceSystem (transposed : StnMatrix) (dimension : Nat) : StnMatrix :=
  match transposed with
  | [] => []
  | _ :: restRows => stnPinRow dimension :: stnMapAppendZero restRows

/-- **Forward elimination** — structural recursion on the `Nat` fuel (= row count),
NOT `WellFounded.fix`.  Scale the head row so its pivot at `column` is one, clear
that column from every remaining row, recurse at the next column.  Produces a
unit-diagonal upper-triangular augmented matrix for a nonsingular, diagonally
pivoted system. -/
def stnForward : Nat → Nat → StnMatrix → StnMatrix
  | 0, _, rows => rows
  | Nat.succ _, _, [] => []
  | Nat.succ fuel, column, headRow :: restRows =>
      let normalisedRow := stnScale (qnfInv (stnGet column headRow)) headRow
      let clearedRows := stnClearRows column normalisedRow restRows
      normalisedRow :: stnForward fuel (column + 1) clearedRows

/-- **Back-substitution** — structural recursion on the reduced row list.  For each
row (leading one at its own column) read `xᵢ = rhs − Σ_{j>i} coeff_j · x_j`, where
the higher solution `x_{i+1}, …` is the recursive result for the tail. -/
def stnBack (dimension : Nat) : StnMatrix → List QnfRat
  | [] => []
  | row :: rest =>
      let higherSolution := stnBack dimension rest
      let coefficients := stnTake dimension row
      let higherCoefficients :=
        stnDrop (coefficients.length - higherSolution.length) coefficients
      qnfSub (stnGet dimension row) (stnVecDot higherCoefficients higherSolution) ::
        higherSolution

/-- Reduce an augmented system to unit-diagonal upper-triangular form. -/
def stnRowReduce (system : StnMatrix) : StnMatrix :=
  stnForward system.length 0 system

/-- Solve a nonsingular augmented system: forward-eliminate, then back-substitute. -/
def stnSolveSystem (dimension : Nat) (system : StnMatrix) : List QnfRat :=
  stnBack dimension (stnRowReduce system)

/-! ## T3 — the stationary vector and its soundness -/

/-- Read the (unnormalised) null-space vector of `Qᵀ` pinned at `π₀ = 1`. -/
def stnNullSpaceVector (transposed : StnMatrix) (dimension : Nat) : List QnfRat :=
  stnSolveSystem dimension (stnNullSpaceSystem transposed dimension)

/-- Rescale a vector by the reciprocal of its `qnfAdd`-fold so its entries sum to
`qnfOne` — reuses the NET-15 `srnRowSum` and the `QnfRat` field inverse. -/
def stnNormalise (vector : List QnfRat) : List QnfRat :=
  stnScale (qnfInv (srnRowSum vector)) vector

/-- **The stationary distribution** of a stochastic rate net over its fuel-bounded
reachable markings: solve `π Q = 0` by exact rational elimination on `Qᵀ`, then
normalise so `Σ π = 1`.  Sound when the CTMC is irreducible (single recurrent class
⇒ `rank Q = n − 1` ⇒ one-dimensional null space); the reducible case is walled
below. -/
def stnStationaryOf (net : SrnNet) (fuel : Nat) : List QnfRat :=
  let reachable := srnReachableMarkings net fuel
  let generator := srnGeneratorMatrix net reachable
  let dimension := reachable.length
  stnNormalise (stnNullSpaceVector (stnTranspose generator) dimension)

/-! ## T4 — the walls -/

/-- DECIDED: the exact stationary distribution of a finite irreducible CTMC is
computed by rational Gaussian elimination on the generator (`stnStationaryOf`), with
the column-side balance soundness (`π Q = 0` per coordinate) and normalisation
(`Σ π = 1`) fired below.  This flips the NET-15 wall
`srnHasStationaryDistribution`. -/
def stnHasStationaryDistribution : Bool := true

/-- **WALL** — an unbounded stochastic rate net has infinitely many reachable
markings, so its CTMC is an infinite-state chain: `srnReachableMarkings` never
converges and `srnGeneratorMatrix` is not a finite `StnMatrix`.  Enumerating the
FULL state space is the Petri-net coverability / WSTS well-quasi-order problem —
exactly the NET-4 Dickson impossibility `fxNet4_dicksonWall = false` (the almost-full
PRODUCT over `List Nat`, whose both-`later` case needs the non-structural
`WellFounded.fix`, unavailable in Init).  This solver ships only over the
fuel-converged finite reachable set, exactly as the NET-15 generator does.
Burned attacks: (1) raising the BFS fuel only under-approximates — a coordinate that
grows without bound never converges, so no fuel value certifies "these are ALL the
states"; (2) a structural decreasing measure on the round-to-round marking-set chain
would need the `Nat^k`-WQO to bound antichain growth — the same walled
`WellFounded.fix`. -/
def stnHasInfiniteStateStationary : Bool := false

/-- **WALL** — a REDUCIBLE (non-irreducible) CTMC has two or more recurrent classes,
hence `dim (null space of Qᵀ) ≥ 2`: ANY convex combination of the per-class
stationary vectors is itself stationary, so NO single canonical `π` exists.  The
reduced echelon has `≥ 2` free variables and `stnNullSpaceVector`'s "pin `π₀ = 1`"
choice is arbitrary among a `≥ 2`-parameter family.  Concrete obstruction: two
disjoint two-state toggles run in parallel (a four-state generator that is block
diagonal) — `[a·π_A , (1−a)·π_B]` is stationary for every `a ∈ [0,1]`.  This is a
genuine mathematical non-uniqueness, not a proof gap: the solver is SOUND only under
an irreducibility precondition.  Burned attacks: (1) adding a second pin row
(`π₀ = 1` and `π_k = 1`) over-determines one recurrent class and leaves the other
free — no canonical joint choice; (2) selecting "the" stationary vector by a
lexicographic tie-break on the free coordinates depends on the (owner-false)
syntactic RREF uniqueness `rreHasRrefUniqueness` AND still picks one point of a
positive-dimensional family arbitrarily. -/
def stnHasReducibleUniqueness : Bool := false

/-- **WALL** — the time-dependent transient distribution `π(t) = π(0) · exp(t Q)`
(uniformization = NET-17) is a matrix exponential / limit: it requires Bishop reals,
not exact `QnfRat`.  No finite `rfl` certificate over the rationals exists, and its
convergence proof needs an analytic (ergodicity / contraction) argument absent here.
Burned attacks: (1) truncating the exponential series `Σ (tQ)^k / k!` gives a
rational approximant but never the exact `π(t)` — the tail is nonzero for every
finite truncation; (2) the embedded uniformized jump chain `P = I + Q/Λ` iterated `m`
times converges to the stationary `π` only as `m → ∞`, again a real limit with no
finite exact witness.  Explicitly deferred to NET-17. -/
def stnHasTransientDistribution : Bool := false

/-- The infinite-state wall is definitionally the NET-15 unbounded-state-space wall
(itself the NET-4 Dickson wall by `srnUnboundedWallEqualsDickson`). -/
theorem stnInfiniteWallEqualsUnbounded :
    stnHasInfiniteStateStationary = srnHasUnboundedStateSpace := rfl

/-! ## T5 — concrete generators, expected rationals, and ground fires -/

/-- The toggle generator `Q = [[-1/2, 1/2], [1/3, -1/3]]` over the reachable
markings `[[1,0], [0,1]]`. -/
def stnToggleGen : StnMatrix :=
  srnGeneratorMatrix srnToggleNet (srnReachableMarkings srnToggleNet 4)

/-- The cyclic generator over the reachable markings `[[1,0,0], [0,1,0], [0,0,1]]`. -/
def stnCycleGen : StnMatrix :=
  srnGeneratorMatrix srnCycleNet (srnReachableMarkings srnCycleNet 5)

/-- The rational `2/5`. -/
def stnTwoFifths : QnfRat :=
  qnfNormalize ({ numerator := 2, denominatorPredecessor := 4 } : RationalPair)

/-- The rational `3/5`. -/
def stnThreeFifths : QnfRat :=
  qnfNormalize ({ numerator := 3, denominatorPredecessor := 4 } : RationalPair)

/-- The rational `3/2` — the toggle null vector's second entry before normalisation. -/
def stnThreeHalves : QnfRat :=
  qnfNormalize ({ numerator := 3, denominatorPredecessor := 1 } : RationalPair)

/-- The rational `2/11`. -/
def stnTwoElevenths : QnfRat :=
  qnfNormalize ({ numerator := 2, denominatorPredecessor := 10 } : RationalPair)

/-- The rational `3/11`. -/
def stnThreeElevenths : QnfRat :=
  qnfNormalize ({ numerator := 3, denominatorPredecessor := 10 } : RationalPair)

/-- The rational `6/11`. -/
def stnSixElevenths : QnfRat :=
  qnfNormalize ({ numerator := 6, denominatorPredecessor := 10 } : RationalPair)

/-- Fire: the toggle transposed generator is `[[-1/2, 1/3], [1/2, -1/3]]`. -/
theorem stnToggleTransposeShape :
    stnTranspose stnToggleGen =
      [[qnfNeg srnHalf, srnThird], [srnHalf, qnfNeg srnThird]] := rfl

/-- Fire: the forward elimination of the toggle null-space system is the
unit-diagonal upper-triangular `[[1, 0 | 1], [0, 1 | 3/2]]`. -/
theorem stnToggleRowReduce :
    stnRowReduce (stnNullSpaceSystem (stnTranspose stnToggleGen) 2) =
      [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, stnThreeHalves]] := rfl

/-- Fire: the toggle null vector pinned at `π₀ = 1` is `[1, 3/2]`. -/
theorem stnToggleNullVector :
    stnNullSpaceVector (stnTranspose stnToggleGen) 2 = [qnfOne, stnThreeHalves] := rfl

/-- **Ground fire**: the toggle stationary distribution is exactly `[2/5, 3/5]`. -/
theorem stnToggleStationary :
    stnStationaryOf srnToggleNet 4 = [stnTwoFifths, stnThreeFifths] := rfl

/-- **Soundness fire (normalisation)**: the toggle stationary distribution sums to
`qnfOne`. -/
theorem stnToggleSumsToOne :
    srnRowSum (stnStationaryOf srnToggleNet 4) = qnfOne := rfl

/-- **Balance soundness (column 0)**: the toggle `π` dotted with the first generator
column is `qnfZero` — the first coordinate of `π Q = 0`. -/
theorem stnToggleBalanceColumnZero :
    stnVecDot (stnStationaryOf srnToggleNet 4) (stnColumn 0 stnToggleGen) = qnfZero := rfl

/-- **Balance soundness (column 1)**: the toggle `π` dotted with the second generator
column is `qnfZero`. -/
theorem stnToggleBalanceColumnOne :
    stnVecDot (stnStationaryOf srnToggleNet 4) (stnColumn 1 stnToggleGen) = qnfZero := rfl

/-- **Ground fire (3-state)**: the cyclic stationary distribution is exactly
`[2/11, 3/11, 6/11]`, proportional to the exit-rate reciprocals `2, 3, 6`. -/
theorem stnCycleStationary :
    stnStationaryOf srnCycleNet 5 =
      [stnTwoElevenths, stnThreeElevenths, stnSixElevenths] := rfl

/-- **Soundness fire (3-state normalisation)**: the cyclic stationary distribution
sums to `qnfOne`. -/
theorem stnCycleSumsToOne :
    srnRowSum (stnStationaryOf srnCycleNet 5) = qnfOne := rfl

/-- **Balance soundness (cyclic column 0)**. -/
theorem stnCycleBalanceColumnZero :
    stnVecDot (stnStationaryOf srnCycleNet 5) (stnColumn 0 stnCycleGen) = qnfZero := rfl

/-- **Balance soundness (cyclic column 1)**. -/
theorem stnCycleBalanceColumnOne :
    stnVecDot (stnStationaryOf srnCycleNet 5) (stnColumn 1 stnCycleGen) = qnfZero := rfl

/-- **Balance soundness (cyclic column 2)**. -/
theorem stnCycleBalanceColumnTwo :
    stnVecDot (stnStationaryOf srnCycleNet 5) (stnColumn 2 stnCycleGen) = qnfZero := rfl

/-- Wall fire: the infinite-state stationary marker is `false`. -/
theorem stnInfiniteStateStationaryIsFalse : stnHasInfiniteStateStationary = false := rfl

/-- Wall fire: the reducible-uniqueness marker is `false`. -/
theorem stnReducibleUniquenessIsFalse : stnHasReducibleUniqueness = false := rfl

/-- Wall fire: the transient-distribution marker is `false`. -/
theorem stnTransientDistributionIsFalse : stnHasTransientDistribution = false := rfl

/-- Decision fire: the stationary-distribution capability is DECIDED `true`. -/
theorem stnStationaryDistributionIsTrue : stnHasStationaryDistribution = true := rfl

end FX1Poly.Polygraph.Net
