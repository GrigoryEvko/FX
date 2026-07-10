import FX1Poly.Polygraph.Omega.Steiner.CoordinateArithmetic

/-! # Polygraph/Omega/Steiner/ChainCell — the boundary-faithful full-chain carrier (OMEGA-2.5 r1, B1)

★ **The chain table.**  OMEGA-2's `SteinerCell` (`Steiner/CellCoordinates.lean`) collapses a free
`dim`-cell to a SINGLE top-dimension integer vector — dimension-agnostic, so it FORGETS the lower
boundary poles (that is the lossy-whisker obstruction, `Reconstruct.lean:18-21`).  This file ships the
ADDITIVE sibling `SteinerChainCell`: the honest Steiner atom-table
`⟨x_0^-, x_0^+, …, x_{m-1}^-, x_{m-1}^+, x_m⟩` — one `(source, target)` POLE PAIR per dimension below
the top, plus the top vector.  The pole rows record the boundary context the single vector drops, so
the whisker-conflated pairs OMEGA-2 could not separate become separable (JOB 3, `WhiskerFix.lean`).

## The carrier decision (recon JOB 1)

  * `SteinerChainCell = { poles : List (CellVector × CellVector), top : CellVector }`.  The pole list is
    ordered TOP-FIRST (index 0 = the top-adjacent pole `(x_{m-1}^-, x_{m-1}^+)`), a cons-only build (no
    `List.append`, no `List.concat` — the propext-clean discipline of `CoordinateArithmetic`).
  * REJECTED — bare rows `List (List Int)`: a whiskered cell's source and target rows differ off a
    parallel cell (`boundarySource ≠ boundaryTarget`), so one row per dimension cannot encode the
    positivity (`±`) split the whisker fix needs.  The pole PAIR is the honest atom.
  * `DecidableEq SteinerChainCell` is STRUCTURAL (the `List (List Int × List Int)` / `List Int`
    Init deciders), propext-clean — exactly `DecidableCellEq.lean:29-35`'s idiom lifted to two fields.

## The rowwise arithmetic kit (recon JOB 4 (i)/(ii))

`addPoleTable` adds two pole tables componentwise (`addCoordinates` on each `±` leg), fully-enumerated
cons-only arms mirroring `addCoordinates` — NO Init `List.zipWith` / `List.map₂` / `List.append`.  Its
abelian laws (`addPoleTable_comm` / `_assoc` / the two nil absorbers / `_length_eq`) fold the per-leg
`CoordinateArithmetic` lemmas, which are themselves built over the LOCAL `intAddComm` / `intAddAssoc`
kit (Init's `Int.add_comm` LEAKS propext — see `CoordinateArithmetic.lean:23-24`).

## composeAtFull — the codimension-0 (top) composite

`composeAtFull` is the free vertical composite `*_{top}` at chain granularity: the top vectors ADD
(`addCoordinates`), the shared lower rows are KEPT (agreement below the glue), and the top pole is glued
`(source from x, target from y)`.  Its homomorphism against `linearizeFull` is UNCONDITIONAL
(`LinearizeFull.lean`, `linearizeFull_vcomp_composeAtFull`) — the shared-boundary crux the recon flagged
DISSOLVES because `linearizeFull` reads its lower rows off `boundarySource` directly (no composability
side condition, no `Option`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Steiner

open FX1Poly.ComputerAlgebra

/-! ## The chain carrier -/

/-- A **Steiner chain cell** — the boundary-faithful atom table of a free `dim`-cell: one
`(source, target)` POLE PAIR per dimension below the top (ordered TOP-FIRST), plus the top vector.  The
positivity split (`source = d^-`, `target = d^+`) the single vector `SteinerCell` collapses is recorded
here, so whiskered cells with distinct boundary context are distinguishable. -/
structure SteinerChainCell where
  /-- The boundary poles below the top dimension, top-adjacent first: `poles[i] = (x^-, x^+)` at the
  `(dim - 1 - i)`-boundary. -/
  poles : List (CellVector × CellVector)
  /-- The top-dimension integer vector (the OMEGA-2 single vector). -/
  top : CellVector

/-! ## Structural decidable equality (propext-clean) -/

/-- **Structural decidable equality of chain cells** — both fields decide over the Init `List`/`Prod`/
`Int` structural deciders (no indexed inductive, no `propext`), exactly `DecidableCellEq`'s idiom lifted
to two fields. -/
instance decidableSteinerChainCellEq : DecidableEq SteinerChainCell :=
  fun leftCell rightCell =>
    if polesEqual : leftCell.poles = rightCell.poles then
      if topsEqual : leftCell.top = rightCell.top then
        isTrue (by
          cases leftCell
          cases rightCell
          exact congr (congrArg SteinerChainCell.mk polesEqual) topsEqual)
      else
        isFalse (fun cellsEqual => topsEqual (congrArg SteinerChainCell.top cellsEqual))
    else
      isFalse (fun cellsEqual => polesEqual (congrArg SteinerChainCell.poles cellsEqual))

/-! ## The rowwise pole-table arithmetic kit -/

/-- Add one pole PAIR componentwise: sources add, targets add (via `addCoordinates`). -/
def addPolePair : (CellVector × CellVector) → (CellVector × CellVector) → (CellVector × CellVector)
  | (leftSource, leftTarget), (rightSource, rightTarget) =>
      (addCoordinates leftSource rightSource, addCoordinates leftTarget rightTarget)

/-- **Rowwise pole-table addition** — add two pole tables row by row, fully-enumerated cons-only arms
(mirroring `addCoordinates`; the ragged arms truncate, so equal-length use is exact). -/
def addPoleTable :
    List (CellVector × CellVector) → List (CellVector × CellVector) → List (CellVector × CellVector)
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | leftPole :: leftRest, rightPole :: rightRest =>
      addPolePair leftPole rightPole :: addPoleTable leftRest rightRest

/-! ### The pole-pair abelian laws (fold the per-leg `CoordinateArithmetic` lemmas) -/

/-- **Pole-pair addition commutes** — each leg by `addCoordinates_comm`. -/
theorem addPolePair_comm : (leftPole rightPole : CellVector × CellVector) →
    addPolePair leftPole rightPole = addPolePair rightPole leftPole
  | (leftSource, leftTarget), (rightSource, rightTarget) => by
      show (addCoordinates leftSource rightSource, addCoordinates leftTarget rightTarget)
        = (addCoordinates rightSource leftSource, addCoordinates rightTarget leftTarget)
      rw [addCoordinates_comm leftSource rightSource, addCoordinates_comm leftTarget rightTarget]

/-- **Pole-pair addition associates** — each leg by `addCoordinates_assoc`. -/
theorem addPolePair_assoc : (leftPole middlePole rightPole : CellVector × CellVector) →
    addPolePair (addPolePair leftPole middlePole) rightPole
      = addPolePair leftPole (addPolePair middlePole rightPole)
  | (leftSource, leftTarget), (middleSource, middleTarget), (rightSource, rightTarget) => by
      show (addCoordinates (addCoordinates leftSource middleSource) rightSource,
            addCoordinates (addCoordinates leftTarget middleTarget) rightTarget)
        = (addCoordinates leftSource (addCoordinates middleSource rightSource),
            addCoordinates leftTarget (addCoordinates middleTarget rightTarget))
      rw [addCoordinates_assoc leftSource middleSource rightSource,
        addCoordinates_assoc leftTarget middleTarget rightTarget]

/-! ### The pole-table abelian laws -/

/-- `addPoleTable` with an empty LEFT operand truncates to empty. -/
theorem addPoleTable_nil_left : (rightTable : List (CellVector × CellVector)) →
    addPoleTable [] rightTable = []
  | [] => rfl
  | _ :: _ => rfl

/-- `addPoleTable` with an empty RIGHT operand truncates to empty. -/
theorem addPoleTable_nil_right : (leftTable : List (CellVector × CellVector)) →
    addPoleTable leftTable [] = []
  | [] => rfl
  | _ :: _ => rfl

/-- **Rowwise pole-table addition commutes** — the cons arm by `addPolePair_comm`, the ragged arms
symmetric. -/
theorem addPoleTable_comm : (leftTable rightTable : List (CellVector × CellVector)) →
    addPoleTable leftTable rightTable = addPoleTable rightTable leftTable
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | leftPole :: leftRest, rightPole :: rightRest => by
      show addPolePair leftPole rightPole :: addPoleTable leftRest rightRest
        = addPolePair rightPole leftPole :: addPoleTable rightRest leftRest
      rw [addPolePair_comm leftPole rightPole, addPoleTable_comm leftRest rightRest]

/-- **Rowwise pole-table addition associates** — the cons arm by `addPolePair_assoc`, the ragged arms
collapse through the nil absorbers. -/
theorem addPoleTable_assoc : (leftTable middleTable rightTable : List (CellVector × CellVector)) →
    addPoleTable (addPoleTable leftTable middleTable) rightTable
      = addPoleTable leftTable (addPoleTable middleTable rightTable)
  | [], _, _ => by
      rw [addPoleTable_nil_left, addPoleTable_nil_left, addPoleTable_nil_left]
  | _ :: _, [], _ => by
      rw [addPoleTable_nil_right, addPoleTable_nil_left, addPoleTable_nil_right]
  | _ :: _, _ :: _, [] => by
      rw [addPoleTable_nil_right, addPoleTable_nil_right, addPoleTable_nil_right]
  | leftPole :: leftRest, middlePole :: middleRest, rightPole :: rightRest => by
      show addPolePair (addPolePair leftPole middlePole) rightPole
          :: addPoleTable (addPoleTable leftRest middleRest) rightRest
        = addPolePair leftPole (addPolePair middlePole rightPole)
          :: addPoleTable leftRest (addPoleTable middleRest rightRest)
      rw [addPolePair_assoc leftPole middlePole rightPole,
        addPoleTable_assoc leftRest middleRest rightRest]

/-- **Equal-length rowwise addition preserves length** — the exactness fact (no truncation fires). -/
theorem addPoleTable_length_eq : (leftTable rightTable : List (CellVector × CellVector)) →
    leftTable.length = rightTable.length →
    (addPoleTable leftTable rightTable).length = leftTable.length
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], lengthsEqual => Nat.noConfusion lengthsEqual
  | _ :: leftRest, _ :: rightRest, lengthsEqual => by
      show (addPoleTable leftRest rightRest).length + 1 = leftRest.length + 1
      exact congrArg (· + 1) (addPoleTable_length_eq leftRest rightRest (Nat.succ.inj lengthsEqual))

/-! ### The degenerate zero pole table + a zero law -/

/-- The **degenerate pole row** at a given ambient length — both legs the all-zero vector. -/
def zeroPoleRow (ambient : Nat) : CellVector × CellVector := (zeroVector ambient, zeroVector ambient)

/-- The **degenerate pole table** of a given row count at a given ambient length. -/
def zeroPoleTable (ambient : Nat) : Nat → List (CellVector × CellVector)
  | 0 => []
  | rows + 1 => zeroPoleRow ambient :: zeroPoleTable ambient rows

/-- `zeroPoleTable ambient rows` has length `rows`. -/
theorem zeroPoleTable_length : (ambient rows : Nat) → (zeroPoleTable ambient rows).length = rows
  | _, 0 => rfl
  | ambient, rows + 1 => congrArg (· + 1) (zeroPoleTable_length ambient rows)

/-- **The degenerate pole row is a LEFT unit** for pole-pair addition at its own ambient length — the
identity-cell pole in arithmetic form. -/
theorem addPolePair_zeroPoleRow_left (ambient : Nat) (poleSource poleTarget : CellVector)
    (sourceLength : poleSource.length = ambient) (targetLength : poleTarget.length = ambient) :
    addPolePair (zeroPoleRow ambient) (poleSource, poleTarget) = (poleSource, poleTarget) := by
  subst sourceLength
  show (addCoordinates (zeroVector poleSource.length) poleSource,
        addCoordinates (zeroVector poleSource.length) poleTarget) = (poleSource, poleTarget)
  rw [addCoordinates_zeroVector_left poleSource, ← targetLength,
    addCoordinates_zeroVector_left poleTarget]

/-! ## composeAtFull — the codimension-0 (top) composite -/

/-- Glue two pole tables at the top pole: source from the left, target from the right, keeping the
left's shared lower rows.  The ragged arms fall back to whichever table is nonempty. -/
def gluePoleHead :
    List (CellVector × CellVector) → List (CellVector × CellVector) → List (CellVector × CellVector)
  | [], [] => []
  | [], rightPole :: rightRest => rightPole :: rightRest
  | leftPole :: leftRest, [] => leftPole :: leftRest
  | leftPole :: leftRest, rightPole :: _ => (leftPole.1, rightPole.2) :: leftRest

/-- ★ **The chain-granularity vertical composite `*_{top}`** — the free vcomp of two `(dim+1)`-cells at
chain granularity: the top vectors ADD, the shared lower rows are kept, and the top pole is glued
(outer source from `leftCell`, outer target from `rightCell`).  Total; its homomorphism against
`linearizeFull` is UNCONDITIONAL (`LinearizeFull.lean`), so the shared-boundary crux the recon flagged
does not appear (no composability side condition, no `Option`). -/
def composeAtFull (leftCell rightCell : SteinerChainCell) : SteinerChainCell where
  poles := gluePoleHead leftCell.poles rightCell.poles
  top := addCoordinates leftCell.top rightCell.top

/-! ## Non-vacuity evals (the carrier + ops + decider all compute) -/

/-- The carrier is inhabited and its equality decides `true` on a match. -/
example : (⟨[([1], [2])], [3]⟩ : SteinerChainCell) = ⟨[([1], [2])], [3]⟩ := rfl

/-- Distinct top vectors decide `false`. -/
example : decide ((⟨[], [1]⟩ : SteinerChainCell) = ⟨[], [2]⟩) = false := rfl

/-- Distinct pole tables decide `false`. -/
example : decide ((⟨[([1], [0])], [7]⟩ : SteinerChainCell) = ⟨[([0], [0])], [7]⟩) = false := rfl

/-- Rowwise pole-table addition computes: `[1]+[3]=[4]`, `[2]+[4]=[6]`. -/
example : addPoleTable [([1], [2])] [([3], [4])] = [([4], [6])] := rfl

/-- `addPoleTable` commutes on a concrete pair (an eval-level instance of `addPoleTable_comm`). -/
example : addPoleTable [([1], [2])] [([3], [4])] = addPoleTable [([3], [4])] [([1], [2])] := rfl

/-- `composeAtFull` glues the top pole `([1], _) * (_, [4]) = ([1], [4])` and adds the tops
`[10] + [20] = [30]`. -/
example :
    composeAtFull ⟨[([1], [2])], [10]⟩ ⟨[([3], [4])], [20]⟩ = ⟨[([1], [4])], [30]⟩ := rfl

/-- The degenerate pole table has the declared length. -/
example : (zeroPoleTable 3 2).length = 2 := rfl

end FX1Poly.Polygraph.Steiner
