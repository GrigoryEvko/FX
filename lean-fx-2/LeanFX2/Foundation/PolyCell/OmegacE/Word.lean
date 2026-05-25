import LeanFX2.Foundation.PolyCell.OmegacE.OmegacEAt

/-!
# omega-cE Scaffold Words

Finite words over the current omega-cE generator scaffold.  This file only
packages lists of declared scaffold generators at a fixed dimension and gives
computable list operations used by later Makkai/Forest work.

It does not decide word equality, construct the HLOR pushout, or prove any
universal coherent-equivalence property.
-/

namespace LeanFX2.Foundation.PolyCell.OmegacE

/-- Suspend every scaffold generator in a list by one dimension. -/
def OmegacECell.suspendList (dimension : Nat) :
    List (OmegacECell dimension) → List (OmegacECell (dimension + 1))
  | [] => []
  | cell :: remainingCells =>
      cell.suspend :: OmegacECell.suspendList dimension remainingCells

/-- Read the numeric slot values of a list of scaffold generators. -/
def OmegacECell.slotValuesOfList (dimension : Nat) :
    List (OmegacECell dimension) → List Nat
  | [] => []
  | cell :: remainingCells =>
      OmegacECell.slotValueOf cell ::
        OmegacECell.slotValuesOfList dimension remainingCells

/-- Read the declared-count index values of a list of scaffold generators. -/
def OmegacECell.declaredIndexValuesOfList (dimension : Nat) :
    List (OmegacECell dimension) → List Nat
  | [] => []
  | cell :: remainingCells =>
      OmegacECell.declaredIndexValueOf cell ::
        OmegacECell.declaredIndexValuesOfList dimension remainingCells

/-- Suspending a list preserves its length. -/
theorem OmegacECell.length_suspendList {dimension : Nat}
    (cells : List (OmegacECell dimension)) :
    (OmegacECell.suspendList dimension cells).length = cells.length := by
  induction cells with
  | nil => rfl
  | cons cell remainingCells inductionHypothesis =>
      dsimp only [OmegacECell.suspendList, List.length]
      rw [inductionHypothesis]

/-- Suspending a list distributes over list append. -/
theorem OmegacECell.suspendList_append {dimension : Nat}
    (firstCells secondCells : List (OmegacECell dimension)) :
    OmegacECell.suspendList dimension (firstCells ++ secondCells) =
      OmegacECell.suspendList dimension firstCells ++
        OmegacECell.suspendList dimension secondCells := by
  induction firstCells with
  | nil =>
      change
        OmegacECell.suspendList dimension secondCells =
          OmegacECell.suspendList dimension secondCells
      rfl
  | cons cell remainingCells inductionHypothesis =>
      change
        cell.suspend ::
            OmegacECell.suspendList dimension
              (remainingCells ++ secondCells) =
          cell.suspend ::
            (OmegacECell.suspendList dimension remainingCells ++
              OmegacECell.suspendList dimension secondCells)
      exact congrArg (List.cons cell.suspend) inductionHypothesis

/-- Appending scaffold-generator lists adds their lengths. -/
theorem OmegacECell.length_append {dimension : Nat}
    (firstCells secondCells : List (OmegacECell dimension)) :
    (firstCells ++ secondCells).length =
      firstCells.length + secondCells.length := by
  induction firstCells with
  | nil =>
      change secondCells.length = 0 + secondCells.length
      rw [Nat.zero_add]
  | cons cell remainingCells inductionHypothesis =>
      change
        Nat.succ ((remainingCells ++ secondCells).length) =
          Nat.succ remainingCells.length + secondCells.length
      rw [inductionHypothesis, Nat.succ_add]

/-- Suspending a list preserves numeric slot values pointwise. -/
theorem OmegacECell.slotValuesOfList_suspendList {dimension : Nat}
    (cells : List (OmegacECell dimension)) :
    OmegacECell.slotValuesOfList (dimension + 1)
        (OmegacECell.suspendList dimension cells) =
      OmegacECell.slotValuesOfList dimension cells := by
  induction cells with
  | nil => rfl
  | cons cell remainingCells inductionHypothesis =>
      dsimp only [OmegacECell.suspendList, OmegacECell.slotValuesOfList]
      rw [OmegacECell.slotValueOf_suspend cell, inductionHypothesis]

/-- Suspending a list preserves declared-count index values pointwise. -/
theorem OmegacECell.declaredIndexValuesOfList_suspendList
    {dimension : Nat} (cells : List (OmegacECell dimension)) :
    OmegacECell.declaredIndexValuesOfList (dimension + 1)
        (OmegacECell.suspendList dimension cells) =
      OmegacECell.declaredIndexValuesOfList dimension cells := by
  induction cells with
  | nil => rfl
  | cons cell remainingCells inductionHypothesis =>
      dsimp only [OmegacECell.suspendList,
        OmegacECell.declaredIndexValuesOfList]
      rw [OmegacECell.declaredIndexValueOf_suspend cell,
        inductionHypothesis]

/-- A finite word over scaffold generators at one dimension. -/
structure OmegacEWord (dimension : Nat) where
  /-- The word as a finite list of current scaffold generators. -/
  cells : List (OmegacECell dimension)
  deriving DecidableEq, Repr

namespace OmegacEWord

/-- Empty scaffold word. -/
def empty (dimension : Nat) : OmegacEWord dimension where
  cells := []

/-- One-generator scaffold word. -/
def singleton {dimension : Nat}
    (cell : OmegacECell dimension) : OmegacEWord dimension where
  cells := [cell]

/-- Concatenate two scaffold words at the same dimension. -/
def append {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    OmegacEWord dimension where
  cells := firstWord.cells ++ secondWord.cells

/-- Word length. -/
def length {dimension : Nat} (word : OmegacEWord dimension) : Nat :=
  word.cells.length

/-- Suspend every generator in a word by one dimension. -/
def suspend {dimension : Nat} (word : OmegacEWord dimension) :
    OmegacEWord (dimension + 1) where
  cells := OmegacECell.suspendList dimension word.cells

/-- Numeric slot projection for a scaffold word. -/
def slotValues {dimension : Nat}
    (word : OmegacEWord dimension) : List Nat :=
  OmegacECell.slotValuesOfList dimension word.cells

/-- Numeric declared-index projection for a scaffold word. -/
def declaredIndexValues {dimension : Nat}
    (word : OmegacEWord dimension) : List Nat :=
  OmegacECell.declaredIndexValuesOfList dimension word.cells

/-- The empty scaffold word has length zero. -/
theorem length_empty (dimension : Nat) :
    (empty dimension).length = 0 := rfl

/-- A singleton scaffold word has length one. -/
theorem length_singleton {dimension : Nat}
    (cell : OmegacECell dimension) :
    (singleton cell).length = 1 := rfl

/-- Concatenating scaffold words adds their lengths. -/
theorem length_append {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    (append firstWord secondWord).length =
      firstWord.length + secondWord.length := by
  cases firstWord with
  | mk firstCells =>
      cases secondWord with
      | mk secondCells =>
          exact OmegacECell.length_append firstCells secondCells

/-- Suspension preserves scaffold-word length. -/
theorem length_suspend {dimension : Nat}
    (word : OmegacEWord dimension) :
    word.suspend.length = word.length :=
  OmegacECell.length_suspendList word.cells

/-- Suspension distributes over scaffold-word append at the cell-list level. -/
theorem suspend_append_cells {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    (append firstWord secondWord).suspend.cells =
      (append firstWord.suspend secondWord.suspend).cells := by
  dsimp only [append, suspend]
  exact OmegacECell.suspendList_append firstWord.cells secondWord.cells

/-- Suspension preserves numeric slot values pointwise. -/
theorem slotValues_suspend {dimension : Nat}
    (word : OmegacEWord dimension) :
    word.suspend.slotValues = word.slotValues :=
  OmegacECell.slotValuesOfList_suspendList word.cells

/-- Suspension preserves numeric declared-index values pointwise. -/
theorem declaredIndexValues_suspend {dimension : Nat}
    (word : OmegacEWord dimension) :
    word.suspend.declaredIndexValues = word.declaredIndexValues :=
  OmegacECell.declaredIndexValuesOfList_suspendList word.cells

end OmegacEWord

end LeanFX2.Foundation.PolyCell.OmegacE
