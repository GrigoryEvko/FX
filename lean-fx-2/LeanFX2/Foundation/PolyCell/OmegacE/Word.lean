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

/-- Numeric slot projection distributes over scaffold-list append. -/
theorem OmegacECell.slotValuesOfList_append {dimension : Nat}
    (firstCells secondCells : List (OmegacECell dimension)) :
    OmegacECell.slotValuesOfList dimension (firstCells ++ secondCells) =
      OmegacECell.slotValuesOfList dimension firstCells ++
        OmegacECell.slotValuesOfList dimension secondCells := by
  induction firstCells with
  | nil =>
      change
        OmegacECell.slotValuesOfList dimension secondCells =
          OmegacECell.slotValuesOfList dimension secondCells
      rfl
  | cons cell remainingCells inductionHypothesis =>
      change
        OmegacECell.slotValueOf cell ::
            OmegacECell.slotValuesOfList dimension
              (remainingCells ++ secondCells) =
          OmegacECell.slotValueOf cell ::
            (OmegacECell.slotValuesOfList dimension remainingCells ++
              OmegacECell.slotValuesOfList dimension secondCells)
      exact congrArg (List.cons (OmegacECell.slotValueOf cell))
        inductionHypothesis

/-- Declared-index projection distributes over scaffold-list append. -/
theorem OmegacECell.declaredIndexValuesOfList_append {dimension : Nat}
    (firstCells secondCells : List (OmegacECell dimension)) :
    OmegacECell.declaredIndexValuesOfList dimension
        (firstCells ++ secondCells) =
      OmegacECell.declaredIndexValuesOfList dimension firstCells ++
        OmegacECell.declaredIndexValuesOfList dimension secondCells := by
  induction firstCells with
  | nil =>
      change
        OmegacECell.declaredIndexValuesOfList dimension secondCells =
          OmegacECell.declaredIndexValuesOfList dimension secondCells
      rfl
  | cons cell remainingCells inductionHypothesis =>
      change
        OmegacECell.declaredIndexValueOf cell ::
            OmegacECell.declaredIndexValuesOfList dimension
              (remainingCells ++ secondCells) =
          OmegacECell.declaredIndexValueOf cell ::
            (OmegacECell.declaredIndexValuesOfList dimension remainingCells ++
              OmegacECell.declaredIndexValuesOfList dimension secondCells)
      exact congrArg (List.cons (OmegacECell.declaredIndexValueOf cell))
        inductionHypothesis

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

/-- Select a scaffold generator from a raw numeric slot value.

The current scaffold has exactly two generator slots.  Raw code values are
normalized by interpreting zero as the first slot and every nonzero value as
the second slot. -/
def OmegacECell.atSlotValue (dimension : Nat) (slotValue : Nat) :
    OmegacECell dimension :=
  if slotValue == 0 then
    OmegacECell.firstAtDim dimension
  else
    OmegacECell.secondAtDim dimension

/-- Normalize a raw numeric slot value to the two-slot scaffold code. -/
def OmegacECell.normalizeSlotValue (slotValue : Nat) : Nat :=
  if slotValue == 0 then
    0
  else
    1

/-- Decode a list of raw slot values into scaffold generators. -/
def OmegacECell.cellsOfSlotValues (dimension : Nat) :
    List Nat → List (OmegacECell dimension)
  | [] => []
  | slotValue :: remainingSlotValues =>
      OmegacECell.atSlotValue dimension slotValue ::
        OmegacECell.cellsOfSlotValues dimension remainingSlotValues

/-- Normalize a list of raw slot values to canonical two-slot codes. -/
def OmegacECell.normalizeSlotValues : List Nat → List Nat
  | [] => []
  | slotValue :: remainingSlotValues =>
      OmegacECell.normalizeSlotValue slotValue ::
        OmegacECell.normalizeSlotValues remainingSlotValues

/-- Decoding a raw zero slot gives the first scaffold generator. -/
theorem OmegacECell.atSlotValue_zero (dimension : Nat) :
    OmegacECell.atSlotValue dimension 0 =
      OmegacECell.firstAtDim dimension := rfl

/-- Decoding raw slot one gives the second scaffold generator. -/
theorem OmegacECell.atSlotValue_one (dimension : Nat) :
    OmegacECell.atSlotValue dimension 1 =
      OmegacECell.secondAtDim dimension := rfl

/-- Raw zero normalizes to the canonical zero slot code. -/
theorem OmegacECell.normalizeSlotValue_zero :
    OmegacECell.normalizeSlotValue 0 = 0 := rfl

/-- Raw one normalizes to the canonical one slot code. -/
theorem OmegacECell.normalizeSlotValue_one :
    OmegacECell.normalizeSlotValue 1 = 1 := rfl

/-- Slot-value normalization is idempotent. -/
theorem OmegacECell.normalizeSlotValue_idempotent (slotValue : Nat) :
    OmegacECell.normalizeSlotValue
        (OmegacECell.normalizeSlotValue slotValue) =
      OmegacECell.normalizeSlotValue slotValue := by
  cases slotValue with
  | zero => rfl
  | succ _ => rfl

/-- Reading back a generator decoded from a raw slot returns the normalized
numeric code. -/
theorem OmegacECell.slotValueOf_atSlotValue (dimension : Nat)
    (slotValue : Nat) :
    OmegacECell.slotValueOf
        (OmegacECell.atSlotValue dimension slotValue) =
      OmegacECell.normalizeSlotValue slotValue := by
  cases slotValue with
  | zero =>
      exact OmegacECell.slotValueOf_firstAtDim dimension
  | succ slotTail =>
      change
        OmegacECell.slotValueOf
            (OmegacECell.secondAtDim dimension) = 1
      exact OmegacECell.slotValueOf_secondAtDim dimension

/-- Decoding preserves list length. -/
theorem OmegacECell.length_cellsOfSlotValues (dimension : Nat)
    (slotValues : List Nat) :
    (OmegacECell.cellsOfSlotValues dimension slotValues).length =
      slotValues.length := by
  induction slotValues with
  | nil => rfl
  | cons slotValue remainingSlotValues inductionHypothesis =>
      dsimp only [OmegacECell.cellsOfSlotValues, List.length]
      rw [inductionHypothesis]

/-- Normalization preserves list length. -/
theorem OmegacECell.length_normalizeSlotValues
    (slotValues : List Nat) :
    (OmegacECell.normalizeSlotValues slotValues).length =
      slotValues.length := by
  induction slotValues with
  | nil => rfl
  | cons slotValue remainingSlotValues inductionHypothesis =>
      dsimp only [OmegacECell.normalizeSlotValues, List.length]
      rw [inductionHypothesis]

/-- Decoding raw slot lists distributes over append. -/
theorem OmegacECell.cellsOfSlotValues_append (dimension : Nat)
    (firstSlotValues secondSlotValues : List Nat) :
    OmegacECell.cellsOfSlotValues dimension
        (firstSlotValues ++ secondSlotValues) =
      OmegacECell.cellsOfSlotValues dimension firstSlotValues ++
        OmegacECell.cellsOfSlotValues dimension secondSlotValues := by
  induction firstSlotValues with
  | nil =>
      change
        OmegacECell.cellsOfSlotValues dimension secondSlotValues =
          OmegacECell.cellsOfSlotValues dimension secondSlotValues
      rfl
  | cons slotValue remainingSlotValues inductionHypothesis =>
      change
        OmegacECell.atSlotValue dimension slotValue ::
            OmegacECell.cellsOfSlotValues dimension
              (remainingSlotValues ++ secondSlotValues) =
          OmegacECell.atSlotValue dimension slotValue ::
            (OmegacECell.cellsOfSlotValues dimension remainingSlotValues ++
              OmegacECell.cellsOfSlotValues dimension secondSlotValues)
      exact congrArg (List.cons (OmegacECell.atSlotValue dimension slotValue))
        inductionHypothesis

/-- Slot-list normalization distributes over append. -/
theorem OmegacECell.normalizeSlotValues_append
    (firstSlotValues secondSlotValues : List Nat) :
    OmegacECell.normalizeSlotValues (firstSlotValues ++ secondSlotValues) =
      OmegacECell.normalizeSlotValues firstSlotValues ++
        OmegacECell.normalizeSlotValues secondSlotValues := by
  induction firstSlotValues with
  | nil =>
      change
        OmegacECell.normalizeSlotValues secondSlotValues =
          OmegacECell.normalizeSlotValues secondSlotValues
      rfl
  | cons slotValue remainingSlotValues inductionHypothesis =>
      change
        OmegacECell.normalizeSlotValue slotValue ::
            OmegacECell.normalizeSlotValues
              (remainingSlotValues ++ secondSlotValues) =
          OmegacECell.normalizeSlotValue slotValue ::
            (OmegacECell.normalizeSlotValues remainingSlotValues ++
              OmegacECell.normalizeSlotValues secondSlotValues)
      exact congrArg (List.cons (OmegacECell.normalizeSlotValue slotValue))
        inductionHypothesis

/-- Slot-list normalization is idempotent. -/
theorem OmegacECell.normalizeSlotValues_idempotent
    (slotValues : List Nat) :
    OmegacECell.normalizeSlotValues
        (OmegacECell.normalizeSlotValues slotValues) =
      OmegacECell.normalizeSlotValues slotValues := by
  induction slotValues with
  | nil => rfl
  | cons slotValue remainingSlotValues inductionHypothesis =>
      dsimp only [OmegacECell.normalizeSlotValues]
      rw [OmegacECell.normalizeSlotValue_idempotent slotValue,
        inductionHypothesis]

/-- Reading back decoded raw slots returns the normalized raw slot list. -/
theorem OmegacECell.slotValuesOfList_cellsOfSlotValues
    (dimension : Nat) (slotValues : List Nat) :
    OmegacECell.slotValuesOfList dimension
        (OmegacECell.cellsOfSlotValues dimension slotValues) =
      OmegacECell.normalizeSlotValues slotValues := by
  induction slotValues with
  | nil => rfl
  | cons slotValue remainingSlotValues inductionHypothesis =>
      dsimp only [OmegacECell.cellsOfSlotValues,
        OmegacECell.slotValuesOfList, OmegacECell.normalizeSlotValues]
      rw [OmegacECell.slotValueOf_atSlotValue dimension slotValue,
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

/-- Numeric slot projection distributes over scaffold-word append. -/
theorem slotValues_append {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    (append firstWord secondWord).slotValues =
      firstWord.slotValues ++ secondWord.slotValues := by
  cases firstWord with
  | mk firstCells =>
      cases secondWord with
      | mk secondCells =>
          exact OmegacECell.slotValuesOfList_append firstCells secondCells

/-- Numeric declared-index projection distributes over scaffold-word append. -/
theorem declaredIndexValues_append {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    (append firstWord secondWord).declaredIndexValues =
      firstWord.declaredIndexValues ++ secondWord.declaredIndexValues := by
  cases firstWord with
  | mk firstCells =>
      cases secondWord with
      | mk secondCells =>
          exact OmegacECell.declaredIndexValuesOfList_append
            firstCells secondCells

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

/-- Dimension-independent numeric code for scaffold words.

This is a serialization scaffold, not Makkai word equality.  It remembers only
the two declared generator slots of the current omega-cE scaffold. -/
structure OmegacEWordCode where
  /-- Raw numeric slot values.  Values are normalized by `normalize`. -/
  slotValues : List Nat
  deriving DecidableEq, Repr

namespace OmegacEWordCode

/-- Empty word code. -/
def empty : OmegacEWordCode where
  slotValues := []

/-- One raw-slot word code. -/
def singleton (slotValue : Nat) : OmegacEWordCode where
  slotValues := [slotValue]

/-- Append two word codes. -/
def append (firstCode secondCode : OmegacEWordCode) :
    OmegacEWordCode where
  slotValues := firstCode.slotValues ++ secondCode.slotValues

/-- Word-code length. -/
def length (code : OmegacEWordCode) : Nat :=
  code.slotValues.length

/-- Normalize raw numeric slots into canonical two-slot codes. -/
def normalize (code : OmegacEWordCode) : OmegacEWordCode where
  slotValues := OmegacECell.normalizeSlotValues code.slotValues

/-- Decode a word code at a chosen dimension. -/
def toWord (dimension : Nat) (code : OmegacEWordCode) :
    OmegacEWord dimension where
  cells := OmegacECell.cellsOfSlotValues dimension code.slotValues

/-- Encode a scaffold word by recording its numeric slot values. -/
def ofWord {dimension : Nat} (word : OmegacEWord dimension) :
    OmegacEWordCode where
  slotValues := word.slotValues

/-- The empty word code has length zero. -/
theorem length_empty : empty.length = 0 := rfl

/-- A singleton word code has length one. -/
theorem length_singleton (slotValue : Nat) :
    (singleton slotValue).length = 1 := rfl

/-- Appending word codes adds their lengths. -/
theorem length_append (firstCode secondCode : OmegacEWordCode) :
    (append firstCode secondCode).length =
      firstCode.length + secondCode.length := by
  cases firstCode with
  | mk firstSlotValues =>
      cases secondCode with
      | mk secondSlotValues =>
          induction firstSlotValues with
          | nil =>
              change secondSlotValues.length = 0 + secondSlotValues.length
              rw [Nat.zero_add]
          | cons slotValue remainingSlotValues inductionHypothesis =>
              change
                (remainingSlotValues ++ secondSlotValues).length =
                  remainingSlotValues.length + secondSlotValues.length
                at inductionHypothesis
              change
                Nat.succ ((remainingSlotValues ++ secondSlotValues).length) =
                  Nat.succ remainingSlotValues.length +
                    secondSlotValues.length
              rw [inductionHypothesis, Nat.succ_add]

/-- Normalization preserves word-code length. -/
theorem length_normalize (code : OmegacEWordCode) :
    code.normalize.length = code.length := by
  cases code with
  | mk slotValues =>
      exact OmegacECell.length_normalizeSlotValues slotValues

/-- Normalization distributes over word-code append. -/
theorem normalize_append (firstCode secondCode : OmegacEWordCode) :
    (append firstCode secondCode).normalize =
      append firstCode.normalize secondCode.normalize := by
  cases firstCode with
  | mk firstSlotValues =>
      cases secondCode with
      | mk secondSlotValues =>
          exact congrArg OmegacEWordCode.mk
            (OmegacECell.normalizeSlotValues_append
              firstSlotValues secondSlotValues)

/-- Word-code normalization is idempotent. -/
theorem normalize_idempotent (code : OmegacEWordCode) :
    code.normalize.normalize = code.normalize := by
  cases code with
  | mk slotValues =>
      exact congrArg OmegacEWordCode.mk
        (OmegacECell.normalizeSlotValues_idempotent slotValues)

/-- Decoding preserves word-code length. -/
theorem length_toWord (dimension : Nat) (code : OmegacEWordCode) :
    (code.toWord dimension).length = code.length := by
  cases code with
  | mk slotValues =>
      exact OmegacECell.length_cellsOfSlotValues dimension slotValues

/-- Decoding word-code append is scaffold-word append. -/
theorem toWord_append (dimension : Nat)
    (firstCode secondCode : OmegacEWordCode) :
    (append firstCode secondCode).toWord dimension =
      OmegacEWord.append (firstCode.toWord dimension)
        (secondCode.toWord dimension) := by
  cases firstCode with
  | mk firstSlotValues =>
      cases secondCode with
      | mk secondSlotValues =>
          exact congrArg OmegacEWord.mk
            (OmegacECell.cellsOfSlotValues_append dimension
              firstSlotValues secondSlotValues)

/-- Encoding a decoded word yields the normalized word code. -/
theorem ofWord_toWord (dimension : Nat) (code : OmegacEWordCode) :
    ofWord (code.toWord dimension) = code.normalize := by
  cases code with
  | mk slotValues =>
      dsimp only [ofWord, toWord, OmegacEWord.slotValues, normalize]
      exact congrArg OmegacEWordCode.mk
        (OmegacECell.slotValuesOfList_cellsOfSlotValues dimension slotValues)

/-- Encoding scaffold-word append is word-code append. -/
theorem ofWord_append {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    ofWord (OmegacEWord.append firstWord secondWord) =
      append (ofWord firstWord) (ofWord secondWord) := by
  cases firstWord with
  | mk firstCells =>
      cases secondWord with
      | mk secondCells =>
          exact congrArg OmegacEWordCode.mk
            (OmegacECell.slotValuesOfList_append firstCells secondCells)

/-- Encoding a suspended scaffold word preserves its code. -/
theorem ofWord_suspend {dimension : Nat}
    (word : OmegacEWord dimension) :
    ofWord word.suspend = ofWord word := by
  cases word with
  | mk cells =>
      exact congrArg OmegacEWordCode.mk
        (OmegacEWord.slotValues_suspend { cells := cells })

end OmegacEWordCode

end LeanFX2.Foundation.PolyCell.OmegacE
