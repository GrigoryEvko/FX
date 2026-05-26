import LeanFX2.Foundation.PolyCell.Core.RawCellV2

/-! # Foundation/PolyCell/Core/RawSizeV2 — well-founded size measures

Size inequalities use core Nat lemmas, NEVER omega. -/

namespace LeanFX2.Foundation.PolyCell.Core

mutual
  def RawTermV2.size {scope : Nat} : RawTermV2 scope → Nat
    | .mkGen _ _ children => children.size + 1

  def RawTermChildrenV2.size {shifts : List Nat} {scope : Nat}
      : RawTermChildrenV2 shifts scope → Nat
    | .childNil => 0
    | .childCons head tail => head.size + tail.size + 1
end

def RawCellV2.size {scope : Nat} : RawCellV2 scope → Nat
  | .termBase term => term.size + 1
  | .generatingCell _ source target => source.size + target.size + 1
  | .verticalComposite first second => first.size + second.size + 1
  | .horizontalComposite left right => left.size + right.size + 1
  | .identityCell base => base.size + 1

-- a < a + b + 1
private theorem leftLtSumSucc (leftVal rightVal : Nat)
    : leftVal < leftVal + rightVal + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_right leftVal rightVal)

-- b < a + b + 1
private theorem rightLtSumSucc (leftVal rightVal : Nat)
    : rightVal < leftVal + rightVal + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_left rightVal leftVal)

-- a < a + 1
private theorem ltSuccSelf (val : Nat) : val < val + 1 := Nat.lt_succ_self val

-- RawCellV2 size_lt lemmas
theorem RawCellV2.size_lt_termBase {scope : Nat} (term : RawTermV2 scope)
    : term.size < (RawCellV2.termBase term).size := ltSuccSelf _

theorem RawCellV2.size_lt_generatingCell_source {scope : Nat}
    (ruleId : Nat) (source target : RawCellV2 scope)
    : source.size < (RawCellV2.generatingCell ruleId source target).size :=
  leftLtSumSucc _ _

theorem RawCellV2.size_lt_generatingCell_target {scope : Nat}
    (ruleId : Nat) (source target : RawCellV2 scope)
    : target.size < (RawCellV2.generatingCell ruleId source target).size :=
  rightLtSumSucc _ _

theorem RawCellV2.size_lt_verticalComposite_first {scope : Nat}
    (first second : RawCellV2 scope)
    : first.size < (RawCellV2.verticalComposite first second).size :=
  leftLtSumSucc _ _

theorem RawCellV2.size_lt_verticalComposite_second {scope : Nat}
    (first second : RawCellV2 scope)
    : second.size < (RawCellV2.verticalComposite first second).size :=
  rightLtSumSucc _ _

theorem RawCellV2.size_lt_horizontalComposite_left {scope : Nat}
    (left right : RawCellV2 scope)
    : left.size < (RawCellV2.horizontalComposite left right).size :=
  leftLtSumSucc _ _

theorem RawCellV2.size_lt_horizontalComposite_right {scope : Nat}
    (left right : RawCellV2 scope)
    : right.size < (RawCellV2.horizontalComposite left right).size :=
  rightLtSumSucc _ _

theorem RawCellV2.size_lt_identityCell {scope : Nat} (base : RawCellV2 scope)
    : base.size < (RawCellV2.identityCell base).size := ltSuccSelf _

-- RawTermChildrenV2 size_lt lemmas
theorem RawTermChildrenV2.size_lt_childCons_head
    {scope shift : Nat} {restShifts : List Nat}
    (head : RawTermV2 (scope + shift)) (tail : RawTermChildrenV2 restShifts scope)
    : head.size < (RawTermChildrenV2.childCons head tail).size :=
  leftLtSumSucc _ _

theorem RawTermChildrenV2.size_lt_childCons_tail
    {scope shift : Nat} {restShifts : List Nat}
    (head : RawTermV2 (scope + shift)) (tail : RawTermChildrenV2 restShifts scope)
    : tail.size < (RawTermChildrenV2.childCons head tail).size :=
  rightLtSumSucc _ _

end LeanFX2.Foundation.PolyCell.Core
