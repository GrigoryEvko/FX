import FX1Poly.Core.RawCell

/-! # Foundation/PolyCell/Core/RawSize — well-founded size measures

Size inequalities use core Nat lemmas, NEVER omega. -/

namespace FX1Poly.Core

mutual
  def RawTerm.size {scope : Nat} : RawTerm scope → Nat
    | .mkGen _ _ children => children.size + 1

  def RawTermChildren.size {shifts : List Nat} {scope : Nat}
      : RawTermChildren shifts scope → Nat
    | .childNil => 0
    | .childCons head tail => head.size + tail.size + 1
end

def RawCell.size {scope : Nat} : RawCell scope → Nat
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

-- RawCell size_lt lemmas
theorem RawCell.size_lt_termBase {scope : Nat} (term : RawTerm scope)
    : term.size < (RawCell.termBase term).size := ltSuccSelf _

theorem RawCell.size_lt_generatingCell_source {scope : Nat}
    (ruleId : Nat) (source target : RawCell scope)
    : source.size < (RawCell.generatingCell ruleId source target).size :=
  leftLtSumSucc _ _

theorem RawCell.size_lt_generatingCell_target {scope : Nat}
    (ruleId : Nat) (source target : RawCell scope)
    : target.size < (RawCell.generatingCell ruleId source target).size :=
  rightLtSumSucc _ _

theorem RawCell.size_lt_verticalComposite_first {scope : Nat}
    (first second : RawCell scope)
    : first.size < (RawCell.verticalComposite first second).size :=
  leftLtSumSucc _ _

theorem RawCell.size_lt_verticalComposite_second {scope : Nat}
    (first second : RawCell scope)
    : second.size < (RawCell.verticalComposite first second).size :=
  rightLtSumSucc _ _

theorem RawCell.size_lt_horizontalComposite_left {scope : Nat}
    (left right : RawCell scope)
    : left.size < (RawCell.horizontalComposite left right).size :=
  leftLtSumSucc _ _

theorem RawCell.size_lt_horizontalComposite_right {scope : Nat}
    (left right : RawCell scope)
    : right.size < (RawCell.horizontalComposite left right).size :=
  rightLtSumSucc _ _

theorem RawCell.size_lt_identityCell {scope : Nat} (base : RawCell scope)
    : base.size < (RawCell.identityCell base).size := ltSuccSelf _

-- RawTermChildren size_lt lemmas
theorem RawTermChildren.size_lt_childCons_head
    {scope shift : Nat} {restShifts : List Nat}
    (head : RawTerm (scope + shift)) (tail : RawTermChildren restShifts scope)
    : head.size < (RawTermChildren.childCons head tail).size :=
  leftLtSumSucc _ _

theorem RawTermChildren.size_lt_childCons_tail
    {scope shift : Nat} {restShifts : List Nat}
    (head : RawTerm (scope + shift)) (tail : RawTermChildren restShifts scope)
    : tail.size < (RawTermChildren.childCons head tail).size :=
  rightLtSumSucc _ _

end FX1Poly.Core
