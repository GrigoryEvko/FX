import FX1Poly.Core.RawTermDecEq

/-! # Foundation/PolyCell/Core/RawCellDecEq — propext-free DecidableEq

Well-founded on RawCell.size. Core Nat lemmas for decreasing_by,
never omega. -/

namespace FX1Poly.Core

def RawCell.decEq {scope : Nat}
    (left right : RawCell scope) : Decidable (left = right) :=
  match left, right with
  | .termBase termA, .termBase termB =>
    match RawTerm.decEq termA termB with
    | .isTrue h => .isTrue (by subst h; rfl)
    | .isFalse h => .isFalse (by intro heq; cases heq; exact h rfl)
  | .termBase _, .generatingCell _ _ _ => .isFalse (by intro h; cases h)
  | .termBase _, .verticalComposite _ _ => .isFalse (by intro h; cases h)
  | .termBase _, .horizontalComposite _ _ => .isFalse (by intro h; cases h)
  | .termBase _, .identityCell _ => .isFalse (by intro h; cases h)
  | .generatingCell _ _ _, .termBase _ => .isFalse (by intro h; cases h)
  | .generatingCell ruleA srcA tgtA, .generatingCell ruleB srcB tgtB =>
    if ruleEq : ruleA = ruleB then by
      subst ruleEq
      exact match RawCell.decEq srcA srcB with
      | .isTrue srcEq => by
        subst srcEq
        exact match RawCell.decEq tgtA tgtB with
        | .isTrue tgtEq => .isTrue (by subst tgtEq; rfl)
        | .isFalse tgtNeq => .isFalse (by intro h; cases h; exact tgtNeq rfl)
      | .isFalse srcNeq => .isFalse (by intro h; cases h; exact srcNeq rfl)
    else .isFalse (by intro h; cases h; exact ruleEq rfl)
  | .generatingCell _ _ _, .verticalComposite _ _ => .isFalse (by intro h; cases h)
  | .generatingCell _ _ _, .horizontalComposite _ _ => .isFalse (by intro h; cases h)
  | .generatingCell _ _ _, .identityCell _ => .isFalse (by intro h; cases h)
  | .verticalComposite _ _, .termBase _ => .isFalse (by intro h; cases h)
  | .verticalComposite _ _, .generatingCell _ _ _ => .isFalse (by intro h; cases h)
  | .verticalComposite fstA sndA, .verticalComposite fstB sndB =>
    match RawCell.decEq fstA fstB with
    | .isTrue fstEq => by
      subst fstEq
      exact match RawCell.decEq sndA sndB with
      | .isTrue sndEq => .isTrue (by subst sndEq; rfl)
      | .isFalse sndNeq => .isFalse (by intro h; cases h; exact sndNeq rfl)
    | .isFalse fstNeq => .isFalse (by intro h; cases h; exact fstNeq rfl)
  | .verticalComposite _ _, .horizontalComposite _ _ => .isFalse (by intro h; cases h)
  | .verticalComposite _ _, .identityCell _ => .isFalse (by intro h; cases h)
  | .horizontalComposite _ _, .termBase _ => .isFalse (by intro h; cases h)
  | .horizontalComposite _ _, .generatingCell _ _ _ => .isFalse (by intro h; cases h)
  | .horizontalComposite _ _, .verticalComposite _ _ => .isFalse (by intro h; cases h)
  | .horizontalComposite leftA rightA, .horizontalComposite leftB rightB =>
    match RawCell.decEq leftA leftB with
    | .isTrue leftEq => by
      subst leftEq
      exact match RawCell.decEq rightA rightB with
      | .isTrue rightEq => .isTrue (by subst rightEq; rfl)
      | .isFalse rightNeq => .isFalse (by intro h; cases h; exact rightNeq rfl)
    | .isFalse leftNeq => .isFalse (by intro h; cases h; exact leftNeq rfl)
  | .horizontalComposite _ _, .identityCell _ => .isFalse (by intro h; cases h)
  | .identityCell _, .termBase _ => .isFalse (by intro h; cases h)
  | .identityCell _, .generatingCell _ _ _ => .isFalse (by intro h; cases h)
  | .identityCell _, .verticalComposite _ _ => .isFalse (by intro h; cases h)
  | .identityCell _, .horizontalComposite _ _ => .isFalse (by intro h; cases h)
  | .identityCell baseA, .identityCell baseB =>
    match RawCell.decEq baseA baseB with
    | .isTrue baseEq => .isTrue (by subst baseEq; rfl)
    | .isFalse baseNeq => .isFalse (by intro h; cases h; exact baseNeq rfl)
termination_by left.size
decreasing_by all_goals (
  first
  | exact RawCell.size_lt_termBase _
  | exact RawCell.size_lt_generatingCell_source _ _ _
  | exact RawCell.size_lt_generatingCell_target _ _ _
  | exact RawCell.size_lt_verticalComposite_first _ _
  | exact RawCell.size_lt_verticalComposite_second _ _
  | exact RawCell.size_lt_horizontalComposite_left _ _
  | exact RawCell.size_lt_horizontalComposite_right _ _
  | exact RawCell.size_lt_identityCell _)

instance instDecidableEqRawCell {scope : Nat}
    : DecidableEq (RawCell scope) := RawCell.decEq

end FX1Poly.Core
