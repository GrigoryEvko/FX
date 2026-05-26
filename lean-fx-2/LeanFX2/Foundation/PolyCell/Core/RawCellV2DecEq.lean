import LeanFX2.Foundation.PolyCell.Core.RawTermV2DecEq

/-! # Foundation/PolyCell/Core/RawCellV2DecEq — propext-free DecidableEq

Well-founded on RawCellV2.size. Core Nat lemmas for decreasing_by,
never omega. -/

namespace LeanFX2.Foundation.PolyCell.Core

def RawCellV2.decEq {scope : Nat}
    (left right : RawCellV2 scope) : Decidable (left = right) :=
  match left, right with
  | .termBase termA, .termBase termB =>
    match RawTermV2.decEq termA termB with
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
      exact match RawCellV2.decEq srcA srcB with
      | .isTrue srcEq => by
        subst srcEq
        exact match RawCellV2.decEq tgtA tgtB with
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
    match RawCellV2.decEq fstA fstB with
    | .isTrue fstEq => by
      subst fstEq
      exact match RawCellV2.decEq sndA sndB with
      | .isTrue sndEq => .isTrue (by subst sndEq; rfl)
      | .isFalse sndNeq => .isFalse (by intro h; cases h; exact sndNeq rfl)
    | .isFalse fstNeq => .isFalse (by intro h; cases h; exact fstNeq rfl)
  | .verticalComposite _ _, .horizontalComposite _ _ => .isFalse (by intro h; cases h)
  | .verticalComposite _ _, .identityCell _ => .isFalse (by intro h; cases h)
  | .horizontalComposite _ _, .termBase _ => .isFalse (by intro h; cases h)
  | .horizontalComposite _ _, .generatingCell _ _ _ => .isFalse (by intro h; cases h)
  | .horizontalComposite _ _, .verticalComposite _ _ => .isFalse (by intro h; cases h)
  | .horizontalComposite leftA rightA, .horizontalComposite leftB rightB =>
    match RawCellV2.decEq leftA leftB with
    | .isTrue leftEq => by
      subst leftEq
      exact match RawCellV2.decEq rightA rightB with
      | .isTrue rightEq => .isTrue (by subst rightEq; rfl)
      | .isFalse rightNeq => .isFalse (by intro h; cases h; exact rightNeq rfl)
    | .isFalse leftNeq => .isFalse (by intro h; cases h; exact leftNeq rfl)
  | .horizontalComposite _ _, .identityCell _ => .isFalse (by intro h; cases h)
  | .identityCell _, .termBase _ => .isFalse (by intro h; cases h)
  | .identityCell _, .generatingCell _ _ _ => .isFalse (by intro h; cases h)
  | .identityCell _, .verticalComposite _ _ => .isFalse (by intro h; cases h)
  | .identityCell _, .horizontalComposite _ _ => .isFalse (by intro h; cases h)
  | .identityCell baseA, .identityCell baseB =>
    match RawCellV2.decEq baseA baseB with
    | .isTrue baseEq => .isTrue (by subst baseEq; rfl)
    | .isFalse baseNeq => .isFalse (by intro h; cases h; exact baseNeq rfl)
termination_by left.size
decreasing_by all_goals (
  first
  | exact RawCellV2.size_lt_termBase _
  | exact RawCellV2.size_lt_generatingCell_source _ _ _
  | exact RawCellV2.size_lt_generatingCell_target _ _ _
  | exact RawCellV2.size_lt_verticalComposite_first _ _
  | exact RawCellV2.size_lt_verticalComposite_second _ _
  | exact RawCellV2.size_lt_horizontalComposite_left _ _
  | exact RawCellV2.size_lt_horizontalComposite_right _ _
  | exact RawCellV2.size_lt_identityCell _)

instance instDecidableEqRawCellV2 {scope : Nat}
    : DecidableEq (RawCellV2 scope) := RawCellV2.decEq

end LeanFX2.Foundation.PolyCell.Core
