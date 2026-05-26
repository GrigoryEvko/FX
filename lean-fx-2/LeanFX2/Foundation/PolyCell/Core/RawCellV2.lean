import LeanFX2.Foundation.PolyCell.Core.RawTermV2

/-! # Foundation/PolyCell/Core/RawCellV2 — the v2 un-indexed cell layer

Scope-indexed ONLY; dimension is COMPUTED by `RawCellV2.dim`, never a
type index.  This dissolves the entire propext-leak class fought through
TCB.7/TCB.8 (the dual `(dim, rawCell)` match, the partial ctor enum at
`dim+1`).  A dim-mismatched verticalComposite is representable (and
rejected by the certifier) rather than unconstructable. -/

namespace LeanFX2.Foundation.PolyCell.Core

inductive RawCellV2 : Nat → Type where
  | termBase :
      {scope : Nat} → RawTermV2 scope → RawCellV2 scope
  | generatingCell :
      {scope : Nat} → (ruleId : Nat) →
      RawCellV2 scope → RawCellV2 scope → RawCellV2 scope
  | verticalComposite :
      {scope : Nat} → RawCellV2 scope → RawCellV2 scope → RawCellV2 scope
  | horizontalComposite :
      {scope : Nat} → RawCellV2 scope → RawCellV2 scope → RawCellV2 scope
  | identityCell :
      {scope : Nat} → RawCellV2 scope → RawCellV2 scope

/-- Dimension recovered structurally.  Matches the cell ALONE (the
propext-clean retargetProfile shape).  Total, structural recursion,
no `termination_by`. -/
@[reducible] def RawCellV2.dim {scope : Nat} : RawCellV2 scope → Nat
  | .termBase _                 => 0
  | .generatingCell _ source _  => source.dim + 1
  | .verticalComposite first _  => first.dim
  | .horizontalComposite left _ => left.dim
  | .identityCell base          => base.dim + 1

end LeanFX2.Foundation.PolyCell.Core
