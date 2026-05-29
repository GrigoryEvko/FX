import FX1Poly.Core.RawTerm

/-! # Foundation/PolyCell/Core/RawCell — the v2 un-indexed cell layer

Scope-indexed ONLY; dimension is COMPUTED by `RawCell.dim`, never a
type index.  This dissolves the entire propext-leak class fought through
TCB.7/TCB.8 (the dual `(dim, rawCell)` match, the partial ctor enum at
`dim+1`).  A dim-mismatched verticalComposite is representable (and
rejected by the certifier) rather than unconstructable. -/

namespace FX1Poly.Core

inductive RawCell : Nat → Type where
  | termBase :
      {scope : Nat} → RawTerm scope → RawCell scope
  | generatingCell :
      {scope : Nat} → (ruleId : Nat) →
      RawCell scope → RawCell scope → RawCell scope
  | verticalComposite :
      {scope : Nat} → RawCell scope → RawCell scope → RawCell scope
  | horizontalComposite :
      {scope : Nat} → RawCell scope → RawCell scope → RawCell scope
  | identityCell :
      {scope : Nat} → RawCell scope → RawCell scope

/-- Dimension recovered structurally.  Matches the cell ALONE (the
propext-clean retargetProfile shape).  Total, structural recursion,
no `termination_by`. -/
@[reducible] def RawCell.dim {scope : Nat} : RawCell scope → Nat
  | .termBase _                 => 0
  | .generatingCell _ source _  => source.dim + 1
  | .verticalComposite first _  => first.dim
  | .horizontalComposite left _ => left.dim
  | .identityCell base          => base.dim + 1

end FX1Poly.Core
