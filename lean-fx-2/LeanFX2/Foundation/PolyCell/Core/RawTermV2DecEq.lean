import LeanFX2.Foundation.PolyCell.Core.RawSizeV2

/-! # Foundation/PolyCell/Core/RawTermV2DecEq — propext-free DecidableEq -/

namespace LeanFX2.Foundation.PolyCell.Core

-- Payload equality decided per-generator (Fin/Nat/Unit all have decEq)
def decEqPayload (generator : Generator) (scope : Nat)
    (payloadA payloadB : generator.payload scope) : Decidable (payloadA = payloadB) := by
  cases generator <;> (
    first
    | exact instDecidableEqFin _ payloadA payloadB  -- gen_var → Fin scope
    | exact Nat.decEq payloadA payloadB             -- gen_universeCode → Nat
    | exact match payloadA, payloadB with | (), () => .isTrue rfl)  -- all others → Unit

mutual
  def RawTermV2.decEq {scope : Nat}
      : (left right : RawTermV2 scope) → Decidable (left = right)
    | .mkGen genA payA childrenA, .mkGen genB payB childrenB =>
      if genEqual : genA = genB then by
        subst genEqual
        exact match decEqPayload genA scope payA payB with
        | .isTrue payEqual => by
          subst payEqual
          exact match RawTermChildrenV2.decEq childrenA childrenB with
          | .isTrue childEq => .isTrue (by subst childEq; rfl)
          | .isFalse childNeq => .isFalse (by intro h; cases h; exact childNeq rfl)
        | .isFalse payNeq => .isFalse (by intro h; cases h; exact payNeq rfl)
      else
        .isFalse (by intro h; cases h; exact genEqual rfl)

  def RawTermChildrenV2.decEq {shifts : List Nat} {scope : Nat}
      : (left right : RawTermChildrenV2 shifts scope) → Decidable (left = right)
    | .childNil, .childNil => .isTrue rfl
    | .childCons headA tailA, .childCons headB tailB =>
      match RawTermV2.decEq headA headB with
      | .isTrue headEq => by
        subst headEq
        exact match RawTermChildrenV2.decEq tailA tailB with
        | .isTrue tailEq => .isTrue (by subst tailEq; rfl)
        | .isFalse tailNeq => .isFalse (by intro h; cases h; exact tailNeq rfl)
      | .isFalse headNeq => .isFalse (by intro h; cases h; exact headNeq rfl)
end

instance instDecidableEqRawTermV2 {scope : Nat}
    : DecidableEq (RawTermV2 scope) := RawTermV2.decEq

instance instDecidableEqRawTermChildrenV2 {shifts : List Nat} {scope : Nat}
    : DecidableEq (RawTermChildrenV2 shifts scope) := RawTermChildrenV2.decEq

end LeanFX2.Foundation.PolyCell.Core
