import FX1Poly.Core.RawSize

/-! # Foundation/PolyCell/Core/RawTermDecEq — propext-free DecidableEq -/

namespace FX1Poly.Core

-- Payload equality decided per-generator (Fin/Nat/Unit all have decEq)
def decEqPayload (generator : Generator) (scope : Nat)
    (payloadA payloadB : generator.payload scope) : Decidable (payloadA = payloadB) := by
  cases generator <;> (
    first
    | exact instDecidableEqFin _ payloadA payloadB  -- gen_var → Fin scope
    | exact Nat.decEq payloadA payloadB             -- gen_universeCode → Nat
    | exact match payloadA, payloadB with | (), () => .isTrue rfl)  -- all others → Unit

mutual
  def RawTerm.decEq {scope : Nat}
      : (left right : RawTerm scope) → Decidable (left = right)
    | .mkGen genA payA childrenA, .mkGen genB payB childrenB =>
      if genEqual : genA = genB then by
        subst genEqual
        exact match decEqPayload genA scope payA payB with
        | .isTrue payEqual => by
          subst payEqual
          exact match RawTermChildren.decEq childrenA childrenB with
          | .isTrue childEq => .isTrue (by subst childEq; rfl)
          | .isFalse childNeq => .isFalse (by intro h; cases h; exact childNeq rfl)
        | .isFalse payNeq => .isFalse (by intro h; cases h; exact payNeq rfl)
      else
        .isFalse (by intro h; cases h; exact genEqual rfl)

  def RawTermChildren.decEq {shifts : List Nat} {scope : Nat}
      : (left right : RawTermChildren shifts scope) → Decidable (left = right)
    | .childNil, .childNil => .isTrue rfl
    | .childCons headA tailA, .childCons headB tailB =>
      match RawTerm.decEq headA headB with
      | .isTrue headEq => by
        subst headEq
        exact match RawTermChildren.decEq tailA tailB with
        | .isTrue tailEq => .isTrue (by subst tailEq; rfl)
        | .isFalse tailNeq => .isFalse (by intro h; cases h; exact tailNeq rfl)
      | .isFalse headNeq => .isFalse (by intro h; cases h; exact headNeq rfl)
end

instance instDecidableEqRawTerm {scope : Nat}
    : DecidableEq (RawTerm scope) := RawTerm.decEq

instance instDecidableEqRawTermChildren {shifts : List Nat} {scope : Nat}
    : DecidableEq (RawTermChildren shifts scope) := RawTermChildren.decEq

end FX1Poly.Core
