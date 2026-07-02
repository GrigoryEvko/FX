/-! # FX1Poly/ComputerAlgebra/Number/IntSubNatNat — the subNatNat case-analysis kit
    (FLOAT-1 brick 2)

`Int.subNatNat` is the pivot of every mixed-sign `Int.add` arm, so the whole hand-rolled
associativity/distributivity/order corpus reduces to a small kit of `subNatNat` computation
lemmas.  Init's own versions are propext-dirty (omega/simp proofs), so this module rebuilds the
kit zero-axiom.

The technique is the BRIDGE FUNCTION: `subNatNatFromDifferences` restates `Int.subNatNat m n`
as a function of the two differences `n - m` and `m - n` — definitionally (`rfl`).  Every kit
lemma then becomes a term-mode `congrArg` over a clean Nat subtraction fact
(`Nat.succ_sub_succ`, `Nat.zero_sub`) plus structural recursion — no match-motive surgery, no
tactics, no rewriting under a `match`.

Kit contents:
  * `intSubNatNatSuccSucc` — the workhorse: both arguments shift down by one.
  * `intSubNatNatZeroRight` / `intSubNatNatZeroLeftSucc` — the two base rows.
  * `intSubNatNatShiftInvariant` — translation invariance (`+ shiftAmount` on both sides).
  * `intSubNatNatSelf` — `subNatNat n n = 0`.
  * `intSubNatNatLeftSurplus` / `intSubNatNatRightSurplus` — the two closed forms
    (`subNatNat (surplus + n) n = ofNat surplus`; `subNatNat n (n + d + 1) = negSucc d`)
    that the elimination principle and the associativity case-bash consume.
  * `intAddRightNeg` / `intAddLeftNeg` — the first payoff: additive inverse cancellation
    (Init's `Int.add_right_neg` / `Int.add_left_neg` are propext-dirty), each arm collapsing
    to `intSubNatNatSelf` definitionally.

## Zero-axiom

Definitional bridge + `congrArg`/`Eq.trans` chains over clean Nat lemmas + structural
recursion.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/Number/IntSubNatNat.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-- **The bridge function**: `Int.subNatNat m n` as a function of the two differences.
`subNatNatFromDifferences (n - m) (m - n)` is DEFINITIONALLY `Int.subNatNat m n` (see
`subNatNatAsDifferences`), which turns argument-rewriting into plain `congrArg`. -/
def subNatNatFromDifferences (negativeDifference positiveDifference : Nat) : Int :=
  match negativeDifference with
  | 0 => Int.ofNat positiveDifference
  | deficitPredecessor + 1 => Int.negSucc deficitPredecessor

/-- The bridge is definitional. -/
theorem subNatNatAsDifferences (leftValue rightValue : Nat) :
    Int.subNatNat leftValue rightValue =
      subNatNatFromDifferences (rightValue - leftValue) (leftValue - rightValue) := rfl

/-- **The workhorse**: shifting both arguments down by one leaves `subNatNat` fixed.  A single
two-place congruence over `Nat.succ_sub_succ` through the bridge. -/
theorem intSubNatNatSuccSucc (leftValue rightValue : Nat) :
    Int.subNatNat (leftValue + 1) (rightValue + 1) = Int.subNatNat leftValue rightValue :=
  show subNatNatFromDifferences ((rightValue + 1) - (leftValue + 1))
        ((leftValue + 1) - (rightValue + 1)) =
      subNatNatFromDifferences (rightValue - leftValue) (leftValue - rightValue) from
    congr (congrArg subNatNatFromDifferences (Nat.succ_sub_succ rightValue leftValue))
      (Nat.succ_sub_succ leftValue rightValue)

/-- `subNatNat value 0 = ofNat value` — the nonnegative base row (`Nat.zero_sub` is clean). -/
theorem intSubNatNatZeroRight (value : Nat) : Int.subNatNat value 0 = Int.ofNat value :=
  congrArg (subNatNatFromDifferences · value) (Nat.zero_sub value)

/-- `subNatNat 0 (n+1) = negSucc n` — the negative base row, definitional. -/
theorem intSubNatNatZeroLeftSucc (value : Nat) :
    Int.subNatNat 0 (value + 1) = Int.negSucc value := rfl

/-- Translation invariance: adding the same shift to both arguments leaves `subNatNat`
fixed.  Structural recursion on the shift through `intSubNatNatSuccSucc`. -/
theorem intSubNatNatShiftInvariant (leftValue rightValue : Nat) : ∀ shiftAmount : Nat,
    Int.subNatNat (leftValue + shiftAmount) (rightValue + shiftAmount) =
      Int.subNatNat leftValue rightValue
  | 0 => rfl
  | shiftAmount + 1 =>
      (intSubNatNatSuccSucc (leftValue + shiftAmount) (rightValue + shiftAmount)).trans
        (intSubNatNatShiftInvariant leftValue rightValue shiftAmount)

/-- `subNatNat n n = 0` — the cancellation diagonal. -/
theorem intSubNatNatSelf : ∀ value : Nat, Int.subNatNat value value = 0
  | 0 => rfl
  | value + 1 => (intSubNatNatSuccSucc value value).trans (intSubNatNatSelf value)

/-- The nonnegative closed form: when the left argument exceeds the right by `surplus`, the
result is `ofNat surplus`. -/
theorem intSubNatNatLeftSurplus (surplus : Nat) : ∀ rightValue : Nat,
    Int.subNatNat (surplus + rightValue) rightValue = Int.ofNat surplus
  | 0 => intSubNatNatZeroRight surplus
  | rightValue + 1 =>
      (intSubNatNatSuccSucc (surplus + rightValue) rightValue).trans
        (intSubNatNatLeftSurplus surplus rightValue)

/-- The negative closed form: when the right argument exceeds the left by `deficit + 1`, the
result is `negSucc deficit`. -/
theorem intSubNatNatRightSurplus (deficit : Nat) : ∀ leftValue : Nat,
    Int.subNatNat leftValue (leftValue + (deficit + 1)) = Int.negSucc deficit
  | 0 => congrArg Int.negSucc (Nat.zero_add deficit)
  | leftValue + 1 =>
      (congrArg (Int.subNatNat (leftValue + 1))
          (congrArg Nat.succ (Nat.succ_add leftValue deficit))).trans
        ((intSubNatNatSuccSucc leftValue (leftValue + (deficit + 1))).trans
          (intSubNatNatRightSurplus deficit leftValue))

/-! ## First payoff: additive inverse cancellation

Both mixed-sign `Int.add` arms at `(value, -value)` compute definitionally to
`subNatNat (n+1) (n+1)`, so cancellation IS `intSubNatNatSelf`. -/

/-- `value + -value = 0` (Init's `Int.add_right_neg` is propext-dirty). -/
theorem intAddRightNeg : ∀ value : Int, value + -value = 0
  | .ofNat 0 => rfl
  | .ofNat (valuePredecessor + 1) => intSubNatNatSelf (valuePredecessor + 1)
  | .negSucc valuePredecessor => intSubNatNatSelf (valuePredecessor + 1)

/-- `-value + value = 0` (Init's `Int.add_left_neg` is propext-dirty). -/
theorem intAddLeftNeg : ∀ value : Int, -value + value = 0
  | .ofNat 0 => rfl
  | .ofNat (valuePredecessor + 1) => intSubNatNatSelf (valuePredecessor + 1)
  | .negSucc valuePredecessor => intSubNatNatSelf (valuePredecessor + 1)

end FX1Poly.ComputerAlgebra
