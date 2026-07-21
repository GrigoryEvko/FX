/-! # FixedWidth/OverflowMode — the dim-16 overflow-mode preorder

FX §6.3 dim 16 makes the overflow dimension a four-element set
`{exact, wrap, trap, saturate}` ordered as a bounded-below preorder: `exact` is
the bottom (`exact ≤ everything`), and `wrap`, `trap`, `saturate` are pairwise
incomparable.  This is a lattice fragment, distinct from the arithmetic each mode
selects (that lives on `BitVec`, `OverflowArithmetic`).

The order is a `Bool` program (`overflowLe`) — fully enumerated, no wildcard, so
no `propext` leaks — with the three preorder facts (reflexive, `exact` is least,
transitive) proved by finite case analysis.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- The four overflow modes (FX §6.3 dim 16). -/
inductive OverflowMode
  | exact
  | wrap
  | trap
  | saturate

/-- The mode preorder as a `Bool` program.  Fully enumerated (16 arms):
reflexive on the diagonal, `exact` below everything, all other off-diagonal
pairs incomparable (`false`). -/
def overflowLe : OverflowMode → OverflowMode → Bool
  | .exact, .exact => true
  | .exact, .wrap => true
  | .exact, .trap => true
  | .exact, .saturate => true
  | .wrap, .exact => false
  | .wrap, .wrap => true
  | .wrap, .trap => false
  | .wrap, .saturate => false
  | .trap, .exact => false
  | .trap, .wrap => false
  | .trap, .trap => true
  | .trap, .saturate => false
  | .saturate, .exact => false
  | .saturate, .wrap => false
  | .saturate, .trap => false
  | .saturate, .saturate => true

/-- Reflexivity: every mode is `≤` itself. -/
theorem overflowLeRefl : ∀ mode : OverflowMode, overflowLe mode mode = true
  | .exact => rfl
  | .wrap => rfl
  | .trap => rfl
  | .saturate => rfl

/-- `exact` is the bottom: below every mode. -/
theorem exactIsBottom : ∀ mode : OverflowMode, overflowLe .exact mode = true
  | .exact => rfl
  | .wrap => rfl
  | .trap => rfl
  | .saturate => rfl

/-- Transitivity: the preorder composes.  Above `exact` the order is thin
(reflexive only), so each surviving pair forces the middle to equal the first. -/
theorem overflowLeTrans : ∀ (leftMode middleMode rightMode : OverflowMode),
    overflowLe leftMode middleMode = true → overflowLe middleMode rightMode = true →
      overflowLe leftMode rightMode = true
  | .exact, .exact, rightMode, _, _ => exactIsBottom rightMode
  | .exact, .wrap, rightMode, _, _ => exactIsBottom rightMode
  | .exact, .trap, rightMode, _, _ => exactIsBottom rightMode
  | .exact, .saturate, rightMode, _, _ => exactIsBottom rightMode
  | .wrap, .wrap, _, _, rightHolds => rightHolds
  | .wrap, .exact, _, leftFails, _ => Bool.noConfusion leftFails
  | .wrap, .trap, _, leftFails, _ => Bool.noConfusion leftFails
  | .wrap, .saturate, _, leftFails, _ => Bool.noConfusion leftFails
  | .trap, .trap, _, _, rightHolds => rightHolds
  | .trap, .exact, _, leftFails, _ => Bool.noConfusion leftFails
  | .trap, .wrap, _, leftFails, _ => Bool.noConfusion leftFails
  | .trap, .saturate, _, leftFails, _ => Bool.noConfusion leftFails
  | .saturate, .saturate, _, _, rightHolds => rightHolds
  | .saturate, .exact, _, leftFails, _ => Bool.noConfusion leftFails
  | .saturate, .wrap, _, leftFails, _ => Bool.noConfusion leftFails
  | .saturate, .trap, _, leftFails, _ => Bool.noConfusion leftFails

end FX1Poly.ComputerAlgebra
