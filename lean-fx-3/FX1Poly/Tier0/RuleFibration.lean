/-! # FX1Poly/Tier0/RuleFibration — the maximally generic rule fibration substrate

The abstract skeleton of "what rules a head fires at an axis", with NOTHING fixed: the axes, the
heads, and the per-axis rule payloads are all parameters.  This is the index-abstract foundation of
the (∞,ω)-polygraph cell-rule fibration — Core instantiates the axes at `CellSort` and the heads at
`Generator`; the typed layer wires the `.type` axis to the typing-row lookup.

A `RuleFibration Axis Head payload` assigns to each axis a per-head list of rules at that axis, where
`payload : Axis → Type` lets each axis carry its own rule type (a `type`-axis lookup is statically a
list of type rows, a `grade`-axis lookup a list of grade rules, etc.).  The lookup, the decidable
inhabitation test, and the per-head orthogonality certificate are stated here ONCE, generic over the
axis — so every fibration axis downstream gets identical machinery.

This file is `Init`-only and Tier0-low (no Core dependency), so Core and the cell substrate may
import it.  Zero-axiom: a structure, list/`Nat.ble` operations, and structural `List.Mem` reasoning.
Audit-gated in `FX1PolyAudit/AuditRuleFibration.lean`. -/

namespace FX1Poly.Tier0

/-- ★ **The generic rule fibration.**  For each `axis`, the per-`head` list of rules at that axis.
The payload family `payload : Axis → Type` makes the rule type axis-dependent.  This is the abstract
substrate the cell-rule fibration (over the seven `CellSort` axes and the `Generator` heads) is one
instance of. -/
structure RuleFibration (Axis : Type) (Head : Type) (payload : Axis → Type) where
  /-- The rules a head fires at a given axis. -/
  rowsAt : (axis : Axis) → Head → List (payload axis)

namespace RuleFibration

variable {Axis Head : Type} {payload : Axis → Type}

/-- Pipe an axis through a head: the rules it fires there. -/
def lookup (fibration : RuleFibration Axis Head payload) (axis : Axis) (head : Head) :
    List (payload axis) :=
  fibration.rowsAt axis head

/-- A head INHABITS the fibre at `axis` iff it fires at least one rule there.  Decidable by
construction (a list-emptiness test). -/
def inhabits (fibration : RuleFibration Axis Head payload) (axis : Axis) (head : Head) : Bool :=
  !(fibration.rowsAt axis head).isEmpty

/-- Per-cell orthogonality: at most one rule fires at this (axis, head).  When this holds for every
head, the axis lookup is a partial FUNCTION — the head determines its rule. -/
def isOrthogonalAt (fibration : RuleFibration Axis Head payload) (axis : Axis) (head : Head) :
    Bool :=
  Nat.ble (fibration.rowsAt axis head).length 1

/-- Orthogonality at `axis` across a roster of heads. -/
def isOrthogonalOverAt (fibration : RuleFibration Axis Head payload) (axis : Axis)
    (heads : List Head) : Bool :=
  heads.all (fun head => fibration.isOrthogonalAt axis head)

/-- **Inhabitation is sound**: a head inhabits the fibre at an axis exactly when some rule fires
there.  Structural (`List.Mem` constructors), so `propext`-clean. -/
theorem inhabits_eq_true_iff (fibration : RuleFibration Axis Head payload) (axis : Axis)
    (head : Head) :
    fibration.inhabits axis head = true ↔ ∃ rule, rule ∈ fibration.rowsAt axis head := by
  unfold inhabits
  cases hRows : fibration.rowsAt axis head with
  | nil =>
      apply Iff.intro
      · intro fires; exact Bool.noConfusion fires
      · rintro ⟨rule, isMember⟩; cases isMember
  | cons firstRule restRules =>
      apply Iff.intro
      · intro _; exact ⟨firstRule, List.Mem.head restRules⟩
      · intro _; rfl

end RuleFibration

end FX1Poly.Tier0
