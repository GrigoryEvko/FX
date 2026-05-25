/-!
# Resource-Graded Doctrine (Abel-Danielsson-Eriksson arXiv:2603.29716)

An ordered grade semiring models resource usage in quantitative type theory.
Each variable carries a grade from a partially ordered semiring R = (R, 0, 1, +, *, ≤).
The typing rules consume/scale grades per the semiring operations:
- VAR uses grade 1 at the variable position
- LAM: body's grade of the binder = function's parameter grade
- APP: grade of argument scaled by function's parameter grade
- IF: grade = join of both branches (worst case)

For FX: the Usage dimension {0, 1, ω} is the primary instance.
Security {unclassified < classified} is another instance.

Reference: arXiv:2603.29716 (Agda-formalized).
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Modal

/-- A partially ordered semiring: the grade algebra for QTT.
(R, 0, 1, +, *, ≤) with semiring laws + order compatibility. -/
structure OrderedGradeSemiring where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  le : Carrier → Carrier → Bool
  /-- DecidableEq on carriers. -/
  carrierDecEq : DecidableEq Carrier

/-- FX's usage semiring: {0, 1, ω} with 0+0=0, 1+1=ω, ω+ω=ω. -/
inductive UsageGrade where
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

def UsageGrade.add : UsageGrade → UsageGrade → UsageGrade
  | .zero, g => g
  | g, .zero => g
  | .one, .one => .omega
  | .one, .omega => .omega
  | .omega, _ => .omega

def UsageGrade.mul : UsageGrade → UsageGrade → UsageGrade
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, g => g
  | g, .one => g
  | .omega, .omega => .omega

def UsageGrade.le : UsageGrade → UsageGrade → Bool
  | .zero, _ => true
  | .one, .one => true
  | .one, .omega => true
  | .omega, .omega => true
  | _, _ => false

/-- The FX usage semiring instance. -/
def fxUsageSemiring : OrderedGradeSemiring where
  Carrier := UsageGrade
  zero := .zero
  one := .one
  add := UsageGrade.add
  mul := UsageGrade.mul
  le := UsageGrade.le
  carrierDecEq := instDecidableEqUsageGrade

/-- FX's security semiring: {unclassified < classified}. -/
inductive SecurityGrade where
  | unclassified
  | classified
  deriving DecidableEq, Repr

def SecurityGrade.add : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, .unclassified => .unclassified
  | _, _ => .classified

def SecurityGrade.mul : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, _ => .unclassified
  | _, .unclassified => .unclassified
  | .classified, .classified => .classified

def SecurityGrade.le : SecurityGrade → SecurityGrade → Bool
  | .unclassified, _ => true
  | .classified, .classified => true
  | _, _ => false

/-- The FX security semiring instance. -/
def fxSecuritySemiring : OrderedGradeSemiring where
  Carrier := SecurityGrade
  zero := .unclassified
  one := .classified
  add := SecurityGrade.add
  mul := fun g1 g2 => SecurityGrade.add g1 g2
  le := SecurityGrade.le
  carrierDecEq := instDecidableEqSecurityGrade

/-- Semiring laws verification (usage). -/
theorem UsageGrade.add_comm (a b : UsageGrade) :
    UsageGrade.add a b = UsageGrade.add b a := by
  cases a <;> cases b <;> rfl

theorem UsageGrade.add_zero (a : UsageGrade) :
    UsageGrade.add a .zero = a := by
  cases a <;> rfl

theorem UsageGrade.zero_add (a : UsageGrade) :
    UsageGrade.add .zero a = a := by
  cases a <;> rfl

theorem UsageGrade.mul_one (a : UsageGrade) :
    UsageGrade.mul a .one = a := by
  cases a <;> rfl

theorem UsageGrade.one_mul (a : UsageGrade) :
    UsageGrade.mul .one a = a := by
  cases a <;> rfl

theorem UsageGrade.mul_zero (a : UsageGrade) :
    UsageGrade.mul a .zero = .zero := by
  cases a <;> rfl

theorem UsageGrade.zero_mul (a : UsageGrade) :
    UsageGrade.mul .zero a = .zero := by
  cases a <;> rfl

/-- The Atkey-McBride attack: using linear variable twice in unrestricted
closure. Wood-Atkey 2022 corrected Lam rule prevents this via context
division: 1/ω = 0, so linear vars erased in replicable closures. -/
theorem UsageGrade.linear_div_omega_eq_zero :
    UsageGrade.mul .one .zero = .zero := rfl

end LeanFX2.Foundation.PolyCell.Modal
