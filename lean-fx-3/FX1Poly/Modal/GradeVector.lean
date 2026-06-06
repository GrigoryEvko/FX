import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Modal/GradeVector — the per-binding usage grade vector (DIM2-2, §6.2 / §7.7)

The graded typing judgment `Γ ⊢_p e : A` (§6.2) carries, alongside the type context `Γ`, a grade
VECTOR `p` recording how each binding is used.  This file ships that vector and its pointwise
algebra over the usage ordered semiring `fxUsageSemiring` (DIM2-1):

  * `GradeVector` — a cons-list of `UsageGrade`s.  Deliberately UNINDEXED (no scope index);
    alignment with the scope-indexed `TypingContext` is by `length` (mirroring
    `TypingContext.length`).  This is what keeps the binary pointwise `add` propext-free: an
    indexed vector's two-scrutinee `add` match must prove the cross-cases (`nil`/`cons`) impossible
    by INDEX injectivity, which the Lean match compiler discharges through `propext`; an unindexed
    list's `add` is a genuinely total match with no impossible arms, so it is axiom-clean.

  * `GradeVector.add` — pointwise addition: context splitting / parallel use (§7.7, the
    separating-conjunction `*` realized as grade `+`).  Truncates to the shorter operand, so the
    laws hold for ANY two vectors (and a fortiori for the equal-length vectors of a fixed context).

  * `GradeVector.scale` — scalar multiplication: scale every binding's grade by one scalar (the App
    rule's `r * p`, §6.2 — the cost of an argument scaled by the parameter's grade).

  * `GradeVector.zero` — the all-zero (ghost / erased) vector at a given length: the additive
    identity and the scalar annihilator's value.

The proved laws make grade vectors a (left) SEMIMODULE over `fxUsageSemiring`: `(GradeVector, add,
zero)` is a commutative monoid (`add_comm` / `add_assoc` / `add_zero` / `zero_add`), and `scale` is
a scalar action distributing over both additions and respecting scalar multiplication and unit
(`scale_add` / `scale_add_scalar` / `scale_scale` / `scale_one_scalar`, with `scale_zero_scalar`
the annihilation `0 · p = 0`).  These are exactly the operations the Wood/Atkey graded Lam and App
rules (DIM2-3) consume.

## Zero-axiom verification

`GradeVector` is a plain (unindexed) inductive, so every operation's match is total and its
equation lemmas are propext-free; the laws close by structural `induction … <;> rfl` /
`simp only [<def>]` + `rw [<UsageGrade law>, restIH]`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before
landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- A grade vector: one usage grade per binding, as a cons-list.  Unindexed; alignment with the
type context is by `length` (mirroring `TypingContext.length`), which keeps the binary pointwise
`add` match total and propext-free. -/
inductive GradeVector where
  | nil : GradeVector
  | cons : UsageGrade → GradeVector → GradeVector
  deriving DecidableEq, Repr

/-- The number of graded bindings.  Equals the scope of the context it grades (a CHECKED coherence,
not an unstated invariant — cf. `TypingContext.length`). -/
def GradeVector.length : GradeVector → Nat
  | .nil => 0
  | .cons _ restGrades => restGrades.length + 1

/-- The all-zero grade vector of a given length: every binding erased / ghost.  The additive
identity (`add_zero` / `zero_add`) and the value of `scale`-by-zero (`scale_zero_scalar`). -/
def GradeVector.zero : Nat → GradeVector
  | 0 => .nil
  | scope + 1 => .cons UsageGrade.zero (GradeVector.zero scope)

/-- Pointwise addition — context splitting / parallel use (§7.7): the separating conjunction `*`
realized as grade `+`.  Truncates to the shorter operand (so the monoid laws need no length
side-condition). -/
def GradeVector.add : GradeVector → GradeVector → GradeVector
  | .nil, _ => .nil
  | .cons _ _, .nil => .nil
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      .cons (UsageGrade.add firstHead secondHead) (GradeVector.add firstRest secondRest)

/-- Scalar multiplication: scale every binding's grade by `scaleGrade` (the App rule's `r * p`,
§6.2 — the argument's cost scaled by the parameter's grade). -/
def GradeVector.scale (scaleGrade : UsageGrade) : GradeVector → GradeVector
  | .nil => .nil
  | .cons headGrade restGrades =>
      .cons (UsageGrade.mul scaleGrade headGrade) (GradeVector.scale scaleGrade restGrades)

/-! ## Length coherence -/

/-- The zero vector at `scope` has exactly `scope` bindings. -/
theorem GradeVector.zero_length (scope : Nat) : (GradeVector.zero scope).length = scope := by
  induction scope with
  | zero => rfl
  | succ scope restIH => show (GradeVector.zero scope).length + 1 = scope + 1; rw [restIH]

/-- Scaling preserves the binding count (it is pointwise, not structural). -/
theorem GradeVector.scale_length (scaleGrade : UsageGrade) (someVector : GradeVector) :
    (GradeVector.scale scaleGrade someVector).length = someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show (GradeVector.scale scaleGrade restGrades).length + 1 = restGrades.length + 1
      rw [restIH]

/-! ## Commutative-monoid laws for `(GradeVector, add, zero)` -/

/-- Pointwise addition is commutative (lifts `UsageGrade.add_comm`; truncation is symmetric). -/
theorem GradeVector.add_comm (firstVector secondVector : GradeVector) :
    GradeVector.add firstVector secondVector = GradeVector.add secondVector firstVector := by
  induction firstVector generalizing secondVector with
  | nil => cases secondVector <;> rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          simp only [GradeVector.add]
          rw [UsageGrade.add_comm firstHead secondHead, restIH secondRest]

/-- Pointwise addition is associative (lifts `UsageGrade.add_assoc`; the truncation lengths agree). -/
theorem GradeVector.add_assoc (firstVector secondVector thirdVector : GradeVector) :
    GradeVector.add (GradeVector.add firstVector secondVector) thirdVector =
      GradeVector.add firstVector (GradeVector.add secondVector thirdVector) := by
  induction firstVector generalizing secondVector thirdVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => cases thirdVector <;> rfl
      | cons secondHead secondRest =>
          cases thirdVector with
          | nil => rfl
          | cons thirdHead thirdRest =>
              simp only [GradeVector.add]
              rw [UsageGrade.add_assoc firstHead secondHead thirdHead, restIH secondRest thirdRest]

/-- The zero vector (at the operand's own length) is a right identity for addition. -/
theorem GradeVector.add_zero (someVector : GradeVector) :
    GradeVector.add someVector (GradeVector.zero someVector.length) = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.length, GradeVector.zero, GradeVector.add]
      rw [UsageGrade.add_zero headGrade, restIH]

/-- The zero vector (at the operand's own length) is a left identity for addition. -/
theorem GradeVector.zero_add (someVector : GradeVector) :
    GradeVector.add (GradeVector.zero someVector.length) someVector = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.length, GradeVector.zero, GradeVector.add]
      rw [UsageGrade.zero_add headGrade, restIH]

/-! ## Scalar-action laws (the semimodule structure over `fxUsageSemiring`) -/

/-- Scaling by `0` annihilates to the zero vector (`0 · p = 0`). -/
theorem GradeVector.scale_zero_scalar (someVector : GradeVector) :
    GradeVector.scale UsageGrade.zero someVector = GradeVector.zero someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale, GradeVector.zero, GradeVector.length]
      rw [UsageGrade.zero_mul headGrade, restIH]

/-- Scaling by `1` is the identity (`1 · p = p`). -/
theorem GradeVector.scale_one_scalar (someVector : GradeVector) :
    GradeVector.scale UsageGrade.one someVector = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale]
      rw [UsageGrade.one_mul headGrade, restIH]

/-- A scalar distributes over a vector sum: `s · (p + q) = s · p + s · q`. -/
theorem GradeVector.scale_add (scaleGrade : UsageGrade) (firstVector secondVector : GradeVector) :
    GradeVector.scale scaleGrade (GradeVector.add firstVector secondVector) =
      GradeVector.add (GradeVector.scale scaleGrade firstVector)
        (GradeVector.scale scaleGrade secondVector) := by
  induction firstVector generalizing secondVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          simp only [GradeVector.add, GradeVector.scale]
          rw [UsageGrade.left_distrib scaleGrade firstHead secondHead, restIH secondRest]

/-- Scalar multiplication composes: `s · (t · p) = (s * t) · p`. -/
theorem GradeVector.scale_scale (firstScale secondScale : UsageGrade) (someVector : GradeVector) :
    GradeVector.scale firstScale (GradeVector.scale secondScale someVector) =
      GradeVector.scale (UsageGrade.mul firstScale secondScale) someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale]
      rw [UsageGrade.mul_assoc firstScale secondScale headGrade, restIH]

/-- A scalar sum distributes over a vector: `(s + t) · p = s · p + t · p`. -/
theorem GradeVector.scale_add_scalar (firstScale secondScale : UsageGrade) (someVector : GradeVector) :
    GradeVector.scale (UsageGrade.add firstScale secondScale) someVector =
      GradeVector.add (GradeVector.scale firstScale someVector)
        (GradeVector.scale secondScale someVector) := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVector.scale, GradeVector.add]
      rw [UsageGrade.right_distrib firstScale secondScale headGrade, restIH]

end FX1Poly.Modal
