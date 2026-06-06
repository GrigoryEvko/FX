import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Modal/GradeVector — the per-binding usage grade vector (§6.2 / §7.7)

The graded typing judgment `Γ ⊢_p e : A` (§6.2) carries, alongside the type context `Γ`, a grade
VECTOR `p` recording how each binding is used.  This file ships that vector and its pointwise
algebra over the usage ordered semiring `fxUsageSemiring`:

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
rules consume.

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

/-! ## Context division `G / p` — the corrected Lam rule's capture discipline (§6.2/§27.1)

The Wood/Atkey Lam rule forms a closure of grade `p` by dividing the captured context `G` by `p`:
`G / p`, pointwise `· / p` over `UsageGrade.div` (the residual of multiplication, `ResourceGraded`).
Its soundness — you can never recover more than you had — is `scale p (G / p) ≤ G` pointwise,
proved here against a pointwise-`≤` predicate (so it needs no new vector order). -/

/-- Context division `G / p`: divide every binding's grade by the scalar `divisorGrade` (§6.2 — the
corrected Lam rule's capture discipline).  Pointwise `· / divisorGrade`. -/
def GradeVector.contextDivide (divisorGrade : UsageGrade) : GradeVector → GradeVector
  | .nil => .nil
  | .cons headGrade restGrades =>
      .cons (UsageGrade.div headGrade divisorGrade)
        (GradeVector.contextDivide divisorGrade restGrades)

/-- Context division preserves the binding count. -/
theorem GradeVector.contextDivide_length (divisorGrade : UsageGrade) (someVector : GradeVector) :
    (GradeVector.contextDivide divisorGrade someVector).length = someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show (GradeVector.contextDivide divisorGrade restGrades).length + 1 = restGrades.length + 1
      rw [restIH]

/-- Pointwise order on equal-length grade vectors: `firstVector ≤ secondVector` binding-by-binding
(via `UsageGrade.le`).  A local predicate so context-division soundness needs no global vector
order; vectors of different lengths are incomparable (`False`). -/
def GradeVector.IsPointwiseBelow : GradeVector → GradeVector → Prop
  | .nil, .nil => True
  | .nil, .cons _ _ => False
  | .cons _ _, .nil => False
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      (UsageGrade.le firstHead secondHead = true) ∧
        GradeVector.IsPointwiseBelow firstRest secondRest

/-- **Context-division soundness (the vector counit): `scale p (G / p) ≤ G` pointwise.**  Scaling
the divided context back up by `p` never exceeds the original `G` — the fact the corrected Lam rule
relies on.  Lifts `UsageGrade.mul_div_le` binding-by-binding. -/
theorem GradeVector.scale_contextDivide_below (divisorGrade : UsageGrade) (someVector : GradeVector) :
    GradeVector.IsPointwiseBelow
      (GradeVector.scale divisorGrade (GradeVector.contextDivide divisorGrade someVector))
      someVector := by
  induction someVector with
  | nil => exact True.intro
  | cons headGrade restGrades restIH =>
      exact ⟨UsageGrade.mul_div_le divisorGrade headGrade, restIH⟩

/-! ## Grade-vector order: `IsPointwiseBelow` is a partial order + operation monotonicity

The grade-checking judgment compares grade vectors with `IsPointwiseBelow` (the Lam rule's
premise is a `≤` check).  Here that comparison is shown to be a genuine partial order (reflexive /
transitive / antisymmetric) under which `add` and `scale` are monotone, and — the headline —
`contextDivide` is the right adjoint of `scale` (the Galois connection `contextDivide_residuation`),
the vector-level lift of `UsageGrade.div_residuation`.  The mismatched-length cases are discharged
by `.elim` (`IsPointwiseBelow` on different lengths reduces to `False`). -/

/-- Reflexivity: every grade vector is pointwise-below itself. -/
theorem GradeVector.IsPointwiseBelow.refl (someVector : GradeVector) :
    GradeVector.IsPointwiseBelow someVector someVector := by
  induction someVector with
  | nil => exact True.intro
  | cons headGrade restGrades restIH => exact ⟨UsageGrade.le_refl headGrade, restIH⟩

/-- Transitivity of the pointwise order. -/
theorem GradeVector.IsPointwiseBelow.trans {firstVector secondVector thirdVector : GradeVector}
    (firstBelowSecond : GradeVector.IsPointwiseBelow firstVector secondVector)
    (secondBelowThird : GradeVector.IsPointwiseBelow secondVector thirdVector) :
    GradeVector.IsPointwiseBelow firstVector thirdVector := by
  induction firstVector generalizing secondVector thirdVector with
  | nil =>
      cases secondVector with
      | nil =>
          cases thirdVector with
          | nil => exact True.intro
          | cons _ _ => exact secondBelowThird.elim
      | cons _ _ => exact firstBelowSecond.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact firstBelowSecond.elim
      | cons secondHead secondRest =>
          cases thirdVector with
          | nil => exact secondBelowThird.elim
          | cons thirdHead thirdRest =>
              exact ⟨UsageGrade.le_trans firstBelowSecond.1 secondBelowThird.1,
                restIH firstBelowSecond.2 secondBelowThird.2⟩

/-- Antisymmetry — the pointwise order is a PARTIAL order: mutual `≤` forces equality. -/
theorem GradeVector.IsPointwiseBelow.antisymm {firstVector secondVector : GradeVector}
    (firstBelowSecond : GradeVector.IsPointwiseBelow firstVector secondVector)
    (secondBelowFirst : GradeVector.IsPointwiseBelow secondVector firstVector) :
    firstVector = secondVector := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => rfl
      | cons _ _ => exact firstBelowSecond.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact firstBelowSecond.elim
      | cons secondHead secondRest =>
          have headEq : firstHead = secondHead :=
            UsageGrade.le_antisymm firstBelowSecond.1 secondBelowFirst.1
          have restEq : firstRest = secondRest := restIH firstBelowSecond.2 secondBelowFirst.2
          rw [headEq, restEq]

/-- `scale` is monotone in the vector argument: `v ≤ w → scale b v ≤ scale b w`. -/
theorem GradeVector.IsPointwiseBelow.scale_mono (scaleGrade : UsageGrade)
    {firstVector secondVector : GradeVector}
    (below : GradeVector.IsPointwiseBelow firstVector secondVector) :
    GradeVector.IsPointwiseBelow (GradeVector.scale scaleGrade firstVector)
      (GradeVector.scale scaleGrade secondVector) := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => exact True.intro
      | cons _ _ => exact below.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact below.elim
      | cons secondHead secondRest =>
          exact ⟨UsageGrade.mul_le_mul_left scaleGrade below.1, restIH below.2⟩

/-- `add` is monotone in both vector arguments: `v₁ ≤ w₁ → v₂ ≤ w₂ → v₁ + v₂ ≤ w₁ + w₂`. -/
theorem GradeVector.IsPointwiseBelow.add_mono
    {firstVector firstBound secondVector secondBound : GradeVector}
    (firstBelow : GradeVector.IsPointwiseBelow firstVector firstBound)
    (secondBelow : GradeVector.IsPointwiseBelow secondVector secondBound) :
    GradeVector.IsPointwiseBelow (GradeVector.add firstVector secondVector)
      (GradeVector.add firstBound secondBound) := by
  induction firstVector generalizing firstBound secondVector secondBound with
  | nil =>
      cases firstBound with
      | nil => exact True.intro
      | cons _ _ => exact firstBelow.elim
  | cons firstHead firstRest restIH =>
      cases firstBound with
      | nil => exact firstBelow.elim
      | cons firstBoundHead firstBoundRest =>
          cases secondVector with
          | nil =>
              cases secondBound with
              | nil => exact True.intro
              | cons _ _ => exact secondBelow.elim
          | cons secondHead secondRest =>
              cases secondBound with
              | nil => exact secondBelow.elim
              | cons secondBoundHead secondBoundRest =>
                  exact ⟨UsageGrade.add_le_add firstBelow.1 secondBelow.1,
                    restIH firstBelow.2 secondBelow.2⟩

/-- **The context-division Galois connection (vector residuation): `scale b q ≤ G ↔ q ≤ G / b`.**
Context division is the right adjoint of scaling — the vector-level lift of
`UsageGrade.div_residuation`.  This is the precise universal property the corrected Lam rule's
context division relies on: a grade vector `q` fits under `G` after scaling by `b` exactly when it
fits under the divided context `G / b`. -/
theorem GradeVector.contextDivide_residuation (divisorGrade : UsageGrade)
    (quotientCandidate dividendVector : GradeVector) :
    GradeVector.IsPointwiseBelow (GradeVector.scale divisorGrade quotientCandidate) dividendVector ↔
      GradeVector.IsPointwiseBelow quotientCandidate
        (GradeVector.contextDivide divisorGrade dividendVector) := by
  induction quotientCandidate generalizing dividendVector with
  | nil =>
      cases dividendVector with
      | nil => exact Iff.rfl
      | cons _ _ => exact Iff.rfl
  | cons quotientHead quotientRest restIH =>
      cases dividendVector with
      | nil => exact Iff.rfl
      | cons dividendHead dividendRest =>
          have headIff :
              (UsageGrade.le (UsageGrade.mul divisorGrade quotientHead) dividendHead = true) ↔
                (UsageGrade.le quotientHead (UsageGrade.div dividendHead divisorGrade) = true) := by
            rw [UsageGrade.mul_comm divisorGrade quotientHead]
            exact UsageGrade.div_residuation dividendHead divisorGrade quotientHead
          exact Iff.intro
            (fun ⟨headBelow, restBelow⟩ => ⟨headIff.mp headBelow, (restIH dividendRest).mp restBelow⟩)
            (fun ⟨headBelow, restBelow⟩ =>
              ⟨headIff.mpr headBelow, (restIH dividendRest).mpr restBelow⟩)

/-! ## Singleton and tail — the var-rule usage vector and binder stripping

A variable's usage vector is `single scope position 1` (grade `1` at its de Bruijn position, `0`
elsewhere); a binder's usage of the outer context drops the binder's own grade (`tail`).  These are
exactly the operations the per-binding occurrence usage (`UsageDiscipline`) is built from. -/

/-- A singleton grade vector of length `scope`: `grade` at `position`, `0` elsewhere (and all-zero
if `position ≥ scope`).  The var rule's usage vector. -/
def GradeVector.single : (scope : Nat) → (position : Nat) → UsageGrade → GradeVector
  | 0, _, _ => .nil
  | scope + 1, 0, grade => .cons grade (GradeVector.zero scope)
  | scope + 1, pos + 1, grade => .cons UsageGrade.zero (GradeVector.single scope pos grade)

/-- Drop the newest binding's grade (the head): the outer-context usage of a binder from its body. -/
def GradeVector.tail : GradeVector → GradeVector
  | .nil => .nil
  | .cons _ restGrades => restGrades

/-- A singleton vector has exactly `scope` bindings (it is the var rule's full-length usage). -/
theorem GradeVector.single_length (scope position : Nat) (grade : UsageGrade) :
    (GradeVector.single scope position grade).length = scope := by
  induction scope generalizing position with
  | zero => rfl
  | succ scope restIH =>
      cases position with
      | zero =>
          show (GradeVector.zero scope).length + 1 = scope + 1
          rw [GradeVector.zero_length]
      | succ position =>
          show (GradeVector.single scope position grade).length + 1 = scope + 1
          rw [restIH]

/-! ## Decidable pointwise order — the computable usage-check decision procedure

The grade-checker doesn't run the `Prop`-valued `IsPointwiseBelow`; it runs this Boolean version.
`isPointwiseBelowBool_correct` proves the two agree (soundness + completeness), so the computable
check is a faithful decision procedure for the pointwise order. -/

/-- Computable pointwise-`≤` on grade vectors (truncating; `false` on length mismatch).  The
Boolean realization of `IsPointwiseBelow` — what a grade-checker actually runs. -/
def GradeVector.isPointwiseBelowBool : GradeVector → GradeVector → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ => false
  | .cons _ _, .nil => false
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      (UsageGrade.le firstHead secondHead) && (GradeVector.isPointwiseBelowBool firstRest secondRest)

/-- **Soundness + completeness of the Boolean check:** `isPointwiseBelowBool a b = true ↔
IsPointwiseBelow a b` — the decision procedure exactly decides the pointwise order.  Proved
propext-free: the iff is built by explicit `Iff.intro` with `Eq`-rewrites only (rewriting WITH an
`Iff` — e.g. `Bool.and_eq_true` — would pull `propext`; here `&&` is split by casing the head). -/
theorem GradeVector.isPointwiseBelowBool_correct (firstVector secondVector : GradeVector) :
    GradeVector.isPointwiseBelowBool firstVector secondVector = true ↔
      GradeVector.IsPointwiseBelow firstVector secondVector := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | cons _ _ => exact ⟨fun contra => Bool.noConfusion contra, fun contra => contra.elim⟩
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact ⟨fun contra => Bool.noConfusion contra, fun contra => contra.elim⟩
      | cons secondHead secondRest =>
          show (UsageGrade.le firstHead secondHead &&
                GradeVector.isPointwiseBelowBool firstRest secondRest) = true ↔
              (UsageGrade.le firstHead secondHead = true) ∧
                GradeVector.IsPointwiseBelow firstRest secondRest
          constructor
          · intro hbool
            have headOk : UsageGrade.le firstHead secondHead = true := by
              cases hle : UsageGrade.le firstHead secondHead with
              | true => rfl
              | false => rw [hle] at hbool; exact Bool.noConfusion hbool
            have restBool : GradeVector.isPointwiseBelowBool firstRest secondRest = true := by
              rw [headOk] at hbool; exact hbool
            exact ⟨headOk, (restIH secondRest).mp restBool⟩
          · intro hprop
            have restBool : GradeVector.isPointwiseBelowBool firstRest secondRest = true :=
              (restIH secondRest).mpr hprop.2
            rw [hprop.1]
            exact restBool

end FX1Poly.Modal
