import FX1Poly.Modal.SecurityNoninterferenceGeneral

/-! # FX1Poly/Modal/GradedApplicationFlow
    — the §6.2 App-scaling rule read pointwise, GENERIC over any lawful resource semiring (all 21 dimensions)

Firing-52's `SecurityNoninterferenceGeneral` proved the App-scaling flow law for the SECURITY semiring only:
an application's grade decomposes positionally as `functionGrades.get i + binderGrade · argumentGrades.get i`,
and a classified function-position poisons the result.  But that decomposition is the §6.2 App rule
`grades = functionGrades + binderGrade · argumentGrades` (App rule of `HasGradeOver`, GradedTypingGeneric),
and it holds over EVERY graded dimension — usage (linearity), complexity (cost), security, … — because the
rule is generic in the resource semiring `R`.  This file lifts the flow law to its proper generic form:

  * `GradeVectorOver.get_add_lawful` / `get_scale_lawful` — the get-commutations over ANY
    `IsLawfulOrderedGradeSemiring` (the `nil` arm uses `lawful.add_zero` / `lawful.mul_zero` where the
    security instance used `rfl`).
  * **`HasGradeOver.applicationGradeAt`** — the App-scaling rule read pointwise, for any `R`:
    `grades.get i = R.add (functionGrades.get i) (R.mul binderGrade (argumentGrades.get i))`.  Generalizes
    `securityApplicationGradeAt` from `fxSecuritySemiring` to all dimensions at once.
  * **`HasGradeOver.applicationGradePoisonsOfAbsorbing`** — the dimension-agnostic POISON law: any grade
    `absorber` that is top-absorbing for `R.add` (`absorber + x = absorber`) and used by the function at
    position `i` poisons the application's grade at `i`.  The general principle behind firing-52's
    classified-poison.

`securityFunctionPoison_viaGeneric` demonstrates the subsumption: the generic poison at `fxSecuritySemiring`
with `absorber = classified` (absorbing by `SecurityGrade.classified_poisons_add`) recovers firing-52's
`securityClassifiedFunctionPoisonsApplication`.  Every future dimension's flow-soundness becomes a one-line
corollary of `applicationGradeAt` (or, when the dimension has an absorbing grade, of
`applicationGradePoisonsOfAbsorbing`).

## Zero-axiom verification

`get_add_lawful` / `get_scale_lawful` are two-vector / one-vector inductions threading `lawful.add_zero` /
`lawful.mul_zero` (the length-mismatch arm is `Nat.noConfusion`).  `applicationGradeAt` is
`HasGradeOver.invertApp` + the `hasGradeOver_length` invariant (App operands share a length) + the two
get-commutations; the poison law rewrites with the `absorbs` hypothesis.  Reuses the `GradeVectorOver.get`
definition shipped in `SecurityNoninterferenceGeneral`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Modal

/-- **get commutes with pointwise add** for EQUAL-LENGTH vectors, over ANY lawful semiring.  The generic twin
of firing-52's `getAddSecurity`; the `nil` arm closes by `lawful.add_zero` (where the security instance was
`rfl`).  Equal length is the regime the App rule supplies (`hasGradeOver_length`); the mismatch arm is
`Nat.noConfusion`. -/
theorem GradeVectorOver.get_add_lawful {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R)
    (firstVector secondVector : GradeVectorOver R)
    (lengthEq : firstVector.length = secondVector.length) (position : Nat) :
    (GradeVectorOver.add firstVector secondVector).get position
      = R.add (firstVector.get position) (secondVector.get position) := by
  induction firstVector generalizing secondVector position with
  | nil =>
      cases secondVector with
      | nil => exact (lawful.add_zero R.zero).symm
      | cons _ _ => exact Nat.noConfusion lengthEq
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact Nat.noConfusion lengthEq
      | cons secondHead secondRest =>
          cases position with
          | zero => rfl
          | succ predecessor =>
              exact restIH secondRest (Nat.succ.inj lengthEq) predecessor

/-- **get commutes with scalar multiplication**, over ANY lawful semiring.  Unconditional — `scale` preserves
length and the past-the-end case is `g * 0 = 0` (`lawful.mul_zero`).  The generic twin of `getScaleSecurity`. -/
theorem GradeVectorOver.get_scale_lawful {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (scaleGrade : R.Carrier)
    (someVector : GradeVectorOver R) (position : Nat) :
    (GradeVectorOver.scale scaleGrade someVector).get position
      = R.mul scaleGrade (someVector.get position) := by
  induction someVector generalizing position with
  | nil => exact (lawful.mul_zero scaleGrade).symm
  | cons headGrade restGrades restIH =>
      cases position with
      | zero => rfl
      | succ predecessor => exact restIH predecessor

/-- **The App-scaling rule read pointwise (§6.2), over ANY lawful resource semiring.**  At every position, an
application's grade is the function's grade combined (via `R.add`) with the binder-scaled (`R.mul binderGrade`)
argument's grade.  Generalizes firing-52's `securityApplicationGradeAt` from `fxSecuritySemiring` to all 21
graded dimensions — the structural backbone every dimension's flow-soundness reads off.  `HasGradeOver.invertApp`
+ the `hasGradeOver_length` invariant (so the App operands share a length, feeding `get_add_lawful`) +
`get_scale_lawful`. -/
theorem HasGradeOver.applicationGradeAt {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R)
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
    {function argument : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades (.app function argument) resultType)
    (position : Nat) :
    ∃ (binderGrade : R.Carrier) (domain : GTypeOver R)
      (functionGrades argumentGrades : GradeVectorOver R),
      HasGradeOver R typeContext functionGrades function (.arrow binderGrade domain resultType) ∧
        HasGradeOver R typeContext argumentGrades argument domain ∧
          grades.get position
            = R.add (functionGrades.get position)
                (R.mul binderGrade (argumentGrades.get position)) := by
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    gradesEq⟩ := HasGradeOver.invertApp typed
  have functionLength : functionGrades.length = typeContext.length := hasGradeOver_length functionTyped
  have argumentLength : argumentGrades.length = typeContext.length := hasGradeOver_length argumentTyped
  refine ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, ?_⟩
  subst gradesEq
  rw [GradeVectorOver.get_add_lawful lawful functionGrades
        (GradeVectorOver.scale binderGrade argumentGrades)
        (by rw [GradeVectorOver.scale_length, functionLength, argumentLength]) position,
      GradeVectorOver.get_scale_lawful lawful binderGrade argumentGrades position]

/-- **Generic absorbing-element poison law.**  If an `absorber` grade is top-absorbing for `R.add`
(`absorber + x = absorber`) and the function uses position `i` at `absorber`, the application's grade at `i`
is `absorber` — the function's grade cannot be downgraded by applying it.  The dimension-agnostic backbone of
noninterference: at `fxSecuritySemiring` with `absorber = classified` it is firing-52's classified-poison;
at any future dimension with an `R.add`-absorbing grade of the same role it holds verbatim.  Reads the
pointwise decomposition off `applicationGradeAt`, then collapses the head with the `absorbs` hypothesis. -/
theorem HasGradeOver.applicationGradePoisonsOfAbsorbing {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R)
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
    {function argument : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades (.app function argument) resultType)
    (position : Nat) (absorber : R.Carrier)
    (absorbs : ∀ otherGrade : R.Carrier, R.add absorber otherGrade = absorber) :
    ∃ (binderGrade : R.Carrier) (domain : GTypeOver R)
      (functionGrades argumentGrades : GradeVectorOver R),
      HasGradeOver R typeContext functionGrades function (.arrow binderGrade domain resultType) ∧
        HasGradeOver R typeContext argumentGrades argument domain ∧
          (functionGrades.get position = absorber → grades.get position = absorber) := by
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    gradeEq⟩ := HasGradeOver.applicationGradeAt lawful typed position
  refine ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    fun functionAbsorberAt => ?_⟩
  rw [gradeEq, functionAbsorberAt, absorbs]

/-- **Subsumption smoke.**  The generic poison at `fxSecuritySemiring` with `absorber = classified`
(`SecurityGrade.classified_poisons_add` witnesses the absorbing law) recovers firing-52's
`securityClassifiedFunctionPoisonsApplication` — the security noninterference witness is the security instance
of the dimension-agnostic principle. -/
theorem securityFunctionPoison_viaGeneric
    {typeContext : List (GTypeOver fxSecuritySemiring)} {grades : GradeVectorOver fxSecuritySemiring}
    {function argument : GradedLambda} {resultType : GTypeOver fxSecuritySemiring}
    (typed : HasGradeOver fxSecuritySemiring typeContext grades (.app function argument) resultType)
    (position : Nat) :
    ∃ (binderGrade : SecurityGrade) (domain : GTypeOver fxSecuritySemiring)
      (functionGrades argumentGrades : GradeVectorOver fxSecuritySemiring),
      HasGradeOver fxSecuritySemiring typeContext functionGrades function
          (.arrow binderGrade domain resultType) ∧
        HasGradeOver fxSecuritySemiring typeContext argumentGrades argument domain ∧
          (functionGrades.get position = SecurityGrade.classified →
            grades.get position = SecurityGrade.classified) :=
  HasGradeOver.applicationGradePoisonsOfAbsorbing fxSecuritySemiring_isLawful typed position
    SecurityGrade.classified SecurityGrade.classified_poisons_add

end FX1Poly.Modal
