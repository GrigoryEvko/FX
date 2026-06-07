import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Modal/SecurityNoninterferenceGeneral
    — the general App-rule security-flow law: classified inputs cannot be laundered through application
      (§12.2 / §27.2 noninterference, generalized from the shipped witnesses to ALL terms)

The §27.2/§27.3 Layer-1 corpus (`KnownUnsoundnessCorpus`, Part 5) ships the first security-dimension
noninterference WITNESSES — `securityDirectUseCannotBePublic` and `securitySelectorAppCannotLaunderSelector` —
but those are statements about TWO FIXED terms (a directly-used variable, a specific Church selector
application).  This file lifts the implicit-flow defense from examples to a THEOREM over every well-graded
application: it reads the §6.2 App-scaling rule `grades = functionGrades + binderGrade · argumentGrades`
POSITIONALLY and derives that classified secrecy at any position propagates into the result.

## The positional App-scaling law

The graded judgment `HasGradeOver fxSecuritySemiring` records, per de Bruijn position, the secrecy level at
which a variable is used.  `securityApplicationGradeAt` inverts an application and exposes, at every position
`i`:

    grades.get i  =  (functionGrades.get i)  +  binderGrade · (argumentGrades.get i)

— the App-scaling rule of §6.2, read off one position at a time.  Because `fxSecuritySemiring`'s `add` is the
secrecy JOIN (`classified` is top-absorbing: `classified + x = classified`) and its `mul` is the MEET, the
two propagation corollaries follow:

  * **`securityClassifiedFunctionPoisonsApplication`** — if the function uses position `i` at `classified`,
    the application's grade at `i` is `classified`.  A secret function cannot be downgraded by applying it
    (the general form of "implicit flow via branch on secret", since Church-encoded branching is application);
    generalizes `securitySelectorAppCannotLaunderSelector` from the fixed selector to EVERY application.
  * **`securityClassifiedArgumentPoisonsApplication`** — if the binder is `classified` (the argument is
    actually consumed at secret level) and the argument uses position `i` at `classified`, the result's grade
    at `i` is `classified`.  A secret argument fed to a secret-consuming function cannot be laundered.

## Zero-axiom verification

`GradeVectorOver.get` is a structural positional lookup.  `getAddSecurity` / `getScaleSecurity` are
two-vector / one-vector inductions whose impossible length-mismatch arm is `Nat.noConfusion` (propext-free).
`securityApplicationGradeAt` is `HasGradeOver.invertApp` + the `hasGradeOver_length` invariant (so the App
operands share a length) + the two get-commutations.  The corollaries close by `SecurityGrade`'s 2-element
algebra facts (`classified_poisons_add`, `add_comm`, `mul` by `rfl`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Modal

/-- **Positional grade lookup.**  The grade assigned to de Bruijn index `position`; `R.zero` past the end of
the vector (a variable beyond the recorded bindings is erased).  The positional reader the App-scaling law is
stated through. -/
def GradeVectorOver.get {R : OrderedGradeSemiring} :
    GradeVectorOver R → Nat → R.Carrier
  | .nil, _ => R.zero
  | .cons headGrade _, 0 => headGrade
  | .cons _ restGrades, position + 1 => GradeVectorOver.get restGrades position

/-- **get commutes with pointwise add** for EQUAL-LENGTH vectors (security instance).  The App rule's two
operands always share a length (the `hasGradeOver_length` invariant), so this is exactly the regime the
positional law needs.  Two-vector induction; the length-mismatch arm is `Nat.noConfusion`. -/
theorem getAddSecurity (firstVector secondVector : GradeVectorOver fxSecuritySemiring)
    (lengthEq : firstVector.length = secondVector.length) (position : Nat) :
    (GradeVectorOver.add firstVector secondVector).get position
      = SecurityGrade.add (firstVector.get position) (secondVector.get position) := by
  induction firstVector generalizing secondVector position with
  | nil =>
      cases secondVector with
      | nil => rfl
      | cons _ _ => exact Nat.noConfusion lengthEq
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact Nat.noConfusion lengthEq
      | cons secondHead secondRest =>
          cases position with
          | zero => rfl
          | succ predecessor =>
              exact restIH secondRest (Nat.succ.inj lengthEq) predecessor

/-- **get commutes with scalar multiplication** (security instance).  Unconditional — `scale` preserves
length and `g * unclassified = unclassified`, so the past-the-end case is `g · 0 = 0`.  Single-vector
induction. -/
theorem getScaleSecurity (scaleGrade : SecurityGrade)
    (someVector : GradeVectorOver fxSecuritySemiring) (position : Nat) :
    (GradeVectorOver.scale scaleGrade someVector).get position
      = SecurityGrade.mul scaleGrade (someVector.get position) := by
  induction someVector generalizing position with
  | nil => cases scaleGrade <;> rfl
  | cons headGrade restGrades restIH =>
      cases position with
      | zero => rfl
      | succ predecessor => exact restIH predecessor

/-- **The App-scaling rule read pointwise (§6.2).**  Inverting an application exposes, at every position, the
result grade as the function's grade JOINED with the binder-scaled argument's grade:
`grades.get i = functionGrades.get i + binderGrade · argumentGrades.get i`.  The structural backbone of the
security noninterference corollaries below.  `invertApp` + the `hasGradeOver_length` invariant (the App
operands share a length, so `getAddSecurity` applies) + `getScaleSecurity`. -/
theorem securityApplicationGradeAt
    {context : List (GTypeOver fxSecuritySemiring)} {grades : GradeVectorOver fxSecuritySemiring}
    {function argument : GradedLambda} {resultType : GTypeOver fxSecuritySemiring}
    (typed : HasGradeOver fxSecuritySemiring context grades (.app function argument) resultType)
    (position : Nat) :
    ∃ (binderGrade : SecurityGrade) (domain : GTypeOver fxSecuritySemiring)
      (functionGrades argumentGrades : GradeVectorOver fxSecuritySemiring),
      HasGradeOver fxSecuritySemiring context functionGrades function
          (.arrow binderGrade domain resultType) ∧
        HasGradeOver fxSecuritySemiring context argumentGrades argument domain ∧
          grades.get position
            = SecurityGrade.add (functionGrades.get position)
                (SecurityGrade.mul binderGrade (argumentGrades.get position)) := by
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    gradesEq⟩ := HasGradeOver.invertApp typed
  have functionLength : functionGrades.length = context.length := hasGradeOver_length functionTyped
  have argumentLength : argumentGrades.length = context.length := hasGradeOver_length argumentTyped
  refine ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, ?_⟩
  subst gradesEq
  rw [getAddSecurity functionGrades (GradeVectorOver.scale binderGrade argumentGrades)
        (by rw [GradeVectorOver.scale_length, functionLength, argumentLength]) position,
      getScaleSecurity binderGrade argumentGrades position]

/-- **No laundering through a classified function (general, all applications).**  If the function of an
application uses position `i` at `classified`, the application's grade at `i` is `classified` — the
function's secrecy cannot be downgraded by applying it.  The general form of "implicit flow via branch on
secret" (Church-encoded branching is application), generalizing the firing-50 witness
`securitySelectorAppCannotLaunderSelector` from a fixed selector term to EVERY application.  Closes by
`classified + x = classified` (`SecurityGrade.classified_poisons_add`). -/
theorem securityClassifiedFunctionPoisonsApplication
    {context : List (GTypeOver fxSecuritySemiring)} {grades : GradeVectorOver fxSecuritySemiring}
    {function argument : GradedLambda} {resultType : GTypeOver fxSecuritySemiring}
    (typed : HasGradeOver fxSecuritySemiring context grades (.app function argument) resultType)
    (position : Nat) :
    ∃ (binderGrade : SecurityGrade) (domain : GTypeOver fxSecuritySemiring)
      (functionGrades argumentGrades : GradeVectorOver fxSecuritySemiring),
      HasGradeOver fxSecuritySemiring context functionGrades function
          (.arrow binderGrade domain resultType) ∧
        HasGradeOver fxSecuritySemiring context argumentGrades argument domain ∧
          (functionGrades.get position = SecurityGrade.classified →
            grades.get position = SecurityGrade.classified) := by
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    gradeEq⟩ := securityApplicationGradeAt typed position
  refine ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    fun functionClassifiedAt => ?_⟩
  rw [gradeEq, functionClassifiedAt, SecurityGrade.classified_poisons_add]

/-- **No laundering through a classified argument (general, all applications).**  If the binder is
`classified` (the argument is genuinely consumed at secret level) and the argument uses position `i` at
`classified`, the application's grade at `i` is `classified` — a secret argument fed to a secret-consuming
function cannot be downgraded.  Closes by `classified · classified = classified` (`SecurityGrade.mul` by
`rfl`) then `x + classified = classified` (`add_comm` + `classified_poisons_add`). -/
theorem securityClassifiedArgumentPoisonsApplication
    {context : List (GTypeOver fxSecuritySemiring)} {grades : GradeVectorOver fxSecuritySemiring}
    {function argument : GradedLambda} {resultType : GTypeOver fxSecuritySemiring}
    (typed : HasGradeOver fxSecuritySemiring context grades (.app function argument) resultType)
    (position : Nat) :
    ∃ (binderGrade : SecurityGrade) (domain : GTypeOver fxSecuritySemiring)
      (functionGrades argumentGrades : GradeVectorOver fxSecuritySemiring),
      HasGradeOver fxSecuritySemiring context functionGrades function
          (.arrow binderGrade domain resultType) ∧
        HasGradeOver fxSecuritySemiring context argumentGrades argument domain ∧
          (binderGrade = SecurityGrade.classified →
            argumentGrades.get position = SecurityGrade.classified →
            grades.get position = SecurityGrade.classified) := by
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    gradeEq⟩ := securityApplicationGradeAt typed position
  refine ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
    fun binderClassified argumentClassifiedAt => ?_⟩
  rw [gradeEq, binderClassified, argumentClassifiedAt]
  show SecurityGrade.add (functionGrades.get position)
      (SecurityGrade.mul SecurityGrade.classified SecurityGrade.classified) = SecurityGrade.classified
  rw [show SecurityGrade.mul SecurityGrade.classified SecurityGrade.classified
        = SecurityGrade.classified from rfl,
      SecurityGrade.add_comm, SecurityGrade.classified_poisons_add]

end FX1Poly.Modal
