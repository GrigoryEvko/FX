import FX1Poly.Modal.GradedTypingGeneric

/-! # FX1Poly/Modal/GradedWeakeningGeneric — generic weakening for `HasGradeOver R` (all graded dimensions)

Weakening — `HasGradeOver R` is stable under `GradedLambda.shift`, inserting a `R.zero` (ghost /
unused) grade for the freshly-inserted binding — is the SAME de Bruijn argument for every dimension.
This file ships that argument ONCE, generic over any `OrderedGradeSemiring`, from the generic judgment
`HasGradeOver R`.

  * `insertTypeAtOver` / `GradeVectorOver.insertAt` — insert a type / a grade at de Bruijn position
    `cutDepth` (parallel insertions: the new binding's type and its inserted `R.zero` grade).
  * The de Bruijn machinery (`length_insertTypeAtOver`, `lookup_some_ltOver`, `lookup_insertTypeAtOver_lt`
    / `_ge`, `insertAt_zero`, `single_insertAt_lt` / `_ge`, `insertAt_scale`, `insertAt_add`) — how
    insertion interacts with length, lookup, the var-rule singleton, scaling, and addition.
  * `hasGradeOver_weakening` — **the weakening lemma**: `HasGradeOver R` survives `GradedLambda.shift`
    at any cut `cutDepth ≤ |Γ|`, inserting a `R.zero` grade.  By induction on the derivation: the var
    case splits below / at-or-above the cut, the λ-case threads the cut to `cutDepth + 1`, the App case
    distributes insertion over the App-scaled grade sum.  This is the de Bruijn weakening lemma the
    generic substitution lemma's λ-case consumes.

The only place the generic version diverges from the usage dimension's concrete proof is the GRADE
ARITHMETIC: `R.add R.zero R.zero` and `R.mul scaleGrade R.zero` do NOT compute for an abstract semiring
(the usage `rfl`s rely on `UsageGrade` reduction), so `insertAt_add` / `insertAt_scale` route through the
`IsLawfulOrderedGradeSemiring` bundle (`zero_add` / `mul_zero`).  The lemma therefore takes a `lawful`
witness; everything else (the lookup / length / insertion structure) is purely structural and
lawfulness-free.

## Zero-axiom verification

`insertTypeAtOver` / `GradeVectorOver.insertAt` are structural recursion; the lookup / length / single
lemmas are structural inductions with `Nat.noConfusion` / `Nat.not_succ_le_zero` on the impossible
arms (no `Nat.succ_ne_zero`, which pulls `propext`); `insertAt_scale` / `insertAt_add` rewrite with the
bundle fields; `hasGradeOver_weakening` is a derivation induction (`if_pos`/`if_neg` to compute `shift`,
`single_insertAt_lt`/`_ge` to relocate the var grade, `insertAt_add`/`insertAt_scale` for the App grade
sum).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (every
declaration probed with `#print axioms` before landing).  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Insert a type at de Bruijn position `cutDepth` in a context (clamps to the end if out of range,
which never arises since the cut is within the context — see the `cutDepth ≤ length` premises). -/
def insertTypeAtOver {R : OrderedGradeSemiring} :
    Nat → GTypeOver R → List (GTypeOver R) → List (GTypeOver R)
  | 0, newType, types => newType :: types
  | _ + 1, newType, [] => [newType]
  | depth + 1, newType, headType :: restTypes => headType :: insertTypeAtOver depth newType restTypes

/-- Insert a grade at position `cutDepth` in a grade vector (parallel to `insertTypeAtOver`). -/
def GradeVectorOver.insertAt {R : OrderedGradeSemiring} :
    Nat → R.Carrier → GradeVectorOver R → GradeVectorOver R
  | 0, grade, vector => .cons grade vector
  | _ + 1, grade, .nil => .cons grade .nil
  | depth + 1, grade, .cons headGrade restGrades =>
      .cons headGrade (GradeVectorOver.insertAt depth grade restGrades)

/-! ## Length + lookup interaction with insertion -/

/-- Insertion grows the context length by exactly one. -/
theorem length_insertTypeAtOver {R : OrderedGradeSemiring} (cutDepth : Nat) (newType : GTypeOver R)
    (types : List (GTypeOver R)) :
    (insertTypeAtOver cutDepth newType types).length = types.length + 1 := by
  induction cutDepth generalizing types with
  | zero => rfl
  | succ depth restIH =>
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show (insertTypeAtOver depth newType restTypes).length + 1 = restTypes.length + 1 + 1
          rw [restIH restTypes]

/-- A successful lookup pins its index inside the context (the var-rule in-range invariant). -/
theorem lookup_some_ltOver {R : OrderedGradeSemiring} :
    ∀ (types : List (GTypeOver R)) (index : Nat) (foundType : GTypeOver R),
      GTypeOver.lookup types index = some foundType → index < types.length
  | [], index, foundType, lookupEq => by
      have reduced : (none : Option (GTypeOver R)) = some foundType := lookupEq
      nomatch reduced
  | _ :: _, 0, _, _ => Nat.succ_pos _
  | _ :: restTypes, index + 1, foundType, lookupEq =>
      Nat.succ_lt_succ (lookup_some_ltOver restTypes index foundType lookupEq)

/-- Lookup below the cut is unaffected by insertion. -/
theorem lookup_insertTypeAtOver_lt {R : OrderedGradeSemiring} (newType : GTypeOver R) :
    ∀ (cutDepth index : Nat) (types : List (GTypeOver R)), index < cutDepth → cutDepth ≤ types.length →
      GTypeOver.lookup (insertTypeAtOver cutDepth newType types) index = GTypeOver.lookup types index
  | 0, _, _, indexLt, _ => absurd indexLt (Nat.not_lt_zero _)
  | depth + 1, 0, types, _, depthLe => by
      cases types with
      | nil => exact absurd depthLe (Nat.not_succ_le_zero _)
      | cons headType restTypes => rfl
  | depth + 1, index + 1, types, indexLt, depthLe => by
      cases types with
      | nil => exact absurd depthLe (Nat.not_succ_le_zero _)
      | cons headType restTypes =>
          show GTypeOver.lookup (insertTypeAtOver depth newType restTypes) index =
            GTypeOver.lookup restTypes index
          exact lookup_insertTypeAtOver_lt newType depth index restTypes
            (Nat.lt_of_succ_lt_succ indexLt) (Nat.le_of_succ_le_succ depthLe)

/-- Lookup at or above the cut shifts by one across insertion. -/
theorem lookup_insertTypeAtOver_ge {R : OrderedGradeSemiring} (newType : GTypeOver R) :
    ∀ (cutDepth index : Nat) (types : List (GTypeOver R)), cutDepth ≤ index →
      GTypeOver.lookup (insertTypeAtOver cutDepth newType types) (index + 1) =
        GTypeOver.lookup types index
  | 0, _, _, _ => rfl
  | depth + 1, 0, _, depthLe => absurd depthLe (Nat.not_succ_le_zero _)
  | depth + 1, index + 1, types, depthLe => by
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show GTypeOver.lookup (insertTypeAtOver depth newType restTypes) (index + 1)
              = GTypeOver.lookup restTypes index
          exact lookup_insertTypeAtOver_ge newType depth index restTypes (Nat.le_of_succ_le_succ depthLe)

/-! ## Grade-vector insertion lemmas -/

/-- Inserting a `R.zero` into the zero (all-ghost) vector yields the one-longer zero vector. -/
theorem GradeVectorOver.insertAt_zero {R : OrderedGradeSemiring} (cutDepth scope : Nat) :
    GradeVectorOver.insertAt cutDepth R.zero (GradeVectorOver.zero R scope) =
      GradeVectorOver.zero R (scope + 1) := by
  induction cutDepth generalizing scope with
  | zero => rfl
  | succ depth restIH =>
      cases scope with
      | zero => rfl
      | succ restScope =>
          exact congrArg (GradeVectorOver.cons R.zero) (restIH restScope)

/-- The var-rule singleton under grade insertion BELOW the cut: marked position unchanged. -/
theorem GradeVectorOver.single_insertAt_lt {R : OrderedGradeSemiring} (grade : R.Carrier) :
    ∀ (cutDepth scope index : Nat), index < cutDepth → index < scope →
      GradeVectorOver.insertAt cutDepth R.zero (GradeVectorOver.single R scope index grade) =
        GradeVectorOver.single R (scope + 1) index grade
  | 0, _, index, indexLtCut, _ => absurd indexLtCut (Nat.not_lt_zero index)
  | _ + 1, 0, index, _, indexLtScope => absurd indexLtScope (Nat.not_lt_zero index)
  | cutDepth + 1, scope + 1, 0, _, _ =>
      congrArg (GradeVectorOver.cons grade) (GradeVectorOver.insertAt_zero cutDepth scope)
  | cutDepth + 1, scope + 1, index + 1, indexLtCut, indexLtScope =>
      congrArg (GradeVectorOver.cons R.zero)
        (GradeVectorOver.single_insertAt_lt grade cutDepth scope index
          (Nat.lt_of_succ_lt_succ indexLtCut) (Nat.lt_of_succ_lt_succ indexLtScope))

/-- The var-rule singleton under grade insertion AT OR ABOVE the cut: marked position shifts by one
(exactly as `shift` shifts the de Bruijn index). -/
theorem GradeVectorOver.single_insertAt_ge {R : OrderedGradeSemiring} (grade : R.Carrier) :
    ∀ (cutDepth scope index : Nat), cutDepth ≤ index → index < scope →
      GradeVectorOver.insertAt cutDepth R.zero (GradeVectorOver.single R scope index grade) =
        GradeVectorOver.single R (scope + 1) (index + 1) grade
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, index, _, indexLtScope => absurd indexLtScope (Nat.not_lt_zero index)
  | cutDepth + 1, _ + 1, 0, cutLeIndex, _ => absurd cutLeIndex (Nat.not_succ_le_zero cutDepth)
  | cutDepth + 1, scope + 1, index + 1, cutLeIndex, indexLtScope =>
      congrArg (GradeVectorOver.cons R.zero)
        (GradeVectorOver.single_insertAt_ge grade cutDepth scope index
          (Nat.le_of_succ_le_succ cutLeIndex) (Nat.lt_of_succ_lt_succ indexLtScope))

/-- Inserting a `R.zero` commutes with scaling (`scaleGrade · R.zero = R.zero` fills the inserted slot;
the only spot that needs the semiring's `mul_zero` law). -/
theorem GradeVectorOver.insertAt_scale {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth : Nat) (scaleGrade : R.Carrier)
    (someVector : GradeVectorOver R) :
    GradeVectorOver.insertAt cutDepth R.zero (GradeVectorOver.scale scaleGrade someVector) =
      GradeVectorOver.scale scaleGrade (GradeVectorOver.insertAt cutDepth R.zero someVector) := by
  induction cutDepth generalizing someVector with
  | zero =>
      show GradeVectorOver.cons R.zero (GradeVectorOver.scale scaleGrade someVector) =
        GradeVectorOver.cons (R.mul scaleGrade R.zero) (GradeVectorOver.scale scaleGrade someVector)
      rw [lawful.mul_zero scaleGrade]
  | succ depth restIH =>
      cases someVector with
      | nil =>
          show GradeVectorOver.cons R.zero GradeVectorOver.nil =
            GradeVectorOver.cons (R.mul scaleGrade R.zero) GradeVectorOver.nil
          rw [lawful.mul_zero scaleGrade]
      | cons headGrade restGrades =>
          exact congrArg (GradeVectorOver.cons (R.mul scaleGrade headGrade)) (restIH restGrades)

/-- Inserting a `R.zero` distributes over pointwise add (the two operands must share a length so
neither truncates differently; the inserted `R.add R.zero R.zero = R.zero` needs the bundle's
`zero_add` — the usage `rfl` relies on `UsageGrade` reduction, which an abstract semiring lacks). -/
theorem GradeVectorOver.insertAt_add {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth : Nat) :
    ∀ (firstVector secondVector : GradeVectorOver R), firstVector.length = secondVector.length →
      GradeVectorOver.insertAt cutDepth R.zero (GradeVectorOver.add firstVector secondVector) =
        GradeVectorOver.add (GradeVectorOver.insertAt cutDepth R.zero firstVector)
          (GradeVectorOver.insertAt cutDepth R.zero secondVector) := by
  induction cutDepth with
  | zero =>
      intro firstVector secondVector _
      show GradeVectorOver.cons R.zero (GradeVectorOver.add firstVector secondVector) =
        GradeVectorOver.cons (R.add R.zero R.zero) (GradeVectorOver.add firstVector secondVector)
      rw [lawful.zero_add R.zero]
  | succ depth restIH =>
      intro firstVector secondVector lengthEq
      cases firstVector with
      | nil =>
          cases secondVector with
          | nil =>
              show GradeVectorOver.cons R.zero GradeVectorOver.nil =
                GradeVectorOver.cons (R.add R.zero R.zero) GradeVectorOver.nil
              rw [lawful.zero_add R.zero]
          | cons _ secondRest =>
              have contra : secondRest.length + 1 = 0 := lengthEq.symm
              exact Nat.noConfusion contra
      | cons firstHead firstRest =>
          cases secondVector with
          | nil =>
              have contra : firstRest.length + 1 = 0 := lengthEq
              exact Nat.noConfusion contra
          | cons secondHead secondRest =>
              have restLengthEq : firstRest.length = secondRest.length := Nat.succ.inj lengthEq
              exact congrArg (GradeVectorOver.cons (R.add firstHead secondHead))
                (restIH firstRest secondRest restLengthEq)

/-! ## Weakening -/

/-- **Weakening**: `HasGradeOver R` is stable under `GradedLambda.shift` at any cut `cutDepth ≤ |Γ|`,
inserting a `R.zero` (ghost / unused) grade for the freshly-inserted binding.  The generic analogue of
`hasUsage_weakening`; by induction on the derivation: the var case splits below / at-or-above the cut
(relocating the var grade via `single_insertAt_lt` / `_ge`), the λ-case threads the cut to
`cutDepth + 1`, the App case distributes insertion over the App-scaled grade sum (`insertAt_add` +
`insertAt_scale`).  The de Bruijn weakening lemma the generic substitution lemma's λ-case consumes. -/
theorem hasGradeOver_weakening {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R} {term : GradedLambda}
    {resultType : GTypeOver R} (typed : HasGradeOver R typeContext grades term resultType) :
    ∀ (cutDepth : Nat) (newBinding : GTypeOver R), cutDepth ≤ typeContext.length →
      HasGradeOver R (insertTypeAtOver cutDepth newBinding typeContext)
        (GradeVectorOver.insertAt cutDepth R.zero grades)
        (GradedLambda.shift cutDepth term) resultType := by
  induction typed with
  | var typeContext index varType lookupOk =>
      intro cutDepth newBinding cutLe
      rcases Nat.lt_or_ge index cutDepth with indexLtCut | indexGeCut
      · have shiftEq : GradedLambda.shift cutDepth (GradedLambda.var index) =
            GradedLambda.var index := by
          show (if index < cutDepth then GradedLambda.var index else GradedLambda.var (index + 1)) =
            GradedLambda.var index
          rw [if_pos indexLtCut]
        rw [shiftEq,
            GradeVectorOver.single_insertAt_lt R.one cutDepth typeContext.length index indexLtCut
              (Nat.lt_of_lt_of_le indexLtCut cutLe),
            ← length_insertTypeAtOver cutDepth newBinding typeContext]
        exact HasGradeOver.var (insertTypeAtOver cutDepth newBinding typeContext) index varType
          (by rw [lookup_insertTypeAtOver_lt newBinding cutDepth index typeContext indexLtCut cutLe];
              exact lookupOk)
      · have shiftEq : GradedLambda.shift cutDepth (GradedLambda.var index)
            = GradedLambda.var (index + 1) := by
          show (if index < cutDepth then GradedLambda.var index else GradedLambda.var (index + 1)) =
            GradedLambda.var (index + 1)
          rw [if_neg (Nat.not_lt.mpr indexGeCut)]
        rw [shiftEq,
            GradeVectorOver.single_insertAt_ge R.one cutDepth typeContext.length index indexGeCut
              (lookup_some_ltOver typeContext index varType lookupOk),
            ← length_insertTypeAtOver cutDepth newBinding typeContext]
        exact HasGradeOver.var (insertTypeAtOver cutDepth newBinding typeContext) (index + 1) varType
          (by rw [lookup_insertTypeAtOver_ge newBinding cutDepth index typeContext indexGeCut];
              exact lookupOk)
  | lam typeContext binderGrade domain codomain outerGrades body _ bodyIH =>
      intro cutDepth newBinding cutLe
      show HasGradeOver R (insertTypeAtOver cutDepth newBinding typeContext)
        (GradeVectorOver.insertAt cutDepth R.zero outerGrades)
        (GradedLambda.lam (GradedLambda.shift (cutDepth + 1) body))
        (GTypeOver.arrow binderGrade domain codomain)
      exact HasGradeOver.lam (insertTypeAtOver cutDepth newBinding typeContext) binderGrade domain
        codomain (GradeVectorOver.insertAt cutDepth R.zero outerGrades)
        (GradedLambda.shift (cutDepth + 1) body)
        (bodyIH (cutDepth + 1) newBinding (Nat.succ_le_succ cutLe))
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro cutDepth newBinding cutLe
      have lenScale : (GradeVectorOver.scale binderGrade argumentGrades).length =
          typeContext.length := by
        rw [GradeVectorOver.scale_length]; exact hasGradeOver_length argumentTyped
      have gradeEq : GradeVectorOver.insertAt cutDepth R.zero
          (GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades)) =
            GradeVectorOver.add (GradeVectorOver.insertAt cutDepth R.zero functionGrades)
              (GradeVectorOver.scale binderGrade
                (GradeVectorOver.insertAt cutDepth R.zero argumentGrades)) := by
        rw [GradeVectorOver.insertAt_add lawful cutDepth functionGrades
              (GradeVectorOver.scale binderGrade argumentGrades)
              (by rw [hasGradeOver_length functionTyped, lenScale]),
            GradeVectorOver.insertAt_scale lawful]
      show HasGradeOver R (insertTypeAtOver cutDepth newBinding typeContext)
        (GradeVectorOver.insertAt cutDepth R.zero
          (GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades)))
        (GradedLambda.app (GradedLambda.shift cutDepth function)
          (GradedLambda.shift cutDepth argument)) codomain
      rw [gradeEq]
      exact HasGradeOver.app (insertTypeAtOver cutDepth newBinding typeContext) binderGrade domain
        codomain (GradeVectorOver.insertAt cutDepth R.zero functionGrades)
        (GradeVectorOver.insertAt cutDepth R.zero argumentGrades)
        (GradedLambda.shift cutDepth function) (GradedLambda.shift cutDepth argument)
        (functionIH cutDepth newBinding cutLe) (argumentIH cutDepth newBinding cutLe)

end FX1Poly.Modal
