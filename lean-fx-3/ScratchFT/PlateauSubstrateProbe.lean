import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Core.RawSize

/-! Probe: STR-8b plateau-master prerequisite substrate — cell-specific strict size bounds
(lam body, app function/argument) + child-normality lemmas (app argument, lam body, generic
mkGen-children Bool extraction).  The plateau master recurses on (size, normality)-threaded
subterms; these are the per-arm descent obligations. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- A λ's body is strictly smaller than the λ. -/
theorem RawTerm.size_lt_lamCell_body {scope : Nat} (body : RawTerm (scope + 1)) :
    body.size < (lamCell body).size :=
  Nat.lt_trans
    (RawTermChildren.size_lt_childCons_head (scope := scope) (shift := 1) body
      (.childNil : RawTermChildren [] scope))
    (Nat.lt_succ_self _)

/-- An application's function is strictly smaller than the application. -/
theorem RawTerm.size_lt_appCell_function {scope : Nat}
    (functionTerm argument : RawTerm scope) :
    functionTerm.size < (appCell functionTerm argument).size :=
  Nat.lt_trans
    (RawTermChildren.size_lt_childCons_head (scope := scope) (shift := 0) functionTerm
      (.childCons argument .childNil : RawTermChildren [0] scope))
    (Nat.lt_succ_self _)

/-- An application's argument is strictly smaller than the application. -/
theorem RawTerm.size_lt_appCell_argument {scope : Nat}
    (functionTerm argument : RawTerm scope) :
    argument.size < (appCell functionTerm argument).size :=
  Nat.lt_trans
    (Nat.lt_trans
      (RawTermChildren.size_lt_childCons_head (scope := scope) (shift := 0) argument
        (.childNil : RawTermChildren [] scope))
      (RawTermChildren.size_lt_childCons_tail (scope := scope) (shift := 0) functionTerm
        (.childCons argument .childNil : RawTermChildren [0] scope)))
    (Nat.lt_succ_self _)

/-- **Subterm-of-normal (argument).**  A normal application has a normal argument child: an
argument step lifts via the tail congruence, which a normal application blocks.  Twin of the
shipped `appNormal_functionNormal`. -/
theorem appNormal_argumentNormal {scope : Nat} (functionTerm argument : RawTerm scope)
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    RawTerm.isStepNormalForm argument := by
  refine Decidable.byContradiction (fun notNormal => ?_)
  obtain ⟨reduct, argumentStep⟩ := exists_step_of_not_isStepNormalForm notNormal
  exact RawTerm.isStepNormalForm_blocks_step normal (appCell functionTerm reduct)
    (Step.cong .gen_app ()
      (StepChildren.there (parentScope := scope) (headShift := 0) functionTerm
        (StepChildren.here (.childNil : RawTermChildren [] scope) argumentStep)))

/-- **Subterm-of-normal (λ-body).**  A normal λ has a normal body: a body step lifts via the head
congruence under the binder shift, which a normal λ blocks. -/
theorem lamNormal_bodyNormal {scope : Nat} (body : RawTerm (scope + 1))
    (normal : RawTerm.isStepNormalForm (lamCell body)) :
    RawTerm.isStepNormalForm body := by
  refine Decidable.byContradiction (fun notNormal => ?_)
  obtain ⟨reduct, bodyStep⟩ := exists_step_of_not_isStepNormalForm notNormal
  exact RawTerm.isStepNormalForm_blocks_step normal (lamCell reduct)
    (Step.cong .gen_lam ()
      (StepChildren.here (.childNil : RawTermChildren [] scope) bodyStep))

/-- **Generic children-of-normal extraction**: a normal term's child spine is Bool-normal. -/
theorem RawTerm.isStepNormalForm_childrenNormal {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (normal : RawTerm.isStepNormalForm (.mkGen generator payload children)) :
    RawTermChildren.areStepNormalFormsBool children = true := by
  dsimp only [RawTerm.isStepNormalForm, RawTerm.isStepNormalFormBool] at normal
  cases rootValue : RawTerm.hasRootStepSource (.mkGen generator payload children) <;>
    rw [rootValue] at normal
  · rw [Bool.not_false, Bool.true_and] at normal
    exact normal
  · rw [Bool.not_true, Bool.false_and] at normal
    exact Bool.noConfusion normal

/-- **Spine-head extraction**: a Bool-normal cons spine has a normal head. -/
theorem RawTermChildren.areStepNormalFormsBool_head {scope shift : Nat}
    {restShifts : List Nat} {head : RawTerm (scope + shift)}
    {tail : RawTermChildren restShifts scope}
    (normal : RawTermChildren.areStepNormalFormsBool
      (RawTermChildren.childCons head tail) = true) :
    RawTerm.isStepNormalForm head := by
  have unfoldEq : RawTermChildren.areStepNormalFormsBool
      (RawTermChildren.childCons head tail) =
      (RawTerm.isStepNormalFormBool head &&
        RawTermChildren.areStepNormalFormsBool tail) := rfl
  rw [unfoldEq] at normal
  cases headValue : RawTerm.isStepNormalFormBool head <;> rw [headValue] at normal
  · rw [Bool.false_and] at normal
    exact Bool.noConfusion normal
  · exact headValue

/-- **Spine-tail extraction**: a Bool-normal cons spine has a Bool-normal tail. -/
theorem RawTermChildren.areStepNormalFormsBool_tail {scope shift : Nat}
    {restShifts : List Nat} {head : RawTerm (scope + shift)}
    {tail : RawTermChildren restShifts scope}
    (normal : RawTermChildren.areStepNormalFormsBool
      (RawTermChildren.childCons head tail) = true) :
    RawTermChildren.areStepNormalFormsBool tail = true := by
  have unfoldEq : RawTermChildren.areStepNormalFormsBool
      (RawTermChildren.childCons head tail) =
      (RawTerm.isStepNormalFormBool head &&
        RawTermChildren.areStepNormalFormsBool tail) := rfl
  rw [unfoldEq] at normal
  cases headValue : RawTerm.isStepNormalFormBool head <;> rw [headValue] at normal
  · rw [Bool.false_and] at normal
    exact Bool.noConfusion normal
  · rw [Bool.true_and] at normal
    exact normal

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RawTerm.size_lt_lamCell_body
#print axioms FX1Poly.Typed.RawTerm.size_lt_appCell_function
#print axioms FX1Poly.Typed.RawTerm.size_lt_appCell_argument
#print axioms FX1Poly.Typed.appNormal_argumentNormal
#print axioms FX1Poly.Typed.lamNormal_bodyNormal
#print axioms FX1Poly.Typed.RawTerm.isStepNormalForm_childrenNormal
#print axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_head
#print axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_tail
