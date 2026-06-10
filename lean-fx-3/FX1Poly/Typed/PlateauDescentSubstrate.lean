import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Core.RawSize

/-! # FX1Poly/Typed/PlateauDescentSubstrate — descent obligations for the plateau master

The pinned-reflection plateau master (the normal-subject, size-recursive reflection that
discharges both piElim head residuals) recurses on (size, normality)-threaded subterms.  This
file ships the per-arm descent obligations:

  * strict size bounds for the recursion cells — `size_lt_lamCell_body` (the piIntro arm),
    `size_lt_appCell_function` / `size_lt_appCell_argument` (the spine arm);
  * child-normality — `appNormal_argumentNormal` (twin of the shipped function lemma, tail
    congruence) and `lamNormal_bodyNormal` (head congruence under the binder shift), via the
    step-lifting contradiction template;
  * the GENERIC mkGen extraction — `isStepNormalForm_childrenNormal` +
    `areStepNormalFormsBool_head`/`_tail` (the genFormationPi telescope leg's normality thread),
    via Bool-conjunct surgery (`rfl`-unfold equations for the two-discriminant mutual match —
    `dsimp only` cannot reduce it — then `Bool.true_and`/`false_and`/`not_*` rewrites; all
    rfl-lemmas, propext-clean).

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- A λ's body is strictly smaller than the λ (Church-style: the body is the second child, after the
domain annotation). -/
theorem RawTerm.size_lt_lamCell_body {scope : Nat} (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1)) :
    body.size < (lamCell domainAnn body).size :=
  Nat.lt_trans
    (Nat.lt_trans
      (RawTermChildren.size_lt_childCons_head (scope := scope) (shift := 1) body
        (.childNil : RawTermChildren [] scope))
      (RawTermChildren.size_lt_childCons_tail (scope := scope) (shift := 0) domainAnn
        (.childCons body .childNil : RawTermChildren [1] scope)))
    (Nat.lt_succ_self _)

/-- A λ's domain annotation is strictly smaller than the λ (Church-style: the domain is the FIRST
child, before the body).  The domain twin of `size_lt_lamCell_body`, needed by the guarded piIntro
arm's domain-reflection recursion. -/
theorem RawTerm.size_lt_lamCell_domain {scope : Nat} (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1)) :
    domainAnn.size < (lamCell domainAnn body).size :=
  Nat.lt_trans
    (RawTermChildren.size_lt_childCons_head (scope := scope) (shift := 0) domainAnn
      (.childCons body .childNil : RawTermChildren [1] scope))
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
theorem lamNormal_bodyNormal {scope : Nat} (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1))
    (normal : RawTerm.isStepNormalForm (lamCell domainAnn body)) :
    RawTerm.isStepNormalForm body := by
  refine Decidable.byContradiction (fun notNormal => ?_)
  obtain ⟨reduct, bodyStep⟩ := exists_step_of_not_isStepNormalForm notNormal
  exact RawTerm.isStepNormalForm_blocks_step normal (lamCell domainAnn reduct)
    (Step.cong .gen_lam ()
      (StepChildren.there (parentScope := scope) (headShift := 0) domainAnn
        (StepChildren.here (.childNil : RawTermChildren [] scope) bodyStep)))

/-- **Subterm-of-normal (λ-domain).**  A normal λ has a normal domain annotation: a domain step lifts
via the head congruence at the parent scope, which a normal λ blocks.  The domain twin of
`lamNormal_bodyNormal`, needed by the guarded piIntro arm's domain-reflection recursion. -/
theorem lamNormal_domainNormal {scope : Nat} (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1))
    (normal : RawTerm.isStepNormalForm (lamCell domainAnn body)) :
    RawTerm.isStepNormalForm domainAnn := by
  refine Decidable.byContradiction (fun notNormal => ?_)
  obtain ⟨reduct, domainStep⟩ := exists_step_of_not_isStepNormalForm notNormal
  exact RawTerm.isStepNormalForm_blocks_step normal (lamCell reduct body)
    (Step.cong .gen_lam ()
      (StepChildren.here (.childCons body .childNil : RawTermChildren [1] scope) domainStep))

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
