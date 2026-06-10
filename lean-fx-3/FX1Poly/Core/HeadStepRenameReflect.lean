import FX1Poly.Core.HeadStep
import FX1Poly.Core.WhnfInterpretationDeterminism
import FX1Poly.Core.CandidateInterpretationRename
import FX1Poly.Core.CompoundRenamePreservation

/-! # Foundation/PolyCell/Core/HeadStepRenameReflect
    — weak-head reduction is REFLECTED by renaming (head-normality is rename-stable)

`HeadStepCommute` proves weak-head reduction is PRESERVED by renaming
(`HeadStep term reduct → HeadStep (rename rho term) (rename rho reduct)`).  The conversion-invariant
interpretation `InterpretsWhnf` additionally needs the CONVERSE for its `neutralApp` arm: a stuck
application stays stuck after renaming.  Equivalently, renaming REFLECTS weak-head steps —

  `HeadStep (rename rho term) reduct → ∃ sourceReduct, HeadStep term sourceReduct`

— so a head-normal term renames to a head-normal term.  The proof is induction on the HeadStep
derivation (the `appCongruence` recursion is discharged by the induction hypothesis) with one
renaming-inversion: `rename rho t` being an application cell forces `t` to be an application cell with
renamed children (and being a λ cell forces `t` to be a λ cell).  Both inversions use that renaming
preserves the head generator (`RawTerm.rename_rootGenerator`) and the `rename_app_reduces` /
`rename_lam_reduces` rfl-distributions; the cell injections are NON-dependent (both sides share the
literal head generator, so no `HEq`).

## Zero-axiom verification

`cases` on the single-constructor `RawTerm` and the concrete-shape `RawTermChildren`, plus `injection`
on same-head cells; induction on the two-constructor `HeadStep`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- Renaming inversion at an application head: if `rename rho t` is an application cell, then `t` is an
application cell whose children rename to the components. -/
theorem RawTerm.rename_eq_app {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {functionReduct argumentReduct : RawTerm targetScope}
    (renameEquation :
      RawTerm.rename rho term =
        .mkGen .gen_app () (.childCons functionReduct (.childCons argumentReduct .childNil))) :
    ∃ (functionTerm argument : RawTerm sourceScope),
      term = .mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)) ∧
        RawTerm.rename rho functionTerm = functionReduct ∧
        RawTerm.rename rho argument = argumentReduct := by
  have rootEquation : term.rootGenerator = Generator.gen_app := by
    have congruence := congrArg RawTerm.rootGenerator renameEquation
    rw [RawTerm.rename_rootGenerator] at congruence
    exact congruence
  match term, rootEquation with
  | .mkGen generator payload children, rootEquation =>
      change generator = Generator.gen_app at rootEquation
      subst rootEquation
      match payload, children with
      | (), .childCons functionTerm (.childCons argument .childNil) =>
          rw [RawTerm.rename_app_reduces] at renameEquation
          injection renameEquation with _scopeEquation _generatorEquation _payloadEquation
            childrenEquation
          injection childrenEquation with _childScopeEquation _childShiftEquation
            _childRestShiftsEquation functionEquation childTailEquation
          injection childTailEquation with _tailScopeEquation _tailShiftEquation
            _tailRestShiftsEquation argumentEquation _nilEquation
          exact ⟨functionTerm, argument, rfl, functionEquation, argumentEquation⟩

/-- Renaming inversion at a λ head: if `rename rho t` is a λ cell, then `t` is a λ cell.

Church-style: the lambda carries a domain annotation as its first child; the
inversion exposes a source domain annotation and a source body. -/
theorem RawTerm.rename_eq_lam {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {domainReduct : RawTerm targetScope}
    {bodyReduct : RawTerm (targetScope + 1)}
    (renameEquation :
      RawTerm.rename rho term =
        .mkGen .gen_lam ()
          (.childCons domainReduct (.childCons bodyReduct .childNil))) :
    ∃ (domainAnn : RawTerm sourceScope) (body : RawTerm (sourceScope + 1)),
      term =
        .mkGen .gen_lam ()
          (.childCons domainAnn (.childCons body .childNil)) := by
  have rootEquation : term.rootGenerator = Generator.gen_lam := by
    have congruence := congrArg RawTerm.rootGenerator renameEquation
    rw [RawTerm.rename_rootGenerator] at congruence
    exact congruence
  match term, rootEquation with
  | .mkGen generator payload children, rootEquation =>
      change generator = Generator.gen_lam at rootEquation
      subst rootEquation
      match payload, children with
      | (), .childCons domainAnn (.childCons body .childNil) =>
          exact ⟨domainAnn, body, rfl⟩

/-- **Renaming reflects weak-head reduction**: if the renamed term takes a weak-head step, the term
itself takes one.  Induction on the HeadStep derivation: the `beta` case inverts the renamed redex back
to a source redex; the `appCongruence` case inverts the application and recurses via the induction
hypothesis on the function. -/
theorem HeadStep.rename_reflects {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {reduct : RawTerm targetScope}
    (headStep : HeadStep (RawTerm.rename rho term) reduct) :
    ∃ sourceReduct : RawTerm sourceScope, HeadStep term sourceReduct := by
  suffices aux : ∀ {renamedTerm reductInner : RawTerm targetScope},
      HeadStep renamedTerm reductInner →
      ∀ {sourceTerm : RawTerm sourceScope}, RawTerm.rename rho sourceTerm = renamedTerm →
        ∃ sourceReduct : RawTerm sourceScope, HeadStep sourceTerm sourceReduct by
    exact aux headStep rfl
  intro renamedTerm reductInner headStepInner
  induction headStepInner with
  | beta =>
      intro sourceTerm renameEquation
      obtain ⟨functionTerm, argument, sourceEquation, functionRename, _argumentRename⟩ :=
        RawTerm.rename_eq_app rho renameEquation
      obtain ⟨domainAnn, body, functionEquation⟩ :=
        RawTerm.rename_eq_lam rho functionRename
      subst sourceEquation
      subst functionEquation
      exact ⟨RawTerm.subst0 body argument, HeadStep.beta⟩
  | appCongruence _functionStep functionInductiveHypothesis =>
      intro sourceTerm renameEquation
      obtain ⟨functionTerm, argument, sourceEquation, functionRename, _argumentRename⟩ :=
        RawTerm.rename_eq_app rho renameEquation
      obtain ⟨functionSourceReduct, functionSourceStep⟩ :=
        functionInductiveHypothesis functionRename
      subst sourceEquation
      exact ⟨.mkGen .gen_app () (.childCons functionSourceReduct (.childCons argument .childNil)),
        HeadStep.appCongruence functionSourceStep⟩

/-- **Renaming preserves head-normality**: if no weak-head step fires on `term`, none fires on
`rename rho term`.  The contrapositive of `rename_reflects` — exactly what `InterpretsWhnf.rename`'s
`neutralApp` arm consumes. -/
theorem HeadStep.rename_preserves_headNormal {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    (headNormal : ∀ reduct : RawTerm sourceScope, ¬ HeadStep term reduct) :
    ∀ reduct : RawTerm targetScope, ¬ HeadStep (RawTerm.rename rho term) reduct := by
  intro reduct renamedStep
  obtain ⟨sourceReduct, sourceStep⟩ := HeadStep.rename_reflects rho renamedStep
  exact headNormal sourceReduct sourceStep

end FX1Poly.Core
