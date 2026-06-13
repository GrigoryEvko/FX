import FX1Poly.Core.IotaHeadStep

/-! # Foundation/PolyCell/Core/WeakHeadStep
    — the full deterministic weak-head reduction (β + ι + scrutinee-congruence)

`HeadStep` captures weak-head β (contract the head β-redex / reduce into the function spine) and
`IotaHeadStep` captures root-ι (contract an eliminator-on-constructor redex).  Neither alone is a
COMPLETE weak-head reduction once eliminators can be typed: an eliminator whose scrutinee is itself
*reducible* — `natRec (someRedex) z s` — is neither `HeadStep`-reducible (`gen_natRec`-rooted, not
`gen_app`) nor `IotaHeadStep`-reducible (the scrutinee is not yet a constructor), yet it is NOT weak-head
normal: weak-head-normalize the scrutinee first, then fire ι.  `WeakHeadStep` is that complete relation:

  * `beta` — contract the head β-redex (as `HeadStep.beta`);
  * `appCongruence` — reduce the FUNCTION of an application by `WeakHeadStep` (recursive: catches a
    function that is itself an eliminator-redex, which `HeadStep`'s β-only congruence misses);
  * `rootIota` — any root-ι step (`IotaHeadStep`);
  * `scrutineeCong<Eliminator>` — reduce the SCRUTINEE of an eliminator by `WeakHeadStep`, one rule per
    eliminator, at its scrutinee position (child 0 for `fst`/`snd`; child 2 — LAST — for the Phase-Z
    `idJ`/`idStrictRec` whose spines are `(motive, baseCase, witness)`; child 3 — LAST — for the Phase-Z
    `boolElim` / `natElim` / `natRec` / `listElim` / `optionMatch` / `eitherMatch` whose spines are
    `(motive, then/zero/nil/none/left, else/succ/cons/some/right, scrutinee)`).

This is the relation a large-elimination-ready dependent reducibility relation dispatches on: the
`neutral` arm's honest guard is `¬ WeakHeadStep` (genuinely stuck — no β, no ι, no reducible scrutinee),
and one `whnfExpand` arm subsumes both `headExpand` and `iotaExpand`.  With `WeakHeadStep` the
weak-head-normal forms are closed under arbitrary internal reduction, which is exactly what makes
conversion-invariance of the reducibility relation UNCONDITIONAL (not merely fragment-restricted).

This brick ships the relation, the no-step-from-λ inversion, and the embedding into full `Step`.

## Zero-axiom verification

A thirteen-constructor inductive `Prop`; `not_from_lam` by `cases` (the β/app/scrutinee constructors are
`gen_app`/eliminator-rooted, the `rootIota` premise is an `IotaHeadStep` on a λ — all impossible by index
unification); `toStep` by forward constructor mapping (`HeadStep`/`IotaHeadStep` β-ι reducts plus the
uniform `Step.cong`/`StepChildren` congruence at each scrutinee position).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Weak-head reduction (complete).**  β at the head, `WeakHeadStep` into the function position, any
root-ι, and `WeakHeadStep` into each eliminator's scrutinee position.  Deterministic by construction (a
term has at most one weak-head redex). -/
inductive WeakHeadStep {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  /-- Head β-contraction.  Church-style: the λ carries a domain annotation as
      its first child; contraction discards it. -/
  | beta {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
      {argument : RawTerm scope} :
      WeakHeadStep
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam ()
              (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        (RawTerm.subst0 body argument)
  /-- Reduce the function of an application (recursive in `WeakHeadStep`). -/
  | appCongruence {function functionReduct argument : RawTerm scope} :
      WeakHeadStep function functionReduct →
      WeakHeadStep
        (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
        (.mkGen .gen_app () (.childCons functionReduct (.childCons argument .childNil)))
  /-- Any root-ι step. -/
  | rootIota {term reduct : RawTerm scope} :
      IotaHeadStep term reduct → WeakHeadStep term reduct
  /-- Reduce the scrutinee of `boolElim` (Phase-Z: scrutinee is the LAST child;
      the motive heads the spine at `scope + 1`). -/
  | scrutineeBoolElim {motive : RawTerm (scope + 1)}
      {scrutinee scrutineeReduct thenBranch elseBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch (.childCons scrutinee .childNil)))))
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch (.childCons scrutineeReduct .childNil)))))
  /-- Reduce the scrutinee of `fst`. -/
  | scrutineeFst {scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_fst () (.childCons scrutinee .childNil))
        (.mkGen .gen_fst () (.childCons scrutineeReduct .childNil))
  /-- Reduce the scrutinee of `snd`. -/
  | scrutineeSnd {scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_snd () (.childCons scrutinee .childNil))
        (.mkGen .gen_snd () (.childCons scrutineeReduct .childNil))
  /-- Reduce the scrutinee of `natElim` (Phase-Z: scrutinee is the LAST child;
      the motive heads the spine at `scope + 1`, succ-branch at `scope + 2`). -/
  | scrutineeNatElim {motive : RawTerm (scope + 1)}
      {scrutinee scrutineeReduct zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons scrutinee .childNil)))))
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons scrutineeReduct .childNil)))))
  /-- Reduce the scrutinee of `natRec` (Phase-Z: scrutinee LAST). -/
  | scrutineeNatRec {motive : RawTerm (scope + 1)}
      {scrutinee scrutineeReduct zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons scrutinee .childNil)))))
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch (.childCons scrutineeReduct .childNil)))))
  /-- Reduce the scrutinee of `listElim` (Phase-Z: scrutinee is the LAST child;
      the motive heads the spine at `scope + 1`). -/
  | scrutineeListElim {motive : RawTerm (scope + 1)}
      {scrutinee scrutineeReduct nilBranch consBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons scrutinee .childNil)))))
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons scrutineeReduct .childNil)))))
  /-- Reduce the scrutinee of `optionMatch` (Phase-Z: scrutinee is the LAST child;
      the motive heads the spine at `scope + 1`). -/
  | scrutineeOptionMatch {motive : RawTerm (scope + 1)}
      {scrutinee scrutineeReduct noneBranch someBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch (.childCons scrutinee .childNil)))))
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch (.childCons scrutineeReduct .childNil)))))
  /-- Reduce the scrutinee of `eitherMatch` (Phase-Z: scrutinee is the LAST child;
      the motive heads the spine at `scope + 1`). -/
  | scrutineeEitherMatch {motive : RawTerm (scope + 1)}
      {scrutinee scrutineeReduct leftBranch rightBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch (.childCons scrutinee .childNil)))))
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch (.childCons scrutineeReduct .childNil)))))
  /-- Reduce the witness scrutinee of `idJ` (Phase-Z: scrutinee is the LAST child
      at child 2; the motive heads the spine at `scope + 2`). -/
  | scrutineeIdJ {motive : RawTerm (scope + 2)}
      {baseCase scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_idJ ()
          (.childCons motive (.childCons baseCase (.childCons scrutinee .childNil))))
        (.mkGen .gen_idJ ()
          (.childCons motive (.childCons baseCase (.childCons scrutineeReduct .childNil))))
  /-- Reduce the witness scrutinee of `idStrictRec` (Phase-Z: scrutinee is the LAST
      child at child 2; the motive heads the spine at `scope + 2`). -/
  | scrutineeIdStrictRec {motive : RawTerm (scope + 2)}
      {baseCase scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_idStrictRec ()
          (.childCons motive (.childCons baseCase (.childCons scrutinee .childNil))))
        (.mkGen .gen_idStrictRec ()
          (.childCons motive (.childCons baseCase (.childCons scrutineeReduct .childNil))))

  /-- **A table-native row fires at the root** — endpoint-β
      (`pathApp(pathLam(body), arg) ↝ subst0 body arg`), carried as the
      row's firing equation so the weak-head strategy tracks the
      canonical table without a per-rule positive decomposition. -/
  | pathBeta {spine : RawTermChildren Generator.gen_pathApp.binderShifts scope}
      {reduct : RawTerm scope}
      (fires : pathBetaIotaRow.firesOn? () spine = some reduct) :
      WeakHeadStep (.mkGen .gen_pathApp () spine) reduct
  /-- Quotient lift on the constructor:
      `quotRec(kernelFn, respectsRel, quotMk(v)) ↝ app(kernelFn, v)`. -/
  | quotRecMk {spine : RawTermChildren Generator.gen_quotRec.binderShifts scope}
      {reduct : RawTerm scope}
      (fires : quotRecMkIotaRow.firesOn? () spine = some reduct) :
      WeakHeadStep (.mkGen .gen_quotRec () spine) reduct
  /-- Dependent quotient eliminator on the constructor:
      `quotElim(depMotive, depKernel, quotMk(v)) ↝ app(depKernel, v)`. -/
  | quotElimMk {spine : RawTermChildren Generator.gen_quotElim.binderShifts scope}
      {reduct : RawTerm scope}
      (fires : quotElimMkIotaRow.firesOn? () spine = some reduct) :
      WeakHeadStep (.mkGen .gen_quotElim () spine) reduct
  /-- Truncation recursor on the constructor:
      `truncRec(kernelFn, truncIntro(v)) ↝ app(kernelFn, v)`. -/
  | truncRecIntro {truncationLevel : Nat}
      {spine : RawTermChildren Generator.gen_truncRec.binderShifts scope}
      {reduct : RawTerm scope}
      (fires : truncRecIntroIotaRow.firesOn? truncationLevel spine = some reduct) :
      WeakHeadStep (.mkGen .gen_truncRec truncationLevel spine) reduct

  /-- Reduce the function of a path application (the endpoint-β scrutinee at
      slot 0), the table-native twin of `appCongruence`. -/
  | pathAppCongruence {function functionReduct argument : RawTerm scope} :
      WeakHeadStep function functionReduct →
      WeakHeadStep
        (.mkGen .gen_pathApp () (.childCons function (.childCons argument .childNil)))
        (.mkGen .gen_pathApp () (.childCons functionReduct (.childCons argument .childNil)))
  /-- Reduce the scrutinee of `quotRec` (slot 2; `kernelFn` / `respectsRel` lead). -/
  | scrutineeQuotRec {kernelFn respectsRel scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_quotRec ()
          (.childCons kernelFn (.childCons respectsRel (.childCons scrutinee .childNil))))
        (.mkGen .gen_quotRec ()
          (.childCons kernelFn (.childCons respectsRel (.childCons scrutineeReduct .childNil))))
  /-- Reduce the scrutinee of `quotElim` (slot 2; `depMotive` / `depKernel` lead). -/
  | scrutineeQuotElim {depMotive depKernel scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_quotElim ()
          (.childCons depMotive (.childCons depKernel (.childCons scrutinee .childNil))))
        (.mkGen .gen_quotElim ()
          (.childCons depMotive (.childCons depKernel (.childCons scrutineeReduct .childNil))))
  /-- Reduce the scrutinee of `truncRec` (slot 1; `kernelFn` leads, level in payload). -/
  | scrutineeTruncRec {truncationLevel : Nat}
      {kernelFn scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_truncRec truncationLevel
          (.childCons kernelFn (.childCons scrutinee .childNil)))
        (.mkGen .gen_truncRec truncationLevel
          (.childCons kernelFn (.childCons scrutineeReduct .childNil)))

/-- A λ-abstraction has no weak-head step: every `WeakHeadStep` constructor concludes an application- or
eliminator-headed subject (the `rootIota` premise an `IotaHeadStep` on the λ, itself impossible). -/
theorem WeakHeadStep.not_from_lam {scope : Nat}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {reduct : RawTerm scope} :
    ¬ WeakHeadStep
        (.mkGen .gen_lam ()
          (.childCons domainAnn (.childCons body .childNil)))
        reduct := by
  intro weakHeadStep
  cases weakHeadStep with
  | rootIota iotaStep => cases iotaStep

/-- A path-λ has no weak-head step (the endpoint-β scrutinee value). -/
theorem WeakHeadStep.not_from_pathLam {scope : Nat}
    {body : RawTerm (scope + 1)} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_pathLam () (.childCons body .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with
  | rootIota iotaStep => cases iotaStep

/-- A quotient-introduction has no weak-head step (the quotient-lift scrutinee value). -/
theorem WeakHeadStep.not_from_quotMk {scope : Nat}
    {value : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_quotMk () (.childCons value .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with
  | rootIota iotaStep => cases iotaStep

/-- A truncation-introduction has no weak-head step (the truncation-recursor scrutinee value); the
introduction carries the truncation level in its payload. -/
theorem WeakHeadStep.not_from_truncIntro {scope : Nat} {level : Nat}
    {value : RawTerm scope} {reduct : RawTerm scope} :
    ¬ WeakHeadStep (.mkGen .gen_truncIntro level (.childCons value .childNil)) reduct := by
  intro weakHeadStep
  cases weakHeadStep with
  | rootIota iotaStep => cases iotaStep

/-- The endpoint-β firing pins its function slot to a path-λ, which has no weak-head step — so the
`pathBeta`-vs-`pathAppCongruence` weak-head overlap is vacuous. -/
theorem pathBetaFunctionNoStep {scope : Nat}
    {function argument reduct functionReduct : RawTerm scope}
    (fires : pathBetaIotaRow.firesOn? ()
        (.childCons function (.childCons argument .childNil)) = some reduct)
    (functionStep : WeakHeadStep function functionReduct) : False := by
  cases function with
  | mkGen functionGenerator functionPayload functionChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases functionPayload
      cases functionChildren with
      | childCons body bodyNil =>
          cases bodyNil
          exact WeakHeadStep.not_from_pathLam functionStep

/-- The quotient-lift firing pins its scrutinee slot to a quotient introduction, which has no weak-head
step — so `quotRecMk`-vs-`scrutineeQuotRec` is vacuous. -/
theorem quotRecScrutineeNoStep {scope : Nat}
    {kernelFn respectsRel scrutinee reduct scrutineeReduct : RawTerm scope}
    (fires : quotRecMkIotaRow.firesOn? ()
        (.childCons kernelFn (.childCons respectsRel (.childCons scrutinee .childNil)))
      = some reduct)
    (scrutineeStep : WeakHeadStep scrutinee scrutineeReduct) : False := by
  cases scrutinee with
  | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineePayload
      cases scrutineeChildren with
      | childCons value valueNil =>
          cases valueNil
          exact WeakHeadStep.not_from_quotMk scrutineeStep

/-- The dependent quotient eliminator firing pins its scrutinee slot to a quotient introduction — so
`quotElimMk`-vs-`scrutineeQuotElim` is vacuous. -/
theorem quotElimScrutineeNoStep {scope : Nat}
    {depMotive depKernel scrutinee reduct scrutineeReduct : RawTerm scope}
    (fires : quotElimMkIotaRow.firesOn? ()
        (.childCons depMotive (.childCons depKernel (.childCons scrutinee .childNil)))
      = some reduct)
    (scrutineeStep : WeakHeadStep scrutinee scrutineeReduct) : False := by
  cases scrutinee with
  | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineePayload
      cases scrutineeChildren with
      | childCons value valueNil =>
          cases valueNil
          exact WeakHeadStep.not_from_quotMk scrutineeStep

/-- The truncation recursor firing pins its scrutinee slot to a truncation introduction — so
`truncRecIntro`-vs-`scrutineeTruncRec` is vacuous. -/
theorem truncRecScrutineeNoStep {scope : Nat} {truncationLevel : Nat}
    {kernelFn scrutinee reduct scrutineeReduct : RawTerm scope}
    (fires : truncRecIntroIotaRow.firesOn? truncationLevel
        (.childCons kernelFn (.childCons scrutinee .childNil)) = some reduct)
    (scrutineeStep : WeakHeadStep scrutinee scrutineeReduct) : False := by
  cases scrutinee with
  | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineeChildren with
      | childCons value valueNil =>
          cases valueNil
          exact WeakHeadStep.not_from_truncIntro scrutineeStep

/-- **Weak-head reduction embeds into full reduction.**  `beta` is `Step.beta`; `appCongruence` and each
`scrutineeCong` are the uniform `Step.cong` congruence at the function / scrutinee child; `rootIota` is
`IotaHeadStep.toStep`.  Through this embedding `WeakHeadStep` inherits subject reduction, strong-
normalization accessibility, and every `Step`-closure property. -/
theorem WeakHeadStep.toStep {scope : Nat} {term reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep term reduct) : Step term reduct := by
  induction weakHeadStep with
  | beta => exact Step.beta
  | appCongruence _functionStep functionToStep =>
      exact Step.cong .gen_app () (StepChildren.here _ functionToStep)
  | rootIota iotaStep => exact iotaStep.toStep
  | scrutineeBoolElim _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_boolElim ()
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep))))
  | scrutineeFst _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_fst () (StepChildren.here _ scrutineeToStep)
  | scrutineeSnd _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_snd () (StepChildren.here _ scrutineeToStep)
  | scrutineeNatElim _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_natElim ()
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep))))
  | scrutineeNatRec _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_natRec ()
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep))))
  | scrutineeListElim _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_listElim ()
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep))))
  | scrutineeOptionMatch _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_optionMatch ()
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep))))
  | scrutineeEitherMatch _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_eitherMatch ()
        (StepChildren.there _
          (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep))))
  | scrutineeIdJ _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_idJ ()
        (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep)))
  | scrutineeIdStrictRec _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_idStrictRec ()
        (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep)))
  | pathBeta fires => exact .tableRedex pathBetaIotaRow_memTable () fires
  | quotRecMk fires => exact .tableRedex quotRecMkIotaRow_memTable () fires
  | quotElimMk fires => exact .tableRedex quotElimMkIotaRow_memTable () fires
  | truncRecIntro fires =>
      exact .tableRedex truncRecIntroIotaRow_memTable _ fires
  | pathAppCongruence _functionStep functionToStep =>
      exact Step.cong .gen_pathApp () (StepChildren.here _ functionToStep)
  | scrutineeQuotRec _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_quotRec ()
        (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep)))
  | scrutineeQuotElim _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_quotElim ()
        (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ scrutineeToStep)))
  | scrutineeTruncRec _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_truncRec _
        (StepChildren.there _ (StepChildren.here _ scrutineeToStep))

end FX1Poly.Core
