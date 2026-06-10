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
    eliminator, at its scrutinee position (child 0 for `fst`/`snd`/`natElim`/`natRec`/`listElim`/
    `optionMatch`/`eitherMatch`; child 1 for `idJ`/`idStrictRec`; child 3 — LAST — for the Phase-Z
    `boolElim` whose spine is `(motive, then, else, scrutinee)`).

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
  /-- Reduce the scrutinee of `natElim`. -/
  | scrutineeNatElim {scrutinee scrutineeReduct zeroBranch succBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_natElim ()
          (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil))))
        (.mkGen .gen_natElim ()
          (.childCons scrutineeReduct (.childCons zeroBranch (.childCons succBranch .childNil))))
  /-- Reduce the scrutinee of `natRec`. -/
  | scrutineeNatRec {scrutinee scrutineeReduct zeroBranch succBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_natRec ()
          (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil))))
        (.mkGen .gen_natRec ()
          (.childCons scrutineeReduct (.childCons zeroBranch (.childCons succBranch .childNil))))
  /-- Reduce the scrutinee of `listElim`. -/
  | scrutineeListElim {scrutinee scrutineeReduct nilBranch consBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_listElim ()
          (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))))
        (.mkGen .gen_listElim ()
          (.childCons scrutineeReduct (.childCons nilBranch (.childCons consBranch .childNil))))
  /-- Reduce the scrutinee of `optionMatch`. -/
  | scrutineeOptionMatch {scrutinee scrutineeReduct noneBranch someBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_optionMatch ()
          (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil))))
        (.mkGen .gen_optionMatch ()
          (.childCons scrutineeReduct (.childCons noneBranch (.childCons someBranch .childNil))))
  /-- Reduce the scrutinee of `eitherMatch`. -/
  | scrutineeEitherMatch {scrutinee scrutineeReduct leftBranch rightBranch : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_eitherMatch ()
          (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil))))
        (.mkGen .gen_eitherMatch ()
          (.childCons scrutineeReduct (.childCons leftBranch (.childCons rightBranch .childNil))))
  /-- Reduce the scrutinee (child 1) of `idJ`. -/
  | scrutineeIdJ {baseCase scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_idJ () (.childCons baseCase (.childCons scrutinee .childNil)))
        (.mkGen .gen_idJ () (.childCons baseCase (.childCons scrutineeReduct .childNil)))
  /-- Reduce the scrutinee (child 1) of `idStrictRec`. -/
  | scrutineeIdStrictRec {baseCase scrutinee scrutineeReduct : RawTerm scope} :
      WeakHeadStep scrutinee scrutineeReduct →
      WeakHeadStep
        (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons scrutinee .childNil)))
        (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons scrutineeReduct .childNil)))

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
      exact Step.cong .gen_natElim () (StepChildren.here _ scrutineeToStep)
  | scrutineeNatRec _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_natRec () (StepChildren.here _ scrutineeToStep)
  | scrutineeListElim _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_listElim () (StepChildren.here _ scrutineeToStep)
  | scrutineeOptionMatch _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_optionMatch () (StepChildren.here _ scrutineeToStep)
  | scrutineeEitherMatch _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_eitherMatch () (StepChildren.here _ scrutineeToStep)
  | scrutineeIdJ _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_idJ () (StepChildren.there _ (StepChildren.here _ scrutineeToStep))
  | scrutineeIdStrictRec _scrutineeStep scrutineeToStep =>
      exact Step.cong .gen_idStrictRec () (StepChildren.there _ (StepChildren.here _ scrutineeToStep))

end FX1Poly.Core
