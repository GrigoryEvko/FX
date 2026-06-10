import FX1Poly.Typed.ChurchSucc
import FX1Poly.Core.RawTermSubstLiftWeaken

/-! # FX1Poly/Typed/ChurchSuccApplies — the operational successor: `churchSucc n A f x ↝* f (n A f x)`

`ChurchSucc` (#1089) shipped the successor CONSTRUCTOR `churchSucc = λn.λA.λf.λx. f (n A f x)`, proved it a value,
and gave its single β-unfold.  Deferred there was the fully-applied reduction — the SUCCESSOR'S DEFINING
COMPUTATIONAL PROPERTY: applying `churchSucc n` to a type, a step, and a base runs the step exactly ONE MORE time
than `n` does.  This file proves it.

The reduction is four β-steps.  Step 1 (the n-binder) is the shipped `churchSucc_betaUnfold` (its reshape is
`rfl`).  Steps 2–4 are the genuine de Bruijn work the numeral computation (#1009) never needed: `n` is the closed
argument threaded under the binders, so after step 1 it sits under a WEAKEN-TOWER (`weaken³ numeral`) that each
later β must collapse one level (`weaken³ → weaken² → weaken → ∅`).  That collapse is exactly the three shipped
substrate lemmas (`subst_lift_weaken`, `subst_lift_singleton_weaken_weaken`, `weaken_subst_singleton`).

  * **`succ_step2_reshape` / `succ_step3_reshape` / `succ_step4_reshape`** — the per-binder β-contractum reshapes.
    Each `unfold`s `subst0` + the body, `show`s the fully-distributed form (subst distributes over `appCell` and
    `lamCell` by `rfl`, exposing the weaken-tower leaf), then `rw`s the cancellation lemmas; the variable leaves
    close by `rfl`.
  * **`churchSucc_applies` (★)** — `churchSucc n A f x ↝* f (n A f x)` for ALL closed `n, A, f, x`.  The four β-steps
    chained, each lifted through the outer applications via `Step.cong .gen_app`.
  * **`churchSucc_iteratesOneMore` (★)** — `churchSucc (numeral d) A f x ↝* f^(d+1) x`.  Via `churchSucc_applies`
    then the shipped numeral iteration (#1009) lifted through `f ·`: the successor of the `d`-th Church numeral runs
    the step `d+1` times — `churchSucc` genuinely implements `n ↦ n+1` on the numeral encoding.
  * **`churchSuccZero_appliesToOne`** — the depth-0 smoke: `churchSucc (numeral 0) A f x ↝* f x` (one iteration).

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

The reshapes are `unfold` + `show` (defeq distribution) + `rw [subst_lift_weaken / subst_lift_singleton_weaken_weaken
/ weaken_subst_singleton]` + `rfl`.  `churchSucc_applies` chains four `Step.beta`s (via `rw [← reshape]; exact
Step.beta`) lifted by `Step.cong`; `churchSucc_iteratesOneMore` is `StepStar.trans_compose` with
`StepStar.appArgument` over the shipped #1009.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- After substituting `numeral` (var3) + `typeA` (var2): n=weaken² numeral, A=weaken² typeA, f=var1, x=var0. -/
def succBody2 (numeral typeA : RawTerm 0) : RawTerm 2 :=
  appCell (variableCell (⟨1, by decide⟩ : Fin 2))
    (appCell (appCell (appCell (RawTerm.weaken (RawTerm.weaken numeral))
        (RawTerm.weaken (RawTerm.weaken typeA)))
      (variableCell (⟨1, by decide⟩ : Fin 2)))
      (variableCell (⟨0, by decide⟩ : Fin 2)))

/-- After also substituting `handlerF` (var1=f): n=weaken numeral, A=weaken typeA, f=weaken handlerF (head+inner),
x=var0. -/
def succBody1 (numeral typeA handlerF : RawTerm 0) : RawTerm 1 :=
  appCell (RawTerm.weaken handlerF)
    (appCell (appCell (appCell (RawTerm.weaken numeral) (RawTerm.weaken typeA))
      (RawTerm.weaken handlerF))
      (variableCell (⟨0, by decide⟩ : Fin 1)))

/-- Step 2 reshape: substitute `typeA` for the A-binder; `numeral`'s weaken-tower collapses one level. -/
theorem succ_step2_reshape (numeral typeA : RawTerm 0) :
    RawTerm.subst0 (lamCell churchSuccDomainAnn (lamCell churchSuccDomainAnn (succBody3 numeral))) typeA
      = lamCell churchSuccDomainAnn (lamCell churchSuccDomainAnn (succBody2 numeral typeA)) := by
  unfold RawTerm.subst0 churchSuccDomainAnn succBody3
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (appCell
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
        (variableCell (⟨1, by decide⟩ : Fin 3)))
      (appCell (appCell (appCell
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
          (RawTerm.weaken (RawTerm.weaken (RawTerm.weaken numeral))))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
          (variableCell (⟨2, by decide⟩ : Fin 3))))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
          (variableCell (⟨1, by decide⟩ : Fin 3))))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
          (variableCell (⟨0, by decide⟩ : Fin 3))))))
      = lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
          (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (succBody2 numeral typeA))
  unfold succBody2
  rw [RawTerm.subst_lift_weaken, RawTerm.subst_lift_singleton_weaken_weaken]
  rfl

/-- Step 3 reshape: substitute `handlerF` for the f-binder; `numeral` & `typeA` towers each collapse one level. -/
theorem succ_step3_reshape (numeral typeA handlerF : RawTerm 0) :
    RawTerm.subst0 (lamCell churchSuccDomainAnn (succBody2 numeral typeA)) handlerF
      = lamCell churchSuccDomainAnn (succBody1 numeral typeA handlerF) := by
  unfold RawTerm.subst0 churchSuccDomainAnn succBody2
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (appCell
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
        (variableCell (⟨1, by decide⟩ : Fin 2)))
      (appCell (appCell (appCell
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
          (RawTerm.weaken (RawTerm.weaken numeral)))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
          (RawTerm.weaken (RawTerm.weaken typeA))))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
          (variableCell (⟨1, by decide⟩ : Fin 2))))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
          (variableCell (⟨0, by decide⟩ : Fin 2)))))
      = lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
          (succBody1 numeral typeA handlerF)
  unfold succBody1
  rw [RawTerm.subst_lift_singleton_weaken_weaken, RawTerm.subst_lift_singleton_weaken_weaken]
  rfl

/-- Step 4 reshape: substitute `baseX` for the x-binder; the remaining single-weaken closed args all cancel. -/
theorem succ_step4_reshape (numeral typeA handlerF baseX : RawTerm 0) :
    RawTerm.subst0 (succBody1 numeral typeA handlerF) baseX
      = appCell handlerF (appCell (appCell (appCell numeral typeA) handlerF) baseX) := by
  unfold RawTerm.subst0 succBody1
  show appCell
      (RawTerm.subst (RawTermSubst.singleton baseX) (RawTerm.weaken handlerF))
      (appCell (appCell (appCell
        (RawTerm.subst (RawTermSubst.singleton baseX) (RawTerm.weaken numeral))
        (RawTerm.subst (RawTermSubst.singleton baseX) (RawTerm.weaken typeA)))
        (RawTerm.subst (RawTermSubst.singleton baseX) (RawTerm.weaken handlerF)))
        (RawTerm.subst (RawTermSubst.singleton baseX)
          (variableCell (⟨0, by decide⟩ : Fin 1))))
      = appCell handlerF (appCell (appCell (appCell numeral typeA) handlerF) baseX)
  simp only [RawTerm.weaken_subst_singleton]
  rfl

/-- **★ The operational successor.**  `churchSucc n A f x ↝* f (n A f x)` — the successor applies the step `f`
exactly once more than `n` does.  Four β-steps, each lifted through the outer applications. -/
theorem churchSucc_applies (numeral typeA handlerF baseX : RawTerm 0) :
    StepStar (appCell (appCell (appCell (appCell churchSucc numeral) typeA) handlerF) baseX)
      (appCell handlerF (appCell (appCell (appCell numeral typeA) handlerF) baseX)) := by
  have step2 : Step (appCell (lamCell churchSuccDomainAnn
        (lamCell churchSuccDomainAnn (lamCell churchSuccDomainAnn (succBody3 numeral)))) typeA)
      (lamCell churchSuccDomainAnn (lamCell churchSuccDomainAnn (succBody2 numeral typeA))) := by
    rw [← succ_step2_reshape numeral typeA]; exact Step.beta
  have step3 : Step (appCell (lamCell churchSuccDomainAnn
        (lamCell churchSuccDomainAnn (succBody2 numeral typeA))) handlerF)
      (lamCell churchSuccDomainAnn (succBody1 numeral typeA handlerF)) := by
    rw [← succ_step3_reshape numeral typeA handlerF]; exact Step.beta
  have step4 : Step (appCell (lamCell churchSuccDomainAnn (succBody1 numeral typeA handlerF)) baseX)
      (appCell handlerF (appCell (appCell (appCell numeral typeA) handlerF) baseX)) := by
    rw [← succ_step4_reshape numeral typeA handlerF baseX]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0]) (.childCons baseX .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0]) (.childCons handlerF .childNil)
            (Step.cong .gen_app ()
              (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0]) (.childCons typeA .childNil)
                (churchSucc_betaUnfold numeral)))))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0]) (.childCons baseX .childNil)
          (Step.cong .gen_app ()
            (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0]) (.childCons handlerF .childNil)
              step2))))
      (StepStar.trans
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0]) (.childCons baseX .childNil)
            step3))
        (StepStar.trans step4 (StepStar.refl _))))

/-- **★ The successor iterates one more time.**  `churchSucc (numeral d) A f x ↝* f^(d+1) x` — applying the
successor of the `d`-th numeral runs the step `d+1` times.  `churchSucc` genuinely implements `n ↦ n+1` on the
Church-numeral encoding.  Via `churchSucc_applies` (→ `f (numeral d A f x)`) then the shipped numeral iteration
(#1009) lifted through `f ·`. -/
theorem churchSucc_iteratesOneMore (depth : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStar (appCell (appCell (appCell (appCell churchSucc (churchNumeralLambda depth)) typeA) handlerF) baseX)
      (iteratedApplication (depth + 1) handlerF baseX) :=
  StepStar.trans_compose
    (churchSucc_applies (churchNumeralLambda depth) typeA handlerF baseX)
    (StepStar.appArgument handlerF
      (churchNumeral_appliedReducesToIterate_general depth typeA handlerF baseX))

/-- Smoke at depth 0: `churchSucc (numeral 0) A f x ↝* f x` (one iteration). -/
theorem churchSuccZero_appliesToOne (typeA handlerF baseX : RawTerm 0) :
    StepStar (appCell (appCell (appCell (appCell churchSucc (churchNumeralLambda 0)) typeA) handlerF) baseX)
      (appCell handlerF baseX) :=
  churchSucc_iteratesOneMore 0 typeA handlerF baseX

end FX1Poly.Typed
