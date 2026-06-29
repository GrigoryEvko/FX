import FX1Poly.Typed.Dimensions.Graded.AppScaledPathLamGrade
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubst
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubstLift
import FX1Poly.Tier0.Term.Subst.RawTermSubst0

/-! # FX1Poly/Typed/AppScaledSubstMetatheory — the App-SCALED grade's substitution metatheory

`AppScaledPathLamGrade.lean` ships the App-scaled dimension grade `RawTerm.appScaledDimensionGrade`
(now with the `gen_var` LEAF case, so it genuinely TRACKS dimension usage), its congruence-half
preservation modulo the root obligation `AppScaledRootRedexPreserved`, and the head-scalar
`functionBinderGrade`.  This file builds the **root-redex half**: the App-scaled SUBSTITUTION
metatheory that discharges the root contractions, threading `pathLam`'s affineness.

## The App-scaled substitution master (the centerpiece)

The β / endpoint-β rows contract `(λ.body) arg ↝ subst0 body arg`.  The reduct's App-scaled grade is
bounded by the App rule's scaling of the redex, by the **substitution-bound master**
`appScaledDimensionGrade_subst_bound`:

  `le (appScaled (subst σ t) dim)
      (add (appScaled t shiftSource) (mul (appScaled t binderSource) weight)) = true`

under a `σ`-profile relating each substituent's grade to the same `add … (mul … weight)` shape on the
variable cell.  This is an INEQUALITY (not an equality): the App-scaling OVER-approximates because
substitution can only LOWER a function head's binder grade (a `var` head is `omega`; the substituted
term's head may be the affine `pathLam`, `one`).  The mathematical heart is the **`gen_app`
inductive step**: distributing `mul` over `add` (`left_distrib` / `right_distrib`) and reassociating
makes the bound an EQUALITY on four atoms `{Fs, Fb·w, r·As, r·Ab·w}` — see
`appScaledAppNodeReassoc`.

Specialised to `subst0` (`appScaledDimensionGrade_subst0_bound`):

  `le (appScaled (subst0 body arg) dim)
      (add (appScaled body (succ dim)) (mul (appScaled body 0) (appScaled arg dim))) = true`

— the weight is the body's OWN freshest-binder App-scaled grade `appScaled body 0`.

## What the root rows need

  * **β** `app (lam dom body) arg ↝ subst0 body arg`: UNCONDITIONAL.  The `lam` head scalar is `omega`,
    so the redex grade dominates `mul (appScaled body 0) (appScaled arg dim)` for ANY body
    (`appScaled body 0 ≤ omega`) — `appScaledRootBeta_le`.
  * **endpoint-β** `pathApp (pathLam body) i ↝ subst0 body i`: CONDITIONAL on the AFFINE premise
    `appScaled body 0 ≤ one` (the `pathLam` scalar is the affine `one`, not `omega`).  Raw
    preservation is FALSE without it (`body = app (app f (var 0)) (var 0)` forces `appScaled body 0 =
    omega`); `appScaledRootPathBeta_le_ofAffine` threads it.
  * **selection rows** (`boolElim`/`fst`/`snd`/… reduct is a direct spine/scrutinee child): the
    sub-grade child-monotonicity `appScaledDimensionGradeFold_head_le` / `_tail_le` — a child's grade
    is below the generic `add`-fold that contains it.

## Zero-axiom

The grade helpers are full 3×3(×…) enumerations (`rfl` / `Bool.noConfusion`); the rename-image mirror
follows the proven `occurrenceCountAt_rename_image` structure (the `gen_var` leaf routes through
`occurrenceCountAt_rename_image` + `natToUsageGrade`; the `gen_app` arm adds head-preservation of
`functionBinderGrade`); the substitution master is a structural recursion with the algebraic App
reassociation; the row lemmas are grade-arithmetic.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/Typed/Dimensions/Graded/AppScaledSubstMetatheory.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal
open FX1Poly.Tier0.Syntax

/-! ## Grade-arithmetic helpers -/

/-- A grade is below its `add` with anything on the RIGHT: `g ≤ g + h`.  (`add` is the usage addition,
`1 + 1 = ω`, so this is monotonicity of `add` in the absent second summand, not idempotence.) -/
theorem UsageGrade.le_add_right (firstGrade secondGrade : UsageGrade) :
    UsageGrade.le firstGrade (UsageGrade.add firstGrade secondGrade) = true := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- A grade is below its `add` with anything on the LEFT: `h ≤ g + h`. -/
theorem UsageGrade.le_add_left (firstGrade secondGrade : UsageGrade) :
    UsageGrade.le secondGrade (UsageGrade.add firstGrade secondGrade) = true := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- The four-way addition exchange `(a + b) + (c + d) = (a + c) + (b + d)` for usage grades — the
commutative-monoid rearrangement the App reassociation needs. -/
theorem UsageGrade.addExchangeFourWay (firstGrade secondGrade thirdGrade fourthGrade : UsageGrade) :
    UsageGrade.add (UsageGrade.add firstGrade secondGrade)
        (UsageGrade.add thirdGrade fourthGrade)
      = UsageGrade.add (UsageGrade.add firstGrade thirdGrade)
          (UsageGrade.add secondGrade fourthGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> cases fourthGrade <;> rfl

/-- **The `gen_app` inductive-step reassociation (the heart of the substitution master).**  Given the
recursive bounds `Bf = Fs + Fb·w` (function child) and `Ba = As + Ab·w` (argument child), the
App-scaled combination `Bf + r·Ba` equals the App rule's grading of the redex `(Fs + r·As) + (Fb +
r·Ab)·w`.  This is an EQUALITY: `left_distrib`/`right_distrib` expand both sides to the SAME four
atoms `{Fs, Fb·w, r·As, r·Ab·w}` (`mul_assoc` identifies `r·(Ab·w) = (r·Ab)·w`), reassembled by the
four-way exchange. -/
theorem appScaledAppNodeReassoc
    (functionShiftGrade functionBinderUsage argumentShiftGrade argumentBinderUsage
      headScalar weight : UsageGrade) :
    UsageGrade.add
        (UsageGrade.add functionShiftGrade (UsageGrade.mul functionBinderUsage weight))
        (UsageGrade.mul headScalar
          (UsageGrade.add argumentShiftGrade (UsageGrade.mul argumentBinderUsage weight)))
      = UsageGrade.add
          (UsageGrade.add functionShiftGrade (UsageGrade.mul headScalar argumentShiftGrade))
          (UsageGrade.mul
            (UsageGrade.add functionBinderUsage (UsageGrade.mul headScalar argumentBinderUsage))
            weight) := by
  rw [UsageGrade.left_distrib, UsageGrade.right_distrib,
    UsageGrade.mul_assoc headScalar argumentBinderUsage weight]
  exact UsageGrade.addExchangeFourWay functionShiftGrade
    (UsageGrade.mul functionBinderUsage weight)
    (UsageGrade.mul headScalar argumentShiftGrade)
    (UsageGrade.mul headScalar (UsageGrade.mul argumentBinderUsage weight))

/-! ## Sub-grade child-monotonicity (the selection-row fact)

A spine child's App-scaled grade is below the generic `add`-fold that contains it — what the SELECTION
rows (`boolElim`/`fst`/`snd`/`natElimZero`/… whose reduct is a direct child of the redex cell) need,
since those eliminators are non-`app` non-`var`, so the redex grade is exactly the generic fold. -/

/-- The head child's grade is below the generic `add`-fold of the whole `childCons` spine. -/
theorem RawTermChildren.appScaledDimensionGradeFold_head_le {scope shift : Nat}
    {restShifts : List Nat} (childHead : RawTerm (scope + shift))
    (childTail : RawTermChildren restShifts scope) (dimension : Fin scope) :
    UsageGrade.le
        (RawTerm.appScaledDimensionGrade childHead
          (RawVarSet.raiseParentPosition shift dimension))
        (RawTermChildren.appScaledDimensionGradeFold
          (.childCons childHead childTail) dimension) = true := by
  rw [RawTermChildren.appScaledDimensionGradeFold_childCons]
  exact UsageGrade.le_add_right _ _

/-- The tail spine's fold is below the generic `add`-fold of the whole `childCons` spine. -/
theorem RawTermChildren.appScaledDimensionGradeFold_tail_le {scope shift : Nat}
    {restShifts : List Nat} (childHead : RawTerm (scope + shift))
    (childTail : RawTermChildren restShifts scope) (dimension : Fin scope) :
    UsageGrade.le
        (RawTermChildren.appScaledDimensionGradeFold childTail dimension)
        (RawTermChildren.appScaledDimensionGradeFold
          (.childCons childHead childTail) dimension) = true := by
  rw [RawTermChildren.appScaledDimensionGradeFold_childCons]
  exact UsageGrade.le_add_left _ _

/-! ## Cell-grade equations for the binder formers (the redex-grade readouts) -/

/-- The App-scaled grade of a `gen_lam` cell `lam dom body` reads `add (appScaled dom dim) (appScaled
body (succ dim))` — the domain annotation plus the body under one binder.  (`gen_lam.binderShifts =
[0, 1]`.) -/
theorem appScaled_lamCell {scope : Nat}
    (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) dimension
      = UsageGrade.add (RawTerm.appScaledDimensionGrade domainAnn dimension)
          (RawTerm.appScaledDimensionGrade body (Fin.succ dimension)) := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_lam ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_lam ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.add
      (RawTerm.appScaledDimensionGrade domainAnn (RawVarSet.raiseParentPosition 0 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade body (RawVarSet.raiseParentPosition 1 dimension))
        UsageGrade.zero)
    = _
  rw [RawVarSet.raiseParentPosition_succ, RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]

/-- The App-scaled grade of a `gen_pathLam` cell `pathLam body` reads `appScaled body (succ dim)` — the
affine interval binder carries NO domain annotation (`gen_pathLam.binderShifts = [1]`). -/
theorem appScaled_pathLamCell {scope : Nat}
    (body : RawTerm (scope + 1)) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade
        (.mkGen .gen_pathLam () (.childCons body .childNil)) dimension
      = RawTerm.appScaledDimensionGrade body (Fin.succ dimension) := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_pathLam ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_pathLam ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.add
      (RawTerm.appScaledDimensionGrade body (RawVarSet.raiseParentPosition 1 dimension))
      UsageGrade.zero = _
  rw [RawVarSet.raiseParentPosition_succ, RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]

/-- The App-scaled grade of a `gen_pathApp` cell `pathApp pathFn arg` reads `add (appScaled pathFn dim)
(appScaled arg dim)` — `gen_pathApp` is NOT `gen_app`, so it takes the generic fold (its head scalar is
not applied; equivalently, `pathLam`'s scalar `one` is the multiplicative identity).  (`binderShifts =
[0, 0]`.) -/
theorem appScaled_pathAppCell {scope : Nat}
    (pathFunction argument : RawTerm scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade
        (.mkGen .gen_pathApp () (.childCons pathFunction (.childCons argument .childNil))) dimension
      = UsageGrade.add (RawTerm.appScaledDimensionGrade pathFunction dimension)
          (RawTerm.appScaledDimensionGrade argument dimension) := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_pathApp ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_pathApp ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.add
      (RawTerm.appScaledDimensionGrade pathFunction (RawVarSet.raiseParentPosition 0 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade argument (RawVarSet.raiseParentPosition 0 dimension))
        UsageGrade.zero) = _
  rw [RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]

/-- The App-scaled grade of a `gen_pair` cell `pair a b` reads `add (appScaled a dim) (appScaled b
dim)`.  (`gen_pair.binderShifts = [0, 0]`.) -/
theorem appScaled_pairCell {scope : Nat}
    (firstComponent secondComponent : RawTerm scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade
        (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
        dimension
      = UsageGrade.add (RawTerm.appScaledDimensionGrade firstComponent dimension)
          (RawTerm.appScaledDimensionGrade secondComponent dimension) := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_pair ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_pair ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.add
      (RawTerm.appScaledDimensionGrade firstComponent (RawVarSet.raiseParentPosition 0 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade secondComponent (RawVarSet.raiseParentPosition 0 dimension))
        UsageGrade.zero) = _
  rw [RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]

/-- `functionBinderGrade (lam …) = omega` — an ordinary `lam`'s parameter is unrestricted. -/
theorem functionBinderGrade_lamCell {scope : Nat}
    (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) :
    RawTerm.functionBinderGrade
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
      = UsageGrade.omega := by
  rw [RawTerm.functionBinderGrade_mkGen,
    if_neg (show Generator.gen_lam ≠ .gen_pathLam from fun headEq => Generator.noConfusion headEq)]

/-! ## The head-scalar is substitution-non-increasing (the App-case ingredient)

The `gen_app` step of the substitution master needs that substituting into a function child can only
LOWER its `functionBinderGrade` scalar: a `gen_var` head reads the conservative `omega`, and the
substituted term's head may be the affine `pathLam` (`one`).  This is exactly WHY the master is an
INEQUALITY rather than an equality, and the ingredient that lets the `gen_app` reassociation
(`appScaledAppNodeReassoc`) close after a `mul_le_mul`. -/

/-- **`functionBinderGrade` never INCREASES under a substitution.**  At a `gen_var` head the scalar is
the conservative top `omega` (dominating the substituent's), so `le … omega` by `le_omega`; at every
other head substitution preserves the generator (`subst_mkGen_of_ne_var`), so the scalar is unchanged
(`le_refl`). -/
theorem RawTerm.functionBinderGrade_subst_le {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (functionTerm : RawTerm sourceScope) :
    UsageGrade.le (RawTerm.functionBinderGrade (RawTerm.subst substitution functionTerm))
      (RawTerm.functionBinderGrade functionTerm) = true := by
  match functionTerm with
  | .mkGen generator payload children =>
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        rw [RawTerm.functionBinderGrade_mkGen,
          if_neg (show Generator.gen_var ≠ .gen_pathLam from fun headEq => Generator.noConfusion headEq)]
        exact UsageGrade.le_omega _
      · rw [RawTerm.subst_mkGen_of_ne_var substitution generatorIsVar payload children,
          RawTerm.functionBinderGrade_mkGen, RawTerm.functionBinderGrade_mkGen]
        exact UsageGrade.le_refl _

/-! ## ★ The App-scaled substitution master (the centerpiece)

The reduct of β / endpoint-β is `subst0 body arg`; its App-scaled grade is bounded by the App rule's
scaling of the dimension in the redex.  `IsAppScaledSubst0Bounded` states exactly that bound (the
weight is the body's OWN freshest-binder App-scaled grade, the structural reading of the App scalar
`r`).  It is an INEQUALITY: the App-scaling over-approximates (substitution can only LOWER a function
head's binder grade), so the reduct's grade sits AT OR BELOW the App-rule grading of the redex. -/

/-- **The App-scaled subst0 bound** (the substitution master, as a statement).  For every body, argument
and dimension, the reduct `subst0 body arg`'s App-scaled grade is below the App-rule grading
`add (appScaled body (succ dim)) (mul (appScaled body 0) (appScaled arg dim))` — body part at the
shifted dimension PLUS the argument part scaled by `var 0`'s App-scaled binder weight in body. -/
def IsAppScaledSubst0Bounded : Prop :=
  ∀ {scope : Nat} (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope),
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body rawArg) dimension)
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade body (Fin.succ dimension))
        (UsageGrade.mul
          (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩)
          (RawTerm.appScaledDimensionGrade rawArg dimension))) = true

/-! The proof of `IsAppScaledSubst0Bounded` generalises over an arbitrary substitution `σ` (with a
two-position `add … (mul … weight)` profile on each substituent's grade) and inducts structurally on
the body, EXACTLY mirroring the proven `occurrenceCountAt_subst_weightProfile` /
`occurrenceCountAt_subst0` route:

  * the `gen_var` LEAF discharges by the profile (its grade routes through the proven occurrence
    machinery);
  * the `gen_app` step is the EQUALITY `appScaledAppNodeReassoc` after a `mul_le_mul` fed by
    `RawTerm.functionBinderGrade_subst_le` (both proven above) — the App-scaling's only inequality
    slack;
  * the generic-fold step distributes `mul … weight` over the spine via `UsageGrade.right_distrib`
    + `UsageGrade.addExchangeFourWay` (the usage-grade twins of `natRightDistribByWeight` /
    `addExchangeFourWay` from the count master).

The remaining bookkeeping is the App-scaled `rename`-image (the leaf via
`occurrenceCountAt_rename_image`, the `gen_app` arm via head-preservation of `functionBinderGrade`),
its `weaken`-succ corollary, and the lift-transport of the profile — the line-for-line analogues of
`RawTermOccurrenceSubst.lean`'s `occurrenceCountAt_rename_image` / `_weaken_succ` /
`lift_hitsWithWeight_succ`.  The two NON-bookkeeping ingredients (the App reassociation and the
head-scalar monotonicity) are discharged here. -/

/-- **The LOOSE substitution bound (weight `omega`), a corollary of the tight master.**  `omega` absorbs
every per-occurrence App-scaling worst case, so this WEAKER bound follows from the tight one by
`le_omega` + `mul_le_mul`.  It is the form β / the recursive iotas (`natSucc`/`listCons`/`idJ` — whose
reduct builds nested `gen_app`) key on: the `omega` slack covers any function-head flip.  Only the
AFFINE endpoint-β needs the tight master's `appScaled body 0` weight rather than `omega`. -/
theorem appScaledDimensionGrade_subst0_looseBound (substBound : IsAppScaledSubst0Bounded)
    {scope : Nat} (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body rawArg) dimension)
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade body (Fin.succ dimension))
        (UsageGrade.mul UsageGrade.omega
          (RawTerm.appScaledDimensionGrade rawArg dimension))) = true := by
  refine UsageGrade.le_trans (substBound body rawArg dimension) ?_
  exact UsageGrade.add_le_add (UsageGrade.le_refl _)
    (UsageGrade.mul_le_mul (UsageGrade.le_omega _) (UsageGrade.le_refl _))

/-! ## The root-redex obligations, threaded through the substitution master

Each lemma takes `IsAppScaledSubst0Bounded` as an explicit premise and proves the root contraction is
App-scaled grade-non-increasing on the CONCRETE redex shape (the `Step` derived-rule shape).  β and the
selection rows are UNCONDITIONAL given the bound; endpoint-β additionally threads the AFFINE premise
`appScaled body 0 ≤ one`. -/

/-- **β is grade-non-increasing (unconditional given the bound).**  `app (lam dom body) arg ↝ subst0
body arg`.  The `lam` head scalar is `omega`, so the redex grade `… + mul omega (appScaled arg dim)`
dominates the bound's `mul (appScaled body 0) (appScaled arg dim)` for ANY body (`appScaled body 0 ≤
omega`). -/
theorem appScaledRootBeta_le (substBound : IsAppScaledSubst0Bounded)
    {scope : Nat} (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) (rawArg : RawTerm scope)
    (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body rawArg) dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons rawArg .childNil))) dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_app, functionBinderGrade_lamCell, appScaled_lamCell]
  refine UsageGrade.le_trans (substBound body rawArg dimension) ?_
  exact UsageGrade.add_le_add
    (UsageGrade.le_add_left _ _)
    (UsageGrade.mul_le_mul (UsageGrade.le_omega _) (UsageGrade.le_refl _))

/-- **Endpoint-β is grade-non-increasing GIVEN affineness.**  `pathApp (pathLam body) i ↝ subst0 body
i`.  The `pathLam` head scalar is the affine `one`, so the redex grade is `add (appScaled body (succ
dim)) (appScaled i dim)`; the bound's `mul (appScaled body 0) (appScaled i dim)` collapses to `≤
appScaled i dim` exactly when the body is AFFINE in its binder (`appScaled body 0 ≤ one`).  Raw
preservation is FALSE without the premise (`body = app (app f (var 0)) (var 0)` forces `appScaled body
0 = omega`). -/
theorem appScaledRootPathBeta_le_ofAffine (substBound : IsAppScaledSubst0Bounded)
    {scope : Nat} (body : RawTerm (scope + 1)) (intervalPoint : RawTerm scope)
    (dimension : Fin scope)
    (bodyIsAffine :
      UsageGrade.le (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩) UsageGrade.one
        = true) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body intervalPoint) dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_pathApp ()
          (.childCons
            (.mkGen .gen_pathLam () (.childCons body .childNil))
            (.childCons intervalPoint .childNil))) dimension) = true := by
  rw [appScaled_pathAppCell, appScaled_pathLamCell]
  refine UsageGrade.le_trans (substBound body intervalPoint dimension) ?_
  refine UsageGrade.add_le_add (UsageGrade.le_refl _) ?_
  refine UsageGrade.le_trans
    (UsageGrade.mul_le_mul bodyIsAffine (UsageGrade.le_refl _)) ?_
  rw [UsageGrade.one_mul]
  exact UsageGrade.le_refl _

/-- **Selection-row schema: `fst (pair a b) ↝ a` is grade-non-increasing (unconditional).**  The
reduct is a direct child of the (non-`app` non-`var`) redex, so its grade is below the generic fold by
sub-grade child-monotonicity.  The representative of every selection row (`boolElim`/`snd`/
`natElimZero`/`listElimNil`/`optionMatchNone`/… — reduct a direct spine/scrutinee child). -/
theorem appScaledRootFstPair_le {scope : Nat}
    (firstComponent secondComponent : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade firstComponent dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_fst ()
          (.childCons
            (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
            .childNil)) dimension) = true := by
  have fstGrade :
      RawTerm.appScaledDimensionGrade
          (.mkGen .gen_fst ()
            (.childCons
              (.mkGen .gen_pair ()
                (.childCons firstComponent (.childCons secondComponent .childNil)))
              .childNil)) dimension
        = RawTerm.appScaledDimensionGrade
            (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
            dimension := by
    rw [RawTerm.appScaledDimensionGrade_nonApp
          (show Generator.gen_fst ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
          (show Generator.gen_fst ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
          (by decide)]
    show UsageGrade.add
        (RawTerm.appScaledDimensionGrade
          (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
          (RawVarSet.raiseParentPosition 0 dimension))
        UsageGrade.zero = _
    rw [RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]
  rw [fstGrade, appScaled_pairCell]
  exact UsageGrade.le_add_right _ _

/-- **Selection-row schema: `snd (pair a b) ↝ b` is grade-non-increasing.**  The mirror of
`appScaledRootFstPair_le` at the second projection: the reduct is the second pair component, below the
generic fold by sub-grade child-monotonicity (`le_add_left` into the second summand). -/
theorem appScaledRootSndPair_le {scope : Nat}
    (firstComponent secondComponent : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade secondComponent dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_snd ()
          (.childCons
            (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
            .childNil)) dimension) = true := by
  have sndGrade :
      RawTerm.appScaledDimensionGrade
          (.mkGen .gen_snd ()
            (.childCons
              (.mkGen .gen_pair ()
                (.childCons firstComponent (.childCons secondComponent .childNil)))
              .childNil)) dimension
        = RawTerm.appScaledDimensionGrade
            (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
            dimension := by
    rw [RawTerm.appScaledDimensionGrade_nonApp
          (show Generator.gen_snd ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
          (show Generator.gen_snd ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
          (by decide)]
    show UsageGrade.add
        (RawTerm.appScaledDimensionGrade
          (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
          (RawVarSet.raiseParentPosition 0 dimension))
        UsageGrade.zero = _
    rw [RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]
  rw [sndGrade, appScaled_pairCell]
  exact UsageGrade.le_add_left _ _

/-- **Selection-row schema: `boolElim … boolTrue ↝ thenBranch` (spine slot 1) is grade-non-increasing.**
The reduct is the cell's spine child at index 1 (shift 0); the cell is non-`app` non-`var` non-recursor,
so its grade is the generic fold, and the child sits below it by `tail_le` (peel the motive) then
`head_le` (the freshest summand).  The representative of the position-1 direct-child selection family
(`natElimZero`/`natRecZero`/`listElimNil`/`optionMatchNone`/`idJRefl`/`idStrictRecRefl`). -/
theorem appScaledRootBoolTrue_le {scope : Nat}
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch scrutinee : RawTerm scope)
    (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade thenBranch dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch (.childCons elseBranch (.childCons scrutinee .childNil)))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_boolElim ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_boolElim ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.le (RawTerm.appScaledDimensionGrade thenBranch dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 1 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade thenBranch (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade elseBranch (RawVarSet.raiseParentPosition 0 dimension))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
            UsageGrade.zero)))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-- **Selection-row schema: `boolElim … boolFalse ↝ elseBranch` (spine slot 2) is grade-non-increasing.**
Position-2 direct-child selection: peel the motive AND the `thenBranch` (two `tail_le`s) before the
`head_le` at `elseBranch`. -/
theorem appScaledRootBoolFalse_le {scope : Nat}
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch scrutinee : RawTerm scope)
    (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade elseBranch dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch (.childCons elseBranch (.childCons scrutinee .childNil)))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_boolElim ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_boolElim ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.le (RawTerm.appScaledDimensionGrade elseBranch dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 1 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade thenBranch (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade elseBranch (RawVarSet.raiseParentPosition 0 dimension))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
            UsageGrade.zero)))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _)
    (UsageGrade.le_trans (UsageGrade.le_add_left _ _) (UsageGrade.le_add_left _ _))

/-- **Selection-row schema: `natElim … natZero ↝ zeroBranch` (spine slot 1) is grade-non-increasing.**
Position-1 direct-child selection at the non-dependent recursor's base case; the `succBranch` (spine
slot 2, shift 2) sits in the dominated tail.  Mirror of `appScaledRootBoolTrue_le` at `gen_natElim`. -/
theorem appScaledRootNatElimZero_le {scope : Nat}
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (scrutinee : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade zeroBranch dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch (.childCons succBranch (.childCons scrutinee .childNil)))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_recursor
        (show Generator.gen_natElim ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_natElim ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  refine UsageGrade.le_trans ?_ (UsageGrade.le_omega_mul _)
  show UsageGrade.le (RawTerm.appScaledDimensionGrade zeroBranch dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 1 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade zeroBranch (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade succBranch (RawVarSet.raiseParentPosition 2 dimension))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
            UsageGrade.zero)))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-- **Selection-row schema: `natRec … natZero ↝ zeroBranch` is grade-non-increasing.**  The
dependent-recursor twin of `appScaledRootNatElimZero_le` at `gen_natRec`. -/
theorem appScaledRootNatRecZero_le {scope : Nat}
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (scrutinee : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade zeroBranch dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch (.childCons succBranch (.childCons scrutinee .childNil)))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_recursor
        (show Generator.gen_natRec ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_natRec ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  refine UsageGrade.le_trans ?_ (UsageGrade.le_omega_mul _)
  show UsageGrade.le (RawTerm.appScaledDimensionGrade zeroBranch dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 1 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade zeroBranch (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade succBranch (RawVarSet.raiseParentPosition 2 dimension))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
            UsageGrade.zero)))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-- **Selection-row schema: `listElim … listNil ↝ nilBranch` (spine slot 1) is grade-non-increasing.**
Position-1 direct-child selection at `gen_listElim` (children `[motive, nilBranch, consBranch,
scrutinee]`). -/
theorem appScaledRootListElimNil_le {scope : Nat}
    (motive : RawTerm (scope + 1)) (nilBranch consBranch scrutinee : RawTerm scope)
    (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade nilBranch dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch (.childCons consBranch (.childCons scrutinee .childNil)))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_recursor
        (show Generator.gen_listElim ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_listElim ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  refine UsageGrade.le_trans ?_ (UsageGrade.le_omega_mul _)
  show UsageGrade.le (RawTerm.appScaledDimensionGrade nilBranch dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 1 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade nilBranch (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade consBranch (RawVarSet.raiseParentPosition 0 dimension))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
            UsageGrade.zero)))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-- **Selection-row schema: `optionMatch … optionNone ↝ noneBranch` (spine slot 1) is
grade-non-increasing.**  Position-1 direct-child selection at `gen_optionMatch`. -/
theorem appScaledRootOptionMatchNone_le {scope : Nat}
    (motive : RawTerm (scope + 1)) (noneBranch someBranch scrutinee : RawTerm scope)
    (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade noneBranch dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil)))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_recursor
        (show Generator.gen_optionMatch ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_optionMatch ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  refine UsageGrade.le_trans ?_ (UsageGrade.le_omega_mul _)
  show UsageGrade.le (RawTerm.appScaledDimensionGrade noneBranch dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 1 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade noneBranch (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade someBranch (RawVarSet.raiseParentPosition 0 dimension))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
            UsageGrade.zero)))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-- **Selection-row schema: `idJ … refl ↝ baseCase` (spine slot 1) is grade-non-increasing.**
Position-1 direct-child selection at `gen_idJ` (three children `[motive, baseCase, scrutinee]`; the
two-binder motive carries shift 2). -/
theorem appScaledRootIdJRefl_le {scope : Nat}
    (motive : RawTerm (scope + 2)) (baseCase scrutinee : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade baseCase dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_idJ ()
          (.childCons motive (.childCons baseCase (.childCons scrutinee .childNil))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_idJ ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_idJ ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.le (RawTerm.appScaledDimensionGrade baseCase dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 2 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade baseCase (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
          UsageGrade.zero))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-- **Selection-row schema: `idStrictRec … refl ↝ baseCase` is grade-non-increasing.**  The
strict-recursor twin of `appScaledRootIdJRefl_le` at `gen_idStrictRec`. -/
theorem appScaledRootIdStrictRecRefl_le {scope : Nat}
    (motive : RawTerm (scope + 2)) (baseCase scrutinee : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade baseCase dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_idStrictRec ()
          (.childCons motive (.childCons baseCase (.childCons scrutinee .childNil))))
        dimension) = true := by
  rw [RawTerm.appScaledDimensionGrade_nonApp
        (show Generator.gen_idStrictRec ≠ .gen_var from fun headEq => Generator.noConfusion headEq)
        (show Generator.gen_idStrictRec ≠ .gen_app from fun headEq => Generator.noConfusion headEq)
        (by decide)]
  show UsageGrade.le (RawTerm.appScaledDimensionGrade baseCase dimension)
    (UsageGrade.add
      (RawTerm.appScaledDimensionGrade motive (RawVarSet.raiseParentPosition 2 dimension))
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade baseCase (RawVarSet.raiseParentPosition 0 dimension))
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade scrutinee (RawVarSet.raiseParentPosition 0 dimension))
          UsageGrade.zero))) = true
  simp only [RawVarSet.raiseParentPosition_zero]
  exact UsageGrade.le_trans (UsageGrade.le_add_right _ _) (UsageGrade.le_add_left _ _)

/-! ## ★ Discharging the substitution master `IsAppScaledSubst0Bounded`

The master is proven by the App-scaled analogue of the count-level
`occurrenceCountAt_subst_weightProfile` / `occurrenceCountAt_subst0` route
(`BetaStablePathLamGrade.lean`).  The pieces, in dependency order:

  1. the App-scaled `rename`-image (a 2-way mutual term/spine equality — `functionBinderGrade` is
     `rename`-invariant, so the App-scaling is exactly preserved), its `weaken`-succ corollary, and the
     `gen_var` arithmetic helpers;
  2. the App-scaled substitution PROFILE (`appScaledHitsWithWeight`) with its one-binder lift transport
     and iterate (mirroring `lift_hitsWithWeight_succ` / `iterateLiftRaw_hitsWithWeight_raised`);
  3. the App-scaled substitution master itself (a 2-way mutual term/spine INEQUALITY — the `gen_app`
     node closes by `appScaledAppNodeReassoc` after a `mul_le_mul` fed by `functionBinderGrade_subst_le`,
     the only inequality slack), and its `subst0` / singleton-profile specialisation. -/

/-- A grade is below ANYTHING via `zero`'s bottom-ness: `zero ≤ g`.  The absent-leaf escape the
profile transport's `var 0` cases use. -/
theorem UsageGrade.zero_le (someGrade : UsageGrade) :
    UsageGrade.le UsageGrade.zero someGrade = true := by
  cases someGrade <;> rfl

/-! ### The App rule's scalar is `rename`-invariant (the rename-image App-node ingredient) -/

/-- **`functionBinderGrade` never CHANGES under a renaming.**  Renaming preserves the head generator
(`rename` of a `gen_var` is a `gen_var`; every other head is rebuilt unchanged by
`rename_mkGen_of_ne_var`), and `functionBinderGrade` reads only the head — so the App scalar is a
renaming INVARIANT.  This is the App-node ingredient of the App-scaled rename-image equality. -/
theorem RawTerm.functionBinderGrade_rename {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) (functionTerm : RawTerm sourceScope) :
    RawTerm.functionBinderGrade (RawTerm.rename someRenaming functionTerm)
      = RawTerm.functionBinderGrade functionTerm := by
  match functionTerm with
  | .mkGen generator payload children =>
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        show RawTerm.functionBinderGrade
            (fold GenAlgebra.canonical someRenaming (.mkGen .gen_var payload children))
          = RawTerm.functionBinderGrade (.mkGen .gen_var payload children)
        dsimp only [fold]
        rw [dif_pos rfl]
        show RawTerm.functionBinderGrade (.mkGen .gen_var (someRenaming payload) .childNil)
          = RawTerm.functionBinderGrade (.mkGen .gen_var payload children)
        rw [RawTerm.functionBinderGrade_mkGen, RawTerm.functionBinderGrade_mkGen,
          if_neg (show Generator.gen_var ≠ .gen_pathLam from fun headEq => Generator.noConfusion headEq)]
      · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
          RawTerm.functionBinderGrade_mkGen, RawTerm.functionBinderGrade_mkGen]

/-- The App-scaled grade of a `gen_app` cell reads the App-node fold (the readout used while threading
the substituted/renamed children through the dispatch). -/
theorem RawTerm.appScaledDimensionGrade_appCell {scope : Nat}
    (payload : Generator.gen_app.payload scope)
    (children : RawTermChildren Generator.gen_app.binderShifts scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade (.mkGen .gen_app payload children) dimension
      = RawTermChildren.appHeadScaledDimensionGrade children dimension := by
  rw [RawTerm.appScaledDimensionGrade_mkGen,
    if_neg (show Generator.gen_app ≠ .gen_var from fun headEq => Generator.noConfusion headEq),
    if_pos rfl]

/-! ### The App-scaled `rename`-image (a 2-way mutual term/spine equality) -/

/-- **Children-spine renaming-image (BOTH folds), threading a size-bounded term callback.**  Given
`termImage` (the App-scaled rename-image for every subterm of size `≤ fuel`), an exact-hit renaming
preserves BOTH the generic `add`-fold (`.1`) and the App-node scaled fold (`.2`) of a child spine whose
size is `≤ fuel`.  Structural recursion on the spine; the head goes through `termImage` (and, for the
App fold, `functionBinderGrade_rename`), the tail recurses.  Taking `termImage` as a callback (rather
than a mutual sibling) sidesteps the dependent-`hits`-argument structural-recursion failure. -/
theorem RawTermChildren.appScaledDimensionGrade_rename_childrenBound {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
    (hits : ∀ candidatePosition : Fin sourceScope,
      someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition)
    (fuel : Nat)
    (termImage : ∀ {subScope subTargetScope : Nat}
      (subRenaming : RawRenaming subScope subTargetScope) (subTerm : RawTerm subScope)
      (subSource : Fin subScope) (subTarget : Fin subTargetScope)
      (subHits : ∀ candidate, subRenaming candidate = subTarget ↔ candidate = subSource),
      RawTerm.size subTerm ≤ fuel →
      RawTerm.appScaledDimensionGrade (RawTerm.rename subRenaming subTerm) subTarget
        = RawTerm.appScaledDimensionGrade subTerm subSource)
    (sizeBound : RawTermChildren.size sourceChildren ≤ fuel) :
    (RawTermChildren.appScaledDimensionGradeFold
        (RawTermChildren.rename someRenaming sourceChildren) targetPosition
      = RawTermChildren.appScaledDimensionGradeFold sourceChildren sourcePosition)
    ∧ (RawTermChildren.appHeadScaledDimensionGrade
        (RawTermChildren.rename someRenaming sourceChildren) targetPosition
      = RawTermChildren.appHeadScaledDimensionGrade sourceChildren sourcePosition) :=
  match binderShifts, sourceChildren with
  | [], .childNil => ⟨rfl, rfl⟩
  | binderShift :: _restShifts, .childCons childHead childTail => by
      have headBound : RawTerm.size childHead ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_head childHead childTail) sizeBound)
      have tailBound : RawTermChildren.size childTail ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_tail childHead childTail) sizeBound)
      have tailImage := RawTermChildren.appScaledDimensionGrade_rename_childrenBound someRenaming
        childTail sourcePosition targetPosition hits fuel termImage tailBound
      refine ⟨?_, ?_⟩
      · show UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (fold GenAlgebra.canonical (iterateLiftRaw someRenaming binderShift) childHead)
              (RawVarSet.raiseParentPosition binderShift targetPosition))
            (RawTermChildren.appScaledDimensionGradeFold
              (foldChildren GenAlgebra.canonical someRenaming childTail) targetPosition)
          = UsageGrade.add
              (RawTerm.appScaledDimensionGrade childHead
                (RawVarSet.raiseParentPosition binderShift sourcePosition))
              (RawTermChildren.appScaledDimensionGradeFold childTail sourcePosition)
        rw [← RawTerm.rename_eq_fold, ← RawTermChildren.rename_eq_foldChildren,
          termImage (iterateLiftRaw someRenaming binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift sourcePosition)
            (RawVarSet.raiseParentPosition binderShift targetPosition)
            (iterateLiftRawHitsRaised hits binderShift) headBound,
          tailImage.1]
      · show UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (fold GenAlgebra.canonical (iterateLiftRaw someRenaming binderShift) childHead)
              (RawVarSet.raiseParentPosition binderShift targetPosition))
            (UsageGrade.mul
              (RawTerm.functionBinderGrade
                (fold GenAlgebra.canonical (iterateLiftRaw someRenaming binderShift) childHead))
              (RawTermChildren.appScaledDimensionGradeFold
                (foldChildren GenAlgebra.canonical someRenaming childTail) targetPosition))
          = UsageGrade.add
              (RawTerm.appScaledDimensionGrade childHead
                (RawVarSet.raiseParentPosition binderShift sourcePosition))
              (UsageGrade.mul
                (RawTerm.functionBinderGrade childHead)
                (RawTermChildren.appScaledDimensionGradeFold childTail sourcePosition))
        rw [← RawTerm.rename_eq_fold, ← RawTermChildren.rename_eq_foldChildren,
          termImage (iterateLiftRaw someRenaming binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift sourcePosition)
            (RawVarSet.raiseParentPosition binderShift targetPosition)
            (iterateLiftRawHitsRaised hits binderShift) headBound,
          RawTerm.functionBinderGrade_rename, tailImage.1]

/-- **The App-scaled rename-image — fuel-bounded form.**  By structural recursion on `fuel`: the
`gen_var` leaf routes through `occurrenceCountAt_rename_image`; the `gen_app` / generic nodes delegate to
`appScaledDimensionGrade_rename_childrenBound`, feeding the fuel induction hypothesis as the size-bounded
term callback. -/
theorem RawTerm.appScaledDimensionGrade_rename_image_fueled :
    ∀ (fuel : Nat) {sourceScope targetScope : Nat}
      (someRenaming : RawRenaming sourceScope targetScope)
      (sourceTerm : RawTerm sourceScope)
      (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
      (hits : ∀ candidatePosition : Fin sourceScope,
        someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition),
      RawTerm.size sourceTerm ≤ fuel →
      RawTerm.appScaledDimensionGrade (RawTerm.rename someRenaming sourceTerm) targetPosition
        = RawTerm.appScaledDimensionGrade sourceTerm sourcePosition := by
  intro fuel
  induction fuel with
  | zero =>
      intro _sourceScope _targetScope _someRenaming sourceTerm _sourcePosition _targetPosition _hits
        sizeBound
      cases sourceTerm with
      | mkGen generator payload children => exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ priorFuel ihFuel =>
      intro _sourceScope _targetScope someRenaming sourceTerm sourcePosition targetPosition hits
        sizeBound
      cases sourceTerm with
      | mkGen generator payload children =>
          by_cases generatorIsVar : generator = .gen_var
          · subst generatorIsVar
            show RawTerm.appScaledDimensionGrade
                (fold GenAlgebra.canonical someRenaming (.mkGen .gen_var payload children))
                targetPosition
              = RawTerm.appScaledDimensionGrade (.mkGen .gen_var payload children) sourcePosition
            dsimp only [fold]
            rw [dif_pos rfl]
            show RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (someRenaming payload) .childNil) targetPosition
              = RawTerm.appScaledDimensionGrade (.mkGen .gen_var payload children) sourcePosition
            rw [RawTerm.appScaledDimensionGrade_var, RawTerm.appScaledDimensionGrade_var]
            exact congrArg natToUsageGrade
              (RawTerm.occurrenceCountAt_rename_image someRenaming
                (.mkGen .gen_var payload children) sourcePosition targetPosition hits)
          · have childrenBound : RawTermChildren.size children ≤ priorFuel :=
              Nat.le_of_succ_le_succ sizeBound
            by_cases generatorIsApp : generator = .gen_app
            · subst generatorIsApp
              rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
                RawTerm.appScaledDimensionGrade_appCell, RawTerm.appScaledDimensionGrade_appCell]
              exact (RawTermChildren.appScaledDimensionGrade_rename_childrenBound someRenaming
                children sourcePosition targetPosition hits priorFuel
                (fun subRenaming subTerm subSource subTarget subHits subBound =>
                  ihFuel subRenaming subTerm subSource subTarget subHits subBound)
                childrenBound).2
            · by_cases generatorIsRecursor : RawTerm.isUnboundedlyDuplicatingRecursor generator
              · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
                  RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                    generatorIsRecursor]
                exact congrArg (UsageGrade.mul UsageGrade.omega)
                  (RawTermChildren.appScaledDimensionGrade_rename_childrenBound someRenaming
                    children sourcePosition targetPosition hits priorFuel
                    (fun subRenaming subTerm subSource subTarget subHits subBound =>
                      ihFuel subRenaming subTerm subSource subTarget subHits subBound)
                    childrenBound).1
              · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
                  RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                    generatorIsRecursor]
                exact (RawTermChildren.appScaledDimensionGrade_rename_childrenBound someRenaming
                  children sourcePosition targetPosition hits priorFuel
                  (fun subRenaming subTerm subSource subTarget subHits subBound =>
                    ihFuel subRenaming subTerm subSource subTarget subHits subBound)
                  childrenBound).1

/-- **Renaming under an EXACT hit preserves the App-scaled dimension grade.**  Instantiates the fuel
form at the term's own size.  At a `gen_var` leaf the grade routes through `occurrenceCountAt_rename_image`;
at a `gen_app` node the App scalar is `rename`-invariant (`functionBinderGrade_rename`), so the
App-scaling is preserved exactly. -/
theorem RawTerm.appScaledDimensionGrade_rename_image {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
    (hits : ∀ candidatePosition : Fin sourceScope,
      someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition) :
    RawTerm.appScaledDimensionGrade (RawTerm.rename someRenaming sourceTerm) targetPosition
      = RawTerm.appScaledDimensionGrade sourceTerm sourcePosition :=
  RawTerm.appScaledDimensionGrade_rename_image_fueled (RawTerm.size sourceTerm) someRenaming
    sourceTerm sourcePosition targetPosition hits (Nat.le_refl _)

/-- **The App-scaled weakening shift primitive.**  `weaken t` at the raised position `Fin.succ p` has
the same App-scaled grade `t` has at `p` — the App-scaled twin of `occurrenceCountAt_weaken_succ`,
discharged via the App-scaled rename-image at the weakening renaming. -/
theorem RawTerm.appScaledDimensionGrade_weaken_succ {scope : Nat}
    (sourceTerm : RawTerm scope) (position : Fin scope) :
    RawTerm.appScaledDimensionGrade (RawTerm.weaken sourceTerm) (Fin.succ position)
      = RawTerm.appScaledDimensionGrade sourceTerm position := by
  rw [RawTerm.weaken_eq_rename]
  exact RawTerm.appScaledDimensionGrade_rename_image RawRenaming.weaken sourceTerm
    position (Fin.succ position)
    (fun candidatePosition => by
      constructor
      · intro weakenHit
        exact Fin.eq_of_val_eq (Nat.succ.inj (congrArg Fin.val weakenHit))
      · intro isSource
        exact Fin.eq_of_val_eq (congrArg (· + 1) (congrArg Fin.val isSource)))

/-! ### `gen_var`-leaf App-scaled grade helpers (the profile-transport arithmetic) -/

/-- A variable cell's App-scaled grade at ITSELF is `one` (the dimension occurs once).  `natToUsageGrade
1 = one` lands the final reduction definitionally. -/
theorem RawTerm.appScaledDimensionGrade_var_self {scope : Nat} (variablePosition : Fin scope) :
    RawTerm.appScaledDimensionGrade (.mkGen .gen_var variablePosition .childNil) variablePosition
      = UsageGrade.one :=
  (RawTerm.appScaledDimensionGrade_var variablePosition .childNil variablePosition).trans
    (congrArg natToUsageGrade (RawTerm.occurrenceCountAt_var_self variablePosition))

/-- A variable cell's App-scaled grade at a DIFFERENT position is `zero` (the dimension is absent).
`natToUsageGrade 0 = zero` lands the final reduction definitionally. -/
theorem RawTerm.appScaledDimensionGrade_var_of_ne {scope : Nat}
    {variablePosition queriedPosition : Fin scope}
    (different : ¬ (queriedPosition = variablePosition)) :
    RawTerm.appScaledDimensionGrade (.mkGen .gen_var variablePosition .childNil) queriedPosition
      = UsageGrade.zero :=
  (RawTerm.appScaledDimensionGrade_var variablePosition .childNil queriedPosition).trans
    (congrArg natToUsageGrade (occurrenceCountAt_var_of_ne different))

/-- `appScaled (var (k+1)) (succ p) = appScaled (var k) p`: the de Bruijn shift on the leaf grade. -/
theorem RawTerm.appScaledDimensionGrade_var_succ {sourceScope : Nat}
    (priorValue : Nat) (priorBound : priorValue < sourceScope)
    (candidateBound : priorValue + 1 < sourceScope + 1) (sourcePosition : Fin sourceScope) :
    RawTerm.appScaledDimensionGrade
        (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
        (Fin.succ sourcePosition)
      = RawTerm.appScaledDimensionGrade
          (.mkGen .gen_var (⟨priorValue, priorBound⟩ : Fin sourceScope) .childNil) sourcePosition := by
  rw [RawTerm.appScaledDimensionGrade_var, RawTerm.appScaledDimensionGrade_var]
  exact congrArg natToUsageGrade
    (occurrenceCountAt_var_succ_eq priorValue priorBound candidateBound sourcePosition).symm

/-! ### The App-scaled substitution profile + its binder transport -/

/-- **A WEIGHTED App-scaled hit profile** for a substitution at `targetPosition`: each substituent
image's App-scaled grade is bounded by the shift indicator PLUS the binder indicator scaled by
`weight` (a `UsageGrade`).  The App-scaled analogue of `RawTermSubst.hitsWithWeight`; an INEQUALITY
because a substituent's function head may LOWER an App scalar (`var` head `omega` → `pathLam` head
`one`). -/
def RawTermSubst.appScaledHitsWithWeight {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope)
    (weight : UsageGrade) : Prop :=
  ∀ candidatePosition : Fin sourceScope,
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (substitution candidatePosition) targetPosition)
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade (.mkGen .gen_var candidatePosition .childNil) shiftSource)
        (UsageGrade.mul
          (RawTerm.appScaledDimensionGrade (.mkGen .gen_var candidatePosition .childNil) binderSource)
          weight)) = true

/-- One binder lift transports a weighted App-scaled profile to the raised positions (same weight):
`var 0` hits no raised source (`zero ≤ …` by `zero_le`); index `k+1` carries the weakened source
substituent whose App-scaled grade at `Fin.succ target` is the un-raised grade
(`appScaledDimensionGrade_weaken_succ`). -/
theorem RawTermSubst.lift_appScaledHitsWithWeight_succ {sourceScope targetScope : Nat}
    {substitution : RawTermSubst sourceScope targetScope}
    {shiftSource binderSource : Fin sourceScope} {targetPosition : Fin targetScope}
    {weight : UsageGrade}
    (profile : RawTermSubst.appScaledHitsWithWeight substitution
      shiftSource binderSource targetPosition weight) :
    RawTermSubst.appScaledHitsWithWeight (RawTermSubst.lift substitution)
      (Fin.succ shiftSource) (Fin.succ binderSource) (Fin.succ targetPosition) weight := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      show UsageGrade.le
          (RawTerm.appScaledDimensionGrade
            (.mkGen .gen_var (⟨0, Nat.zero_lt_succ targetScope⟩ : Fin (targetScope + 1)) .childNil)
            (Fin.succ targetPosition))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
              (Fin.succ shiftSource))
            (UsageGrade.mul
              (RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
                (Fin.succ binderSource))
              weight)) = true
      rw [RawTerm.appScaledDimensionGrade_var_of_ne
            (show ¬ ((Fin.succ targetPosition : Fin (targetScope + 1))
                = ⟨0, Nat.zero_lt_succ targetScope⟩)
              from fun hit => Nat.noConfusion (congrArg Fin.val hit))]
      exact UsageGrade.zero_le _
  | succ priorValue =>
      have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ candidateBound
      show UsageGrade.le
          (RawTerm.appScaledDimensionGrade
            (RawTerm.weaken (substitution ⟨priorValue, priorBound⟩)) (Fin.succ targetPosition))
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
              (Fin.succ shiftSource))
            (UsageGrade.mul
              (RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
                (Fin.succ binderSource))
              weight)) = true
      rw [RawTerm.appScaledDimensionGrade_weaken_succ,
        RawTerm.appScaledDimensionGrade_var_succ priorValue priorBound candidateBound shiftSource,
        RawTerm.appScaledDimensionGrade_var_succ priorValue priorBound candidateBound binderSource]
      exact profile ⟨priorValue, priorBound⟩

/-- Iterated binder lifting transports the weighted App-scaled profile to the raised positions. -/
theorem iterateLift_appScaledHitsWithWeight_raised {sourceScope targetScope : Nat}
    {substitution : RawTermSubst sourceScope targetScope}
    {shiftSource binderSource : Fin sourceScope} {targetPosition : Fin targetScope}
    {weight : UsageGrade}
    (profile : RawTermSubst.appScaledHitsWithWeight substitution
      shiftSource binderSource targetPosition weight) :
    ∀ binderShift : Nat,
      RawTermSubst.appScaledHitsWithWeight (iterateLiftRaw substitution binderShift)
        (RawVarSet.raiseParentPosition binderShift shiftSource)
        (RawVarSet.raiseParentPosition binderShift binderSource)
        (RawVarSet.raiseParentPosition binderShift targetPosition) weight
  | 0 => by
      rw [RawVarSet.raiseParentPosition_zero, RawVarSet.raiseParentPosition_zero,
        RawVarSet.raiseParentPosition_zero]
      exact profile
  | binderShift + 1 => by
      rw [RawVarSet.raiseParentPosition_succ, RawVarSet.raiseParentPosition_succ,
        RawVarSet.raiseParentPosition_succ]
      exact RawTermSubst.lift_appScaledHitsWithWeight_succ
        (iterateLift_appScaledHitsWithWeight_raised profile binderShift)

/-! ### ★ The App-scaled substitution master (a 2-way mutual term/spine INEQUALITY) -/

/-- **Children-spine App-scaled substitution bound (BOTH folds), threading a size-bounded term
callback.**  Given `termBound` (the App-scaled substitution bound for every subterm of size `≤ fuel`), a
weighted profile bounds BOTH the generic `add`-fold (`.1`) and the App-node scaled fold (`.2`) of a
child spine whose size is `≤ fuel`.  The generic fold distributes `mul … weight` over the spine via
`right_distrib` + `addExchangeFourWay`; the App fold closes by `appScaledAppNodeReassoc` after a
`mul_le_mul` fed by `functionBinderGrade_subst_le`.  Structural recursion on the spine. -/
theorem RawTermChildren.appScaledDimensionGrade_subst_childrenBound {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope) (weight : UsageGrade)
    (profile : RawTermSubst.appScaledHitsWithWeight substitution
      shiftSource binderSource targetPosition weight)
    (fuel : Nat)
    (termBound : ∀ {subScope subTargetScope : Nat}
      (subSubstitution : RawTermSubst subScope subTargetScope) (subTerm : RawTerm subScope)
      (subShift subBinder : Fin subScope) (subTarget : Fin subTargetScope) (subWeight : UsageGrade)
      (subProfile : RawTermSubst.appScaledHitsWithWeight subSubstitution
        subShift subBinder subTarget subWeight),
      RawTerm.size subTerm ≤ fuel →
      UsageGrade.le
        (RawTerm.appScaledDimensionGrade (RawTerm.subst subSubstitution subTerm) subTarget)
        (UsageGrade.add (RawTerm.appScaledDimensionGrade subTerm subShift)
          (UsageGrade.mul (RawTerm.appScaledDimensionGrade subTerm subBinder) subWeight)) = true)
    (sizeBound : RawTermChildren.size sourceChildren ≤ fuel) :
    (UsageGrade.le
        (RawTermChildren.appScaledDimensionGradeFold
          (RawTermChildren.subst substitution sourceChildren) targetPosition)
        (UsageGrade.add
          (RawTermChildren.appScaledDimensionGradeFold sourceChildren shiftSource)
          (UsageGrade.mul
            (RawTermChildren.appScaledDimensionGradeFold sourceChildren binderSource) weight)) = true)
    ∧ (UsageGrade.le
        (RawTermChildren.appHeadScaledDimensionGrade
          (RawTermChildren.subst substitution sourceChildren) targetPosition)
        (UsageGrade.add
          (RawTermChildren.appHeadScaledDimensionGrade sourceChildren shiftSource)
          (UsageGrade.mul
            (RawTermChildren.appHeadScaledDimensionGrade sourceChildren binderSource) weight)) = true) :=
  match binderShifts, sourceChildren with
  | [], .childNil => ⟨UsageGrade.zero_le _, UsageGrade.zero_le _⟩
  | binderShift :: _restShifts, .childCons childHead childTail => by
      have headBound : RawTerm.size childHead ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_head childHead childTail) sizeBound)
      have tailBound : RawTermChildren.size childTail ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_tail childHead childTail) sizeBound)
      have tailBoundConj := RawTermChildren.appScaledDimensionGrade_subst_childrenBound substitution
        childTail shiftSource binderSource targetPosition weight profile fuel termBound tailBound
      refine ⟨?_, ?_⟩
      · show UsageGrade.le
            (UsageGrade.add
              (RawTerm.appScaledDimensionGrade
                (fold GenAlgebra.canonical (iterateLiftRaw substitution binderShift) childHead)
                (RawVarSet.raiseParentPosition binderShift targetPosition))
              (RawTermChildren.appScaledDimensionGradeFold
                (foldChildren GenAlgebra.canonical substitution childTail) targetPosition))
            (UsageGrade.add
              (UsageGrade.add
                (RawTerm.appScaledDimensionGrade childHead
                  (RawVarSet.raiseParentPosition binderShift shiftSource))
                (RawTermChildren.appScaledDimensionGradeFold childTail shiftSource))
              (UsageGrade.mul
                (UsageGrade.add
                  (RawTerm.appScaledDimensionGrade childHead
                    (RawVarSet.raiseParentPosition binderShift binderSource))
                  (RawTermChildren.appScaledDimensionGradeFold childTail binderSource))
                weight)) = true
        rw [← RawTerm.subst_eq_fold, ← RawTermChildren.subst_eq_foldChildren]
        refine UsageGrade.le_trans (UsageGrade.add_le_add
          (termBound (iterateLiftRaw substitution binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift shiftSource)
            (RawVarSet.raiseParentPosition binderShift binderSource)
            (RawVarSet.raiseParentPosition binderShift targetPosition) weight
            (iterateLift_appScaledHitsWithWeight_raised profile binderShift) headBound)
          tailBoundConj.1) ?_
        rw [UsageGrade.right_distrib, UsageGrade.addExchangeFourWay]
        exact UsageGrade.le_refl _
      · show UsageGrade.le
            (UsageGrade.add
              (RawTerm.appScaledDimensionGrade
                (fold GenAlgebra.canonical (iterateLiftRaw substitution binderShift) childHead)
                (RawVarSet.raiseParentPosition binderShift targetPosition))
              (UsageGrade.mul
                (RawTerm.functionBinderGrade
                  (fold GenAlgebra.canonical (iterateLiftRaw substitution binderShift) childHead))
                (RawTermChildren.appScaledDimensionGradeFold
                  (foldChildren GenAlgebra.canonical substitution childTail) targetPosition)))
            (UsageGrade.add
              (UsageGrade.add
                (RawTerm.appScaledDimensionGrade childHead
                  (RawVarSet.raiseParentPosition binderShift shiftSource))
                (UsageGrade.mul
                  (RawTerm.functionBinderGrade childHead)
                  (RawTermChildren.appScaledDimensionGradeFold childTail shiftSource)))
              (UsageGrade.mul
                (UsageGrade.add
                  (RawTerm.appScaledDimensionGrade childHead
                    (RawVarSet.raiseParentPosition binderShift binderSource))
                  (UsageGrade.mul
                    (RawTerm.functionBinderGrade childHead)
                    (RawTermChildren.appScaledDimensionGradeFold childTail binderSource)))
                weight)) = true
        rw [← RawTerm.subst_eq_fold, ← RawTermChildren.subst_eq_foldChildren]
        refine UsageGrade.le_trans (UsageGrade.add_le_add
          (termBound (iterateLiftRaw substitution binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift shiftSource)
            (RawVarSet.raiseParentPosition binderShift binderSource)
            (RawVarSet.raiseParentPosition binderShift targetPosition) weight
            (iterateLift_appScaledHitsWithWeight_raised profile binderShift) headBound)
          (UsageGrade.mul_le_mul
            (RawTerm.functionBinderGrade_subst_le (iterateLiftRaw substitution binderShift) childHead)
            tailBoundConj.1)) ?_
        rw [appScaledAppNodeReassoc]
        exact UsageGrade.le_refl _

/-- **★ The App-scaled substitution bound — fuel-bounded form.**  By structural recursion on `fuel`:
the `gen_var` leaf discharges by the profile; the `gen_app` / generic nodes delegate to
`appScaledDimensionGrade_subst_childrenBound`, feeding the fuel induction hypothesis as the size-bounded
term callback. -/
theorem RawTerm.appScaledDimensionGrade_subst_weightProfile_fueled :
    ∀ (fuel : Nat) {sourceScope targetScope : Nat}
      (substitution : RawTermSubst sourceScope targetScope)
      (sourceTerm : RawTerm sourceScope)
      (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope) (weight : UsageGrade)
      (profile : RawTermSubst.appScaledHitsWithWeight substitution
        shiftSource binderSource targetPosition weight),
      RawTerm.size sourceTerm ≤ fuel →
      UsageGrade.le
        (RawTerm.appScaledDimensionGrade (RawTerm.subst substitution sourceTerm) targetPosition)
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade sourceTerm shiftSource)
          (UsageGrade.mul
            (RawTerm.appScaledDimensionGrade sourceTerm binderSource) weight)) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro _sourceScope _targetScope _substitution sourceTerm _shiftSource _binderSource
        _targetPosition _weight _profile sizeBound
      cases sourceTerm with
      | mkGen generator payload children => exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ priorFuel ihFuel =>
      intro _sourceScope _targetScope substitution sourceTerm shiftSource binderSource targetPosition
        weight profile sizeBound
      cases sourceTerm with
      | mkGen generator payload children =>
          by_cases generatorIsVar : generator = .gen_var
          · subst generatorIsVar
            show UsageGrade.le
                (RawTerm.appScaledDimensionGrade
                  (fold GenAlgebra.canonical substitution (.mkGen .gen_var payload children))
                  targetPosition) _ = true
            dsimp only [fold]
            rw [dif_pos rfl]
            exact profile payload
          · have childrenBound : RawTermChildren.size children ≤ priorFuel :=
              Nat.le_of_succ_le_succ sizeBound
            rw [RawTerm.subst_mkGen_of_ne_var substitution generatorIsVar payload children]
            by_cases generatorIsApp : generator = .gen_app
            · subst generatorIsApp
              rw [RawTerm.appScaledDimensionGrade_appCell, RawTerm.appScaledDimensionGrade_appCell,
                RawTerm.appScaledDimensionGrade_appCell]
              exact (RawTermChildren.appScaledDimensionGrade_subst_childrenBound substitution
                children shiftSource binderSource targetPosition weight profile priorFuel
                (fun subSubstitution subTerm subShift subBinder subTarget subWeight subProfile
                    subBound =>
                  ihFuel subSubstitution subTerm subShift subBinder subTarget subWeight subProfile
                    subBound)
                childrenBound).2
            · by_cases generatorIsRecursor : RawTerm.isUnboundedlyDuplicatingRecursor generator
              · rw [RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                    generatorIsRecursor]
                exact UsageGrade.omegaScaledSubstBound
                  (RawTermChildren.appScaledDimensionGrade_subst_childrenBound substitution
                    children shiftSource binderSource targetPosition weight profile priorFuel
                    (fun subSubstitution subTerm subShift subBinder subTarget subWeight subProfile
                        subBound =>
                      ihFuel subSubstitution subTerm subShift subBinder subTarget subWeight
                        subProfile subBound)
                    childrenBound).1
              · rw [RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                    generatorIsRecursor]
                exact (RawTermChildren.appScaledDimensionGrade_subst_childrenBound substitution
                  children shiftSource binderSource targetPosition weight profile priorFuel
                  (fun subSubstitution subTerm subShift subBinder subTarget subWeight subProfile
                      subBound =>
                    ihFuel subSubstitution subTerm subShift subBinder subTarget subWeight subProfile
                      subBound)
                  childrenBound).1

/-- **★ The App-scaled substitution bound.**  Instantiates the fuel form at the term's own size — the
App-scaled analogue of `occurrenceCountAt_subst_weightProfile`, but an INEQUALITY (the App-scaling's
only slack is `functionBinderGrade_subst_le`). -/
theorem RawTerm.appScaledDimensionGrade_subst_weightProfile {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope)
    (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope) (weight : UsageGrade)
    (profile : RawTermSubst.appScaledHitsWithWeight substitution
      shiftSource binderSource targetPosition weight) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst substitution sourceTerm) targetPosition)
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade sourceTerm shiftSource)
        (UsageGrade.mul
          (RawTerm.appScaledDimensionGrade sourceTerm binderSource) weight)) = true :=
  RawTerm.appScaledDimensionGrade_subst_weightProfile_fueled (RawTerm.size sourceTerm) substitution
    sourceTerm shiftSource binderSource targetPosition weight profile (Nat.le_refl _)

/-- **The singleton substitution satisfies the weighted App-scaled profile.**  `singleton arg` at
target `position` has shift source `Fin.succ position`, binder source `var 0`, and weight `arg`'s OWN
App-scaled grade at `position` — the App-scaled twin of `RawTermSubst.singleton_hitsWithWeight`. -/
theorem RawTermSubst.singleton_appScaledHitsWithWeight {scope : Nat}
    (rawArg : RawTerm scope) (position : Fin scope) :
    RawTermSubst.appScaledHitsWithWeight (RawTermSubst.singleton rawArg)
      (Fin.succ position) ⟨0, Nat.succ_pos scope⟩ position
      (RawTerm.appScaledDimensionGrade rawArg position) := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      show UsageGrade.le
          (RawTerm.appScaledDimensionGrade rawArg position)
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil) (Fin.succ position))
            (UsageGrade.mul
              (RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil)
                ⟨0, Nat.succ_pos scope⟩)
              (RawTerm.appScaledDimensionGrade rawArg position))) = true
      have shiftMiss :
          RawTerm.appScaledDimensionGrade
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (Fin.succ position) = UsageGrade.zero :=
        RawTerm.appScaledDimensionGrade_var_of_ne
          (fun hit => Nat.noConfusion (congrArg Fin.val hit))
      have binderHit :
          RawTerm.appScaledDimensionGrade
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)) = UsageGrade.one :=
        RawTerm.appScaledDimensionGrade_var_self ⟨0, candidateBound⟩
      rw [shiftMiss, binderHit, UsageGrade.one_mul, UsageGrade.zero_add]
      exact UsageGrade.le_refl _
  | succ priorValue =>
      have priorBound : priorValue < scope := Nat.lt_of_succ_lt_succ candidateBound
      show UsageGrade.le
          (RawTerm.appScaledDimensionGrade
            (.mkGen .gen_var (⟨priorValue, priorBound⟩ : Fin scope) .childNil) position)
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (scope + 1)) .childNil)
              (Fin.succ position))
            (UsageGrade.mul
              (RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (scope + 1)) .childNil)
                ⟨0, Nat.succ_pos scope⟩)
              (RawTerm.appScaledDimensionGrade rawArg position))) = true
      have binderMiss :
          RawTerm.appScaledDimensionGrade
            (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)) = UsageGrade.zero :=
        RawTerm.appScaledDimensionGrade_var_of_ne
          (fun hit => Nat.noConfusion (congrArg Fin.val hit))
      rw [binderMiss, UsageGrade.zero_mul, UsageGrade.add_zero,
        RawTerm.appScaledDimensionGrade_var_succ priorValue priorBound candidateBound position]
      exact UsageGrade.le_refl _

/-- **★ THE SUBSTITUTION MASTER, DISCHARGED.**  `IsAppScaledSubst0Bounded` proven: instantiate the
weighted App-scaled substitution master at `σ := singleton arg`, shift source `Fin.succ dimension`,
binder source `var 0`, weight `appScaled arg dimension`, with the singleton profile.  `subst0` is
`subst (singleton …)`, so the conclusion lands definitionally. -/
theorem isAppScaledSubst0Bounded_holds : IsAppScaledSubst0Bounded := by
  intro scope body rawArg dimension
  exact RawTerm.appScaledDimensionGrade_subst_weightProfile (RawTermSubst.singleton rawArg) body
    (Fin.succ dimension) ⟨0, Nat.succ_pos scope⟩ dimension
    (RawTerm.appScaledDimensionGrade rawArg dimension)
    (RawTermSubst.singleton_appScaledHitsWithWeight rawArg dimension)

/-- **The tight App-scaled `subst0` bound, hypothesis-free.**  `appScaledDimensionGrade_subst0_bound`
re-exports the master without the `IsAppScaledSubst0Bounded` premise (now discharged). -/
theorem appScaledDimensionGrade_subst0_bound {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body rawArg) dimension)
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade body (Fin.succ dimension))
        (UsageGrade.mul
          (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩)
          (RawTerm.appScaledDimensionGrade rawArg dimension))) = true :=
  isAppScaledSubst0Bounded_holds body rawArg dimension

/-- The LOOSE (`omega`-weight) bound, hypothesis-free. -/
theorem appScaledDimensionGrade_subst0_looseBound_unconditional {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body rawArg) dimension)
      (UsageGrade.add
        (RawTerm.appScaledDimensionGrade body (Fin.succ dimension))
        (UsageGrade.mul UsageGrade.omega
          (RawTerm.appScaledDimensionGrade rawArg dimension))) = true :=
  appScaledDimensionGrade_subst0_looseBound isAppScaledSubst0Bounded_holds body rawArg dimension

/-- **β is grade-non-increasing, hypothesis-free** (the discharged master removes the premise). -/
theorem appScaledRootBeta_le_unconditional {scope : Nat}
    (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) (rawArg : RawTerm scope)
    (dimension : Fin scope) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body rawArg) dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons rawArg .childNil))) dimension) = true :=
  appScaledRootBeta_le isAppScaledSubst0Bounded_holds domainAnn body rawArg dimension

/-- **Endpoint-β is grade-non-increasing GIVEN affineness, hypothesis-free** in the substitution
master (still threads the AFFINE premise `appScaled body 0 ≤ one`, which is genuinely needed). -/
theorem appScaledRootPathBeta_le_ofAffine_unconditional {scope : Nat}
    (body : RawTerm (scope + 1)) (intervalPoint : RawTerm scope) (dimension : Fin scope)
    (bodyIsAffine :
      UsageGrade.le (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩) UsageGrade.one
        = true) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade (RawTerm.subst0 body intervalPoint) dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen .gen_pathApp ()
          (.childCons
            (.mkGen .gen_pathLam () (.childCons body .childNil))
            (.childCons intervalPoint .childNil))) dimension) = true :=
  appScaledRootPathBeta_le_ofAffine isAppScaledSubst0Bounded_holds body intervalPoint dimension
    bodyIsAffine

/-! ## ★ The App-scaled grade DOMINATES the raw count (the count-bridge for consumers)

The App-scaled grade is at least the count's image: `natToUsageGrade (occ t d) ≤ appScaled t d`.  At a
`gen_app` node the App-scaling MULTIPLIES the argument grade by the function's binder grade, which is
always `≥ one` (`gen_pathLam ↦ one`, every other head ↦ `omega`), so the count's plain sum is dominated by
the App-scaled sum.  This is the bridge a consumer needing the RAW affine count uses: from
`appScaled body d ≤ one` derive `occ body d ≤ 1` (`appScaledAffine_impliesCountAffine`). -/

/-- **A grade is below its scaling by ANY function's binder grade.**  `functionBinderGrade` is either
`one` (the affine `gen_pathLam`) or `omega` (every other head), both `≥ one`, so `g ≤ functionBinderGrade
f * g` for every `g`.  The App-node ingredient of the count-domination. -/
theorem UsageGrade.self_le_functionBinderGrade_mul {scope : Nat} (functionTerm : RawTerm scope)
    (someGrade : UsageGrade) :
    UsageGrade.le someGrade
      (UsageGrade.mul (RawTerm.functionBinderGrade functionTerm) someGrade) = true := by
  cases functionTerm with
  | mkGen generator payload children =>
      rw [RawTerm.functionBinderGrade_mkGen]
      by_cases generatorIsPathLam : generator = .gen_pathLam
      · rw [if_pos generatorIsPathLam, UsageGrade.one_mul]
        exact UsageGrade.le_refl _
      · rw [if_neg generatorIsPathLam]
        cases someGrade <;> rfl

/-- **Children-spine count-domination (BOTH folds), threading a size-bounded term callback.**  Given
`termDom` (count-domination for every subterm of size `≤ fuel`), the count's image is below BOTH the
generic `add`-fold (`.1`) and the App-node scaled fold (`.2`) of a child spine whose size is `≤ fuel`.
The generic fold sums (`addHom`); the App fold additionally scales the tail by the head's binder grade
(`self_le_functionBinderGrade_mul`).  Structural recursion on the spine. -/
theorem RawTermChildren.appScaledDimensionGrade_dominatesCount_childrenBound {parentScope : Nat}
    {binderShifts : List Nat} (sourceChildren : RawTermChildren binderShifts parentScope)
    (dimension : Fin parentScope) (fuel : Nat)
    (termDom : ∀ {subScope : Nat} (subTerm : RawTerm subScope) (subDimension : Fin subScope),
      RawTerm.size subTerm ≤ fuel →
      UsageGrade.le (natToUsageGrade (RawTerm.occurrenceCountAt subTerm subDimension))
        (RawTerm.appScaledDimensionGrade subTerm subDimension) = true)
    (sizeBound : RawTermChildren.size sourceChildren ≤ fuel) :
    (UsageGrade.le (natToUsageGrade (RawTermChildren.occurrenceCountAt sourceChildren dimension))
        (RawTermChildren.appScaledDimensionGradeFold sourceChildren dimension) = true)
    ∧ (UsageGrade.le (natToUsageGrade (RawTermChildren.occurrenceCountAt sourceChildren dimension))
        (RawTermChildren.appHeadScaledDimensionGrade sourceChildren dimension) = true) :=
  match binderShifts, sourceChildren with
  | [], .childNil => ⟨by rfl, by rfl⟩
  | binderShift :: _restShifts, .childCons childHead childTail => by
      have headBound : RawTerm.size childHead ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_head childHead childTail) sizeBound)
      have tailBound : RawTermChildren.size childTail ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_tail childHead childTail) sizeBound)
      have tailDom := RawTermChildren.appScaledDimensionGrade_dominatesCount_childrenBound
        childTail dimension fuel termDom tailBound
      have headDom := termDom childHead
        (RawVarSet.raiseParentPosition binderShift dimension) headBound
      refine ⟨?_, ?_⟩
      · show UsageGrade.le
            (natToUsageGrade
              (RawTerm.occurrenceCountAt childHead
                  (RawVarSet.raiseParentPosition binderShift dimension) +
                RawTermChildren.occurrenceCountAt childTail dimension))
            (UsageGrade.add
              (RawTerm.appScaledDimensionGrade childHead
                (RawVarSet.raiseParentPosition binderShift dimension))
              (RawTermChildren.appScaledDimensionGradeFold childTail dimension)) = true
        rw [natToUsageGrade_addHom]
        exact UsageGrade.add_le_add headDom tailDom.1
      · show UsageGrade.le
            (natToUsageGrade
              (RawTerm.occurrenceCountAt childHead
                  (RawVarSet.raiseParentPosition binderShift dimension) +
                RawTermChildren.occurrenceCountAt childTail dimension))
            (UsageGrade.add
              (RawTerm.appScaledDimensionGrade childHead
                (RawVarSet.raiseParentPosition binderShift dimension))
              (UsageGrade.mul (RawTerm.functionBinderGrade childHead)
                (RawTermChildren.appScaledDimensionGradeFold childTail dimension))) = true
        rw [natToUsageGrade_addHom]
        exact UsageGrade.add_le_add headDom
          (UsageGrade.le_trans tailDom.1
            (UsageGrade.self_le_functionBinderGrade_mul childHead _))

/-- **Count-domination — fuel-bounded form.**  Structural recursion on `fuel`: the `gen_var` leaf is an
EQUALITY (`appScaled (var p) d = natToUsageGrade (occ (var p) d)`); the `gen_app` / generic nodes delegate
to `appScaledDimensionGrade_dominatesCount_childrenBound`, feeding the fuel IH as the term callback. -/
theorem RawTerm.appScaledDimensionGrade_dominatesCount_fueled :
    ∀ (fuel : Nat) {scope : Nat} (sourceTerm : RawTerm scope) (dimension : Fin scope),
      RawTerm.size sourceTerm ≤ fuel →
      UsageGrade.le (natToUsageGrade (RawTerm.occurrenceCountAt sourceTerm dimension))
        (RawTerm.appScaledDimensionGrade sourceTerm dimension) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro scope sourceTerm dimension sizeBound
      cases sourceTerm with
      | mkGen generator payload children => exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ priorFuel ihFuel =>
      intro scope sourceTerm dimension sizeBound
      cases sourceTerm with
      | mkGen generator payload children =>
          by_cases generatorIsVar : generator = .gen_var
          · subst generatorIsVar
            rw [RawTerm.appScaledDimensionGrade_var]
            exact UsageGrade.le_refl _
          · have childrenBound : RawTermChildren.size children ≤ priorFuel :=
              Nat.le_of_succ_le_succ sizeBound
            have childrenDom := RawTermChildren.appScaledDimensionGrade_dominatesCount_childrenBound
              children dimension priorFuel
              (fun subTerm subDimension subBound => ihFuel subTerm subDimension subBound)
              childrenBound
            have occEq : RawTerm.occurrenceCountAt (.mkGen generator payload children) dimension
                = RawTermChildren.occurrenceCountAt children dimension := by
              dsimp only [RawTerm.occurrenceCountAt]; rw [dif_neg generatorIsVar]
            by_cases generatorIsApp : generator = .gen_app
            · subst generatorIsApp
              rw [occEq, RawTerm.appScaledDimensionGrade_appCell]
              exact childrenDom.2
            · by_cases generatorIsRecursor : RawTerm.isUnboundedlyDuplicatingRecursor generator
              · rw [occEq, RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                  generatorIsRecursor]
                exact UsageGrade.le_trans childrenDom.1 (UsageGrade.le_omega_mul _)
              · rw [occEq, RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                  generatorIsRecursor]
                exact childrenDom.1

/-- **★ The App-scaled grade dominates the raw count.**  `natToUsageGrade (occ t d) ≤ appScaled t d` —
the App-scaling only ever OVER-counts the dimension (the function binder grade is `≥ one`), so the
count's image sits at or below the App-scaled grade.  Instantiates the fuel form at the term's own size. -/
theorem RawTerm.appScaledDimensionGrade_dominatesCount {scope : Nat}
    (sourceTerm : RawTerm scope) (dimension : Fin scope) :
    UsageGrade.le (natToUsageGrade (RawTerm.occurrenceCountAt sourceTerm dimension))
      (RawTerm.appScaledDimensionGrade sourceTerm dimension) = true :=
  RawTerm.appScaledDimensionGrade_dominatesCount_fueled (RawTerm.size sourceTerm) sourceTerm dimension
    (Nat.le_refl _)

/-- **`natToUsageGrade n ≤ one → n ≤ 1`.**  The reverse of `natToUsageGrade_monotone` at the affine grade:
a count whose image is below `one` is itself `≤ 1` (a count `≥ 2` images to `omega ≰ one`). -/
theorem natToUsageGrade_le_one_impliesCountLeOne :
    ∀ (count : Nat), UsageGrade.le (natToUsageGrade count) UsageGrade.one = true → count ≤ 1
  | 0, _ => Nat.zero_le 1
  | 1, _ => Nat.le_refl 1
  | _ + 2, omegaLeOne => Bool.noConfusion omegaLeOne

/-- **★ The App-scaled affine grade implies the raw affine count.**  From `appScaled body d ≤ one` derive
`occ body d ≤ 1`: the count's image is dominated by `appScaled body d ≤ one`, and a count with image
`≤ one` is `≤ 1`.  The bridge a count-needing consumer (the pathLam inversion's affine surfacing) uses
after the side-condition swap. -/
theorem RawTerm.appScaledAffine_impliesCountAffine {scope : Nat}
    (sourceTerm : RawTerm scope) (dimension : Fin scope)
    (appScaledAffine :
      UsageGrade.le (RawTerm.appScaledDimensionGrade sourceTerm dimension) UsageGrade.one = true) :
    RawTerm.occurrenceCountAt sourceTerm dimension ≤ 1 :=
  natToUsageGrade_le_one_impliesCountLeOne _
    (UsageGrade.le_trans
      (RawTerm.appScaledDimensionGrade_dominatesCount sourceTerm dimension) appScaledAffine)

/-! ## ★ The App-scaled grade transports through a binder-crossing renaming / substitution

The pathLam-intro builders cross the dimension binder via `iterateLiftRaw _ 1`.  After the side-condition
swap their affine premise is `appScaled body 0 ≤ one`, so the substitution / weakening preservation lemmas
must transport the App-SCALED grade at the freshest binder, not the raw count.  Renaming PRESERVES it
exactly (the lift hits `var 0` at `var 0`); substitution can only LOWER it (a function head may flip to
the affine `gen_pathLam`), so substitution gives an inequality. -/

/-- **A renaming that AVOIDS a target position grades that position at `zero`.**  Children-spine form
(BOTH folds), threading a size-bounded term callback: if `someRenaming` never produces `avoidedPosition`,
the renamed spine grades it `zero` — every leaf is at a non-target position (`zero`), and the App-node
scaling of a `zero` tail stays `zero` (`mul _ zero`).  The App-scaled twin of
`occurrenceCountAt_rename_avoided` (children half). -/
theorem RawTermChildren.appScaledDimensionGrade_rename_avoided_childrenBound
    {sourceScope targetScope : Nat} {binderShifts : List Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (avoidedPosition : Fin targetScope)
    (avoids : ∀ candidate, someRenaming candidate ≠ avoidedPosition)
    (fuel : Nat)
    (termAvoid : ∀ {subScope subTargetScope : Nat}
      (subRenaming : RawRenaming subScope subTargetScope) (subTerm : RawTerm subScope)
      (subAvoided : Fin subTargetScope)
      (subAvoids : ∀ candidate, subRenaming candidate ≠ subAvoided),
      RawTerm.size subTerm ≤ fuel →
      RawTerm.appScaledDimensionGrade (RawTerm.rename subRenaming subTerm) subAvoided
        = UsageGrade.zero)
    (sizeBound : RawTermChildren.size sourceChildren ≤ fuel) :
    (RawTermChildren.appScaledDimensionGradeFold
        (RawTermChildren.rename someRenaming sourceChildren) avoidedPosition = UsageGrade.zero)
    ∧ (RawTermChildren.appHeadScaledDimensionGrade
        (RawTermChildren.rename someRenaming sourceChildren) avoidedPosition = UsageGrade.zero) :=
  match binderShifts, sourceChildren with
  | [], .childNil => ⟨rfl, rfl⟩
  | binderShift :: _restShifts, .childCons childHead childTail => by
      have headBound : RawTerm.size childHead ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_head childHead childTail) sizeBound)
      have tailBound : RawTermChildren.size childTail ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le
          (RawTermChildren.size_lt_childCons_tail childHead childTail) sizeBound)
      have tailAvoid := RawTermChildren.appScaledDimensionGrade_rename_avoided_childrenBound
        someRenaming childTail avoidedPosition avoids fuel termAvoid tailBound
      have headAvoid := termAvoid (iterateLiftRaw someRenaming binderShift) childHead
        (RawVarSet.raiseParentPosition binderShift avoidedPosition)
        (iterateLiftRawAvoidsRaised avoids binderShift) headBound
      refine ⟨?_, ?_⟩
      · show UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (fold GenAlgebra.canonical (iterateLiftRaw someRenaming binderShift) childHead)
              (RawVarSet.raiseParentPosition binderShift avoidedPosition))
            (RawTermChildren.appScaledDimensionGradeFold
              (foldChildren GenAlgebra.canonical someRenaming childTail) avoidedPosition)
          = UsageGrade.zero
        rw [← RawTerm.rename_eq_fold, ← RawTermChildren.rename_eq_foldChildren, headAvoid, tailAvoid.1]
        rfl
      · show UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (fold GenAlgebra.canonical (iterateLiftRaw someRenaming binderShift) childHead)
              (RawVarSet.raiseParentPosition binderShift avoidedPosition))
            (UsageGrade.mul
              (RawTerm.functionBinderGrade
                (fold GenAlgebra.canonical (iterateLiftRaw someRenaming binderShift) childHead))
              (RawTermChildren.appScaledDimensionGradeFold
                (foldChildren GenAlgebra.canonical someRenaming childTail) avoidedPosition))
          = UsageGrade.zero
        rw [← RawTerm.rename_eq_fold, ← RawTermChildren.rename_eq_foldChildren, headAvoid,
          tailAvoid.1, UsageGrade.mul_zero]
        rfl

/-- **A renaming that AVOIDS a target position grades that position at `zero`** — fuel-bounded term form.
The `gen_var` leaf grades the renamed variable at the avoided position by `zero` (its image is not the
avoided position); the `gen_app` / generic nodes delegate to the children form. -/
theorem RawTerm.appScaledDimensionGrade_rename_avoided_fueled :
    ∀ (fuel : Nat) {sourceScope targetScope : Nat}
      (someRenaming : RawRenaming sourceScope targetScope) (sourceTerm : RawTerm sourceScope)
      (avoidedPosition : Fin targetScope)
      (avoids : ∀ candidate, someRenaming candidate ≠ avoidedPosition),
      RawTerm.size sourceTerm ≤ fuel →
      RawTerm.appScaledDimensionGrade (RawTerm.rename someRenaming sourceTerm) avoidedPosition
        = UsageGrade.zero := by
  intro fuel
  induction fuel with
  | zero =>
      intro _sourceScope _targetScope _someRenaming sourceTerm _avoidedPosition _avoids sizeBound
      cases sourceTerm with
      | mkGen generator payload children => exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ priorFuel ihFuel =>
      intro _sourceScope _targetScope someRenaming sourceTerm avoidedPosition avoids sizeBound
      cases sourceTerm with
      | mkGen generator payload children =>
          by_cases generatorIsVar : generator = .gen_var
          · subst generatorIsVar
            show RawTerm.appScaledDimensionGrade
                (fold GenAlgebra.canonical someRenaming (.mkGen .gen_var payload children))
                avoidedPosition = UsageGrade.zero
            dsimp only [fold]
            rw [dif_pos rfl]
            show RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (someRenaming payload) .childNil) avoidedPosition = UsageGrade.zero
            exact RawTerm.appScaledDimensionGrade_var_of_ne (fun hit => avoids payload hit.symm)
          · have childrenBound : RawTermChildren.size children ≤ priorFuel :=
              Nat.le_of_succ_le_succ sizeBound
            by_cases generatorIsApp : generator = .gen_app
            · subst generatorIsApp
              rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
                RawTerm.appScaledDimensionGrade_appCell]
              exact (RawTermChildren.appScaledDimensionGrade_rename_avoided_childrenBound someRenaming
                children avoidedPosition avoids priorFuel
                (fun subRenaming subTerm subAvoided subAvoids subBound =>
                  ihFuel subRenaming subTerm subAvoided subAvoids subBound)
                childrenBound).2
            · by_cases generatorIsRecursor : RawTerm.isUnboundedlyDuplicatingRecursor generator
              · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
                  RawTerm.appScaledDimensionGrade_recursor generatorIsVar generatorIsApp
                    generatorIsRecursor,
                  (RawTermChildren.appScaledDimensionGrade_rename_avoided_childrenBound someRenaming
                    children avoidedPosition avoids priorFuel
                    (fun subRenaming subTerm subAvoided subAvoids subBound =>
                      ihFuel subRenaming subTerm subAvoided subAvoids subBound)
                    childrenBound).1,
                  UsageGrade.mul_zero]
              · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children,
                  RawTerm.appScaledDimensionGrade_nonApp generatorIsVar generatorIsApp
                    generatorIsRecursor]
                exact (RawTermChildren.appScaledDimensionGrade_rename_avoided_childrenBound someRenaming
                  children avoidedPosition avoids priorFuel
                  (fun subRenaming subTerm subAvoided subAvoids subBound =>
                    ihFuel subRenaming subTerm subAvoided subAvoids subBound)
                  childrenBound).1

/-- **A weakened term grades the freshest position at `zero`.**  `appScaled (weaken t) 0 = zero` — the
weakening renaming `Fin.succ` never produces position `0`.  The App-scaled twin of
`occurrenceCountAt_weaken_zeroPosition`, the ingredient the lifted-substitution preservation reads at the
deeper-variable substituents. -/
theorem RawTerm.appScaledDimensionGrade_weaken_zeroPosition {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.appScaledDimensionGrade (RawTerm.weaken sourceTerm) ⟨0, Nat.succ_pos scope⟩
      = UsageGrade.zero := by
  rw [RawTerm.weaken_eq_rename]
  exact RawTerm.appScaledDimensionGrade_rename_avoided_fueled (RawTerm.size sourceTerm)
    RawRenaming.weaken sourceTerm ⟨0, Nat.succ_pos scope⟩
    (fun candidate absurdEq => Nat.noConfusion (congrArg Fin.val absurdEq)) (Nat.le_refl _)

/-- **A lifted renaming preserves the freshest-binder App-scaled grade exactly.**
`appScaled (rename (iterateLiftRaw rho 1) body) 0 = appScaled body 0`: the lift hits `var 0` exactly at
`var 0`, so the App-scaled grade at the freshest dimension is unchanged.  The weakening side's affine
premise transport after the side-condition swap. -/
theorem RawTerm.appScaledDimensionGrade_rename_lift_zeroPosition {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (body : RawTerm (sourceScope + 1)) :
    RawTerm.appScaledDimensionGrade
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) ⟨0, Nat.succ_pos targetScope⟩
      = RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos sourceScope⟩ :=
  RawTerm.appScaledDimensionGrade_rename_image (iterateLiftRaw rawRenaming 1) body
    ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos targetScope⟩
    (by
      intro candidatePosition
      obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
      cases candidateValue with
      | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ priorValue =>
          exact ⟨fun hit => Nat.noConfusion (congrArg Fin.val hit),
            fun isZero => Nat.noConfusion (congrArg Fin.val isZero)⟩)

/-- **The lifted-substitution App-scaled profile at the freshest binder** (weight `zero`): every
substituent image's grade at `var 0` is below the variable's own grade at `var 0`.  `var 0` maps to
`var 0` (grade `one`, `le`-equal); a deeper `var (k+1)` maps to a weakened substituent (grade `zero` at
position `0`, `appScaledDimensionGrade_weaken_zeroPosition`).  The App-scaled twin of
`lift_hitsExactlyAt_zero`. -/
theorem RawTermSubst.lift_appScaledHitsWithWeight_zero {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTermSubst.appScaledHitsWithWeight (RawTermSubst.lift substitution)
      ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos sourceScope⟩
      ⟨0, Nat.succ_pos targetScope⟩ UsageGrade.zero := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      show UsageGrade.le
          (RawTerm.appScaledDimensionGrade
            (.mkGen .gen_var (⟨0, Nat.zero_lt_succ targetScope⟩ : Fin (targetScope + 1)) .childNil)
            ⟨0, Nat.succ_pos targetScope⟩)
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
              ⟨0, Nat.succ_pos sourceScope⟩)
            (UsageGrade.mul
              (RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
                ⟨0, Nat.succ_pos sourceScope⟩)
              UsageGrade.zero)) = true
      rw [RawTerm.appScaledDimensionGrade_var_self, RawTerm.appScaledDimensionGrade_var_self,
        UsageGrade.mul_zero, UsageGrade.add_zero]
      rfl
  | succ priorValue =>
      have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ candidateBound
      show UsageGrade.le
          (RawTerm.appScaledDimensionGrade
            (RawTerm.weaken (substitution ⟨priorValue, priorBound⟩)) ⟨0, Nat.succ_pos targetScope⟩)
          (UsageGrade.add
            (RawTerm.appScaledDimensionGrade
              (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
              ⟨0, Nat.succ_pos sourceScope⟩)
            (UsageGrade.mul
              (RawTerm.appScaledDimensionGrade
                (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
                ⟨0, Nat.succ_pos sourceScope⟩)
              UsageGrade.zero)) = true
      rw [RawTerm.appScaledDimensionGrade_weaken_zeroPosition]
      exact UsageGrade.zero_le _

/-- **★ A lifted substitution does not INCREASE the freshest-binder App-scaled grade.**
`appScaled (subst (iterateLiftRaw sigma 1) body) 0 ≤ appScaled body 0`: the lift fixes `var 0` and the
deeper substituents are weakened (never reintroduce `var 0`), so the App-scaled grade at the freshest
dimension can only DROP (a substituted function head may flip to the affine `gen_pathLam`).  The
substitution side's affine premise transport after the side-condition swap (via the substitution master at
the freshest-binder profile, weight `zero`). -/
theorem RawTerm.appScaledDimensionGrade_subst_lift_zeroPosition_le {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (body : RawTerm (sourceScope + 1)) :
    UsageGrade.le
      (RawTerm.appScaledDimensionGrade
        (RawTerm.subst (iterateLiftRaw substitution 1) body) ⟨0, Nat.succ_pos targetScope⟩)
      (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos sourceScope⟩) = true := by
  have master := RawTerm.appScaledDimensionGrade_subst_weightProfile (iterateLiftRaw substitution 1) body
    ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos targetScope⟩
    UsageGrade.zero (RawTermSubst.lift_appScaledHitsWithWeight_zero substitution)
  rw [UsageGrade.mul_zero, UsageGrade.add_zero] at master
  exact master

end FX1Poly.Typed
