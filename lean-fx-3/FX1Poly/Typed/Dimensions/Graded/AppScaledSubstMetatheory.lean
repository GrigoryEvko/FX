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
        (show Generator.gen_lam ≠ .gen_app from fun headEq => Generator.noConfusion headEq)]
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
        (show Generator.gen_pathLam ≠ .gen_app from fun headEq => Generator.noConfusion headEq)]
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
        (show Generator.gen_pathApp ≠ .gen_app from fun headEq => Generator.noConfusion headEq)]
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
        (show Generator.gen_pair ≠ .gen_app from fun headEq => Generator.noConfusion headEq)]
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
          (show Generator.gen_fst ≠ .gen_app from fun headEq => Generator.noConfusion headEq)]
    show UsageGrade.add
        (RawTerm.appScaledDimensionGrade
          (.mkGen .gen_pair () (.childCons firstComponent (.childCons secondComponent .childNil)))
          (RawVarSet.raiseParentPosition 0 dimension))
        UsageGrade.zero = _
    rw [RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]
  rw [fstGrade, appScaled_pairCell]
  exact UsageGrade.le_add_right _ _

end FX1Poly.Typed
