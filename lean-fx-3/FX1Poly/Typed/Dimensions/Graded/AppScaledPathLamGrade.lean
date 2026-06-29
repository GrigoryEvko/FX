import FX1Poly.Typed.Dimensions.Graded.BetaStablePathLamGrade
import FX1Poly.Core.Rewriting.Reduction.Step.Step
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable

/-! # FX1Poly/Typed/AppScaledPathLamGrade — the App-SCALED (beta-stable) dimension grade for `pathLam`

`BetaStablePathLamGrade.lean` shipped the grade-level substitution lemma `dimensionUsageGrade_subst0`
(the SR-stability KEY) but flagged the genuine beta-stable PREMISE as remaining: the current
`pathLamIntroRule.sideCondition` reads only one position's RAW occurrence count
(`RawTerm.dimensionUsageGrade body 0`), which is beta-FRAGILE because a redex `(lam y. pair y y) (g @ i)`
inside the body duplicates the dimension `i` only when it reduces.  This file builds that premise:
the **App-SCALED dimension grade** — a recursive accounting that, at every application node, scales the
argument's dimension grade by the function's binder grade, so the crux body grades the dimension at
`omega * one = omega` (rejecting the redex BEFORE it can step).

## What this file ships (each piece zero-axiom)

  * **`RawTerm.functionBinderGrade`** — the App rule's scalar `r` read off the function term's ROOT
    generator: `gen_pathLam ↦ one` (the affine interval binder) and EVERY OTHER head ↦ `omega`
    (CONSERVATIVE: an ordinary `lam`'s parameter is unrestricted; a NEUTRAL function's true scalar is
    its Pi-binder grade, which is typing-dependent — over-approximating to `omega` is SOUND, it may
    over-restrict an affine-neutral application but never admits a non-affine body).  This is the
    user-accepted "conservative-relative-to-SR-stable" discipline.
  * **`RawTerm.appScaledDimensionGrade`** (with the spine companions
    `RawTermChildren.appScaledDimensionGradeFold` / `appHeadScaledDimensionGrade`) — the recursive
    App-scaled accounting: at a generic node it `add`-folds the children's grades (shifting the
    dimension index under each binder, mirroring `occurrenceCountAt`); at a `gen_app` node it is
    `add (appScaled f) (mul (functionBinderGrade f) (appScaled a))` — App-scaling `funcGrade + r *
    argGrade` (§6.2) realized structurally; at a STRUCTURAL RECURSOR node
    (`isUnboundedlyDuplicatingRecursor` — `gen_natElim` / `gen_natRec` / `gen_listElim`) the whole
    child-fold is `omega`-scaled, because the recursor's iota contraction replays its children up to
    `m^k` times, so a dimension used anywhere inside a recursor is unboundedly-used and the affine
    `≤ one` bound rejects it.
  * **`RawTerm.functionBinderGrade_step_monotone`** — `functionBinderGrade` never INCREASES under a
    `Step`: a congruence step preserves the head generator (so the scalar is unchanged), and a root
    redex has an ELIMINATOR head (never `gen_pathLam`, so the scalar is the top `omega`).  The
    head-scalar fact the App-node congruence preservation needs.
  * **`iotaRuleTable_elimGenerator_ne_pathLam`** — every canonical iota row's eliminator generator is
    not `gen_pathLam` (per-row enumeration over the 22-row table).
  * the grade-arithmetic helpers `UsageGrade.le_omega` (omega is the top) and `UsageGrade.mul_le_mul`
    (two-sided multiplicative monotonicity), the App-node combinators the congruence preservation uses.

## Honest scope

This file lands the DEFINITION (step 1 of the swap plan) and the CONGRUENCE half of beta-stability
(step 2): `appScaledDimensionGrade_step_le_of_rootPreserved` proves the App-scaled grade never
increases under ANY `Step` GIVEN the root-redex obligation `AppScaledRootRedexPreserved` (every table
row fires to a below-grade reduct).  ALL congruence arms (`cong` + both `StepChildren` arms, at app and
non-app nodes) are discharged unconditionally; the remaining work is exactly the root obligation.

`AppScaledRootRedexPreserved` is GENUINELY conditional, not an unconditional raw-term lemma — which is
precisely why it is isolated as a named hypothesis rather than discharged here:

  * the gen_app BETA row `(lam body) arg ↝ subst0 body arg` is below-grade UNCONDITIONALLY — the ordinary
    `lam`'s scalar `functionBinderGrade (lam) = omega` supplies the slack, so the reduct's dimension grade
    `≤ funcGrade + omega * argGrade` = the redex grade.
  * the SELECTION rows (boolElim/fst/snd/natElimZero/listElimNil/…) have the reduct as a direct child of
    the redex cell, so they need only the sub-grade fact `appScaled child ≤ appScaled parent`.
  * the PATH-β row `pathApp (pathLam inner) i ↝ subst0 inner i` only carries the affine scalar `one`, so a
    raw NON-affine `inner` (e.g. `app (app f (var 0)) (var 0)`) blows the reduct's dimension grade to
    `omega > one`: unconditional raw preservation is FALSE here.  It closes only when the `pathLam` body's
    affineness `appScaled inner 0 ≤ one` is supplied — available at the TYPED layer (every `pathLam` was
    admitted by the affine `sideCondition`), so step 4's subject-reduction re-proof must THREAD that
    premise from typing/inversion at each path-β site, not assume unconditional raw preservation.

The β/selection rows need the App-scaled analogue of the `occurrenceCountAt` substitution metatheory;
the path-β row additionally threads the typed affine premise.  See the final-report plan.

## Zero-axiom

The grade definition recurses structurally over the `mkGen` spine (mirrors `occurrenceCountAt`); the
grade helpers are finite case enumerations (`rfl` / `Bool.noConfusion`); the table fact is the proven
per-row `List.Mem` decomposition (`Generator.noConfusion` at each leaf); the preservation recurses
structurally on a `Nat` FUEL (the term level, `appScaledDimensionGrade_step_le_ofRootPreserved_fueled`)
threading a size-bounded congruence callback through the spine
(`appScaledDimensionGrade_stepChildren_le_ofTermBound`, structural on its own `Nat` fuel), closed by the
monotonicity combinators — no mutual block, no indexed-derivation recursion.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/Typed/Dimensions/Graded/AppScaledPathLamGrade.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-! ## Grade-arithmetic helpers (the App-node monotonicity combinators) -/

/-- `omega` is the TOP of the affine usage chain `zero ≤ one ≤ omega`: every grade is below it.  The
fact that a function whose scalar is `omega` dominates any stepped scalar. -/
theorem UsageGrade.le_omega (someGrade : UsageGrade) :
    UsageGrade.le someGrade UsageGrade.omega = true := by
  cases someGrade <;> rfl

/-- **Two-sided multiplicative monotonicity** `a ≤ a' → b ≤ b' → a * b ≤ a' * b'`.  The App-node
companion to the shipped one-sided `UsageGrade.mul_le_mul_left`: it scales BOTH the function binder
grade and the argument grade when an application's children both move under a step. -/
theorem UsageGrade.mul_le_mul {firstGrade firstBound secondGrade secondBound : UsageGrade}
    (firstBelow : UsageGrade.le firstGrade firstBound = true)
    (secondBelow : UsageGrade.le secondGrade secondBound = true) :
    UsageGrade.le (UsageGrade.mul firstGrade secondGrade)
      (UsageGrade.mul firstBound secondBound) = true := by
  cases firstGrade <;> cases firstBound <;> cases secondGrade <;> cases secondBound <;>
    first | rfl | exact Bool.noConfusion firstBelow | exact Bool.noConfusion secondBelow

/-- `x ≤ omega * x` — a grade is below its own `omega`-scaling.  At a structural-recursor cell the
App-scaled grade is the `omega`-scaled child-fold, which therefore dominates the un-scaled fold (so the
raw occurrence count, already `≤` the un-scaled fold, stays `≤` the recursor grade). -/
theorem UsageGrade.le_omega_mul (someGrade : UsageGrade) :
    UsageGrade.le someGrade (UsageGrade.mul UsageGrade.omega someGrade) = true := by
  cases someGrade <;> rfl

/-- **`omega`-scaling preserves the App-scaled substitution bound.**  From `a ≤ b + c * w` derive
`omega * a ≤ omega * b + (omega * c) * w`.  The recursor arm's substitution-bound closer: the whole
child-fold is `omega`-scaled, so the bound's three readouts each pick up the `omega` factor (`omega`
distributes over `+` and associates through the `* w` scaling).  Finite check over the `{0,1,omega}`
carrier. -/
theorem UsageGrade.omegaScaledSubstBound {gradeSubst gradeShift gradeBinder weight : UsageGrade}
    (bound : UsageGrade.le gradeSubst
      (UsageGrade.add gradeShift (UsageGrade.mul gradeBinder weight)) = true) :
    UsageGrade.le (UsageGrade.mul UsageGrade.omega gradeSubst)
      (UsageGrade.add (UsageGrade.mul UsageGrade.omega gradeShift)
        (UsageGrade.mul (UsageGrade.mul UsageGrade.omega gradeBinder) weight)) = true := by
  cases gradeSubst <;> cases gradeShift <;> cases gradeBinder <;> cases weight <;>
    first | rfl | exact Bool.noConfusion bound

/-! ## The App rule's scalar, read off the function's root generator -/

/-- **The App rule's scalar `r`, read structurally off the function's ROOT generator.**  `gen_pathLam`
contributes the affine `one` (the interval binder is used at most once); every other head contributes
the conservative `omega`.  An ordinary `lam`'s parameter is genuinely unrestricted (`omega` is exact);
a NEUTRAL function's true scalar is its Pi-binder grade (a typing-layer fact), and over-approximating it
to `omega` is SOUND — `mul omega g ≥ mul r g` for every real binder grade `r`, so the App-scaled grade
only ever OVER-counts the dimension, never under-counts it.  This is the user-accepted
"conservative-relative-to-SR-stable" discipline: it may reject an affine-neutral application but never
admits a non-affine `pathLam` body. -/
def RawTerm.functionBinderGrade {scope : Nat} (functionTerm : RawTerm scope) : UsageGrade :=
  match functionTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_pathLam then UsageGrade.one else UsageGrade.omega

/-- `functionBinderGrade` unfolded at a generic cell: the decidable head test. -/
theorem RawTerm.functionBinderGrade_mkGen {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    RawTerm.functionBinderGrade (.mkGen generator payload children)
      = if generator = .gen_pathLam then UsageGrade.one else UsageGrade.omega :=
  rfl

/-! ## Every canonical iota row eliminates a non-`pathLam` head -/

/-- **Every canonical iota row's eliminator generator is not `gen_pathLam`.**  The 22-row table
enumerates eliminators (`gen_app`, `gen_boolElim`, `gen_fst`, …, `gen_pathApp`, `gen_ungel`); none is
the `pathLam` INTRODUCTION.  Per-row `List.Mem` decomposition, each leaf closed by
`Generator.noConfusion` (distinct constructors).  The fact `functionBinderGrade_step_monotone` uses to
know a root redex's head carries the top scalar `omega`. -/
theorem iotaRuleTable_elimGenerator_ne_pathLam :
    ∀ rule, rule ∈ iotaRuleTable → rule.elimGenerator ≠ .gen_pathLam := by
  intro rule isRow elimIsPathLam
  cases isRow with
  | head => exact Generator.noConfusion elimIsPathLam
  | tail _ isRow => cases isRow with
    | head => exact Generator.noConfusion elimIsPathLam
    | tail _ isRow => cases isRow with
      | head => exact Generator.noConfusion elimIsPathLam
      | tail _ isRow => cases isRow with
        | head => exact Generator.noConfusion elimIsPathLam
        | tail _ isRow => cases isRow with
          | head => exact Generator.noConfusion elimIsPathLam
          | tail _ isRow => cases isRow with
            | head => exact Generator.noConfusion elimIsPathLam
            | tail _ isRow => cases isRow with
              | head => exact Generator.noConfusion elimIsPathLam
              | tail _ isRow => cases isRow with
                | head => exact Generator.noConfusion elimIsPathLam
                | tail _ isRow => cases isRow with
                  | head => exact Generator.noConfusion elimIsPathLam
                  | tail _ isRow => cases isRow with
                    | head => exact Generator.noConfusion elimIsPathLam
                    | tail _ isRow => cases isRow with
                      | head => exact Generator.noConfusion elimIsPathLam
                      | tail _ isRow => cases isRow with
                        | head => exact Generator.noConfusion elimIsPathLam
                        | tail _ isRow => cases isRow with
                          | head => exact Generator.noConfusion elimIsPathLam
                          | tail _ isRow => cases isRow with
                            | head => exact Generator.noConfusion elimIsPathLam
                            | tail _ isRow => cases isRow with
                              | head => exact Generator.noConfusion elimIsPathLam
                              | tail _ isRow => cases isRow with
                                | head => exact Generator.noConfusion elimIsPathLam
                                | tail _ isRow => cases isRow with
                                  | head => exact Generator.noConfusion elimIsPathLam
                                  | tail _ isRow => cases isRow with
                                    | head => exact Generator.noConfusion elimIsPathLam
                                    | tail _ isRow => cases isRow with
                                      | head => exact Generator.noConfusion elimIsPathLam
                                      | tail _ isRow => cases isRow with
                                        | head => exact Generator.noConfusion elimIsPathLam
                                        | tail _ isRow => cases isRow with
                                          | head => exact Generator.noConfusion elimIsPathLam
                                          | tail _ isRow => cases isRow with
                                            | head => exact Generator.noConfusion elimIsPathLam
                                            | tail _ isRow => cases isRow

/-! ## The structural recursors that the affine grade scales by `omega` -/

/-- **The eliminators whose iota contraction may give a child unbounded/unknown multiplicity.**
Two families need the affine App-scaled grade to scale their whole child-fold by `omega`:
(1) the structural recursors `natElim` / `natRec` / `listElim` — `natElim M base step (succ^k zero)`
replays the recursive call (with `M` / `base` / `step` / the predecessor) up to `m^k` times;
(2) the app-of-branch matches `optionMatch` / `eitherMatch` / `quotRec` — `match … (con p) ↝ app branch p`
applies an UNKNOWN branch function to the child `p`, which may use it `omega` times (e.g.
`branch = fn x => pair x x` beta-reaches the diagonal `pair p p`).  Without (2)'s scaling the affine grade
is NOT beta-stable: an affine `optionMatch` over a `pathApp`-of-dimension scrutinee (grade `one`) steps to
`app branch (pathApp …)` of grade `omega`.  Named once so the dispatch, the unfolding equations and the
step-preservation share one proposition and one `Decidable` instance. -/
def RawTerm.isUnboundedlyDuplicatingRecursor (generator : Generator) : Prop :=
  generator = .gen_natElim ∨ generator = .gen_natRec ∨ generator = .gen_listElim
    ∨ generator = .gen_optionMatch ∨ generator = .gen_eitherMatch ∨ generator = .gen_quotRec

instance (generator : Generator) :
    Decidable (RawTerm.isUnboundedlyDuplicatingRecursor generator) := by
  unfold RawTerm.isUnboundedlyDuplicatingRecursor; exact inferInstance

/-! ## The recursive App-scaled dimension grade

A three-way structural recursion over the `mkGen` spine (mirrors `occurrenceCountAt`):

  * `RawTerm.appScaledDimensionGrade` dispatches on the head generator — `gen_app` routes to the
    SCALED fold, everything else to the generic `add`-fold.
  * `RawTermChildren.appScaledDimensionGradeFold` is the generic `add`-fold of the children's grades
    (each child's dimension index raised through its binder shift).
  * `RawTermChildren.appHeadScaledDimensionGrade` is the App-node fold: the FIRST child is the function
    `f`, and the remaining children (the argument spine) are scaled by `functionBinderGrade f`. -/

mutual

/-- **The App-scaled dimension grade of a raw term.**  At a `gen_var` LEAF the grade is the dimension's
occurrence indicator (`natToUsageGrade` of the variable cell's `occurrenceCountAt` — `one` when the leaf
IS the dimension, else `zero`), the base case that makes the grade actually TRACK dimension usage; at a
`gen_app` cell the argument's grade is scaled by the function's binder grade (`add (appScaled f) (mul
(functionBinderGrade f) (appScaled a))`, App-scaling §6.2); at a STRUCTURAL RECURSOR cell
(`gen_natElim` / `gen_natRec` / `gen_listElim`) the WHOLE child-fold is scaled by `omega`, because the
recursor's iota contraction can duplicate any child arbitrarily — `natElim M base step (succ^k zero)`
contracts to a term in which the recursive call (carrying `M`, `base`, `step` and the predecessor) is
replayed up to `m^k` times (`m` = how many times `step` consumes its induction-hypothesis argument), so a
dimension used ANYWHERE inside a recursor must be treated as unboundedly-used and the affine `≤ one` bound
then rejects it BEFORE iteration can multiply it; at every other cell the children's grades are
`add`-folded generically.  Routing the leaf through `natToUsageGrade ∘ occurrenceCountAt` reuses the
proven occurrence machinery and keeps this definition's equations `Eq.rec`-free. -/
def RawTerm.appScaledDimensionGrade {scope : Nat}
    (sourceTerm : RawTerm scope) (dimension : Fin scope) : UsageGrade :=
  match sourceTerm with
  | .mkGen generator payload children =>
      if generator = .gen_var then
        natToUsageGrade
          (RawTerm.occurrenceCountAt (.mkGen generator payload children) dimension)
      else if generator = .gen_app then
        RawTermChildren.appHeadScaledDimensionGrade children dimension
      else if RawTerm.isUnboundedlyDuplicatingRecursor generator then
        UsageGrade.mul UsageGrade.omega
          (RawTermChildren.appScaledDimensionGradeFold children dimension)
      else
        RawTermChildren.appScaledDimensionGradeFold children dimension

/-- The generic `add`-fold of a children spine's App-scaled grades — each child's dimension index
raised through its own binder shift, mirroring `RawTermChildren.occurrenceCountAt`. -/
def RawTermChildren.appScaledDimensionGradeFold {binderShifts : List Nat} {scope : Nat}
    (sourceChildren : RawTermChildren binderShifts scope) (dimension : Fin scope) : UsageGrade :=
  match binderShifts, sourceChildren with
  | [], .childNil => UsageGrade.zero
  | binderShift :: _, .childCons childHead childTail =>
      UsageGrade.add
        (RawTerm.appScaledDimensionGrade childHead
          (RawVarSet.raiseParentPosition binderShift dimension))
        (RawTermChildren.appScaledDimensionGradeFold childTail dimension)

/-- The App-node fold: the head child is the function `f`, the argument spine is scaled by
`functionBinderGrade f`.  For `gen_app` (binder shifts `[0, 0]`, spine `[f, a]`) this is
`add (appScaled f) (mul (functionBinderGrade f) (appScaled a))`. -/
def RawTermChildren.appHeadScaledDimensionGrade {binderShifts : List Nat} {scope : Nat}
    (sourceChildren : RawTermChildren binderShifts scope) (dimension : Fin scope) : UsageGrade :=
  match binderShifts, sourceChildren with
  | [], .childNil => UsageGrade.zero
  | binderShift :: _, .childCons functionChild argumentTail =>
      UsageGrade.add
        (RawTerm.appScaledDimensionGrade functionChild
          (RawVarSet.raiseParentPosition binderShift dimension))
        (UsageGrade.mul
          (RawTerm.functionBinderGrade functionChild)
          (RawTermChildren.appScaledDimensionGradeFold argumentTail dimension))

end

/-! ## Unfolding equations -/

/-- `appScaledDimensionGrade` at a generic cell: the head-generator dispatch (var leaf / app / generic
fold). -/
theorem RawTerm.appScaledDimensionGrade_mkGen {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade (.mkGen generator payload children) dimension
      = if generator = .gen_var then
          natToUsageGrade
            (RawTerm.occurrenceCountAt (.mkGen generator payload children) dimension)
        else if generator = .gen_app then
          RawTermChildren.appHeadScaledDimensionGrade children dimension
        else if RawTerm.isUnboundedlyDuplicatingRecursor generator then
          UsageGrade.mul UsageGrade.omega
            (RawTermChildren.appScaledDimensionGradeFold children dimension)
        else
          RawTermChildren.appScaledDimensionGradeFold children dimension :=
  rfl

/-- `appScaledDimensionGrade` at a `gen_var` LEAF: the dimension occurrence indicator. -/
theorem RawTerm.appScaledDimensionGrade_var {scope : Nat}
    (variablePosition : Fin scope)
    (children : RawTermChildren Generator.gen_var.binderShifts scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade (.mkGen .gen_var variablePosition children) dimension
      = natToUsageGrade
          (RawTerm.occurrenceCountAt (.mkGen .gen_var variablePosition children) dimension) := by
  rw [RawTerm.appScaledDimensionGrade_mkGen, if_pos rfl]

/-- `appScaledDimensionGrade` at a NON-variable NON-application NON-recursor cell folds the children
generically (coefficient `one`). -/
theorem RawTerm.appScaledDimensionGrade_nonApp {scope : Nat} {generator : Generator}
    (generatorIsNotVar : generator ≠ .gen_var)
    (generatorIsNotApp : generator ≠ .gen_app)
    (generatorIsNotRecursor : ¬ RawTerm.isUnboundedlyDuplicatingRecursor generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade (.mkGen generator payload children) dimension
      = RawTermChildren.appScaledDimensionGradeFold children dimension := by
  rw [RawTerm.appScaledDimensionGrade_mkGen, if_neg generatorIsNotVar, if_neg generatorIsNotApp,
    if_neg generatorIsNotRecursor]

/-- `appScaledDimensionGrade` at a STRUCTURAL RECURSOR cell scales the whole child-fold by `omega` —
the multiplicity-aware affine grade that rejects a dimension used anywhere inside a recursor. -/
theorem RawTerm.appScaledDimensionGrade_recursor {scope : Nat} {generator : Generator}
    (generatorIsNotVar : generator ≠ .gen_var)
    (generatorIsNotApp : generator ≠ .gen_app)
    (generatorIsRecursor : RawTerm.isUnboundedlyDuplicatingRecursor generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade (.mkGen generator payload children) dimension
      = UsageGrade.mul UsageGrade.omega
          (RawTermChildren.appScaledDimensionGradeFold children dimension) := by
  rw [RawTerm.appScaledDimensionGrade_mkGen, if_neg generatorIsNotVar, if_neg generatorIsNotApp,
    if_pos generatorIsRecursor]

/-- `appScaledDimensionGrade` at an APPLICATION cell: `add (appScaled f) (mul (functionBinderGrade f)
(appScaled a))`.  The structural realization of the App rule grade `funcGrade + r * argGrade`. -/
theorem RawTerm.appScaledDimensionGrade_app {scope : Nat}
    (functionChild argumentChild : RawTerm scope) (dimension : Fin scope) :
    RawTerm.appScaledDimensionGrade
        (.mkGen .gen_app ()
          (.childCons functionChild (.childCons argumentChild .childNil))) dimension
      = UsageGrade.add
          (RawTerm.appScaledDimensionGrade functionChild dimension)
          (UsageGrade.mul (RawTerm.functionBinderGrade functionChild)
            (RawTerm.appScaledDimensionGrade argumentChild dimension)) := by
  rw [RawTerm.appScaledDimensionGrade_mkGen,
    if_neg (show Generator.gen_app ≠ .gen_var from fun headEq => Generator.noConfusion headEq),
    if_pos rfl]
  show UsageGrade.add
      (RawTerm.appScaledDimensionGrade functionChild
        (RawVarSet.raiseParentPosition 0 dimension))
      (UsageGrade.mul (RawTerm.functionBinderGrade functionChild)
        (UsageGrade.add
          (RawTerm.appScaledDimensionGrade argumentChild
            (RawVarSet.raiseParentPosition 0 dimension))
          UsageGrade.zero))
    = _
  rw [RawVarSet.raiseParentPosition_zero, UsageGrade.add_zero]

/-- The generic fold at a `childCons` node. -/
theorem RawTermChildren.appScaledDimensionGradeFold_childCons {scope shift : Nat}
    {restShifts : List Nat} (childHead : RawTerm (scope + shift))
    (childTail : RawTermChildren restShifts scope) (dimension : Fin scope) :
    RawTermChildren.appScaledDimensionGradeFold
        (.childCons childHead childTail) dimension
      = UsageGrade.add
          (RawTerm.appScaledDimensionGrade childHead
            (RawVarSet.raiseParentPosition shift dimension))
          (RawTermChildren.appScaledDimensionGradeFold childTail dimension) :=
  rfl

/-- The App-node fold at a `childCons` node: the head is the function, the tail is scaled. -/
theorem RawTermChildren.appHeadScaledDimensionGrade_childCons {scope shift : Nat}
    {restShifts : List Nat} (functionChild : RawTerm (scope + shift))
    (argumentTail : RawTermChildren restShifts scope) (dimension : Fin scope) :
    RawTermChildren.appHeadScaledDimensionGrade
        (.childCons functionChild argumentTail) dimension
      = UsageGrade.add
          (RawTerm.appScaledDimensionGrade functionChild
            (RawVarSet.raiseParentPosition shift dimension))
          (UsageGrade.mul (RawTerm.functionBinderGrade functionChild)
            (RawTermChildren.appScaledDimensionGradeFold argumentTail dimension)) :=
  rfl

/-! ## `functionBinderGrade` never increases under a `Step` -/

/-- **The function binder grade never INCREASES under a `Step`.**  A `cong` step preserves the head
generator, so the scalar is UNCHANGED; a `tableRedex` (root) step has an eliminator head — never
`gen_pathLam` (`iotaRuleTable_elimGenerator_ne_pathLam`) — so the redex's scalar is the top `omega`,
dominating any reduct's scalar.  The head-scalar monotonicity the App-node congruence preservation
needs (when the function child of an application reduces). -/
theorem RawTerm.functionBinderGrade_step_monotone {scope : Nat}
    {functionTerm functionTerm' : RawTerm scope}
    (stepFunction : Step functionTerm functionTerm') :
    UsageGrade.le (RawTerm.functionBinderGrade functionTerm')
      (RawTerm.functionBinderGrade functionTerm) = true := by
  cases stepFunction with
  | tableRedex isRow elimPayload fires =>
      rw [RawTerm.functionBinderGrade_mkGen,
        if_neg (iotaRuleTable_elimGenerator_ne_pathLam _ isRow)]
      exact UsageGrade.le_omega _
  | cong gen payload childStep =>
      rw [RawTerm.functionBinderGrade_mkGen, RawTerm.functionBinderGrade_mkGen]
      exact UsageGrade.le_refl _

/-! ## ★ The CONGRUENCE half of beta-stability (preservation modulo the root obligation) -/

/-- **The root-redex preservation OBLIGATION.**  Every canonical iota row, when it fires at the root,
produces a reduct whose App-scaled dimension grade is below the redex's.  This is the residual proof
debt after the congruence arms are discharged: the App-scaled grade is beta-stable iff every root
contraction is grade-non-increasing.  The beta row needs the App-scaled substitution metatheory; the
selection rows need only the sub-grade fact `appScaled child ≤ appScaled parent`. -/
def AppScaledRootRedexPreserved : Prop :=
  ∀ (scope : Nat) (rule : IotaRuleDesc), rule ∈ iotaRuleTable →
    ∀ (elimPayload : rule.elimGenerator.payload scope)
      {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
      {reduct : RawTerm scope},
      rule.firesOn? elimPayload spine = some reduct →
    ∀ (dimension : Fin scope),
      UsageGrade.le
        (RawTerm.appScaledDimensionGrade reduct dimension)
        (RawTerm.appScaledDimensionGrade
          (.mkGen rule.elimGenerator elimPayload spine) dimension) = true

/-- **Both spine foldings never increase under a `StepChildren`, given a size-bounded term callback.**
The congruence engine: given `termLe` (App-scaled preservation for every subterm of size `≤ fuel`), a
`StepChildren` inside a spine whose size is `≤ fuel` lowers BOTH the generic `add`-fold (`.1`) and the
App-node scaled fold (`.2`).  The `here` arm reduces the head child via `termLe` (and, for the App fold,
`functionBinderGrade_step_monotone` for the scalar); the `there` arm recurses into the tail.  The size
bound threads from the spine to each child (`size_lt_childCons_head`/`_tail`), so `termLe` applies.
Recursion is STRUCTURAL ON `fuel` (a `Nat`) — the tail recursion weakens the callback's bound by one as
the fuel decrements.  Taking `termLe` as a parameter (rather than a mutual sibling) keeps the recursion
single (no term/spine mutual block) and the `Nat`-fuel sidesteps the indexed-`StepChildren` recursion
elaboration. -/
theorem RawTermChildren.appScaledDimensionGrade_stepChildren_le_ofTermBound :
    ∀ (fuel : Nat)
      (termLe : ∀ (subScope : Nat) (subBody subBody' : RawTerm subScope) (subDimension : Fin subScope),
        Step subBody subBody' → RawTerm.size subBody ≤ fuel →
        UsageGrade.le (RawTerm.appScaledDimensionGrade subBody' subDimension)
          (RawTerm.appScaledDimensionGrade subBody subDimension) = true)
      {parentScope : Nat} {binderShifts : List Nat}
      {children children' : RawTermChildren binderShifts parentScope}
      (stepChildren : StepChildren children children') (dimension : Fin parentScope),
      RawTermChildren.size children ≤ fuel →
      (UsageGrade.le (RawTermChildren.appScaledDimensionGradeFold children' dimension)
          (RawTermChildren.appScaledDimensionGradeFold children dimension) = true) ∧
        (UsageGrade.le (RawTermChildren.appHeadScaledDimensionGrade children' dimension)
          (RawTermChildren.appHeadScaledDimensionGrade children dimension) = true) := by
  intro fuel
  induction fuel with
  | zero =>
      intro _termLe _parentScope _binderShifts _children _children' stepChildren _dimension sizeBound
      cases stepChildren with
      | here _rest _childStep => exact absurd sizeBound (Nat.not_succ_le_zero _)
      | there _head _restStep => exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ priorFuel ihSpine =>
      intro termLe _parentScope _binderShifts _children _children' stepChildren dimension sizeBound
      cases stepChildren with
      | here rest childStep =>
          have headBound : RawTerm.size _ ≤ priorFuel + 1 :=
            Nat.le_trans (Nat.le_of_lt (RawTermChildren.size_lt_childCons_head _ rest)) sizeBound
          refine ⟨?_, ?_⟩
          · rw [RawTermChildren.appScaledDimensionGradeFold_childCons,
              RawTermChildren.appScaledDimensionGradeFold_childCons]
            exact UsageGrade.add_le_add (termLe _ _ _ _ childStep headBound) (UsageGrade.le_refl _)
          · rw [RawTermChildren.appHeadScaledDimensionGrade_childCons,
              RawTermChildren.appHeadScaledDimensionGrade_childCons]
            exact UsageGrade.add_le_add (termLe _ _ _ _ childStep headBound)
              (UsageGrade.mul_le_mul
                (RawTerm.functionBinderGrade_step_monotone childStep)
                (UsageGrade.le_refl _))
      | there head restStep =>
          have tailBound : RawTermChildren.size _ ≤ priorFuel :=
            Nat.le_of_lt_succ
              (Nat.lt_of_lt_of_le (RawTermChildren.size_lt_childCons_tail head _) sizeBound)
          have tailLe :=
            ihSpine
              (fun subScope subBody subBody' subDimension subStep subBound =>
                termLe subScope subBody subBody' subDimension subStep (Nat.le_succ_of_le subBound))
              restStep dimension tailBound
          refine ⟨?_, ?_⟩
          · rw [RawTermChildren.appScaledDimensionGradeFold_childCons,
              RawTermChildren.appScaledDimensionGradeFold_childCons]
            exact UsageGrade.add_le_add_left _ tailLe.1
          · rw [RawTermChildren.appHeadScaledDimensionGrade_childCons,
              RawTermChildren.appHeadScaledDimensionGrade_childCons]
            exact UsageGrade.add_le_add_left _ (UsageGrade.mul_le_mul_left _ tailLe.1)

/-- **★ The App-scaled dimension grade never increases under any `Step` — fuel-bounded form.**  By
structural recursion on `fuel`: the `cong` case delegates the spine to
`appScaledDimensionGrade_stepChildren_le_ofTermBound`, feeding the fuel induction hypothesis as the
size-bounded term callback (each child of the redex cell has size `≤ fuel`, so the callback applies);
the `tableRedex` case is the root obligation.  This is the CONGRUENCE half of beta-stability, modulo the
root obligation. -/
theorem RawTerm.appScaledDimensionGrade_step_le_ofRootPreserved_fueled
    (rootPreserved : AppScaledRootRedexPreserved) :
    ∀ (fuel : Nat) {scope : Nat} {body body' : RawTerm scope}
      (stepBody : Step body body') (dimension : Fin scope),
      RawTerm.size body ≤ fuel →
      UsageGrade.le (RawTerm.appScaledDimensionGrade body' dimension)
        (RawTerm.appScaledDimensionGrade body dimension) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro scope body body' _stepBody dimension sizeBound
      cases body with
      | mkGen generator payload children =>
          exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ priorFuel ihFuel =>
      intro scope body body' stepBody dimension sizeBound
      cases stepBody with
      | tableRedex isRow elimPayload fires =>
          exact rootPreserved _ _ isRow elimPayload fires dimension
      | cong generator _payload childStep =>
          by_cases genIsVar : generator = .gen_var
          · -- A `gen_var` leaf has NO children (`gen_var.binderShifts = []`), so a `StepChildren`
            -- inside it is impossible — the `cong` case never fires under a variable.
            subst genIsVar
            cases childStep
          · have childrenBound : RawTermChildren.size _ ≤ priorFuel :=
              Nat.le_of_succ_le_succ sizeBound
            by_cases genIsApp : generator = .gen_app
            · subst genIsApp
              rw [RawTerm.appScaledDimensionGrade_mkGen, RawTerm.appScaledDimensionGrade_mkGen,
                if_neg (show Generator.gen_app ≠ .gen_var from
                  fun headEq => Generator.noConfusion headEq),
                if_neg (show Generator.gen_app ≠ .gen_var from
                  fun headEq => Generator.noConfusion headEq),
                if_pos rfl, if_pos rfl]
              exact (RawTermChildren.appScaledDimensionGrade_stepChildren_le_ofTermBound
                priorFuel
                (fun _ _ _ subDimension subStep subBound => ihFuel subStep subDimension subBound)
                childStep dimension childrenBound).2
            · by_cases genIsRecursor : RawTerm.isUnboundedlyDuplicatingRecursor generator
              · -- A STRUCTURAL RECURSOR cell: the whole child-fold is `omega`-scaled, so a congruence
                -- step inside it lowers the fold (`.1`) and `omega`-scaling is monotone in it.
                rw [RawTerm.appScaledDimensionGrade_recursor genIsVar genIsApp genIsRecursor,
                  RawTerm.appScaledDimensionGrade_recursor genIsVar genIsApp genIsRecursor]
                exact UsageGrade.mul_le_mul_left _
                  (RawTermChildren.appScaledDimensionGrade_stepChildren_le_ofTermBound
                    priorFuel
                    (fun _ _ _ subDimension subStep subBound => ihFuel subStep subDimension subBound)
                    childStep dimension childrenBound).1
              · rw [RawTerm.appScaledDimensionGrade_nonApp genIsVar genIsApp genIsRecursor,
                  RawTerm.appScaledDimensionGrade_nonApp genIsVar genIsApp genIsRecursor]
                exact (RawTermChildren.appScaledDimensionGrade_stepChildren_le_ofTermBound
                  priorFuel
                  (fun _ _ _ subDimension subStep subBound => ihFuel subStep subDimension subBound)
                  childStep dimension childrenBound).1

/-- **★ The App-scaled dimension grade never increases under any `Step` — GIVEN the root obligation.**
Every CONGRUENCE arm is discharged here (uniform `cong`, both `StepChildren` arms, at App and non-App
nodes); the only thing assumed is `AppScaledRootRedexPreserved` (the root contractions).  Instantiates
the fuel form at `fuel := RawTerm.size body`, the body's own size — the App-scaled grade is a beta
INVARIANT (modulo the root obligation), so the affine premise `≤ one` it underwrites is preserved. -/
theorem RawTerm.appScaledDimensionGrade_step_le_of_rootPreserved
    (rootPreserved : AppScaledRootRedexPreserved)
    {scope : Nat} {body body' : RawTerm scope}
    (stepBody : Step body body') (dimension : Fin scope) :
    UsageGrade.le (RawTerm.appScaledDimensionGrade body' dimension)
      (RawTerm.appScaledDimensionGrade body dimension) = true :=
  RawTerm.appScaledDimensionGrade_step_le_ofRootPreserved_fueled rootPreserved
    (RawTerm.size body) stepBody dimension (Nat.le_refl _)

end FX1Poly.Typed
