import FX1Poly.Modal.GradedTermSize

/-! # FX1Poly/Modal/GradedLinearTime
    — the strict-linear fragment and the grade→occurrence bound (COST-2a brick 2)

The bridge from GRADES to syntactic occurrence COUNTS — the half of the
linear-time theorem the type system carries.  The load-bearing design
finding (recorded in the brick-1 module): the AFFINE fragment does NOT
bound occurrences, because 0-scaling annihilates an argument's grades
while its syntax remains (`λx. (f x) x` types at binder grade ZERO over
`f : A -0→ A -0→ B` with `x` occurring twice — witnessed below as
committed theorems).  The fragment that genuinely bounds counts is the
STRICT-linear one: every binder grade exactly `1`, so the App rule's
scaling is the identity and the usage arithmetic `fg@i + ag@i` cannot
hide occurrences.

  * `HasStrictLinearGrade` — the strict-linear judgment: `HasGradeOver`
    at the usage semiring with every binder grade pinned to `one`, with
    the forgetful map `toGraded`.
  * `GradeVectorOver.lookupGrade` + its `single`/`add`/`scale` laws —
    the pointwise reading of the §6.2 vector operations.
  * `UsageGrade.boundsCount` — the count-reading of a usage grade
    (`zero` ⟹ absent, `one` ⟹ at most once, `omega` ⟹ unconstrained)
    with its additivity law (sound precisely because strict `add` never
    hides a `one + one` behind a `one`).
  * `HasStrictLinearGrade.countBound` — ★ the grade→count bound: in a
    strict-linear derivation, every variable's syntactic occurrence
    count is bounded by its grade.
  * `HasStrictLinearGrade.betaShrinks` — every strict-linear β-redex
    strictly decreases size (via brick 1's β-size lemma) — the
    single-step engine of `steps < size` (brick 3).
  * The AFFINE COUNTERWITNESS, committed: `affineDuplicatorLam` types at
    binder grade ZERO under `HasGradeOver` while its bound variable
    occurs TWICE — grade 0 does not bound counts outside the strict
    fragment, so the linear-time theorem genuinely needs strictness.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Modal

/-! ## Pointwise grade lookup and its laws -/

/-- Look up one binding's grade by de Bruijn index (out of range reads
the erased grade `R.zero` — sound: well-scoped derivations never look
out of range). -/
def GradeVectorOver.lookupGrade {R : OrderedGradeSemiring} :
    GradeVectorOver R → Nat → R.Carrier
  | .nil, _ => R.zero
  | .cons headGrade _, 0 => headGrade
  | .cons _ restGrades, position + 1 => GradeVectorOver.lookupGrade restGrades position

/-- The all-zero vector reads `R.zero` everywhere. -/
theorem GradeVectorOver.lookupGrade_zero {R : OrderedGradeSemiring} :
    ∀ (scope index : Nat),
      GradeVectorOver.lookupGrade (GradeVectorOver.zero R scope) index = R.zero
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | scope + 1, index + 1 => GradeVectorOver.lookupGrade_zero scope index

/-- The var-rule singleton reads `R.one` at its own position (the
in-range premise carried by the lookup success). -/
theorem GradeVectorOver.lookupGrade_single_self {R : OrderedGradeSemiring} :
    ∀ (typeContext : List (GTypeOver R)) (index : Nat) (varType : GTypeOver R),
      GTypeOver.lookup typeContext index = some varType →
      GradeVectorOver.lookupGrade
        (GradeVectorOver.single R typeContext.length index R.one) index = R.one
  | [], index, _, lookupEq => nomatch index, lookupEq
  | _ :: _, 0, _, _ => rfl
  | _ :: restTypes, position + 1, varType, lookupEq =>
      GradeVectorOver.lookupGrade_single_self restTypes position varType lookupEq

/-- The var-rule singleton reads `R.zero` at every other position. -/
theorem GradeVectorOver.lookupGrade_single_other {R : OrderedGradeSemiring} :
    ∀ (scope position index : Nat), index ≠ position →
      GradeVectorOver.lookupGrade
        (GradeVectorOver.single R scope position R.one) index = R.zero
  | 0, _, _, _ => rfl
  | _ + 1, 0, 0, indexNe => absurd rfl indexNe
  | scope + 1, 0, _ + 1, _ => GradeVectorOver.lookupGrade_zero scope _
  | _ + 1, _ + 1, 0, _ => rfl
  | scope + 1, position + 1, index + 1, indexNe =>
      GradeVectorOver.lookupGrade_single_other scope position index
        (fun innerEq => indexNe (congrArg Nat.succ innerEq))

/-- Pointwise reading of `add` at the usage semiring (equal lengths —
the §6.2 invariant; the usage `add` table is closed, so the out-of-range
default is consistent). -/
theorem GradeVectorOver.lookupGrade_add_usage :
    ∀ (firstGrades secondGrades : GradeVectorOver fxUsageSemiring),
      firstGrades.length = secondGrades.length → ∀ (index : Nat),
      GradeVectorOver.lookupGrade (GradeVectorOver.add firstGrades secondGrades) index
        = UsageGrade.add (GradeVectorOver.lookupGrade firstGrades index)
            (GradeVectorOver.lookupGrade secondGrades index)
  | .nil, .nil, _, _ => rfl
  | .nil, .cons _ _, lengthEq, _ => nomatch lengthEq
  | .cons _ _, .nil, lengthEq, _ => nomatch lengthEq
  | .cons _ _, .cons _ _, _, 0 => rfl
  | .cons _ firstRest, .cons _ secondRest, lengthEq, index + 1 =>
      GradeVectorOver.lookupGrade_add_usage firstRest secondRest
        (Nat.succ.inj lengthEq) index

/-- `one` is a left multiplication unit on usage grades (table fact). -/
theorem UsageGrade.one_mul_eq : ∀ (grade : UsageGrade),
    UsageGrade.mul UsageGrade.one grade = grade
  | .zero => rfl
  | .one => rfl
  | .omega => rfl

/-- Scaling by `one` reads back unchanged (the strict App rule's scaling
is the identity). -/
theorem GradeVectorOver.lookupGrade_scale_one :
    ∀ (someGrades : GradeVectorOver fxUsageSemiring) (index : Nat),
      GradeVectorOver.lookupGrade
        (GradeVectorOver.scale fxUsageSemiring.one someGrades) index
        = GradeVectorOver.lookupGrade someGrades index
  | .nil, _ => rfl
  | .cons headGrade _, 0 => UsageGrade.one_mul_eq headGrade
  | .cons _ restGrades, index + 1 =>
      GradeVectorOver.lookupGrade_scale_one restGrades index

/-! ## The count-reading of a usage grade -/

/-- What a usage grade PROMISES about syntactic occurrences: `zero` ⟹
absent, `one` ⟹ at most once, `omega` ⟹ unconstrained. -/
def UsageGrade.boundsCount : UsageGrade → Nat → Prop
  | .zero, count => count = 0
  | .one, count => count ≤ 1
  | .omega, _ => True

/-- Additivity of the count-reading — sound for the STRICT fragment's
`add` because `one + one = omega` (the table never hides two uses behind
a `one`).  The 0-scaling leak lives exactly outside this lemma: `mul
zero omega = zero` would let an unconstrained count flow into a `zero`
promise, which is why the strict fragment pins scaling to `one`. -/
theorem UsageGrade.boundsCount_add {firstGrade secondGrade : UsageGrade}
    {firstCount secondCount : Nat}
    (firstBound : firstGrade.boundsCount firstCount)
    (secondBound : secondGrade.boundsCount secondCount) :
    (UsageGrade.add firstGrade secondGrade).boundsCount (firstCount + secondCount) := by
  cases firstGrade with
  | zero =>
      cases secondGrade with
      | zero =>
          show firstCount + secondCount = 0
          rw [firstBound, secondBound]
      | one =>
          show firstCount + secondCount ≤ 1
          rw [firstBound, Nat.zero_add]
          exact secondBound
      | omega => exact True.intro
  | one =>
      cases secondGrade with
      | zero =>
          show firstCount + secondCount ≤ 1
          rw [secondBound]
          exact firstBound
      | one => exact True.intro
      | omega => exact True.intro
  | omega => cases secondGrade <;> exact True.intro

/-! ## The strict-linear judgment -/

/-- **The strict-linear graded judgment**: `HasGradeOver` at the usage
semiring with EVERY binder grade pinned to `one` — each function uses
its argument exactly once, so the App scaling is the identity and grades
genuinely bound syntactic occurrence counts (`countBound` below).  The
affine relaxation (binder grade `zero` allowed) breaks the bound — the
committed `affineDuplicatorLam` counterwitness. -/
inductive HasStrictLinearGrade :
    List (GTypeOver fxUsageSemiring) → GradeVectorOver fxUsageSemiring →
      GradedLambda → GTypeOver fxUsageSemiring → Prop where
  | var (typeContext : List (GTypeOver fxUsageSemiring)) (index : Nat)
      (varType : GTypeOver fxUsageSemiring)
      (lookupOk : GTypeOver.lookup typeContext index = some varType) :
      HasStrictLinearGrade typeContext
        (GradeVectorOver.single fxUsageSemiring typeContext.length index
          fxUsageSemiring.one)
        (.var index) varType
  | lam (typeContext : List (GTypeOver fxUsageSemiring))
      (domain codomain : GTypeOver fxUsageSemiring)
      (outerGrades : GradeVectorOver fxUsageSemiring) (body : GradedLambda)
      (bodyTyped : HasStrictLinearGrade (domain :: typeContext)
        (GradeVectorOver.cons fxUsageSemiring.one outerGrades) body codomain) :
      HasStrictLinearGrade typeContext outerGrades (.lam body)
        (.arrow fxUsageSemiring.one domain codomain)
  | app (typeContext : List (GTypeOver fxUsageSemiring))
      (domain codomain : GTypeOver fxUsageSemiring)
      (functionGrades argumentGrades : GradeVectorOver fxUsageSemiring)
      (function argument : GradedLambda)
      (functionTyped : HasStrictLinearGrade typeContext functionGrades function
        (.arrow fxUsageSemiring.one domain codomain))
      (argumentTyped : HasStrictLinearGrade typeContext argumentGrades argument domain) :
      HasStrictLinearGrade typeContext
        (GradeVectorOver.add functionGrades
          (GradeVectorOver.scale fxUsageSemiring.one argumentGrades))
        (.app function argument) codomain

/-- The forgetful map: every strict-linear derivation is a graded
derivation (the strict judgment refines `HasGradeOver`). -/
theorem HasStrictLinearGrade.toGraded {typeContext : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext grades term resultType) :
    HasGradeOver fxUsageSemiring typeContext grades term resultType := by
  induction typed with
  | var typeContext index varType lookupOk =>
      exact HasGradeOver.var typeContext index varType lookupOk
  | lam typeContext domain codomain outerGrades body _ bodyIH =>
      exact HasGradeOver.lam typeContext fxUsageSemiring.one domain codomain
        outerGrades body bodyIH
  | app typeContext domain codomain functionGrades argumentGrades function argument
      _ _ functionIH argumentIH =>
      exact HasGradeOver.app typeContext fxUsageSemiring.one domain codomain
        functionGrades argumentGrades function argument functionIH argumentIH

/-! ## ★ The grade→count bound -/

/-- ★ **The grade→occurrence bound**: in a strict-linear derivation,
every variable's syntactic occurrence count is bounded by its grade —
`zero` ⟹ absent, `one` ⟹ at most once.  The app arm is sound precisely
because the strict scaling is the identity (`lookupGrade_scale_one`) and
the usage `add` table never compresses `one + one`. -/
theorem HasStrictLinearGrade.countBound {typeContext : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext grades term resultType) :
    ∀ (index : Nat),
      (GradeVectorOver.lookupGrade grades index).boundsCount
        (GradedLambda.countOccurrencesAt index term) := by
  induction typed with
  | var typeContext varIndex varType lookupOk =>
      intro index
      by_cases isEqual : varIndex = index
      · rw [← isEqual,
          GradeVectorOver.lookupGrade_single_self typeContext varIndex varType lookupOk]
        show (if varIndex = varIndex then 1 else 0) ≤ 1
        rw [if_pos rfl]
        exact Nat.le_refl 1
      · rw [GradeVectorOver.lookupGrade_single_other typeContext.length varIndex index
            (fun indexEq => isEqual indexEq.symm)]
        show (if varIndex = index then 1 else 0) = 0
        rw [if_neg isEqual]
  | lam typeContext domain codomain outerGrades body _ bodyIH =>
      intro index
      exact bodyIH (index + 1)
  | app typeContext domain codomain functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro index
      rw [GradeVectorOver.lookupGrade_add_usage functionGrades
            (GradeVectorOver.scale fxUsageSemiring.one argumentGrades)
            (by rw [GradeVectorOver.scale_length]
                exact (hasGradeOver_length functionTyped.toGraded).trans
                  (hasGradeOver_length argumentTyped.toGraded).symm)
            index,
        GradeVectorOver.lookupGrade_scale_one argumentGrades index]
      exact UsageGrade.boundsCount_add (functionIH index) (argumentIH index)

/-- A strict-linear lambda's bound variable occurs at most once in its
body (the `countBound` read at the binder position — the head of the
`cons one` the lam rule deposits). -/
theorem HasStrictLinearGrade.lamBodyCountBound
    {typeContext : List (GTypeOver fxUsageSemiring)}
    {outerGrades : GradeVectorOver fxUsageSemiring} {body : GradedLambda}
    {domain codomain : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext outerGrades (.lam body)
      (.arrow fxUsageSemiring.one domain codomain)) :
    GradedLambda.countOccurrencesAt 0 body ≤ 1 := by
  cases typed with
  | lam _ _ _ _ _ bodyTyped => exact bodyTyped.countBound 0

/-- ★ **Every strict-linear β-redex strictly shrinks**: the binder's
grade-`one` promise bounds the body's occurrences, so brick 1's β-size
lemma fires — the single-step engine of the linear-time bound. -/
theorem HasStrictLinearGrade.betaShrinks
    {typeContext : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {body argument : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext grades
      (.app (.lam body) argument) resultType) :
    (GradedLambda.substAt 0 argument body).size
      < (GradedLambda.app (GradedLambda.lam body) argument).size := by
  cases typed with
  | app _ _ _ _ _ _ _ functionTyped _ =>
      exact GradedLambda.size_substAt_lt_redex functionTyped.lamBodyCountBound

/-! ## Smokes — the strict fragment is inhabited and the chain fires -/

/-- The linear identity is strictly linear. -/
theorem linearIdentity_strictlyLinear :
    HasStrictLinearGrade [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow fxUsageSemiring.one .base .base) :=
  HasStrictLinearGrade.lam [] .base .base GradeVectorOver.nil (.var 0)
    (HasStrictLinearGrade.var [.base] 0 .base rfl)

/-- The identity self-application `(λx.x) (λy.y)` is strictly linear at
base-to-base, and `betaShrinks` fires concretely on it: the reduct
(size 2) is smaller than the redex (size 5). -/
theorem identityApplication_strictlyShrinks :
    (GradedLambda.substAt 0 (.lam (.var 0)) (.var 0)).size
      < (GradedLambda.app (.lam (.var 0)) (.lam (.var 0))).size :=
  HasStrictLinearGrade.betaShrinks
    (HasStrictLinearGrade.app [] (.arrow fxUsageSemiring.one .base .base)
      (.arrow fxUsageSemiring.one .base .base)
      GradeVectorOver.nil GradeVectorOver.nil (.lam (.var 0)) (.lam (.var 0))
      (HasStrictLinearGrade.lam [] (.arrow fxUsageSemiring.one .base .base)
        (.arrow fxUsageSemiring.one .base .base) GradeVectorOver.nil (.var 0)
        (HasStrictLinearGrade.var [.arrow fxUsageSemiring.one .base .base] 0
          (.arrow fxUsageSemiring.one .base .base) rfl))
      (HasStrictLinearGrade.lam [] .base .base GradeVectorOver.nil (.var 0)
        (HasStrictLinearGrade.var [.base] 0 .base rfl)))

/-! ## The AFFINE counterwitness — grade 0 does NOT bound occurrences

The 0-scaling leak, committed: over `f : base -0→ base -0→ base` (and a
spare base variable), the body `(f x) x` uses `x` TWICE, yet every
application scales the argument's grades by ZERO — so the lambda types
at binder grade ZERO under the full graded judgment.  An affine β-step
on this lambda DUPLICATES its argument; the linear-time bound genuinely
needs the strict fragment. -/

/-- The duplicating body `(f x) x` — `x` is `var 0`, `f` is `var 1`. -/
def affineDuplicatorBody : GradedLambda :=
  .app (.app (.var 1) (.var 0)) (.var 0)

/-- The discarding function type `base -0→ base -0→ base`. -/
def zeroScalingFunctionType : GTypeOver fxUsageSemiring :=
  .arrow UsageGrade.zero .base (.arrow UsageGrade.zero .base .base)

/-- **The leak, typed**: `λx. (f x) x` carries binder grade ZERO under
the full graded judgment — both applications scale `x`'s grades by
`zero`, annihilating them while the syntax keeps both occurrences. -/
theorem affineDuplicatorLam_typedAtGradeZero :
    HasGradeOver fxUsageSemiring [zeroScalingFunctionType, .base]
      (GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
        GradeVectorOver.nil))
      (.lam affineDuplicatorBody) (.arrow UsageGrade.zero .base .base) :=
  HasGradeOver.lam [zeroScalingFunctionType, .base] UsageGrade.zero .base .base
    (GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
      GradeVectorOver.nil))
    affineDuplicatorBody
    (HasGradeOver.app (.base :: [zeroScalingFunctionType, .base]) UsageGrade.zero
      .base .base
      (GradeVectorOver.add
        (GradeVectorOver.single fxUsageSemiring 3 1 fxUsageSemiring.one)
        (GradeVectorOver.scale UsageGrade.zero
          (GradeVectorOver.single fxUsageSemiring 3 0 fxUsageSemiring.one)))
      (GradeVectorOver.single fxUsageSemiring 3 0 fxUsageSemiring.one)
      (.app (.var 1) (.var 0)) (.var 0)
      (HasGradeOver.app (.base :: [zeroScalingFunctionType, .base]) UsageGrade.zero
        .base (.arrow UsageGrade.zero .base .base)
        (GradeVectorOver.single fxUsageSemiring 3 1 fxUsageSemiring.one)
        (GradeVectorOver.single fxUsageSemiring 3 0 fxUsageSemiring.one)
        (.var 1) (.var 0)
        (HasGradeOver.var (.base :: [zeroScalingFunctionType, .base]) 1
          zeroScalingFunctionType rfl)
        (HasGradeOver.var (.base :: [zeroScalingFunctionType, .base]) 0 .base rfl))
      (HasGradeOver.var (.base :: [zeroScalingFunctionType, .base]) 0 .base rfl))

/-- The leak's bound variable occurs TWICE. -/
theorem affineDuplicatorBody_countsTwice :
    GradedLambda.countOccurrencesAt 0 affineDuplicatorBody = 2 := rfl

/-- **Grade ZERO does not bound the count**: the `boundsCount` reading
fails on the leak — the formal pin that the affine fragment cannot feed
the β-size lemma, and the strict fragment is the honest hypothesis. -/
theorem affineGradeZero_doesNotBoundCount :
    ¬ UsageGrade.boundsCount UsageGrade.zero
        (GradedLambda.countOccurrencesAt 0 affineDuplicatorBody) :=
  fun absurd => nomatch absurd

end FX1Poly.Modal
