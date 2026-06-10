import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.ComplexitySemiring

/-! # FX1Poly/Modal/GradedCostSemantics
    — the verified COST SEMANTICS for the graded λ-calculus: complexity is honestly calculable (COST-1, #1213)

The maximum honest version of "calculate complexity" shippable on the current substrate: a
machine-checked cost semantics, term-indexed and computable, with both a WORST-CASE bound (sound for
EVERY reduction strategy) and an EXACT attained cost (for the canonical normalizer's path).

  * `ReducesInSteps` — step-counted reduction (the cost-instrumented operational semantics), with
    bridges to/from `ReducesStar`.  This is the COST MODEL: one unit per β-step, the abstract cost
    monoid every honest analysis must fix before claiming anything.
  * `oneStepReducts` — the computable one-step reduct enumeration, proven COMPLETE (every `Reduces`
    step is listed — the direction the upper bound consumes) and SOUND (every listed term is a
    genuine reduct — the direction the recursive bound construction consumes).
  * ★ `costBound` — **the computable worst-case cost**: by `Acc.rec` on strong normalization, the
    soundness-threaded sum over all one-step reducts.  `costBound_isSound`: EVERY reduction
    sequence from the term, under ANY strategy, has length at most `costBound` — a verified
    worst-case complexity calculator on the SN fragment.  (Sum-based, per the propext-free
    Nat-sum-bound discipline — `Nat.le_max_*` leaks `propext`; the sum dominates the max, so
    soundness is preserved at the price of slack.)
  * ★ `normalizeCost` — **the exact cost of the canonical strategy**: the step count of the shipped
    normalizer's own path, with `normalizeCost_isExact` (a genuine `ReducesInSteps` chain of
    EXACTLY that length to EXACTLY the normal form — attained, not just bounded),
    `normalizeWithCost_reachesNormalize` (the costed run computes THE normal form, by uniqueness),
    and `normalizeCost_le_costBound` (the sandwich).
  * ★ `HasGradeOver.costCalculator` / `canonicalEvaluationCost` — **complexity is calculable on the
    typed fragment**: every well-graded term, over ANY grade dimension, carries a computable sound
    worst-case bound and a computable exact canonical-evaluation cost.
    `complexityGraded_costIsCalculable` states the bundle at `fxComplexitySemiring` — the §6.3
    Dim-13 narrative instance.

## Honest scope boundary

This is a COST SEMANTICS — the cost is computed FROM THE TERM (by bounded search over the reduction
graph and by instrumented evaluation), not read off the grades.  The grade→cost tie — "the
complexity GRADE bounds the evaluation cost", the §6.3 Dim-13 cost READING of the N-semiring —
remains a hypothesis until the cost-indexed logical relation lands (COST-2; the calf/Danielsson/
dlPCF program).  Worst-case `costBound` is computable but by exhaustive search (exponential to
EVALUATE; verification is indifferent); `normalizeCost` is single-path.  Tight automatic inference
for arbitrary programs is impossible (Rice); what this module ships is the honest decidable side:
verified bounds and verified exact strategy costs on the SN fragment, hence on every well-graded
term.

## Zero-axiom verification

A step-counted inductive, a structural enumeration with hand-rolled membership lemmas (no
`List.mem_*` core lemmas — their axiom status is unaudited; the helpers here are by list induction
with explicit `List.Mem` constructors), a soundness-threaded fold (no `List.attach`), `Acc.rec`
definitions with constant-in-the-proof motives (the `normalize` recipe), and `Nat.le_add_left/right`
sum bounds (the propext-free discipline).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure)

/-! ## The cost model: step-counted reduction -/

/-- **Step-counted reduction** — the cost-instrumented operational semantics: `ReducesInSteps source
steps target` records a reduction sequence of exactly `steps` β-steps.  One unit per step is the
abstract cost monoid; every cost claim below is relative to it. -/
inductive GradedLambda.ReducesInSteps : GradedLambda → Nat → GradedLambda → Prop where
  | refl (term : GradedLambda) : GradedLambda.ReducesInSteps term 0 term
  | head {source middle target : GradedLambda} {restSteps : Nat}
      (firstStep : GradedLambda.Reduces source middle)
      (rest : GradedLambda.ReducesInSteps middle restSteps target) :
      GradedLambda.ReducesInSteps source (restSteps + 1) target

/-- Forgetting the count recovers multi-step reduction. -/
theorem GradedLambda.ReducesInSteps.toStar {source target : GradedLambda} {steps : Nat}
    (chain : GradedLambda.ReducesInSteps source steps target) :
    GradedLambda.ReducesStar source target := by
  induction chain with
  | refl term => exact ReflTransClosure.refl term
  | head firstStep _rest ih => exact ReflTransClosure.head firstStep ih

/-- Every multi-step reduction has SOME step count — the two reduction vocabularies agree. -/
theorem GradedLambda.ReducesStar.existsStepCount {source target : GradedLambda}
    (star : GradedLambda.ReducesStar source target) :
    ∃ steps : Nat, GradedLambda.ReducesInSteps source steps target := by
  induction star with
  | refl term => exact ⟨0, GradedLambda.ReducesInSteps.refl term⟩
  | head firstStep _rest ih =>
      obtain ⟨restSteps, restChain⟩ := ih
      exact ⟨restSteps + 1, GradedLambda.ReducesInSteps.head firstStep restChain⟩

/-! ## Hand-rolled membership lemmas (axiom-status-controlled) -/

/-- Mapping preserves membership (hand-rolled: list induction, explicit `List.Mem` ctors). -/
theorem GradedLambda.memMapOfMem {mapped : GradedLambda → GradedLambda} :
    {elements : List GradedLambda} → {element : GradedLambda} →
      element ∈ elements → mapped element ∈ elements.map mapped := by
  intro elements
  induction elements with
  | nil => intro _ mem; cases mem
  | cons head rest ih =>
      intro element mem
      cases mem with
      | head => exact List.Mem.head (rest.map mapped)
      | tail _ memRest => exact List.Mem.tail (mapped head) (ih memRest)

/-- Membership in the left part survives appending. -/
theorem GradedLambda.memAppendLeft {second : List GradedLambda} :
    {first : List GradedLambda} → {element : GradedLambda} →
      element ∈ first → element ∈ first ++ second := by
  intro first
  induction first with
  | nil => intro _ mem; cases mem
  | cons head rest ih =>
      intro element mem
      cases mem with
      | head => exact List.Mem.head (rest ++ second)
      | tail _ memRest => exact List.Mem.tail head (ih memRest)

/-- Membership in the right part survives appending. -/
theorem GradedLambda.memAppendRight {second : List GradedLambda} {element : GradedLambda}
    (mem : element ∈ second) :
    {first : List GradedLambda} → element ∈ first ++ second := by
  intro first
  induction first with
  | nil => exact mem
  | cons head rest ih => exact List.Mem.tail head ih

/-- Membership in a mapped list has a preimage. -/
theorem GradedLambda.memMapInv {mapped : GradedLambda → GradedLambda} :
    {elements : List GradedLambda} → {image : GradedLambda} →
      image ∈ elements.map mapped →
      ∃ preimage, preimage ∈ elements ∧ mapped preimage = image := by
  intro elements
  induction elements with
  | nil => intro _ mem; cases mem
  | cons head rest ih =>
      intro image mem
      cases mem with
      | head => exact ⟨head, List.Mem.head rest, rfl⟩
      | tail _ memRest =>
          obtain ⟨preimage, memPre, imageEq⟩ := ih memRest
          exact ⟨preimage, List.Mem.tail head memPre, imageEq⟩

/-- Membership in an append splits. -/
theorem GradedLambda.memAppendInv {second : List GradedLambda} :
    {first : List GradedLambda} → {element : GradedLambda} →
      element ∈ first ++ second → element ∈ first ∨ element ∈ second := by
  intro first
  induction first with
  | nil => intro _ mem; exact Or.inr mem
  | cons head rest ih =>
      intro element mem
      cases mem with
      | head => exact Or.inl (List.Mem.head rest)
      | tail _ memRest =>
          cases ih memRest with
          | inl memFirst => exact Or.inl (List.Mem.tail head memFirst)
          | inr memSecond => exact Or.inr memSecond

/-! ## The one-step reduct enumeration -/

/-- **The computable one-step reduct enumeration** — every term the source can reach in one β-step,
mirroring `stepOrNormal`'s head analysis (the β-contractum fires only at a λ-head). -/
def GradedLambda.oneStepReducts : GradedLambda → List GradedLambda
  | .var _ => []
  | .lam body => (GradedLambda.oneStepReducts body).map .lam
  | .app (.lam body) argument =>
      GradedLambda.substAt 0 argument body ::
        ((GradedLambda.oneStepReducts (.lam body)).map (fun function' => .app function' argument)
          ++ (GradedLambda.oneStepReducts argument).map
              (fun argument' => .app (.lam body) argument'))
  | .app (.var index) argument =>
      (GradedLambda.oneStepReducts (.var index)).map (fun function' => .app function' argument)
        ++ (GradedLambda.oneStepReducts argument).map
            (fun argument' => .app (.var index) argument')
  | .app (.app innerFunction innerArgument) argument =>
      (GradedLambda.oneStepReducts (.app innerFunction innerArgument)).map
          (fun function' => .app function' argument)
        ++ (GradedLambda.oneStepReducts argument).map
            (fun argument' => .app (.app innerFunction innerArgument) argument')

/-- **Completeness of the enumeration**: every one-step reduct is listed — the direction the upper
bound consumes (no reduction step escapes the cost accounting). -/
theorem GradedLambda.oneStepReducts_complete {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) :
    reduct ∈ GradedLambda.oneStepReducts source := by
  induction step with
  | beta body argument =>
      exact List.Mem.head _
  | congLam body body' _bodyStep ih =>
      exact GradedLambda.memMapOfMem ih
  | congAppLeft function function' argument functionStep ih =>
      cases function with
      | var index => cases functionStep
      | lam body =>
          exact List.Mem.tail _ (GradedLambda.memAppendLeft (GradedLambda.memMapOfMem ih))
      | app innerFunction innerArgument =>
          exact GradedLambda.memAppendLeft (GradedLambda.memMapOfMem ih)
  | congAppRight function argument argument' _argumentStep ih =>
      cases function with
      | var index => exact GradedLambda.memAppendRight (GradedLambda.memMapOfMem ih)
      | lam body =>
          exact List.Mem.tail _ (GradedLambda.memAppendRight (GradedLambda.memMapOfMem ih))
      | app innerFunction innerArgument =>
          exact GradedLambda.memAppendRight (GradedLambda.memMapOfMem ih)

/-- **Soundness of the enumeration**: every listed term is a genuine one-step reduct — the
direction the recursive bound construction consumes (each summand corresponds to a real step). -/
theorem GradedLambda.oneStepReducts_sound :
    {source listed : GradedLambda} → listed ∈ GradedLambda.oneStepReducts source →
      GradedLambda.Reduces source listed := by
  intro source
  induction source with
  | var index => intro _ mem; cases mem
  | lam body ihBody =>
      intro listed mem
      obtain ⟨body', memBody, listedEq⟩ := GradedLambda.memMapInv mem
      subst listedEq
      exact GradedLambda.Reduces.congLam body body' (ihBody memBody)
  | app function argument ihFunction ihArgument =>
      cases function with
      | lam body =>
          intro listed mem
          cases mem with
          | head => exact GradedLambda.Reduces.beta body argument
          | tail _ memRest =>
              cases GradedLambda.memAppendInv memRest with
              | inl memLeft =>
                  obtain ⟨function', memFunction, listedEq⟩ := GradedLambda.memMapInv memLeft
                  subst listedEq
                  exact GradedLambda.Reduces.congAppLeft (.lam body) function' argument
                    (ihFunction memFunction)
              | inr memRight =>
                  obtain ⟨argument', memArgument, listedEq⟩ := GradedLambda.memMapInv memRight
                  subst listedEq
                  exact GradedLambda.Reduces.congAppRight (.lam body) argument argument'
                    (ihArgument memArgument)
      | var index =>
          intro listed mem
          cases GradedLambda.memAppendInv mem with
          | inl memLeft =>
              obtain ⟨function', memFunction, _⟩ := GradedLambda.memMapInv memLeft
              cases memFunction
          | inr memRight =>
              obtain ⟨argument', memArgument, listedEq⟩ := GradedLambda.memMapInv memRight
              subst listedEq
              exact GradedLambda.Reduces.congAppRight (.var index) argument argument'
                (ihArgument memArgument)
      | app innerFunction innerArgument =>
          intro listed mem
          cases GradedLambda.memAppendInv mem with
          | inl memLeft =>
              obtain ⟨function', memFunction, listedEq⟩ := GradedLambda.memMapInv memLeft
              subst listedEq
              exact GradedLambda.Reduces.congAppLeft (.app innerFunction innerArgument)
                function' argument (ihFunction memFunction)
          | inr memRight =>
              obtain ⟨argument', memArgument, listedEq⟩ := GradedLambda.memMapInv memRight
              subst listedEq
              exact GradedLambda.Reduces.congAppRight (.app innerFunction innerArgument)
                argument argument' (ihArgument memArgument)

/-! ## The worst-case cost bound -/

/-- The soundness-threaded cost fold: for each listed reduct (with its step witness threaded), one
unit plus its recursive cost, all summed.  Threading the soundness through the recursion avoids
`List.attach` and keeps every recursive call justified by a genuine `Reduces` witness. -/
def GradedLambda.costBoundOverReducts (source : GradedLambda)
    (recurse : (reduct : GradedLambda) → GradedLambda.Reduces source reduct → Nat) :
    (reducts : List GradedLambda) →
      ((listed : GradedLambda) → listed ∈ reducts → GradedLambda.Reduces source listed) → Nat
  | [], _ => 0
  | reduct :: rest, soundAll =>
      (1 + recurse reduct (soundAll reduct (List.Mem.head rest)))
        + GradedLambda.costBoundOverReducts source recurse rest
            (fun listed mem => soundAll listed (List.Mem.tail reduct mem))

/-- Each listed reduct's contribution is bounded by the fold — the propext-free SUM-bound discipline
(`Nat.le_add_right`/`Nat.le_add_left`; `Nat.le_max_*` would leak `propext`). -/
theorem GradedLambda.costBoundOverReducts_boundsElement (source : GradedLambda)
    (recurse : (reduct : GradedLambda) → GradedLambda.Reduces source reduct → Nat) :
    {reducts : List GradedLambda} →
    (soundAll : (listed : GradedLambda) → listed ∈ reducts →
      GradedLambda.Reduces source listed) →
    {middle : GradedLambda} → (mem : middle ∈ reducts) →
      1 + recurse middle (soundAll middle mem)
        ≤ GradedLambda.costBoundOverReducts source recurse reducts soundAll := by
  intro reducts
  induction reducts with
  | nil => intro _ _ mem; cases mem
  | cons reduct rest ih =>
      intro soundAll middle mem
      cases mem with
      | head => exact Nat.le_add_right _ _
      | tail _ memRest =>
          have tailBound := ih (fun listed m => soundAll listed (List.Mem.tail reduct m)) memRest
          exact Nat.le_trans tailBound (Nat.le_add_left _ _)

/-- ★ **The computable worst-case cost bound**: by `Acc.rec` on strong normalization (motive
constant `Nat` — the propext-free recipe), the soundness-threaded sum over all one-step reducts.
Sound for EVERY reduction strategy (`costBound_isSound`). -/
def GradedLambda.costBound : (term : GradedLambda) →
    GradedLambda.IsStronglyNormalizing term → Nat :=
  fun _term sn =>
    Acc.rec (motive := fun _candidate _ => Nat)
      (fun candidate _accessible ih =>
        GradedLambda.costBoundOverReducts candidate
          (fun reduct step => ih reduct step)
          (GradedLambda.oneStepReducts candidate)
          (fun _listed mem => GradedLambda.oneStepReducts_sound mem))
      sn

/-- ★ **Worst-case soundness (the complexity-calculation theorem)**: EVERY reduction sequence from
a strongly-normalizing term — under ANY strategy — has length at most `costBound`.  Induction over
the accessibility; each head step's tail bound lifts through the sum via
`costBoundOverReducts_boundsElement` at the completeness membership. -/
theorem GradedLambda.costBound_isSound {term : GradedLambda}
    (sn : GradedLambda.IsStronglyNormalizing term) :
    ∀ {steps : Nat} {target : GradedLambda},
      GradedLambda.ReducesInSteps term steps target →
      steps ≤ GradedLambda.costBound term sn := by
  induction sn with
  | intro candidate accessibleReducts ih =>
      intro steps target chain
      cases chain with
      | refl _ => exact Nat.zero_le _
      | head firstStep rest =>
          have restBound := ih _ firstStep rest
          have elementBound :=
            GradedLambda.costBoundOverReducts_boundsElement candidate
              (fun reduct step =>
                GradedLambda.costBound reduct (accessibleReducts reduct step))
              (fun _listed mem => GradedLambda.oneStepReducts_sound mem)
              (GradedLambda.oneStepReducts_complete firstStep)
          have liftedBound := Nat.succ_le_succ restBound
          rw [Nat.add_comm 1 _] at elementBound
          exact Nat.le_trans liftedBound elementBound

/-! ## The exact cost of the canonical strategy -/

/-- The costed normalizer core: by `Acc.rec` on the SN accessibility, produce the normal form
TOGETHER with the exact step count of the path taken, the step-counted chain witnessing it, and
irreducibility of the result. -/
def GradedLambda.normalizeWithCost (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    { evaluation : GradedLambda × Nat //
      GradedLambda.ReducesInSteps term evaluation.2 evaluation.1
        ∧ GradedLambda.IsNormalForm evaluation.1 } :=
  Acc.rec (motive := fun candidate _ =>
      { evaluation : GradedLambda × Nat //
        GradedLambda.ReducesInSteps candidate evaluation.2 evaluation.1
          ∧ GradedLambda.IsNormalForm evaluation.1 })
    (fun candidate _accessible ih =>
      match GradedLambda.stepOrNormal candidate with
      | .inl ⟨reduct, step⟩ =>
          let ⟨⟨result, cost⟩, chain, resultNF⟩ := ih reduct step
          ⟨(result, cost + 1), GradedLambda.ReducesInSteps.head step chain, resultNF⟩
      | .inr nf => ⟨(candidate, 0), GradedLambda.ReducesInSteps.refl candidate, nf⟩)
    sn

/-- ★ **The exact canonical-evaluation cost**: the step count of the shipped normalizer's own
path. -/
def GradedLambda.normalizeCost (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) : Nat :=
  (GradedLambda.normalizeWithCost term sn).val.2

/-- **Exactness**: the costed run is a genuine step-counted chain of EXACTLY `normalizeCost` steps
to the costed run's result — attained, not just bounded. -/
theorem GradedLambda.normalizeCost_isExact (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    GradedLambda.ReducesInSteps term (GradedLambda.normalizeCost term sn)
      (GradedLambda.normalizeWithCost term sn).val.1 :=
  (GradedLambda.normalizeWithCost term sn).property.1

/-- The costed run computes THE normal form — its result coincides with `normalize`'s, by
uniqueness of normal forms. -/
theorem GradedLambda.normalizeWithCost_reachesNormalize (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    (GradedLambda.normalizeWithCost term sn).val.1 = GradedLambda.normalize term sn :=
  sn.uniqueNormalForm
    (GradedLambda.normalizeCost_isExact term sn).toStar
    (GradedLambda.normalize_reducesStar term sn)
    (GradedLambda.normalizeWithCost term sn).property.2
    (GradedLambda.normalize_isNormalForm term sn)

/-- **The sandwich**: the canonical strategy's exact cost never exceeds the worst-case bound. -/
theorem GradedLambda.normalizeCost_le_costBound (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    GradedLambda.normalizeCost term sn ≤ GradedLambda.costBound term sn :=
  GradedLambda.costBound_isSound sn (GradedLambda.normalizeCost_isExact term sn)

/-- Non-vacuity of the cost model: the identity redex performs exactly one step. -/
theorem GradedLambda.identityRedex_costsOneStep :
    GradedLambda.ReducesInSteps (.app (.lam (.var 0)) (.lam (.var 0))) 1 (.lam (.var 0)) :=
  GradedLambda.ReducesInSteps.head
    (GradedLambda.Reduces.beta (.var 0) (.lam (.var 0)))
    (GradedLambda.ReducesInSteps.refl (.lam (.var 0)))

/-! ## Complexity is calculable on the typed fragment -/

/-- ★ **The cost calculator for well-graded terms**: every term typed by the graded engine — over
ANY grade dimension — has a computable worst-case cost bound (SN supplied by the erasure
transfer). -/
def HasGradeOver.costCalculator {R : OrderedGradeSemiring}
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) : Nat :=
  GradedLambda.costBound term typed.stronglyNormalizing

/-- The calculator is SOUND: no reduction sequence from a well-graded term exceeds it, under any
strategy. -/
theorem HasGradeOver.costCalculator_isSound {R : OrderedGradeSemiring}
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType)
    {steps : Nat} {target : GradedLambda}
    (chain : GradedLambda.ReducesInSteps term steps target) :
    steps ≤ typed.costCalculator :=
  GradedLambda.costBound_isSound typed.stronglyNormalizing chain

/-- The exact canonical-evaluation cost of a well-graded term. -/
def HasGradeOver.canonicalEvaluationCost {R : OrderedGradeSemiring}
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) : Nat :=
  GradedLambda.normalizeCost term typed.stronglyNormalizing

/-- The canonical cost is exact: a genuine chain of exactly that length reaches the normal form. -/
theorem HasGradeOver.canonicalEvaluationCost_isExact {R : OrderedGradeSemiring}
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) :
    GradedLambda.ReducesInSteps term typed.canonicalEvaluationCost
      (GradedLambda.normalize term typed.stronglyNormalizing) := by
  rw [← GradedLambda.normalizeWithCost_reachesNormalize term typed.stronglyNormalizing]
  exact GradedLambda.normalizeCost_isExact term typed.stronglyNormalizing

/-- ★ **Complexity is honestly calculable at the complexity dimension** (the §6.3 Dim-13 narrative
instance): every term well-graded at the N-semiring carries a computable sound worst-case bound AND
a computable exact canonical-evaluation cost reaching its normal form.  What this does NOT claim:
that the GRADE bounds the cost — that tie is COST-2 (the cost-indexed logical relation). -/
theorem complexityGraded_costIsCalculable
    {typeContext : List (GTypeOver fxComplexitySemiring)}
    {grades : GradeVectorOver fxComplexitySemiring}
    {term : GradedLambda} {resultType : GTypeOver fxComplexitySemiring}
    (typed : HasGradeOver fxComplexitySemiring typeContext grades term resultType) :
    (∀ {steps : Nat} {target : GradedLambda},
        GradedLambda.ReducesInSteps term steps target → steps ≤ typed.costCalculator)
      ∧ GradedLambda.ReducesInSteps term typed.canonicalEvaluationCost
          (GradedLambda.normalize term typed.stronglyNormalizing) :=
  ⟨fun chain => typed.costCalculator_isSound chain,
   typed.canonicalEvaluationCost_isExact⟩

end FX1Poly.Modal
