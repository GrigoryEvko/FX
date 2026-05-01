import LeanFX.Syntax.Reduction.Diamond
import LeanFX.Syntax.Reduction.CdParMono

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # Iterated complete development and confluence (W8.3 / #885).

This file builds typed Church-Rosser on top of the diamond
property (`Step.par.diamond`, proved in `Diamond.lean`).

At the typed level, `Step.par.cd_lemma_star` produces a
`Step.parStar` chain (not a single par), so the standard
strip-lemma + Hindley-Rosen argument from the raw level
(`RawConfluence.lean`) does not transfer directly: the chain's
length is not bounded by the input chain's length, defeating any
naive well-founded measure.

The route here is the **iterated complete development**.  Define
`cdIter n term = (Term.cd)^n term`.  Three lemmas drive the
proof:

* `Step.par.cd_monotone bi` — `Step.par.isBi`-witnessed steps
  lift to `parStar` between complete developments
  (`parStar (Term.cd source) (Term.cd target)`).  Tait-style
  induction with ~50 cases, each closed by the matching
  `parStar.<C>_cong` rule (cong cases) or by combining
  `subst0_parStar` with `cd_lemma_star` (β cases).

* `Step.parStar.cd_monotone` — chain induction over `cd_monotone`.

* `Step.parStar.cdIter_completion` — every `parStar.isBi` chain
  of length `n` reaches `cdIter n` of its source.

The headline `Step.parStar.confluence` then takes the maximum
of the two chain lengths and uses `cdIter (max n m)` as the
common reduct.

The `cdIter` definition itself is pure data — it iterates
`Term.cd` `count` times.  No proof obligations attach to it; the
work is in the theorems above. -/

/-- `Term.cdIter count term` applies the complete-development
operator `Term.cd` `count` times to `term`.  Pure structural
recursion on `count` — `cdIter 0 t = t`, `cdIter (n+1) t = cd
(cdIter n t)`.

Used by `Step.parStar.confluence` as the join point: every
`isBi`-chain of length `n` reaches `cdIter n source`, so two
chains of lengths `n` and `m` both reach `cdIter (max n m)
source` after enough cd-iterations. -/
@[reducible] def Term.cdIter
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (count : Nat) (term : Term context termType) :
    Term context termType :=
  match count with
  | 0 => term
  | Nat.succ predecessor => Term.cd (Term.cdIter predecessor term)

/-- `cdIter 0` is the identity. -/
theorem Term.cdIter_zero
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (term : Term context termType) :
    Term.cdIter 0 term = term :=
  rfl

/-- `cdIter (n+1)` is `cd` applied to `cdIter n`. -/
theorem Term.cdIter_succ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (predecessorCount : Nat) (term : Term context termType) :
    Term.cdIter (predecessorCount + 1) term =
      Term.cd (Term.cdIter predecessorCount term) :=
  rfl

/-- `cdIter 1` is exactly `Term.cd`. -/
theorem Term.cdIter_one
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (term : Term context termType) :
    Term.cdIter 1 term = Term.cd term :=
  rfl

/-- Pull-out lemma: `cdIter n (cd t) = cdIter (n+1) t`.  The outer
`cd` and the iterated `cdIter` commute — both produce `cd^(n+1) t`. -/
theorem Term.cdIter_pull_cd_inside
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (count : Nat) (term : Term context termType) :
    Term.cdIter count (Term.cd term) = Term.cdIter (count + 1) term := by
  induction count with
  | zero => rfl
  | succ predecessorCount predecessorIH =>
      simp only [Term.cdIter]
      rw [predecessorIH]

/-! ## Chain extension of `Step.par.cd_monotone`. -/

/-- **Chain version of `Step.par.cd_monotone`.**  Complete development
is monotone wrt `Step.parStarWithBi` chains: a βι-witnessed chain
between source and target lifts to a chain between their developments. -/
theorem Step.parStarWithBi.cd_monotone
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (chain : Step.parStarWithBi sourceTerm targetTerm) :
    Step.parStarWithBi (Term.cd sourceTerm) (Term.cd targetTerm) := by
  induction chain with
  | refl term => exact Step.parStarWithBi.refl (Term.cd term)
  | trans firstBi _rest restIH =>
      exact Step.parStarWithBi.append
        (Step.par.cd_monotone firstBi) restIH

/-- **Iterated version of `Step.parStarWithBi.cd_monotone`.**  For any
iteration count `n`, the chain lifts to `n` iterated developments. -/
theorem Step.parStarWithBi.cdIter_monotone
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (count : Nat)
    (chain : Step.parStarWithBi sourceTerm targetTerm) :
    Step.parStarWithBi
      (Term.cdIter count sourceTerm)
      (Term.cdIter count targetTerm) := by
  induction count with
  | zero => exact chain
  | succ predecessorCount predecessorIH =>
      simp only [Term.cdIter]
      exact Step.parStarWithBi.cd_monotone predecessorIH

/-- **`cdIter` is increasing.**  For any term, applying one more `cd`
iteration produces a parWithBi-related result.  Single-step chain
via `cd_dominates_with_isBi`. -/
theorem Step.parStarWithBi.cdIter_increasing
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (count : Nat) (term : Term ctx termType) :
    Step.parStarWithBi
      (Term.cdIter count term)
      (Term.cdIter (count + 1) term) := by
  simp only [Term.cdIter]
  exact (Step.par.cd_dominates_with_isBi (Term.cdIter count term)).toIsBi.toParStarWithBi

/-- **Monotone in the iteration count.**  For `n ≤ m`, `cdIter n` is
chain-related to `cdIter m`. -/
theorem Step.parStarWithBi.cdIter_le
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {firstCount secondCount : Nat}
    (countOrder : firstCount ≤ secondCount)
    (term : Term ctx termType) :
    Step.parStarWithBi
      (Term.cdIter firstCount term)
      (Term.cdIter secondCount term) := by
  induction countOrder with
  | refl => exact Step.parStarWithBi.refl _
  | step _previousLe predecessorIH =>
      exact Step.parStarWithBi.append predecessorIH
        (Step.parStarWithBi.cdIter_increasing _ term)

/-- **The reach lemma.**  Every parWithBi chain `a ⟶par* b` reaches
some iterated complete development of its source: `b ⟶par* cdIter n a`
for some `n` (the chain's length).

Proof by induction on the chain.  `refl` returns `n = 0`.  `trans` of
length `n+1` extends the IH chain (length `n` from the mid-point) by
applying `cd_lemma_star_with_bi` to the first step (mid → cd a) and
`cdIter_monotone n` to push it through to the n-th iteration. -/
theorem Step.parStarWithBi.cdIter_completion
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (chain : Step.parStarWithBi sourceTerm targetTerm) :
    ∃ count, Step.parStarWithBi targetTerm (Term.cdIter count sourceTerm) := by
  induction chain with
  | refl term => exact ⟨0, Step.parStarWithBi.refl term⟩
  | trans firstBi _rest restIH =>
      rename_i sourceTerm midTerm _ _
      obtain ⟨restCount, restChain⟩ := restIH
      let cdLemmaChain := Step.par.cd_lemma_star_with_bi firstBi
      let bumpedChain :
          Step.parStarWithBi
            (Term.cdIter restCount midTerm)
            (Term.cdIter restCount (Term.cd sourceTerm)) :=
        Step.parStarWithBi.cdIter_monotone restCount cdLemmaChain
      have rewriteEquation :
          Term.cdIter restCount (Term.cd sourceTerm)
            = Term.cdIter (restCount + 1) sourceTerm :=
        Term.cdIter_pull_cd_inside restCount sourceTerm
      let bumpedChainRewritten :
          Step.parStarWithBi
            (Term.cdIter restCount midTerm)
            (Term.cdIter (restCount + 1) sourceTerm) :=
        rewriteEquation ▸ bumpedChain
      exact ⟨restCount + 1,
        Step.parStarWithBi.append restChain bumpedChainRewritten⟩

/-! ## Bridge: `Step.parStar.isBi` to `Step.parStarWithBi`. -/

/-- Convert a `Step.parStar` chain with a `Step.parStar.isBi` witness
to the paired `Step.parStarWithBi` form.  The two structures carry
the same chain shape; this just bundles the isBi witness pointwise. -/
theorem Step.parStar.isBi.toParStarWithBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {chain : Step.parStar sourceTerm targetTerm}
    (chainBi : Step.parStar.isBi chain) :
    Step.parStarWithBi sourceTerm targetTerm := by
  induction chainBi with
  | refl term => exact Step.parStarWithBi.refl term
  | trans firstBi _restBi restIH =>
      exact Step.parStarWithBi.trans firstBi restIH

/-! ## §1 — βι-restricted Church-Rosser. -/

/-- **Typed Church-Rosser for βι-witnessed reductions.**

If `a ⟶par* b` and `a ⟶par* c` (both via βι-witnessed chains), there
exists a common reduct `d` with `b ⟶par* d` and `c ⟶par* d`.

Proof: take `N := max n m` where `n` and `m` are the chain lengths.
By `cdIter_completion`, `b ⟶par* cdIter n a` and `c ⟶par* cdIter m a`.
By `cdIter_le`, `cdIter n a ⟶par* cdIter N a` and likewise for `m`.
Append.  Common reduct: `d := cdIter N a`. -/
theorem Step.parStarWithBi.confluence
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm firstTarget secondTarget : Term ctx termType}
    (firstChain : Step.parStarWithBi sourceTerm firstTarget)
    (secondChain : Step.parStarWithBi sourceTerm secondTarget) :
    ∃ commonReduct : Term ctx termType,
      Step.parStarWithBi firstTarget commonReduct ∧
      Step.parStarWithBi secondTarget commonReduct := by
  obtain ⟨firstCount, firstReachIter⟩ := firstChain.cdIter_completion
  obtain ⟨secondCount, secondReachIter⟩ := secondChain.cdIter_completion
  -- Use sum (firstCount + secondCount) as the join point — propext-free.
  refine ⟨Term.cdIter (firstCount + secondCount) sourceTerm, ?_, ?_⟩
  · exact Step.parStarWithBi.append firstReachIter
      (Step.parStarWithBi.cdIter_le
        (Nat.le_add_right firstCount secondCount) sourceTerm)
  · exact Step.parStarWithBi.append secondReachIter
      (Step.parStarWithBi.cdIter_le
        (Nat.le_add_left secondCount firstCount) sourceTerm)

/-- **Plain `Step.parStar` Church-Rosser corollary.**  Project the
βι-witnessed confluence to plain `Step.parStar` chains.

Note: requires `Step.parStar.isBi` witnesses on the input chains, since
the typed kernel's confluence holds only in the βι-restricted regime.
η-rules are excluded by `Step.par.isBi` because parallel reduction
with extensional-η is not confluent without additional structure. -/
theorem Step.parStar.confluence
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm firstTarget secondTarget : Term ctx termType}
    {firstChain : Step.parStar sourceTerm firstTarget}
    {secondChain : Step.parStar sourceTerm secondTarget}
    (firstChainBi : Step.parStar.isBi firstChain)
    (secondChainBi : Step.parStar.isBi secondChain) :
    ∃ commonReduct : Term ctx termType,
      ∃ commonReductFirstChain : Step.parStar firstTarget commonReduct,
      ∃ commonReductSecondChain : Step.parStar secondTarget commonReduct,
        Step.parStar.isBi commonReductFirstChain ∧
        Step.parStar.isBi commonReductSecondChain := by
  let firstWithBi : Step.parStarWithBi sourceTerm firstTarget :=
    firstChainBi.toParStarWithBi
  let secondWithBi : Step.parStarWithBi sourceTerm secondTarget :=
    secondChainBi.toParStarWithBi
  obtain ⟨commonReduct, firstCommonChain, secondCommonChain⟩ :=
    Step.parStarWithBi.confluence firstWithBi secondWithBi
  exact ⟨commonReduct,
    firstCommonChain.toParStar, secondCommonChain.toParStar,
    firstCommonChain.toIsBi, secondCommonChain.toIsBi⟩

/-! ## §2 — Conv canonical form (#886 / W8.4).

Convertible terms have a common reduct, in the βι-restricted regime.

`Conv.isBi` tracks whether each underlying `Step` (lifted via `toPar`)
satisfies `Step.par.isBi`.  This excludes the η-rules `etaArrow` and
`etaSigma` — η-reductions break Church-Rosser at the parallel-reduction
level (parallel reduction with extensional η is not confluent without
additional structure).

For βι-Conv, every chain through Conv lifts to two parStarWithBi paths
that meet at a common reduct (via the confluence theorem). -/

/-- A `Conv` proof is βι if every underlying `Step` (lifted via `toPar`)
satisfies `Step.par.isBi`.  Excludes `etaArrow` and `etaSigma`. -/
inductive Conv.isBi :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {termType : Ty level scope} →
    {sourceTerm targetTerm : Term ctx termType} →
    Conv sourceTerm targetTerm → Prop
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {termType : Ty level scope} (term : Term ctx termType),
      Conv.isBi (Conv.refl term)
  | sym :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        {firstTerm secondTerm : Term ctx termType}
        {parentConv : Conv firstTerm secondTerm},
      Conv.isBi parentConv → Conv.isBi (Conv.sym parentConv)
  | trans :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        {firstTerm midTerm thirdTerm : Term ctx termType}
        {firstConv : Conv firstTerm midTerm}
        {secondConv : Conv midTerm thirdTerm},
      Conv.isBi firstConv → Conv.isBi secondConv →
      Conv.isBi (Conv.trans firstConv secondConv)
  | fromStep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        {sourceTerm targetTerm : Term ctx termType}
        {step : Step sourceTerm targetTerm},
      Step.par.isBi (Step.toPar step) →
      Conv.isBi (Conv.fromStep step)

/-- Lift a `Conv.isBi`-witnessed proof to a `Step.parStarWithBi`-pair
with a common reduct.

Proof: induction on the `Conv` (and matching `Conv.isBi`).
* `refl t`: common reduct is `t`.
* `sym h`: swap the two chains in the IH.
* `trans h1 h2`: take IH1's common reduct `c1` and IH2's `c2`.  Both
  are reachable from the midterm — apply confluence on `parStarWithBi`
  to find a common reduct of `c1` and `c2`.  Combine.
* `fromStep s`: common reduct is target; lift via `Step.toPar.toParStar`. -/
theorem Conv.canonical_form_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {convProof : Conv sourceTerm targetTerm}
    (convIsBi : Conv.isBi convProof) :
    ∃ commonReduct : Term ctx termType,
      Step.parStarWithBi sourceTerm commonReduct ∧
      Step.parStarWithBi targetTerm commonReduct := by
  induction convIsBi with
  | refl term =>
      exact ⟨term, Step.parStarWithBi.refl term,
        Step.parStarWithBi.refl term⟩
  | sym _parentBi parentIH =>
      obtain ⟨commonReduct, sourceChain, targetChain⟩ := parentIH
      exact ⟨commonReduct, targetChain, sourceChain⟩
  | trans _firstBi _secondBi firstIH secondIH =>
      obtain ⟨firstCommon, sourceToFirst, midToFirst⟩ := firstIH
      obtain ⟨secondCommon, midToSecond, targetToSecond⟩ := secondIH
      -- Confluence on midTerm: midToFirst and midToSecond converge.
      obtain ⟨jointReduct, firstToJoint, secondToJoint⟩ :=
        Step.parStarWithBi.confluence midToFirst midToSecond
      exact ⟨jointReduct,
        Step.parStarWithBi.append sourceToFirst firstToJoint,
        Step.parStarWithBi.append targetToSecond secondToJoint⟩
  | fromStep stepIsBi =>
      rename_i targetTerm _
      exact ⟨targetTerm,
        stepIsBi.toParStarWithBi,
        Step.parStarWithBi.refl targetTerm⟩

/-- Canonical form theorem: convertible terms (in the βι-restricted
regime) have a common reduct via `Step.parStar`.

Closes **#886** (W8.4 / Conv.canonical_form): convertible terms have a
common reduct.  The `Conv.isBi` hypothesis restricts to η-free
convertibility — η-rules are excluded by the `Step.par.isBi`
predicate underlying typed Church-Rosser. -/
theorem Conv.canonical_form
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {convProof : Conv sourceTerm targetTerm}
    (convIsBi : Conv.isBi convProof) :
    ∃ commonReduct : Term ctx termType,
      Step.parStar sourceTerm commonReduct ∧
      Step.parStar targetTerm commonReduct := by
  obtain ⟨commonReduct, sourceWithBi, targetWithBi⟩ :=
    Conv.canonical_form_isBi convIsBi
  exact ⟨commonReduct, sourceWithBi.toParStar, targetWithBi.toParStar⟩

end LeanFX.Syntax
