import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Core.Newman

/-! # FX1Poly/Modal/GradedReductionConfluence — β-confluence for GradedLambda

Completing the usage-dimension `GradedLambda` STLC substrate into a full reference calculus: alongside
strong normalization and subject reduction, β-reduction is CONFLUENT on the strongly-
normalizing (= simply-typed) fragment — so every term has a UNIQUE normal form (toward decidable
definitional equality).  This reuses the abstract, relation-generic Newman's lemma
`FX1Poly.Core.newmanAux` (per-term confluence from local confluence + the term's `Acc`, which is
exactly `IsStronglyNormalizing`), so untyped Ω is no obstacle — confluence is derived FROM SN.

**The reduction-substitutivity infrastructure** the local-confluence
critical-pair analysis consumes:

  * `GradedLambda.ReducesStar` — multi-step β-reduction (the `ReflTransClosure` of `Reduces`).
  * `renameTerm_eq_applySubstitution_var` + `Reduces.renameTerm` / `Reduces.shift` — reduction is
    preserved under renaming/shift (a corollary of the shipped `Reduces.applySubstitution`, since a
    renaming is just a variable-substitution).
  * `ReducesStar.congLam` / `congAppLeft` / `congAppRight` — multi-step congruence closures.
  * `Reduces.substReducedArg` — reducing the substituted argument multi-reduces the substitution
    result (many steps: the body may have several occurrences of the substituted variable).  The
    binder case shifts the argument (`Reduces.shift`) and re-substitutes under the bumped index.

**Local confluence and Newman:**

  * `Reduces.localConfluent` / `Reduces.weaklyConfluent` — **`WeaklyConfluent Reduces`**, the 9-case β
    critical-pair analysis on `app` (beta×beta same reduct; beta-vs-cong nested redexes joined via
    `Reduces.substAt` / `substReducedArg` against a residual `Reduces.beta`; same-side cong-vs-cong via
    the subterm IH + a cong-star; disjoint left-vs-right cong joined in one step each).
  * `IsStronglyNormalizing.confluent` — **confluence on the SN fragment** via the relation-generic
    `newmanAux` (the per-term `Acc` IS `IsStronglyNormalizing`), so untyped Ω is no obstacle.
  * `HasSimpleType.confluent` — the payoff: **every well-simply-typed `GradedLambda` term is
    confluent** (SN supplied by the Tait fundamental theorem).

**Unique normal forms:**

  * `IsNormalForm` (a term admits no step) + `IsNormalForm.eq_of_reducesStar` (a normal form only
    refl-reduces) + `var_isNormalForm` (non-vacuity anchor).
  * `IsStronglyNormalizing.uniqueNormalForm` — an SN term reduces to at most one normal form (confluence
    joins two NFs; each only refl-reduces, so each equals the join point).
  * `HasSimpleType.uniqueNormalForm` — every well-simply-typed term has a unique β-NF (the bridge to
    decidable conversion).

The normalizer (`fireRedex?` + `Acc.rec` on SN) and decidable `Conv` (`normalize a = normalize b`) on
the typed fragment live in `GradedNormalization.lean`.

## Zero-axiom verification

`Reduces.renameTerm`/`shift` are `rw` + the shipped substitution lemma; the cong-stars are inductions
on `ReflTransClosure` (propext-clean — its indices are free variables); `substReducedArg` is a term
induction with explicit `if`-reduction (`rw [if_pos]`/`if_neg]`, never `simp` on `ite`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure Joinable WeaklyConfluent)

/-- Multi-step β-reduction: the reflexive-transitive closure of `Reduces`. -/
abbrev GradedLambda.ReducesStar : GradedLambda → GradedLambda → Prop :=
  ReflTransClosure GradedLambda.Reduces

/-- A renaming is the parallel substitution sending each variable to the renamed variable. -/
theorem GradedLambda.renameTerm_eq_applySubstitution_var (term : GradedLambda) :
    ∀ (indexRenaming : IndexRenaming),
      GradedLambda.renameTerm indexRenaming term
        = GradedLambda.applySubstitution (fun index => GradedLambda.var (indexRenaming index)) term := by
  induction term with
  | var index => intro _; rfl
  | lam body bodyIH =>
      intro indexRenaming
      show GradedLambda.lam (GradedLambda.renameTerm (liftRenaming indexRenaming) body)
        = GradedLambda.lam (GradedLambda.applySubstitution
            (liftSubstitution (fun index => GradedLambda.var (indexRenaming index))) body)
      rw [bodyIH (liftRenaming indexRenaming)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.applySubstitution_congr
      intro index
      cases index with
      | zero => rfl
      | succ _ => rfl
  | app function argument functionIH argumentIH =>
      intro indexRenaming
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH indexRenaming, argumentIH indexRenaming]

/-- **Reduction is preserved under renaming** (a corollary of `Reduces.applySubstitution`: a renaming
is a var-substitution). -/
theorem GradedLambda.Reduces.renameTerm {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) (indexRenaming : IndexRenaming) :
    GradedLambda.Reduces (GradedLambda.renameTerm indexRenaming source)
      (GradedLambda.renameTerm indexRenaming reduct) := by
  rw [GradedLambda.renameTerm_eq_applySubstitution_var source indexRenaming,
    GradedLambda.renameTerm_eq_applySubstitution_var reduct indexRenaming]
  exact step.applySubstitution (fun index => GradedLambda.var (indexRenaming index))

/-- **Reduction is preserved under `shift 0`** (renaming at `incrementIndex`). -/
theorem GradedLambda.Reduces.shift {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) :
    GradedLambda.Reduces (GradedLambda.shift 0 source) (GradedLambda.shift 0 reduct) := by
  rw [shift_zero_eq_renameTerm source, shift_zero_eq_renameTerm reduct]
  exact step.renameTerm incrementIndex

/-- Multi-step congruence: a lambda's body reducing many steps reduces the lambda. -/
theorem GradedLambda.ReducesStar.congLam {body body' : GradedLambda}
    (bodyStar : GradedLambda.ReducesStar body body') :
    GradedLambda.ReducesStar (GradedLambda.lam body) (GradedLambda.lam body') := by
  induction bodyStar with
  | refl _ => exact ReflTransClosure.refl _
  | head first _ inductionHypothesis =>
      exact ReflTransClosure.head (GradedLambda.Reduces.congLam _ _ first) inductionHypothesis

/-- Multi-step congruence: reducing the function part of an application. -/
theorem GradedLambda.ReducesStar.congAppLeft {function function' argument : GradedLambda}
    (functionStar : GradedLambda.ReducesStar function function') :
    GradedLambda.ReducesStar (GradedLambda.app function argument) (GradedLambda.app function' argument) := by
  induction functionStar with
  | refl _ => exact ReflTransClosure.refl _
  | head first _ inductionHypothesis =>
      exact ReflTransClosure.head (GradedLambda.Reduces.congAppLeft _ _ argument first) inductionHypothesis

/-- Multi-step congruence: reducing the argument part of an application. -/
theorem GradedLambda.ReducesStar.congAppRight {function argument argument' : GradedLambda}
    (argumentStar : GradedLambda.ReducesStar argument argument') :
    GradedLambda.ReducesStar (GradedLambda.app function argument) (GradedLambda.app function argument') := by
  induction argumentStar with
  | refl _ => exact ReflTransClosure.refl _
  | head first _ inductionHypothesis =>
      exact ReflTransClosure.head (GradedLambda.Reduces.congAppRight function _ _ first) inductionHypothesis

/-- **Argument-substitutivity**: reducing the substituted argument reduces the substitution result
(many steps, since the body may have several occurrences of the substituted variable). -/
theorem GradedLambda.Reduces.substReducedArg {replacement replacement' : GradedLambda}
    (step : GradedLambda.Reduces replacement replacement') :
    ∀ (cut : Nat) (body : GradedLambda),
      GradedLambda.ReducesStar (GradedLambda.substAt cut replacement body)
        (GradedLambda.substAt cut replacement' body) := by
  intro cut body
  induction body generalizing cut replacement replacement' with
  | var index =>
      by_cases hlt : index < cut
      · have lhs : GradedLambda.substAt cut replacement (GradedLambda.var index) = GradedLambda.var index := by
          rw [GradedLambda.substAt, if_pos hlt]
        have rhs : GradedLambda.substAt cut replacement' (GradedLambda.var index) = GradedLambda.var index := by
          rw [GradedLambda.substAt, if_pos hlt]
        rw [lhs, rhs]; exact ReflTransClosure.refl _
      · by_cases heq : index = cut
        · have lhs : GradedLambda.substAt cut replacement (GradedLambda.var index) = replacement := by
            rw [GradedLambda.substAt, if_neg hlt, if_pos heq]
          have rhs : GradedLambda.substAt cut replacement' (GradedLambda.var index) = replacement' := by
            rw [GradedLambda.substAt, if_neg hlt, if_pos heq]
          rw [lhs, rhs]; exact ReflTransClosure.single step
        · have lhs : GradedLambda.substAt cut replacement (GradedLambda.var index) = GradedLambda.var (index - 1) := by
            rw [GradedLambda.substAt, if_neg hlt, if_neg heq]
          have rhs : GradedLambda.substAt cut replacement' (GradedLambda.var index) = GradedLambda.var (index - 1) := by
            rw [GradedLambda.substAt, if_neg hlt, if_neg heq]
          rw [lhs, rhs]; exact ReflTransClosure.refl _
  | lam innerBody bodyIH =>
      show GradedLambda.ReducesStar
        (GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement) innerBody))
        (GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement') innerBody))
      exact GradedLambda.ReducesStar.congLam (bodyIH step.shift (cut + 1))
  | app function argument functionIH argumentIH =>
      show GradedLambda.ReducesStar
        (GradedLambda.app (GradedLambda.substAt cut replacement function) (GradedLambda.substAt cut replacement argument))
        (GradedLambda.app (GradedLambda.substAt cut replacement' function) (GradedLambda.substAt cut replacement' argument))
      exact (GradedLambda.ReducesStar.congAppLeft (functionIH step cut)).trans
        (GradedLambda.ReducesStar.congAppRight (argumentIH step cut))

/-- **Local (weak) confluence of β**: two divergent single steps from the same term join.  The 9-case
critical-pair analysis on `app` (the only redex shape is `app (lam body) arg`): `beta×beta` is the same
reduct; `beta`-vs-`congAppLeft` joins at the substitution of the reduced body (`Reduces.substAt`)
against a residual `Reduces.beta`; `beta`-vs-`congAppRight` joins at the substitution of the reduced
argument (`substReducedArg`, possibly many steps) against a residual `Reduces.beta`; same-side
`cong`-vs-`cong` uses the subterm IH and a cong-star; disjoint `congAppLeft`-vs-`congAppRight` joins in
one step each.  `var` does not reduce; `lam` is handled by the body IH + `ReducesStar.congLam`. -/
theorem GradedLambda.Reduces.localConfluent :
    ∀ (source : GradedLambda) {leftReduct rightReduct : GradedLambda},
      GradedLambda.Reduces source leftReduct → GradedLambda.Reduces source rightReduct →
        Joinable GradedLambda.Reduces leftReduct rightReduct := by
  intro source
  induction source with
  | var index => intro _ _ leftStep _; cases leftStep
  | lam body ihBody =>
      intro _ _ leftStep rightStep
      cases leftStep with
      | congLam _ leftBody leftStepBody =>
          cases rightStep with
          | congLam _ rightBody rightStepBody =>
              obtain ⟨joinBody, leftToJoin, rightToJoin⟩ := ihBody leftStepBody rightStepBody
              exact ⟨.lam joinBody, GradedLambda.ReducesStar.congLam leftToJoin,
                GradedLambda.ReducesStar.congLam rightToJoin⟩
  | app function argument ihFunction ihArgument =>
      intro _ _ leftStep rightStep
      cases leftStep with
      | beta leftBody _ =>
          cases rightStep with
          | beta _ _ =>
              exact ⟨GradedLambda.substAt 0 argument leftBody,
                ReflTransClosure.refl _, ReflTransClosure.refl _⟩
          | congAppLeft _ rightFn _ rightStepFn =>
              cases rightStepFn with
              | congLam _ rightBody rightStepBody =>
                  exact ⟨GradedLambda.substAt 0 argument rightBody,
                    ReflTransClosure.single (rightStepBody.substAt 0 argument),
                    ReflTransClosure.single (GradedLambda.Reduces.beta rightBody argument)⟩
          | congAppRight _ _ rightArg rightStepArg =>
              exact ⟨GradedLambda.substAt 0 rightArg leftBody,
                rightStepArg.substReducedArg 0 leftBody,
                ReflTransClosure.single (GradedLambda.Reduces.beta leftBody rightArg)⟩
      | congAppLeft _ leftFn _ leftStepFn =>
          cases rightStep with
          | beta rightBody _ =>
              cases leftStepFn with
              | congLam _ leftBody leftStepBody =>
                  exact ⟨GradedLambda.substAt 0 argument leftBody,
                    ReflTransClosure.single (GradedLambda.Reduces.beta leftBody argument),
                    ReflTransClosure.single (leftStepBody.substAt 0 argument)⟩
          | congAppLeft _ rightFn _ rightStepFn =>
              obtain ⟨joinFn, leftToJoin, rightToJoin⟩ := ihFunction leftStepFn rightStepFn
              exact ⟨GradedLambda.app joinFn argument,
                GradedLambda.ReducesStar.congAppLeft leftToJoin,
                GradedLambda.ReducesStar.congAppLeft rightToJoin⟩
          | congAppRight _ _ rightArg rightStepArg =>
              exact ⟨GradedLambda.app leftFn rightArg,
                ReflTransClosure.single
                  (GradedLambda.Reduces.congAppRight leftFn argument rightArg rightStepArg),
                ReflTransClosure.single
                  (GradedLambda.Reduces.congAppLeft function leftFn rightArg leftStepFn)⟩
      | congAppRight _ _ leftArg leftStepArg =>
          cases rightStep with
          | beta rightBody _ =>
              exact ⟨GradedLambda.substAt 0 leftArg rightBody,
                ReflTransClosure.single (GradedLambda.Reduces.beta rightBody leftArg),
                leftStepArg.substReducedArg 0 rightBody⟩
          | congAppLeft _ rightFn _ rightStepFn =>
              exact ⟨GradedLambda.app rightFn leftArg,
                ReflTransClosure.single
                  (GradedLambda.Reduces.congAppLeft function rightFn leftArg rightStepFn),
                ReflTransClosure.single
                  (GradedLambda.Reduces.congAppRight rightFn argument leftArg leftStepArg)⟩
          | congAppRight _ _ rightArg rightStepArg =>
              obtain ⟨joinArg, leftToJoin, rightToJoin⟩ := ihArgument leftStepArg rightStepArg
              exact ⟨GradedLambda.app function joinArg,
                GradedLambda.ReducesStar.congAppRight leftToJoin,
                GradedLambda.ReducesStar.congAppRight rightToJoin⟩

/-- β-reduction on `GradedLambda` is **weakly confluent**. -/
theorem GradedLambda.Reduces.weaklyConfluent : WeaklyConfluent GradedLambda.Reduces := by
  intro source _ _ leftStep rightStep
  exact GradedLambda.Reduces.localConfluent source leftStep rightStep

/-- **Confluence on the strongly-normalizing fragment** (Newman's lemma): a β-SN term's divergent
multi-step reductions join.  `FX1Poly.Core.newmanAux` is relation-generic and consumes exactly the
per-term `Acc` that `IsStronglyNormalizing` packages, so confluence is derived FROM SN — untyped Ω
(which is not SN) is no obstacle. -/
theorem GradedLambda.IsStronglyNormalizing.confluent {source : GradedLambda}
    (sn : GradedLambda.IsStronglyNormalizing source) :
    ∀ {leftReduct rightReduct : GradedLambda},
      GradedLambda.ReducesStar source leftReduct → GradedLambda.ReducesStar source rightReduct →
        Joinable GradedLambda.Reduces leftReduct rightReduct :=
  FX1Poly.Core.newmanAux GradedLambda.Reduces.weaklyConfluent source sn

/-- **Every well-simply-typed `GradedLambda` term is confluent.**  SN — hence (Newman) confluence — is
supplied by the Tait fundamental theorem (`HasSimpleType.stronglyNormalizing`). -/
theorem HasSimpleType.confluent {typeContext : List SimpleType} {term : GradedLambda}
    {resultType : SimpleType} (typed : HasSimpleType typeContext term resultType) :
    ∀ {leftReduct rightReduct : GradedLambda},
      GradedLambda.ReducesStar term leftReduct → GradedLambda.ReducesStar term rightReduct →
        Joinable GradedLambda.Reduces leftReduct rightReduct :=
  typed.stronglyNormalizing.confluent

/-- A term is a **β-normal form** when it admits no reduction step. -/
def GradedLambda.IsNormalForm (term : GradedLambda) : Prop :=
  ∀ {reduct : GradedLambda}, ¬ GradedLambda.Reduces term reduct

/-- Every variable is a normal form (no rule reduces a bare variable) — a non-vacuity anchor showing
`IsNormalForm` is genuinely inhabited. -/
theorem GradedLambda.var_isNormalForm (index : Nat) :
    GradedLambda.IsNormalForm (.var index) := by
  intro reduct step; cases step

/-- A normal form multi-reduces only to itself: `ReducesStar` from a normal form is reflexive. -/
theorem GradedLambda.IsNormalForm.eq_of_reducesStar {term reduct : GradedLambda}
    (nf : GradedLambda.IsNormalForm term) (star : GradedLambda.ReducesStar term reduct) :
    term = reduct := by
  cases star with
  | refl => rfl
  | head firstStep _ => exact (nf firstStep).elim

/-- **Uniqueness of normal forms** on the strongly-normalizing fragment: if a β-SN term reduces (in
many steps) to two normal forms, they are equal.  Confluence joins the two normal forms at a common
reduct; a normal form only refl-reduces, so each normal form equals that join point, hence each
other. -/
theorem GradedLambda.IsStronglyNormalizing.uniqueNormalForm {term firstNF secondNF : GradedLambda}
    (sn : GradedLambda.IsStronglyNormalizing term)
    (firstStar : GradedLambda.ReducesStar term firstNF)
    (secondStar : GradedLambda.ReducesStar term secondNF)
    (firstIsNF : GradedLambda.IsNormalForm firstNF) (secondIsNF : GradedLambda.IsNormalForm secondNF) :
    firstNF = secondNF := by
  obtain ⟨joinPoint, firstToJoin, secondToJoin⟩ := sn.confluent firstStar secondStar
  rw [firstIsNF.eq_of_reducesStar firstToJoin, secondIsNF.eq_of_reducesStar secondToJoin]

/-- **Every well-simply-typed `GradedLambda` term has a unique normal form** (SN from the Tait
fundamental theorem). -/
theorem HasSimpleType.uniqueNormalForm {typeContext : List SimpleType} {term : GradedLambda}
    {resultType : SimpleType} (typed : HasSimpleType typeContext term resultType)
    {firstNF secondNF : GradedLambda}
    (firstStar : GradedLambda.ReducesStar term firstNF)
    (secondStar : GradedLambda.ReducesStar term secondNF)
    (firstIsNF : GradedLambda.IsNormalForm firstNF) (secondIsNF : GradedLambda.IsNormalForm secondNF) :
    firstNF = secondNF :=
  typed.stronglyNormalizing.uniqueNormalForm firstStar secondStar firstIsNF secondIsNF

end FX1Poly.Modal
