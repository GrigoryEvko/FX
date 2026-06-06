import FX1Poly.Modal.GradedReductionSubstitution

/-! # FX1Poly/Modal/GradedFundamentalTheorem — Tait SN + the graded-SN transfer

The orthogonal-composition thesis closed end-to-end.  The TYPE dimension's strong-normalization
obligation (`HasSimpleType → SN`, the classic STLC Tait result) is proved ONCE via the logical
relation; graded strong normalization (`HasUsage → SN`) is then the TRIVIAL corollary through grade
erasure, because the term and the β-reduction are grade-AGNOSTIC — adding the usage dimension does NOT
require redoing the SN metatheory.

  * `GradedLambda.IsStronglyNormalizing.lam` — SN of a body lifts to SN of its lambda.
  * `GradedLambda.Reducible.abstraction` — **the Tait abstraction lemma**: if every reducible
    instantiation of the body's `0`-th variable is reducible, the lambda is reducible at the arrow
    type.  Proved by CR3 on the neutral `app (lam body) argument` with a NESTED induction on SN(body)
    (outer) and SN(argument) (inner); the function-reduction case re-derives the body hypothesis for
    the reduced body via `Reduces.substAt` (iii-b) + CR2.
  * `ReducibleSubstitution` + `cons` — the closing-substitution reducible environment.
  * `HasSimpleType.fundamental` — **the fundamental theorem**: a well-typed term with reducible terms
    substituted for its free variables is reducible (var/lam/app; the λ-case applies the abstraction
    lemma and rewrites the β-reduct via the composition (★) from iii-b into the extended environment).
  * `HasSimpleType.reducible` / `HasSimpleType.stronglyNormalizing` — every well-typed term is
    reducible (identity substitution + `applySubstitution_id`), hence strongly normalizing (CR1).
  * `HasUsage.stronglyNormalizing` — **the headline**: every `HasUsage`-typed term is
    strongly normalizing, via `HasUsage.erase` + STLC-SN.  Graded-SN rides on type-dimension
    SN with no graded re-proof.  `linearIdentity_stronglyNormalizing` / `kCombinator_stronglyNormalizing`
    are concrete non-vacuous witnesses.

## Zero-axiom verification

Funext-free; the abstraction lemma's nested SN-induction reconstructs the inner accessibility witness
explicitly (`Acc.intro argument accArgument`) for the outer IH; `cases` on the indexed `Reduces` is
propext-clean (`GradedLambda` is a plain inductive); `Option.some.inj` for the cons-zero lookup is
clean.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- SN of a body lifts to SN of its lambda (a lambda's only reducts are lambdas of body reducts). -/
theorem GradedLambda.IsStronglyNormalizing.lam {body : GradedLambda}
    (snBody : GradedLambda.IsStronglyNormalizing body) :
    GradedLambda.IsStronglyNormalizing (GradedLambda.lam body) := by
  have generalized : ∀ (innerBody : GradedLambda), GradedLambda.IsStronglyNormalizing innerBody →
      GradedLambda.IsStronglyNormalizing (GradedLambda.lam innerBody) := by
    intro innerBody snInner
    induction snInner with
    | intro innerBody _ innerIH =>
        apply Acc.intro
        intro reduct step
        cases step with
        | congLam _ reducedBody stepBody => exact innerIH reducedBody stepBody
  exact generalized body snBody

/-- **The Tait abstraction lemma**: if every reducible instantiation of the body's `0`-th variable is
reducible, the lambda is reducible at the arrow type.  CR3 on the neutral `app (lam body) argument`
with a nested induction on SN(body) (outer) and SN(argument) (inner); the function-reduction case
(`congAppLeft`) re-derives the hypothesis for the reduced body via `Reduces.substAt` + CR2. -/
theorem GradedLambda.Reducible.abstraction {domain codomain : SimpleType} {body : GradedLambda}
    (hyp : ∀ (argument : GradedLambda), GradedLambda.Reducible domain argument →
      GradedLambda.Reducible codomain (GradedLambda.substAt 0 argument body)) :
    GradedLambda.Reducible (SimpleType.arrow domain codomain) (GradedLambda.lam body) := by
  have snBody : GradedLambda.IsStronglyNormalizing body :=
    GradedLambda.IsStronglyNormalizing.ofSubstAt 0 (GradedLambda.var 0)
      (hyp (GradedLambda.var 0) (GradedLambda.Reducible.var domain 0)).sn
  have appReducible : ∀ (bodyCurrent : GradedLambda), GradedLambda.IsStronglyNormalizing bodyCurrent →
      (∀ (replacement : GradedLambda), GradedLambda.Reducible domain replacement →
        GradedLambda.Reducible codomain (GradedLambda.substAt 0 replacement bodyCurrent)) →
      ∀ (argument : GradedLambda), GradedLambda.IsStronglyNormalizing argument →
        GradedLambda.Reducible domain argument →
          GradedLambda.Reducible codomain (GradedLambda.app (GradedLambda.lam bodyCurrent) argument) := by
    intro bodyCurrent snBodyCurrent
    induction snBodyCurrent with
    | intro bodyCurrent _ bodyIH =>
        intro hypCurrent argument snArgument
        induction snArgument with
        | intro argument accArgument argumentIH =>
            intro redArgument
            refine GradedLambda.Reducible.ofNeutral True.intro ?_
            intro reduct stepApp
            cases stepApp with
            | beta _ _ => exact hypCurrent argument redArgument
            | congAppLeft _ functionReduct _ stepFunction =>
                cases stepFunction with
                | congLam _ reducedBody stepBody =>
                    exact bodyIH reducedBody stepBody
                      (fun replacement redReplacement =>
                        (hypCurrent replacement redReplacement).ofReduces (stepBody.substAt 0 replacement))
                      argument (Acc.intro argument accArgument) redArgument
            | congAppRight _ _ argumentReduct stepArgument =>
                exact argumentIH argumentReduct stepArgument (redArgument.ofReduces stepArgument)
  exact ⟨snBody.lam, fun argument redArgument =>
    appReducible body snBody hyp argument redArgument.sn redArgument⟩

/-- A substitution is reducible at a context when every variable's image is reducible at its declared
type — the closing-substitution environment of the fundamental theorem. -/
def ReducibleSubstitution (typeContext : List SimpleType) (substitution : TermSubstitution) : Prop :=
  ∀ (index : Nat) (varType : SimpleType),
    SimpleType.lookup typeContext index = some varType →
    GradedLambda.Reducible varType (substitution index)

/-- Extend a reducible substitution under a binder (the lam-case environment extension). -/
theorem ReducibleSubstitution.cons {domain : SimpleType} {head : GradedLambda}
    {typeContext : List SimpleType} {tail : TermSubstitution}
    (headReducible : GradedLambda.Reducible domain head)
    (tailReducible : ReducibleSubstitution typeContext tail) :
    ReducibleSubstitution (domain :: typeContext) (consSubstitution head tail) := by
  intro index varType lookupEq
  cases index with
  | zero =>
      have domainEq : domain = varType := Option.some.inj lookupEq
      rw [← domainEq]
      exact headReducible
  | succ predecessor => exact tailReducible predecessor varType lookupEq

/-- **The fundamental theorem of the logical relation**: a well-typed term, with reducible terms
substituted for its free variables, is reducible.  The λ-case applies the abstraction lemma, rewriting
the β-reduct of the substituted body via the composition (★) into the extended environment. -/
theorem HasSimpleType.fundamental {typeContext : List SimpleType} {term : GradedLambda}
    {resultType : SimpleType} (typed : HasSimpleType typeContext term resultType) :
    ∀ (substitution : TermSubstitution), ReducibleSubstitution typeContext substitution →
      GradedLambda.Reducible resultType (GradedLambda.applySubstitution substitution term) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      intro substitution reducibleSubst
      exact reducibleSubst index varType lookupOk
  | lam typeContext domain codomain body _ bodyIH =>
      intro substitution reducibleSubst
      show GradedLambda.Reducible (SimpleType.arrow domain codomain)
        (GradedLambda.lam (GradedLambda.applySubstitution (liftSubstitution substitution) body))
      apply GradedLambda.Reducible.abstraction
      intro argument redArgument
      rw [substAt_zero_applySubstitution_lift body argument substitution]
      exact bodyIH (consSubstitution argument substitution)
        (ReducibleSubstitution.cons redArgument reducibleSubst)
  | app typeContext domain codomain function argument _ _ functionIH argumentIH =>
      intro substitution reducibleSubst
      show GradedLambda.Reducible codomain
        (GradedLambda.app (GradedLambda.applySubstitution substitution function)
          (GradedLambda.applySubstitution substitution argument))
      exact (functionIH substitution reducibleSubst).2
        (GradedLambda.applySubstitution substitution argument) (argumentIH substitution reducibleSubst)

/-- **Every well-typed term is reducible** (the fundamental theorem at the identity substitution,
which the identity-substitution lemma collapses back to the term itself). -/
theorem HasSimpleType.reducible {typeContext : List SimpleType} {term : GradedLambda}
    {resultType : SimpleType} (typed : HasSimpleType typeContext term resultType) :
    GradedLambda.Reducible resultType term := by
  have identityReducible : ReducibleSubstitution typeContext (fun index => GradedLambda.var index) := by
    intro index varType _
    exact GradedLambda.Reducible.var varType index
  have result := typed.fundamental (fun index => GradedLambda.var index) identityReducible
  rw [GradedLambda.applySubstitution_id] at result
  exact result

/-- **STLC strong normalization**: every well-typed `GradedLambda` term is strongly normalizing (the
fundamental theorem + CR1).  This is the TYPE dimension's SN obligation — proved once. -/
theorem HasSimpleType.stronglyNormalizing {typeContext : List SimpleType} {term : GradedLambda}
    {resultType : SimpleType} (typed : HasSimpleType typeContext term resultType) :
    GradedLambda.IsStronglyNormalizing term :=
  typed.reducible.sn

-- Graded SN (`HasUsage.stronglyNormalizing` + the linearIdentity/kCombinator witnesses) is the bespoke
-- usage corollary, split into `GradedStrongNormalization.lean` so this shared STLC fundamental theorem
-- carries no usage-specific (`GradeErasure`/`GradedTyping`) import.

end FX1Poly.Modal
