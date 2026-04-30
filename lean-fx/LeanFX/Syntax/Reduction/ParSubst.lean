import LeanFX.Syntax.Reduction.ParCompatible

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Parallel substitution lemma — typed analogue.

`Term.subst_par_pointwise` is the typed companion of
`RawTerm.subst_par_pointwise` (RawParCompatible).  Statement: with
the underlying type-substitution `σ` held fixed, two TermSubsts
`σt`, `σt'` that are pointwise `Step.par`-related substitute any
term to a `Step.par`-related pair.  Proof: structural induction on
the term; binder cases use `TermSubst.par_lift`; eliminator cases
that introduce `Ty.subst0_subst_commute` casts use
`Step.par.castBoth` to lift the cast on both sides uniformly.

Combined with `Step.par.subst_compatible` (#985), this yields
`Step.par.subst0_par`: `Step.par body body' → Step.par arg arg' →
Step.par (subst0 body arg) (subst0 body' arg')` — the workhorse
for the β cases of typed `Step.par.cd_lemma`. -/

/-- Lifting two pointwise-Step.par-related TermSubsts under a binder
preserves the relation.  At position 0 both produce `Term.var 0`
(modulo the same cast) so `Step.par.refl` closes; at position
`k + 1` both produce `Term.weaken _ (σt ⟨k, _⟩)` (modulo the same
cast), so the lifted relation reduces to renaming-compatibility on
the original step `related ⟨k, _⟩`. -/
theorem TermSubst.par_lift
    {mode : Mode} {scope scope' : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level scope'}
    {typeSubstitution : Subst level scope scope'}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (related : ∀ position,
      Step.par (firstSubstitution position) (secondSubstitution position))
    (newType : Ty level scope) :
    ∀ position,
      Step.par
        ((firstSubstitution.lift newType) position)
        ((secondSubstitution.lift newType) position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.lift]
      exact Step.par.castBoth
        (Ty.subst_weaken_commute newType typeSubstitution).symm
        (Step.par.refl _)
  | ⟨index + 1, isWithinBound⟩ =>
      simp only [TermSubst.lift]
      exact Step.par.castBoth
        (Ty.subst_weaken_commute
          (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩)
          typeSubstitution).symm
        (Step.par.rename_compatible
          (TermRenaming.weaken targetCtx (newType.subst typeSubstitution))
          (related ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩))

/-- **Joint substitution lemma — refl-side.**  When the underlying
type-substitution `σ` is held fixed and two TermSubsts `σt`, `σt'`
are pointwise `Step.par`-related, applying them to the same term
yields `Step.par`-related results.

Proof: structural induction on the term.  In every case the two
sides share the same constructor and the same Ty-level cast
witnesses (since `σ` is fixed); only the recursive `Term.subst`
call differs in its TermSubst argument.  Each constructor closes
by applying the corresponding `Step.par` congruence rule to the
recursive IH.

This is the typed analogue of `RawTerm.subst_par_pointwise`. -/
theorem Term.subst_par_pointwise
    {mode : Mode} {scope scope' : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level scope'}
    {typeSubstitution : Subst level scope scope'}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (related : ∀ position,
      Step.par (firstSubstitution position) (secondSubstitution position)) :
    {T : Ty level scope} → (term : Term sourceCtx T) →
      Step.par
        (Term.subst firstSubstitution term)
        (Term.subst secondSubstitution term)
  | _, .var position => by
      simp only [Term.subst]
      exact related position
  | _, .unit => Step.par.refl _
  | _, .lam (codomainType := codomainType) body => by
      simp only [Term.subst]
      exact Step.par.lam
        (Step.par.castBoth
          (Ty.subst_weaken_commute codomainType typeSubstitution)
          (Term.subst_par_pointwise
            (TermSubst.par_lift related _) body))
  | _, .app function argument =>
      Step.par.app
        (Term.subst_par_pointwise related function)
        (Term.subst_par_pointwise related argument)
  | _, .lamPi body => by
      simp only [Term.subst]
      exact Step.par.lamPi
        (Term.subst_par_pointwise (TermSubst.par_lift related _) body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        function argument => by
      simp only [Term.subst]
      exact Step.par.castBoth
        (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
        (Step.par.appPi
          (Term.subst_par_pointwise related function)
          (Term.subst_par_pointwise related argument))
  | _, .pair (firstType := firstType) (secondType := secondType)
        firstVal secondVal => by
      simp only [Term.subst]
      exact Step.par.pair
        (Term.subst_par_pointwise related firstVal)
        (Step.par.castBoth
          (Ty.subst0_subst_commute secondType firstType typeSubstitution)
          (Term.subst_par_pointwise related secondVal))
  | _, .fst pairTerm =>
      Step.par.fst (Term.subst_par_pointwise related pairTerm)
  | _, .snd (firstType := firstType) (secondType := secondType) pairTerm => by
      simp only [Term.subst]
      exact Step.par.castBoth
        (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
        (Step.par.snd (Term.subst_par_pointwise related pairTerm))
  | _, .boolTrue => Step.par.refl _
  | _, .boolFalse => Step.par.refl _
  | _, .boolElim scrutinee thenBranch elseBranch =>
      Step.par.boolElim
        (Term.subst_par_pointwise related scrutinee)
        (Term.subst_par_pointwise related thenBranch)
        (Term.subst_par_pointwise related elseBranch)
  | _, .natZero => Step.par.refl _
  | _, .natSucc predecessor =>
      Step.par.natSucc (Term.subst_par_pointwise related predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Step.par.natElim
        (Term.subst_par_pointwise related scrutinee)
        (Term.subst_par_pointwise related zeroBranch)
        (Term.subst_par_pointwise related succBranch)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Step.par.natRec
        (Term.subst_par_pointwise related scrutinee)
        (Term.subst_par_pointwise related zeroBranch)
        (Term.subst_par_pointwise related succBranch)
  | _, .listNil => Step.par.refl _
  | _, .listCons head tail =>
      Step.par.listCons
        (Term.subst_par_pointwise related head)
        (Term.subst_par_pointwise related tail)
  | _, .listElim scrutinee nilBranch consBranch =>
      Step.par.listElim
        (Term.subst_par_pointwise related scrutinee)
        (Term.subst_par_pointwise related nilBranch)
        (Term.subst_par_pointwise related consBranch)
  | _, .optionNone => Step.par.refl _
  | _, .optionSome value =>
      Step.par.optionSome (Term.subst_par_pointwise related value)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Step.par.optionMatch
        (Term.subst_par_pointwise related scrutinee)
        (Term.subst_par_pointwise related noneBranch)
        (Term.subst_par_pointwise related someBranch)
  | _, .eitherInl value =>
      Step.par.eitherInl (Term.subst_par_pointwise related value)
  | _, .eitherInr value =>
      Step.par.eitherInr (Term.subst_par_pointwise related value)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Step.par.eitherMatch
        (Term.subst_par_pointwise related scrutinee)
        (Term.subst_par_pointwise related leftBranch)
        (Term.subst_par_pointwise related rightBranch)
  | _, .refl _ => Step.par.refl _
  | _, .idJ baseCase witness =>
      Step.par.idJ
        (Term.subst_par_pointwise related baseCase)
        (Term.subst_par_pointwise related witness)

/-- **Joint substitution at the singleton.**  Pointwise lift of a
single Step.par on the substituent: applying `TermSubst.singleton arg`
vs `TermSubst.singleton arg'` to the same body yields `Step.par`-
related results.  This is the "argument-side" half of
`Step.par.subst0_par`. -/
theorem TermSubst.singleton_par_pointwise
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope}
    {firstArgument secondArgument : Term sourceCtx argType}
    (argumentStep : Step.par firstArgument secondArgument) :
    ∀ position,
      Step.par
        ((TermSubst.singleton firstArgument) position)
        ((TermSubst.singleton secondArgument) position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.singleton]
      exact Step.par.castBoth
        (Ty.weaken_subst_singleton argType argType).symm
        argumentStep
  | ⟨index + 1, isWithinBound⟩ =>
      simp only [TermSubst.singleton]
      exact Step.par.castBoth
        (Ty.weaken_subst_singleton
          (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩)
          argType).symm
        (Step.par.refl _)

/-! ## Reflexive-transitive closure of typed `Step.par`.

Mirrors `RawStep.parStar`.  The relaxed Tait–Martin-Löf method
phrases cd_lemma at the multi-step level: `Step.par t t' →
Step.parStar t' (Term.cd t)`.  This avoids needing a single-step
joint substitution lemma (which fails because `Step.par` is
reflexive but not transitive); instead the β case chains two
`Step.par` steps via `Step.parStar.append`. -/

/-- Reflexive-transitive closure of typed `Step.par`.  The empty
chain witnesses `t = t`; the cons case prepends a single
`Step.par` to a chain of further parallel reductions. -/
inductive Step.parStar :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {termType : Ty level scope} → Term ctx termType → Term ctx termType → Prop
  | refl :
      ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope} (term : Term ctx termType),
      Step.parStar term term
  | trans :
      ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        {firstTerm secondTerm thirdTerm : Term ctx termType},
      Step.par firstTerm secondTerm →
      Step.parStar secondTerm thirdTerm →
      Step.parStar firstTerm thirdTerm

/-- Lift a single parallel step to the reflexive-transitive
closure. -/
theorem Step.par.toParStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.parStar sourceTerm targetTerm :=
  Step.parStar.trans parallelStep (Step.parStar.refl _)

/-- Append a single parallel step to the end of a `parStar` chain. -/
theorem Step.parStar.snoc
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {firstTerm secondTerm thirdTerm : Term ctx termType}
    (chain : Step.parStar firstTerm secondTerm)
    (parallelStep : Step.par secondTerm thirdTerm) :
    Step.parStar firstTerm thirdTerm := by
  induction chain with
  | refl _ => exact Step.par.toParStar parallelStep
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans firstStep (restIH parallelStep)

/-- Concatenate two `parStar` chains. -/
theorem Step.parStar.append
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {firstTerm secondTerm thirdTerm : Term ctx termType}
    (firstChain : Step.parStar firstTerm secondTerm)
    (secondChain : Step.parStar secondTerm thirdTerm) :
    Step.parStar firstTerm thirdTerm := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans firstStep (restIH secondChain)

/-- Multi-step substitution-side compatibility: a `parStar` chain
on the body lifts through any TermSubst.  Used by the β-case of
the relaxed cd_lemma. -/
theorem Step.parStar.subst_compatible
    {mode : Mode} {scope scope' : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level scope'}
    {typeSubstitution : Subst level scope scope'}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level scope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    (parallelChain : Step.parStar beforeTerm afterTerm) :
    Step.parStar
      (Term.subst termSubstitution beforeTerm)
      (Term.subst termSubstitution afterTerm) := by
  induction parallelChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.subst_compatible termSubstitution firstStep)
        restIH

/-- **Multi-step argument-side parallel substitution at the
singleton.**  A `parStar` chain on the singleton's substituent
lifts to a `parStar` chain on `Term.subst0 body`.  Proof: induct
on the chain at the substituent; each `Step.par` step lifts to a
single `Step.par` step on `Term.subst0` via
`Term.subst_par_pointwise` + `TermSubst.singleton_par_pointwise`,
chained via `Step.parStar.trans`.  The β-case of the relaxed
cd_lemma uses this to convert `Step.parStar arg' (cd arg)` (the
argumentIH from the recursive cd_lemma) into a `parStar` chain on
the substituted body. -/
theorem Term.subst0_parStar_argument
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    (body : Term (sourceCtx.cons argType) bodyType)
    {firstArgument secondArgument : Term sourceCtx argType}
    (argumentChain : Step.parStar firstArgument secondArgument) :
    Step.parStar
      (Term.subst0 body firstArgument)
      (Term.subst0 body secondArgument) := by
  induction argumentChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Term.subst_par_pointwise
          (TermSubst.singleton_par_pointwise firstStep) body)
        restIH

/-- **Body-side multi-step subst0**.  A `parStar` chain on the
body lifts to a `parStar` chain on `Term.subst0 body arg` (with
the argument fixed).  Specialisation of
`Step.parStar.subst_compatible` to `TermSubst.singleton arg`. -/
theorem Term.subst0_parStar_body
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    {firstBody secondBody : Term (sourceCtx.cons argType) bodyType}
    (bodyChain : Step.parStar firstBody secondBody)
    (argument : Term sourceCtx argType) :
    Step.parStar
      (Term.subst0 firstBody argument)
      (Term.subst0 secondBody argument) :=
  Step.parStar.subst_compatible (TermSubst.singleton argument) bodyChain

/-- **The cd_lemma β-case workhorse, parStar form.**  Given
multi-step chains on body and argument, the joint
`Term.subst0` step lifts to a multi-step chain.  This is what the
relaxed cd_lemma's β-cases use: we get a `parStar` (not single
`Step.par`), but that's still strong enough for parStar
confluence via the standard strip-lemma argument. -/
theorem Step.parStar.subst0_parStar
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    {firstBody secondBody : Term (sourceCtx.cons argType) bodyType}
    {firstArgument secondArgument : Term sourceCtx argType}
    (bodyChain : Step.parStar firstBody secondBody)
    (argumentChain : Step.parStar firstArgument secondArgument) :
    Step.parStar
      (Term.subst0 firstBody firstArgument)
      (Term.subst0 secondBody secondArgument) :=
  Step.parStar.append
    (Term.subst0_parStar_body bodyChain firstArgument)
    (Term.subst0_parStar_argument secondBody argumentChain)

end LeanFX.Syntax
