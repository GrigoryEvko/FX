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

/-! ## `Step.parStar` congruence rules.

For each `Step.par` congruence constructor used by `Term.cd`, the
corresponding `parStar` rule says: a multi-step chain on a sub-term
lifts to a multi-step chain on the enclosing term.  Each is proved
by induction on the chain, prepending the single-step congruence
rule via `Step.parStar.trans`.

Used by `Step.par.cd_lemma_star` for the cong arms (where the IH
gives a `parStar` chain on the sub-term and the goal is a `parStar`
chain on the enclosing constructor). -/

/-- λ-body congruence at the `parStar` level. -/
theorem Step.parStar.lam_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyChain : Step.parStar body body') :
    Step.parStar
      (Term.lam (codomainType := codomainType) body)
      (Term.lam (codomainType := codomainType) body') := by
  induction bodyChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.lam firstStep) restIH

/-- Π-λ-body congruence at the `parStar` level. -/
theorem Step.parStar.lamPi_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body body' : Term (ctx.cons domainType) codomainType}
    (bodyChain : Step.parStar body body') :
    Step.parStar
      (Term.lamPi (domainType := domainType) body)
      (Term.lamPi (domainType := domainType) body') := by
  induction bodyChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.lamPi firstStep) restIH

/-- One-position `app` congruence: function chain with argument held
fixed.  Standalone helper so the induction motive doesn't drag
outer hypotheses into the IH. -/
theorem Step.parStar.app_cong_function
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm functionTerm' : Term ctx (Ty.arrow domainType codomainType)}
    (argumentTerm : Term ctx domainType)
    (functionChain : Step.parStar functionTerm functionTerm') :
    Step.parStar (Term.app functionTerm argumentTerm)
                 (Term.app functionTerm' argumentTerm) := by
  induction functionChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.app firstStep (Step.par.refl _)) restIH

/-- One-position `app` congruence: argument chain with function held
fixed. -/
theorem Step.parStar.app_cong_argument
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (functionTerm : Term ctx (Ty.arrow domainType codomainType))
    {argumentTerm argumentTerm' : Term ctx domainType}
    (argumentChain : Step.parStar argumentTerm argumentTerm') :
    Step.parStar (Term.app functionTerm argumentTerm)
                 (Term.app functionTerm argumentTerm') := by
  induction argumentChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.app (Step.par.refl _) firstStep) restIH

/-- Non-dependent application congruence at the `parStar` level.
Combines independent function and argument chains via sequential
`Step.parStar.append` of the two single-position helpers. -/
theorem Step.parStar.app_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm functionTerm' : Term ctx (Ty.arrow domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionChain : Step.parStar functionTerm functionTerm')
    (argumentChain : Step.parStar argumentTerm argumentTerm') :
    Step.parStar (Term.app functionTerm argumentTerm)
                 (Term.app functionTerm' argumentTerm') :=
  Step.parStar.append
    (Step.parStar.app_cong_function argumentTerm functionChain)
    (Step.parStar.app_cong_argument functionTerm' argumentChain)

/-- Single-position `appPi` congruence on function. -/
theorem Step.parStar.appPi_cong_function
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm functionTerm' : Term ctx (Ty.piTy domainType codomainType)}
    (argumentTerm : Term ctx domainType)
    (functionChain : Step.parStar functionTerm functionTerm') :
    Step.parStar (Term.appPi functionTerm argumentTerm)
                 (Term.appPi functionTerm' argumentTerm) := by
  induction functionChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.appPi firstStep (Step.par.refl _)) restIH

/-- Single-position `appPi` congruence on argument. -/
theorem Step.parStar.appPi_cong_argument
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (functionTerm : Term ctx (Ty.piTy domainType codomainType))
    {argumentTerm argumentTerm' : Term ctx domainType}
    (argumentChain : Step.parStar argumentTerm argumentTerm') :
    Step.parStar (Term.appPi functionTerm argumentTerm)
                 (Term.appPi functionTerm argumentTerm') := by
  induction argumentChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.appPi (Step.par.refl _) firstStep) restIH

/-- Dependent application congruence at the `parStar` level. -/
theorem Step.parStar.appPi_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm functionTerm' : Term ctx (Ty.piTy domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionChain : Step.parStar functionTerm functionTerm')
    (argumentChain : Step.parStar argumentTerm argumentTerm') :
    Step.parStar (Term.appPi functionTerm argumentTerm)
                 (Term.appPi functionTerm' argumentTerm') :=
  Step.parStar.append
    (Step.parStar.appPi_cong_function argumentTerm functionChain)
    (Step.parStar.appPi_cong_argument functionTerm' argumentChain)

/-- Single-position `pair` congruence on first component. -/
theorem Step.parStar.pair_cong_first
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal firstVal' : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (firstChain : Step.parStar firstVal firstVal') :
    Step.parStar (Term.pair (secondType := secondType) firstVal secondVal)
                 (Term.pair (secondType := secondType) firstVal' secondVal) := by
  induction firstChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.pair firstStep (Step.par.refl _)) restIH

/-- Single-position `pair` congruence on second component. -/
theorem Step.parStar.pair_cong_second
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (secondChain : Step.parStar secondVal secondVal') :
    Step.parStar (Term.pair (secondType := secondType) firstVal secondVal)
                 (Term.pair (secondType := secondType) firstVal secondVal') := by
  induction secondChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.pair (Step.par.refl _) firstStep) restIH

/-- Σ-pair congruence at the `parStar` level. -/
theorem Step.parStar.pair_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal firstVal' : Term ctx firstType}
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (firstChain : Step.parStar firstVal firstVal')
    (secondChain : Step.parStar secondVal secondVal') :
    Step.parStar (Term.pair firstVal secondVal)
                 (Term.pair firstVal' secondVal') :=
  Step.parStar.append
    (Step.parStar.pair_cong_first secondVal firstChain)
    (Step.parStar.pair_cong_second firstVal' secondChain)

/-- First-projection congruence at the `parStar` level. -/
theorem Step.parStar.fst_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairChain : Step.parStar pairTerm pairTerm') :
    Step.parStar (Term.fst pairTerm) (Term.fst pairTerm') := by
  induction pairChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.fst firstStep) restIH

/-- Second-projection congruence at the `parStar` level. -/
theorem Step.parStar.snd_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairChain : Step.parStar pairTerm pairTerm') :
    Step.parStar (Term.snd pairTerm) (Term.snd pairTerm') := by
  induction pairChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.snd firstStep) restIH

/-- Single-position `boolElim` congruence on scrutinee. -/
theorem Step.parStar.boolElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.bool}
    (thenBranch elseBranch : Term ctx resultType)
    (scrutineeChain : Step.parStar scrutinee scrutinee') :
    Step.parStar (Term.boolElim scrutinee thenBranch elseBranch)
                 (Term.boolElim scrutinee' thenBranch elseBranch) := by
  induction scrutineeChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.boolElim firstStep (Step.par.refl _) (Step.par.refl _))
        restIH

/-- Single-position `boolElim` congruence on then-branch. -/
theorem Step.parStar.boolElim_cong_then
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBranch thenBranch' : Term ctx resultType}
    (elseBranch : Term ctx resultType)
    (thenChain : Step.parStar thenBranch thenBranch') :
    Step.parStar (Term.boolElim scrutinee thenBranch elseBranch)
                 (Term.boolElim scrutinee thenBranch' elseBranch) := by
  induction thenChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.boolElim (Step.par.refl _) firstStep (Step.par.refl _))
        restIH

/-- Single-position `boolElim` congruence on else-branch. -/
theorem Step.parStar.boolElim_cong_else
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBranch : Term ctx resultType)
    {elseBranch elseBranch' : Term ctx resultType}
    (elseChain : Step.parStar elseBranch elseBranch') :
    Step.parStar (Term.boolElim scrutinee thenBranch elseBranch)
                 (Term.boolElim scrutinee thenBranch elseBranch') := by
  induction elseChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.boolElim (Step.par.refl _) (Step.par.refl _) firstStep)
        restIH

/-- Boolean eliminator congruence at the `parStar` level.  Three
chained legs (scrutinee, then-branch, else-branch). -/
theorem Step.parStar.boolElim_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.bool}
    {thenBranch thenBranch' : Term ctx resultType}
    {elseBranch elseBranch' : Term ctx resultType}
    (scrutineeChain : Step.parStar scrutinee scrutinee')
    (thenChain : Step.parStar thenBranch thenBranch')
    (elseChain : Step.parStar elseBranch elseBranch') :
    Step.parStar (Term.boolElim scrutinee thenBranch elseBranch)
                 (Term.boolElim scrutinee' thenBranch' elseBranch') :=
  Step.parStar.append
    (Step.parStar.boolElim_cong_scrutinee thenBranch elseBranch scrutineeChain)
    (Step.parStar.append
      (Step.parStar.boolElim_cong_then scrutinee' elseBranch thenChain)
      (Step.parStar.boolElim_cong_else scrutinee' thenBranch' elseChain))

/-- `natSucc` congruence at the `parStar` level. -/
theorem Step.parStar.natSucc_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor predecessor' : Term ctx Ty.nat}
    (predChain : Step.parStar predecessor predecessor') :
    Step.parStar (Term.natSucc predecessor) (Term.natSucc predecessor') := by
  induction predChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.natSucc firstStep) restIH

/-- Single-position `natElim` congruence on scrutinee. -/
theorem Step.parStar.natElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (scrutineeChain : Step.parStar scrutinee scrutinee') :
    Step.parStar (Term.natElim scrutinee zeroBranch succBranch)
                 (Term.natElim scrutinee' zeroBranch succBranch) := by
  induction scrutineeChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.natElim firstStep (Step.par.refl _) (Step.par.refl _))
        restIH

/-- Single-position `natElim` congruence on zero-branch. -/
theorem Step.parStar.natElim_cong_zero
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (zeroChain : Step.parStar zeroBranch zeroBranch') :
    Step.parStar (Term.natElim scrutinee zeroBranch succBranch)
                 (Term.natElim scrutinee zeroBranch' succBranch) := by
  induction zeroChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.natElim (Step.par.refl _) firstStep (Step.par.refl _))
        restIH

/-- Single-position `natElim` congruence on succ-branch. -/
theorem Step.parStar.natElim_cong_succ
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (succChain : Step.parStar succBranch succBranch') :
    Step.parStar (Term.natElim scrutinee zeroBranch succBranch)
                 (Term.natElim scrutinee zeroBranch succBranch') := by
  induction succChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.natElim (Step.par.refl _) (Step.par.refl _) firstStep)
        restIH

/-- `natElim` congruence at the `parStar` level. -/
theorem Step.parStar.natElim_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (scrutineeChain : Step.parStar scrutinee scrutinee')
    (zeroChain : Step.parStar zeroBranch zeroBranch')
    (succChain : Step.parStar succBranch succBranch') :
    Step.parStar (Term.natElim scrutinee zeroBranch succBranch)
                 (Term.natElim scrutinee' zeroBranch' succBranch') :=
  Step.parStar.append
    (Step.parStar.natElim_cong_scrutinee zeroBranch succBranch scrutineeChain)
    (Step.parStar.append
      (Step.parStar.natElim_cong_zero scrutinee' succBranch zeroChain)
      (Step.parStar.natElim_cong_succ scrutinee' zeroBranch' succChain))

/-- Single-position `natRec` congruence on scrutinee. -/
theorem Step.parStar.natRec_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (scrutineeChain : Step.parStar scrutinee scrutinee') :
    Step.parStar (Term.natRec scrutinee zeroBranch succBranch)
                 (Term.natRec scrutinee' zeroBranch succBranch) := by
  induction scrutineeChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.natRec firstStep (Step.par.refl _) (Step.par.refl _))
        restIH

/-- Single-position `natRec` congruence on zero-branch. -/
theorem Step.parStar.natRec_cong_zero
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (zeroChain : Step.parStar zeroBranch zeroBranch') :
    Step.parStar (Term.natRec scrutinee zeroBranch succBranch)
                 (Term.natRec scrutinee zeroBranch' succBranch) := by
  induction zeroChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.natRec (Step.par.refl _) firstStep (Step.par.refl _))
        restIH

/-- Single-position `natRec` congruence on succ-branch. -/
theorem Step.parStar.natRec_cong_succ
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (succChain : Step.parStar succBranch succBranch') :
    Step.parStar (Term.natRec scrutinee zeroBranch succBranch)
                 (Term.natRec scrutinee zeroBranch succBranch') := by
  induction succChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.natRec (Step.par.refl _) (Step.par.refl _) firstStep)
        restIH

/-- `natRec` congruence at the `parStar` level. -/
theorem Step.parStar.natRec_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (scrutineeChain : Step.parStar scrutinee scrutinee')
    (zeroChain : Step.parStar zeroBranch zeroBranch')
    (succChain : Step.parStar succBranch succBranch') :
    Step.parStar (Term.natRec scrutinee zeroBranch succBranch)
                 (Term.natRec scrutinee' zeroBranch' succBranch') :=
  Step.parStar.append
    (Step.parStar.natRec_cong_scrutinee zeroBranch succBranch scrutineeChain)
    (Step.parStar.append
      (Step.parStar.natRec_cong_zero scrutinee' succBranch zeroChain)
      (Step.parStar.natRec_cong_succ scrutinee' zeroBranch' succChain))

/-- Single-position `listCons` congruence on head. -/
theorem Step.parStar.listCons_cong_head
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {head head' : Term ctx elementType}
    (tail : Term ctx (Ty.list elementType))
    (headChain : Step.parStar head head') :
    Step.parStar (Term.listCons head tail) (Term.listCons head' tail) := by
  induction headChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.listCons firstStep (Step.par.refl _)) restIH

/-- Single-position `listCons` congruence on tail. -/
theorem Step.parStar.listCons_cong_tail
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (head : Term ctx elementType)
    {tail tail' : Term ctx (Ty.list elementType)}
    (tailChain : Step.parStar tail tail') :
    Step.parStar (Term.listCons head tail) (Term.listCons head tail') := by
  induction tailChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.listCons (Step.par.refl _) firstStep) restIH

/-- `listCons` congruence at the `parStar` level. -/
theorem Step.parStar.listCons_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {head head' : Term ctx elementType}
    {tail tail' : Term ctx (Ty.list elementType)}
    (headChain : Step.parStar head head')
    (tailChain : Step.parStar tail tail') :
    Step.parStar (Term.listCons head tail) (Term.listCons head' tail') :=
  Step.parStar.append
    (Step.parStar.listCons_cong_head tail headChain)
    (Step.parStar.listCons_cong_tail head' tailChain)

/-- Single-position `listElim` congruence on scrutinee. -/
theorem Step.parStar.listElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType)))
    (scrutineeChain : Step.parStar scrutinee scrutinee') :
    Step.parStar (Term.listElim scrutinee nilBranch consBranch)
                 (Term.listElim scrutinee' nilBranch consBranch) := by
  induction scrutineeChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.listElim firstStep (Step.par.refl _) (Step.par.refl _))
        restIH

/-- Single-position `listElim` congruence on nil-branch. -/
theorem Step.parStar.listElim_cong_nil
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch nilBranch' : Term ctx resultType}
    (consBranch :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType)))
    (nilChain : Step.parStar nilBranch nilBranch') :
    Step.parStar (Term.listElim scrutinee nilBranch consBranch)
                 (Term.listElim scrutinee nilBranch' consBranch) := by
  induction nilChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.listElim (Step.par.refl _) firstStep (Step.par.refl _))
        restIH

/-- Single-position `listElim` congruence on cons-branch. -/
theorem Step.parStar.listElim_cong_cons
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch consBranch' :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType))}
    (consChain : Step.parStar consBranch consBranch') :
    Step.parStar (Term.listElim scrutinee nilBranch consBranch)
                 (Term.listElim scrutinee nilBranch consBranch') := by
  induction consChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.listElim (Step.par.refl _) (Step.par.refl _) firstStep)
        restIH

/-- `listElim` congruence at the `parStar` level. -/
theorem Step.parStar.listElim_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
    {nilBranch nilBranch' : Term ctx resultType}
    {consBranch consBranch' :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType))}
    (scrutineeChain : Step.parStar scrutinee scrutinee')
    (nilChain : Step.parStar nilBranch nilBranch')
    (consChain : Step.parStar consBranch consBranch') :
    Step.parStar (Term.listElim scrutinee nilBranch consBranch)
                 (Term.listElim scrutinee' nilBranch' consBranch') :=
  Step.parStar.append
    (Step.parStar.listElim_cong_scrutinee nilBranch consBranch scrutineeChain)
    (Step.parStar.append
      (Step.parStar.listElim_cong_nil scrutinee' consBranch nilChain)
      (Step.parStar.listElim_cong_cons scrutinee' nilBranch' consChain))

/-- `optionSome` congruence at the `parStar` level. -/
theorem Step.parStar.optionSome_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value value' : Term ctx elementType}
    (valueChain : Step.parStar value value') :
    Step.parStar (Term.optionSome value) (Term.optionSome value') := by
  induction valueChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.optionSome firstStep) restIH

/-- Single-position `optionMatch` congruence on scrutinee. -/
theorem Step.parStar.optionMatch_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (scrutineeChain : Step.parStar scrutinee scrutinee') :
    Step.parStar (Term.optionMatch scrutinee noneBranch someBranch)
                 (Term.optionMatch scrutinee' noneBranch someBranch) := by
  induction scrutineeChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.optionMatch firstStep (Step.par.refl _) (Step.par.refl _))
        restIH

/-- Single-position `optionMatch` congruence on none-branch. -/
theorem Step.parStar.optionMatch_cong_none
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch noneBranch' : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (noneChain : Step.parStar noneBranch noneBranch') :
    Step.parStar (Term.optionMatch scrutinee noneBranch someBranch)
                 (Term.optionMatch scrutinee noneBranch' someBranch) := by
  induction noneChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.optionMatch (Step.par.refl _) firstStep (Step.par.refl _))
        restIH

/-- Single-position `optionMatch` congruence on some-branch. -/
theorem Step.parStar.optionMatch_cong_some
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (someChain : Step.parStar someBranch someBranch') :
    Step.parStar (Term.optionMatch scrutinee noneBranch someBranch)
                 (Term.optionMatch scrutinee noneBranch someBranch') := by
  induction someChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.optionMatch (Step.par.refl _) (Step.par.refl _) firstStep)
        restIH

/-- `optionMatch` congruence at the `parStar` level. -/
theorem Step.parStar.optionMatch_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
    {noneBranch noneBranch' : Term ctx resultType}
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (scrutineeChain : Step.parStar scrutinee scrutinee')
    (noneChain : Step.parStar noneBranch noneBranch')
    (someChain : Step.parStar someBranch someBranch') :
    Step.parStar (Term.optionMatch scrutinee noneBranch someBranch)
                 (Term.optionMatch scrutinee' noneBranch' someBranch') :=
  Step.parStar.append
    (Step.parStar.optionMatch_cong_scrutinee noneBranch someBranch scrutineeChain)
    (Step.parStar.append
      (Step.parStar.optionMatch_cong_none scrutinee' someBranch noneChain)
      (Step.parStar.optionMatch_cong_some scrutinee' noneBranch' someChain))

/-- `eitherInl` congruence at the `parStar` level. -/
theorem Step.parStar.eitherInl_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx leftType}
    (valueChain : Step.parStar value value') :
    Step.parStar (Term.eitherInl (rightType := rightType) value)
                 (Term.eitherInl (rightType := rightType) value') := by
  induction valueChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.eitherInl firstStep) restIH

/-- `eitherInr` congruence at the `parStar` level. -/
theorem Step.parStar.eitherInr_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx rightType}
    (valueChain : Step.parStar value value') :
    Step.parStar (Term.eitherInr (leftType := leftType) value)
                 (Term.eitherInr (leftType := leftType) value') := by
  induction valueChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans (Step.par.eitherInr firstStep) restIH

/-- Single-position `eitherMatch` congruence on scrutinee. -/
theorem Step.parStar.eitherMatch_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (scrutineeChain : Step.parStar scrutinee scrutinee') :
    Step.parStar (Term.eitherMatch scrutinee leftBranch rightBranch)
                 (Term.eitherMatch scrutinee' leftBranch rightBranch) := by
  induction scrutineeChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.eitherMatch firstStep (Step.par.refl _) (Step.par.refl _))
        restIH

/-- Single-position `eitherMatch` congruence on left-branch. -/
theorem Step.parStar.eitherMatch_cong_left
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (leftChain : Step.parStar leftBranch leftBranch') :
    Step.parStar (Term.eitherMatch scrutinee leftBranch rightBranch)
                 (Term.eitherMatch scrutinee leftBranch' rightBranch) := by
  induction leftChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.eitherMatch (Step.par.refl _) firstStep (Step.par.refl _))
        restIH

/-- Single-position `eitherMatch` congruence on right-branch. -/
theorem Step.parStar.eitherMatch_cong_right
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (rightChain : Step.parStar rightBranch rightBranch') :
    Step.parStar (Term.eitherMatch scrutinee leftBranch rightBranch)
                 (Term.eitherMatch scrutinee leftBranch rightBranch') := by
  induction rightChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.eitherMatch (Step.par.refl _) (Step.par.refl _) firstStep)
        restIH

/-- `eitherMatch` congruence at the `parStar` level. -/
theorem Step.parStar.eitherMatch_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (scrutineeChain : Step.parStar scrutinee scrutinee')
    (leftChain : Step.parStar leftBranch leftBranch')
    (rightChain : Step.parStar rightBranch rightBranch') :
    Step.parStar (Term.eitherMatch scrutinee leftBranch rightBranch)
                 (Term.eitherMatch scrutinee' leftBranch' rightBranch') :=
  Step.parStar.append
    (Step.parStar.eitherMatch_cong_scrutinee leftBranch rightBranch scrutineeChain)
    (Step.parStar.append
      (Step.parStar.eitherMatch_cong_left scrutinee' rightBranch leftChain)
      (Step.parStar.eitherMatch_cong_right scrutinee' leftBranch' rightChain))

/-- Single-position `idJ` congruence on base-case. -/
theorem Step.parStar.idJ_cong_base
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd))
    (baseChain : Step.parStar baseCase baseCase') :
    Step.parStar (Term.idJ baseCase witness)
                 (Term.idJ baseCase' witness) := by
  induction baseChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.idJ firstStep (Step.par.refl _)) restIH

/-- Single-position `idJ` congruence on witness. -/
theorem Step.parStar.idJ_cong_witness
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (witnessChain : Step.parStar witness witness') :
    Step.parStar (Term.idJ baseCase witness)
                 (Term.idJ baseCase witness') := by
  induction witnessChain with
  | refl _ => exact Step.parStar.refl _
  | trans firstStep restChain restIH =>
      exact Step.parStar.trans
        (Step.par.idJ (Step.par.refl _) firstStep) restIH

/-- `idJ` congruence at the `parStar` level. -/
theorem Step.parStar.idJ_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (baseChain : Step.parStar baseCase baseCase')
    (witnessChain : Step.parStar witness witness') :
    Step.parStar (Term.idJ baseCase witness)
                 (Term.idJ baseCase' witness') :=
  Step.parStar.append
    (Step.parStar.idJ_cong_base witness baseChain)
    (Step.parStar.idJ_cong_witness baseCase' witnessChain)

end LeanFX.Syntax
