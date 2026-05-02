import LeanFX.Syntax.Reduction.StepStar

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Parallel reduction (`Step.par`) — confluence groundwork.

The parallel-reduction relation is the standard Tait–Martin-Löf vehicle
for proving confluence of `Step`: rather than reduce one redex at a time,
`Step.par` allows simultaneous reduction in *all* subterms in a single
step.  Crucially it is reflexive, so any subterm may "reduce" by zero
steps.

Key properties (proved here / deferred):

  * `Step.par` is reflexive — `Step.par.refl t : Step.par t t`.  Direct
    constructor.
  * `Step → Step.par` — each single Step lifts trivially (this layer).
  * `Step.par → StepStar` — each parallel rule decomposes into a
    sequence of single Step's.  Substantial; deferred.
  * **Diamond property** for `Step.par`: if `Step.par t t₁` and
    `Step.par t t₂`, there exists `t'` with `Step.par t₁ t'` and
    `Step.par t₂ t'`.  This is the Tait–Martin-Löf "strip lemma"
    + confluence chain.  Deferred to a follow-on task; once proved,
    confluence of `StepStar` (and hence decidability of `Conv` over
    canonical forms) follows.

Subject preservation is structural: input and output share `{ctx} {T}`
indices, so every `Step.par` proof witnesses same-typed reduction. -/
inductive Step.par :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Reflexivity — any term parallel-reduces to itself in zero steps. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      Step.par t t
  /-- Parallel reduction inside a non-dependent application. -/
  | app :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {f f' : Term ctx (.arrow domainType codomainType)}
        {a a' : Term ctx domainType},
      Step.par f f' → Step.par a a' →
      Step.par (Term.app f a) (Term.app f' a')
  /-- Parallel reduction inside a non-dependent λ-abstraction's body. -/
  | lam :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken},
      Step.par body body' →
      Step.par (Term.lam (codomainType := codomainType) body)
               (Term.lam (codomainType := codomainType) body')
  /-- Parallel reduction inside a dependent λ-abstraction's body. -/
  | lamPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType},
      Step.par body body' →
      Step.par (Term.lamPi (domainType := domainType) body)
               (Term.lamPi (domainType := domainType) body')
  /-- Parallel reduction inside a dependent application.
  W9.B1.3a — polymorphic over `argumentRaw`; both sides share the same
  argumentRaw and use rfl for resultEq. -/
  | appPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {argumentRaw : RawTerm scope}
        {f f' : Term ctx (.piTy domainType codomainType)}
        {a a' : Term ctx domainType},
      Step.par f f' → Step.par a a' →
      Step.par
        (Term.appPi (argumentRaw := argumentRaw) rfl f a)
        (Term.appPi (argumentRaw := argumentRaw) rfl f' a')
  /-- Parallel reduction inside a Σ-pair's two components. -/
  | pair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step.par firstVal firstVal' → Step.par secondVal secondVal' →
      Step.par (Term.pair firstVal secondVal)
               (Term.pair firstVal' secondVal')
  /-- Parallel reduction inside a first projection. -/
  | fst :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {p p' : Term ctx (.sigmaTy firstType secondType)},
      Step.par p p' → Step.par (Term.fst p) (Term.fst p')
  /-- Parallel reduction inside a second projection.  W9.B1.2:
  `Term.snd` requires `rfl` for resultEq. -/
  | snd :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {p p' : Term ctx (.sigmaTy firstType secondType)},
      Step.par p p' → Step.par (Term.snd p rfl) (Term.snd p' rfl)
  /-- Parallel reduction inside all three positions of a `boolElim`. -/
  | boolElim :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.bool}
        {thenBr thenBr' : Term ctx resultType}
        {elseBr elseBr' : Term ctx resultType},
      Step.par scrutinee scrutinee' →
      Step.par thenBr thenBr' →
      Step.par elseBr elseBr' →
      Step.par (Term.boolElim scrutinee thenBr elseBr)
               (Term.boolElim scrutinee' thenBr' elseBr')
  /-- **Parallel β-reduction (non-dependent)**: `(λ. body) arg →
  body[arg/x]` with parallel reductions in body and arg before
  substitution.  This is the rule that makes confluence work — both the
  body and the argument may reduce in lockstep with the contraction. -/
  | betaApp :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken}
        {arg arg' : Term ctx domainType},
      Step.par body body' → Step.par arg arg' →
      Step.par (Term.app (Term.lam (codomainType := codomainType) body) arg)
               ((Ty.weaken_subst_singleton codomainType domainType) ▸
                  Term.subst0 body' arg')
  /-- **Parallel β-reduction (dependent)**: `(λ. body) arg ⟶
  body[arg/x]` with parallel reductions in body and arg.  W9.B1.1:
  appPi takes `rfl` for resultEq; result is `Term.subst0 body' arg'`
  matching the canonical β-result type. -/
  | betaAppPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType}
        {arg arg' : Term ctx domainType},
      Step.par body body' → Step.par arg arg' →
      Step.par
        (Term.appPi (argumentRaw := RawTerm.unit)
          (Ty.subst0_eq_termSingleton_unit codomainType domainType)
          (Term.lamPi (domainType := domainType) body) arg)
        (Term.subst0 body' arg')
  /-- **Parallel Σ first projection**: `fst (pair a b) → a'` with
  `Step.par a a'`. -/
  | betaFstPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        (secondVal : Term ctx (secondType.subst0 firstType)),
      Step.par firstVal firstVal' →
      Step.par (Term.fst
                 (Term.pair (firstType := firstType)
                            (secondType := secondType) firstVal secondVal))
               firstVal'
  /-- **Parallel Σ second projection**: `snd (pair a b) → b'` with
  `Step.par b b'`.  W9.B1.2: `Term.snd` requires `rfl` for resultEq. -/
  | betaSndPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (firstVal : Term ctx firstType)
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step.par secondVal secondVal' →
      Step.par (Term.snd
                 (Term.pair (firstType := firstType)
                            (secondType := secondType) firstVal secondVal)
                 rfl)
               secondVal'
  /-- **Parallel ι-reduction on `boolTrue`**: `boolElim true t e → t'`
  with `Step.par t t'`. -/
  | iotaBoolElimTrue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {thenBr thenBr' : Term ctx resultType}
        (elseBr : Term ctx resultType),
      Step.par thenBr thenBr' →
      Step.par (Term.boolElim Term.boolTrue thenBr elseBr) thenBr'
  /-- **Parallel ι-reduction on `boolFalse`**: `boolElim false t e →
  e'` with `Step.par e e'`. -/
  | iotaBoolElimFalse :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (thenBr : Term ctx resultType)
        {elseBr elseBr' : Term ctx resultType},
      Step.par elseBr elseBr' →
      Step.par (Term.boolElim Term.boolFalse thenBr elseBr) elseBr'
  /-- Parallel reduction inside a `Term.natSucc`. -/
  | natSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {pred pred' : Term ctx Ty.nat},
      Step.par pred pred' →
      Step.par (Term.natSucc pred) (Term.natSucc pred')
  /-- Parallel reduction inside all three positions of a `Term.natElim`. -/
  | natElim :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step.par scrutinee scrutinee' →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natElim scrutinee zeroBranch succBranch)
               (Term.natElim scrutinee' zeroBranch' succBranch')
  /-- **Parallel ι-reduction on `0`**: `natElim 0 z f → z'` with
  `Step.par z z'`. -/
  | iotaNatElimZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step.par zeroBranch zeroBranch' →
      Step.par (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch'
  /-- Parallel reduction inside all three positions of `Term.natRec`. -/
  | natRec :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step.par scrutinee scrutinee' →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natRec scrutinee zeroBranch succBranch)
               (Term.natRec scrutinee' zeroBranch' succBranch')
  /-- **Parallel ι-reduction on `0`**: `natRec 0 z s → z'` with
  `Step.par z z'`. -/
  | iotaNatRecZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step.par zeroBranch zeroBranch' →
      Step.par (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch'
  /-- **Parallel ι-reduction on `succ n`**:
  `natRec (succ n) z s → s' n' (natRec n' z' s')`.  All three
  subterms parallel-reduce because they all appear in the reduct
  (the IH is constructed from the reduced versions). -/
  | iotaNatRecSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {predecessor predecessor' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step.par predecessor predecessor' →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
               (Term.app (Term.app succBranch' predecessor')
                         (Term.natRec predecessor' zeroBranch' succBranch'))
  /-- **Parallel ι-reduction on `succ n`**: `natElim (succ n) z f → f' n'`
  with `Step.par n n'` and `Step.par f f'`. -/
  | iotaNatElimSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {predecessor predecessor' : Term ctx Ty.nat}
        (zeroBranch : Term ctx resultType)
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step.par predecessor predecessor' →
      Step.par succBranch succBranch' →
      Step.par (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
               (Term.app succBranch' predecessor')
  /-- Parallel reduction inside both head and tail of a `Term.listCons`. -/
  | listCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {hd hd' : Term ctx elementType}
        {tl tl' : Term ctx (Ty.list elementType)},
      Step.par hd hd' → Step.par tl tl' →
      Step.par (Term.listCons hd tl) (Term.listCons hd' tl')
  /-- Parallel reduction inside all three positions of a `Term.listElim`. -/
  | listElim :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step.par scrutinee scrutinee' →
      Step.par nilBranch nilBranch' →
      Step.par consBranch consBranch' →
      Step.par (Term.listElim scrutinee nilBranch consBranch)
               (Term.listElim scrutinee' nilBranch' consBranch')
  /-- **Parallel ι-reduction on `[]`**: `listElim [] n c → n'`
  with `Step.par n n'`. -/
  | iotaListElimNil :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {nilBranch nilBranch' : Term ctx resultType}
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step.par nilBranch nilBranch' →
      Step.par (Term.listElim (elementType := elementType) Term.listNil
                  nilBranch consBranch)
               nilBranch'
  /-- **Parallel ι-reduction on `cons`**: `listElim (cons h t) n c →
  c' h' t'` with parallel reductions in head, tail, and consBranch. -/
  | iotaListElimCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {head head' : Term ctx elementType}
        {tail tail' : Term ctx (Ty.list elementType)}
        (nilBranch : Term ctx resultType)
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step.par head head' →
      Step.par tail tail' →
      Step.par consBranch consBranch' →
      Step.par (Term.listElim (Term.listCons head tail) nilBranch consBranch)
               (Term.app (Term.app consBranch' head') tail')
  /-- Parallel reduction inside the value of `Term.optionSome`. -/
  | optionSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {value value' : Term ctx elementType},
      Step.par value value' →
      Step.par (Term.optionSome value) (Term.optionSome value')
  /-- Parallel reduction inside all three positions of `Term.optionMatch`. -/
  | optionMatch :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)},
      Step.par scrutinee scrutinee' →
      Step.par noneBranch noneBranch' →
      Step.par someBranch someBranch' →
      Step.par (Term.optionMatch scrutinee noneBranch someBranch)
               (Term.optionMatch scrutinee' noneBranch' someBranch')
  /-- **Parallel ι-reduction on `none`**: `optionMatch none n s → n'`
  with `Step.par n n'`. -/
  | iotaOptionMatchNone :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {noneBranch noneBranch' : Term ctx resultType}
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step.par noneBranch noneBranch' →
      Step.par (Term.optionMatch (elementType := elementType) Term.optionNone
                  noneBranch someBranch)
               noneBranch'
  /-- **Parallel ι-reduction on `some`**: `optionMatch (some v) n s → s' v'`
  with parallel reductions in value and someBranch. -/
  | iotaOptionMatchSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {value value' : Term ctx elementType}
        (noneBranch : Term ctx resultType)
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)},
      Step.par value value' →
      Step.par someBranch someBranch' →
      Step.par (Term.optionMatch (Term.optionSome value) noneBranch someBranch)
               (Term.app someBranch' value')
  /-- Parallel reduction inside the value of `Term.eitherInl`. -/
  | eitherInl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx leftType},
      Step.par value value' →
      Step.par (Term.eitherInl (rightType := rightType) value)
               (Term.eitherInl (rightType := rightType) value')
  /-- Parallel reduction inside the value of `Term.eitherInr`. -/
  | eitherInr :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx rightType},
      Step.par value value' →
      Step.par (Term.eitherInr (leftType := leftType) value)
               (Term.eitherInr (leftType := leftType) value')
  /-- Parallel reduction inside all three positions of `Term.eitherMatch`. -/
  | eitherMatch :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)},
      Step.par scrutinee scrutinee' →
      Step.par leftBranch leftBranch' →
      Step.par rightBranch rightBranch' →
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch)
               (Term.eitherMatch scrutinee' leftBranch' rightBranch')
  /-- **Parallel ι-reduction on `inl`**: `eitherMatch (inl v) lb rb → lb' v'`
  with parallel reductions in value and leftBranch. -/
  | iotaEitherMatchInl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {value value' : Term ctx leftType}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step.par value value' →
      Step.par leftBranch leftBranch' →
      Step.par (Term.eitherMatch (Term.eitherInl (rightType := rightType) value)
                  leftBranch rightBranch)
               (Term.app leftBranch' value')
  /-- **Parallel ι-reduction on `inr`**: `eitherMatch (inr v) lb rb → rb' v'`
  with parallel reductions in value and rightBranch. -/
  | iotaEitherMatchInr :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {value value' : Term ctx rightType}
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)},
      Step.par value value' →
      Step.par rightBranch rightBranch' →
      Step.par (Term.eitherMatch (Term.eitherInr (leftType := leftType) value)
                  leftBranch rightBranch)
               (Term.app rightBranch' value')
  /-- **η-contraction for non-dependent arrow** at the parallel level.
  Same shape as `Step.etaArrow`: the η-redex `λx. f.weaken x` contracts
  to `f`.  No subterm-parallel rule because the redex shape is rigid
  (the body must be specifically `f.weaken x`); confluence with βι
  composes through this rule by post-applying the η-contraction. -/
  | etaArrow :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        (f : Term ctx (Ty.arrow domainType codomainType)),
      Step.par (Term.lam (codomainType := codomainType)
                  (Term.app (Term.weaken domainType f)
                            (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
               f
  /-- **η-contraction for Σ-pair** at the parallel level.  W9.B1.2:
  `Term.snd p` requires `rfl` for resultEq. -/
  | etaSigma :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (p : Term ctx (Ty.sigmaTy firstType secondType)),
      Step.par (Term.pair (firstType := firstType)
                           (secondType := secondType)
                  (Term.fst p) (Term.snd p rfl))
               p
  /-- Parallel reduction inside both positions of `Term.idJ`. -/
  | idJ :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)},
      Step.par baseCase baseCase' →
      Step.par witness witness' →
      Step.par (Term.idJ baseCase witness)
               (Term.idJ baseCase' witness')
  /-- **Parallel ι-reduction at refl**: `J base (refl rt) → base'` with
  parallel reduction in baseCase. -/
  | iotaIdJRefl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {endpoint : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType},
      Step.par baseCase baseCase' →
      Step.par (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                         (rightEnd := endpoint) baseCase
                         (Term.refl (carrier := carrier) endpoint))
               baseCase'
  /-- **Deep parallel β-reduction (non-dependent)**: if `f` parallel-
  reduces to a literal lambda `λ. body`, the outer application
  contracts.  Captures `Term.cd`'s aggressive β-app firing on
  developed shapes.  Subsumes the shallow `betaApp` (recoverable by
  passing `Step.par.refl (Term.lam body)` as the deep premise). -/
  | betaAppDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm : Term ctx (Ty.arrow domainType codomainType)}
        {body : Term (ctx.cons domainType) codomainType.weaken}
        {arg arg' : Term ctx domainType},
      Step.par functionTerm
        (Term.lam (codomainType := codomainType) body) →
      Step.par arg arg' →
      Step.par (Term.app functionTerm arg)
               ((Ty.weaken_subst_singleton codomainType domainType) ▸
                  Term.subst0 body arg')
  /-- **Deep parallel β-reduction (dependent)**: if `f` parallel-
  reduces to a literal Π-lambda `λ. body`, the outer application
  contracts.  W9.B1.3a — termSingleton-flavored canonical discharge. -/
  | betaAppPiDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {functionTerm : Term ctx (Ty.piTy domainType codomainType)}
        {body : Term (ctx.cons domainType) codomainType}
        {arg arg' : Term ctx domainType},
      Step.par functionTerm
        (Term.lamPi (domainType := domainType) body) →
      Step.par arg arg' →
      Step.par
        (Term.appPi (argumentRaw := RawTerm.unit)
          (Ty.subst0_eq_termSingleton_unit codomainType domainType)
          functionTerm arg)
        (Term.subst0 body arg')
  -- W9.B1.3a TODO — extend `betaAppPi`/`betaAppPiDeep` argumentRaw
  -- once `Term.subst0_term` migration lands so target type aligns
  -- with non-trivial argumentRaw values.
  /-- **Deep parallel Σ first projection**: if `pairTerm` parallel-
  reduces to a literal pair, fst contracts. -/
  | betaFstPairDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {pairTerm : Term ctx (Ty.sigmaTy firstType secondType)}
        {firstVal : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)},
      Step.par pairTerm
        (Term.pair (firstType := firstType) (secondType := secondType)
                   firstVal secondVal) →
      Step.par (Term.fst pairTerm) firstVal
  /-- **Deep parallel Σ second projection**.  W9.B1.2: `Term.snd`
  requires `rfl` for resultEq. -/
  | betaSndPairDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {pairTerm : Term ctx (Ty.sigmaTy firstType secondType)}
        {firstVal : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)},
      Step.par pairTerm
        (Term.pair (firstType := firstType) (secondType := secondType)
                   firstVal secondVal) →
      Step.par (Term.snd pairTerm rfl) secondVal
  /-- **Deep parallel ι-reduction on `boolTrue`**. -/
  | iotaBoolElimTrueDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr thenBr' : Term ctx resultType}
        (elseBr : Term ctx resultType),
      Step.par scrutinee Term.boolTrue →
      Step.par thenBr thenBr' →
      Step.par (Term.boolElim scrutinee thenBr elseBr) thenBr'
  /-- **Deep parallel ι-reduction on `boolFalse`**. -/
  | iotaBoolElimFalseDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        (thenBr : Term ctx resultType)
        {elseBr elseBr' : Term ctx resultType},
      Step.par scrutinee Term.boolFalse →
      Step.par elseBr elseBr' →
      Step.par (Term.boolElim scrutinee thenBr elseBr) elseBr'
  /-- **Deep parallel ι-reduction on `natZero`** (natElim). -/
  | iotaNatElimZeroDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step.par scrutinee Term.natZero →
      Step.par zeroBranch zeroBranch' →
      Step.par (Term.natElim scrutinee zeroBranch succBranch) zeroBranch'
  /-- **Deep parallel ι-reduction on `natSucc`** (natElim). -/
  | iotaNatElimSuccDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {predecessor : Term ctx Ty.nat}
        (zeroBranch : Term ctx resultType)
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step.par scrutinee (Term.natSucc predecessor) →
      Step.par succBranch succBranch' →
      Step.par (Term.natElim scrutinee zeroBranch succBranch)
               (Term.app succBranch' predecessor)
  /-- **Deep parallel ι-reduction on `natZero`** (natRec). -/
  | iotaNatRecZeroDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step.par scrutinee Term.natZero →
      Step.par zeroBranch zeroBranch' →
      Step.par (Term.natRec scrutinee zeroBranch succBranch) zeroBranch'
  /-- **Deep parallel ι-reduction on `natSucc`** (natRec). -/
  | iotaNatRecSuccDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {predecessor : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step.par scrutinee (Term.natSucc predecessor) →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natRec scrutinee zeroBranch succBranch)
               (Term.app (Term.app succBranch' predecessor)
                         (Term.natRec predecessor zeroBranch' succBranch'))
  /-- **Deep parallel ι-reduction on `listNil`**. -/
  | iotaListElimNilDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step.par scrutinee Term.listNil →
      Step.par nilBranch nilBranch' →
      Step.par (Term.listElim scrutinee nilBranch consBranch) nilBranch'
  /-- **Deep parallel ι-reduction on `listCons`**. -/
  | iotaListElimConsDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {head : Term ctx elementType}
        {tail : Term ctx (Ty.list elementType)}
        (nilBranch : Term ctx resultType)
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step.par scrutinee (Term.listCons head tail) →
      Step.par consBranch consBranch' →
      Step.par (Term.listElim scrutinee nilBranch consBranch)
               (Term.app (Term.app consBranch' head) tail)
  /-- **Deep parallel ι-reduction on `optionNone`**. -/
  | iotaOptionMatchNoneDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step.par scrutinee Term.optionNone →
      Step.par noneBranch noneBranch' →
      Step.par (Term.optionMatch scrutinee noneBranch someBranch) noneBranch'
  /-- **Deep parallel ι-reduction on `optionSome`**. -/
  | iotaOptionMatchSomeDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {value : Term ctx elementType}
        (noneBranch : Term ctx resultType)
        {someBranch someBranch' :
            Term ctx (Ty.arrow elementType resultType)},
      Step.par scrutinee (Term.optionSome value) →
      Step.par someBranch someBranch' →
      Step.par (Term.optionMatch scrutinee noneBranch someBranch)
               (Term.app someBranch' value)
  /-- **Deep parallel ι-reduction on `eitherInl`**. -/
  | iotaEitherMatchInlDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {value : Term ctx leftType}
        {leftBranch leftBranch' :
            Term ctx (Ty.arrow leftType resultType)}
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step.par scrutinee (Term.eitherInl (rightType := rightType) value) →
      Step.par leftBranch leftBranch' →
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch)
               (Term.app leftBranch' value)
  /-- **Deep parallel ι-reduction on `eitherInr`**. -/
  | iotaEitherMatchInrDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {value : Term ctx rightType}
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        {rightBranch rightBranch' :
            Term ctx (Ty.arrow rightType resultType)},
      Step.par scrutinee (Term.eitherInr (leftType := leftType) value) →
      Step.par rightBranch rightBranch' →
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch)
               (Term.app rightBranch' value)
  /-- **Deep parallel ι-reduction on `Term.refl`**: if `witness`
  parallel-reduces to a refl, idJ contracts to its base case.  The
  carrier's left and right endpoints must be the same `endpoint` for
  the witness to typecheck against `Term.refl endpoint`. -/
  | iotaIdJReflDeep :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {endpoint : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {witness : Term ctx (Ty.id carrier endpoint endpoint)},
      Step.par witness
        (Term.refl (carrier := carrier) endpoint) →
      Step.par baseCase baseCase' →
      Step.par (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                          (rightEnd := endpoint)
                          baseCase witness)
               baseCase'

/-- Single-step reduction lifts to parallel reduction.  Each `Step`
constructor has a corresponding `Step.par` form where the non-changing
subterm reduces by reflexivity. -/
theorem Step.toPar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} : Step t₁ t₂ → Step.par t₁ t₂
  | .appLeft s            => .app (Step.toPar s) (.refl _)
  | .appRight s           => .app (.refl _) (Step.toPar s)
  | .lamBody s            => .lam (Step.toPar s)
  | .appPiLeft s          => .appPi (Step.toPar s) (.refl _)
  | .appPiRight s         => .appPi (.refl _) (Step.toPar s)
  | .lamPiBody s          => .lamPi (Step.toPar s)
  | .pairLeft s           => .pair (Step.toPar s) (.refl _)
  | .pairRight s          => .pair (.refl _) (Step.toPar s)
  | .fstCong s            => .fst (Step.toPar s)
  | .sndCong s            => .snd (Step.toPar s)
  | .betaApp body arg     => .betaApp (.refl body) (.refl arg)
  | .betaAppPi body arg   => .betaAppPi (.refl body) (.refl arg)
  | .betaFstPair v w      => .betaFstPair w (.refl v)
  | .betaSndPair v w      => .betaSndPair v (.refl w)
  | .etaArrow f           => .etaArrow f
  | .etaSigma p           => .etaSigma p
  | .boolElimScrutinee s  => .boolElim (Step.toPar s) (.refl _) (.refl _)
  | .boolElimThen s       => .boolElim (.refl _) (Step.toPar s) (.refl _)
  | .boolElimElse s       => .boolElim (.refl _) (.refl _) (Step.toPar s)
  | .iotaBoolElimTrue t e => .iotaBoolElimTrue e (.refl t)
  | .iotaBoolElimFalse t e => .iotaBoolElimFalse t (.refl e)
  | .natSuccPred s        => .natSucc (Step.toPar s)
  | .natElimScrutinee s   => .natElim (Step.toPar s) (.refl _) (.refl _)
  | .natElimZero s        => .natElim (.refl _) (Step.toPar s) (.refl _)
  | .natElimSucc s        => .natElim (.refl _) (.refl _) (Step.toPar s)
  | .iotaNatElimZero z f  => .iotaNatElimZero f (.refl z)
  | .iotaNatElimSucc n _ f => .iotaNatElimSucc _ (.refl n) (.refl f)
  | .natRecScrutinee s    => .natRec (Step.toPar s) (.refl _) (.refl _)
  | .natRecZero s         => .natRec (.refl _) (Step.toPar s) (.refl _)
  | .natRecSucc s         => .natRec (.refl _) (.refl _) (Step.toPar s)
  | .iotaNatRecZero z s   => .iotaNatRecZero s (.refl z)
  | .iotaNatRecSucc n z s =>
      .iotaNatRecSucc (.refl n) (.refl z) (.refl s)
  | .listConsHead s       => .listCons (Step.toPar s) (.refl _)
  | .listConsTail s       => .listCons (.refl _) (Step.toPar s)
  | .listElimScrutinee s  => .listElim (Step.toPar s) (.refl _) (.refl _)
  | .listElimNil s        => .listElim (.refl _) (Step.toPar s) (.refl _)
  | .listElimCons s       => .listElim (.refl _) (.refl _) (Step.toPar s)
  | .iotaListElimNil n c  => .iotaListElimNil c (.refl n)
  | .iotaListElimCons h t _ c =>
      .iotaListElimCons _ (.refl h) (.refl t) (.refl c)
  | .optionSomeValue s    => .optionSome (Step.toPar s)
  | .optionMatchScrutinee s => .optionMatch (Step.toPar s) (.refl _) (.refl _)
  | .optionMatchNone s    => .optionMatch (.refl _) (Step.toPar s) (.refl _)
  | .optionMatchSome s    => .optionMatch (.refl _) (.refl _) (Step.toPar s)
  | .iotaOptionMatchNone n s => .iotaOptionMatchNone s (.refl n)
  | .iotaOptionMatchSome v _ s =>
      .iotaOptionMatchSome _ (.refl v) (.refl s)
  | .eitherInlValue s     => .eitherInl (Step.toPar s)
  | .eitherInrValue s     => .eitherInr (Step.toPar s)
  | .eitherMatchScrutinee s => .eitherMatch (Step.toPar s) (.refl _) (.refl _)
  | .eitherMatchLeft s    => .eitherMatch (.refl _) (Step.toPar s) (.refl _)
  | .eitherMatchRight s   => .eitherMatch (.refl _) (.refl _) (Step.toPar s)
  | .iotaEitherMatchInl v lb rb =>
      .iotaEitherMatchInl rb (.refl v) (.refl lb)
  | .iotaEitherMatchInr v lb rb =>
      .iotaEitherMatchInr lb (.refl v) (.refl rb)
  | .idJBase s              => .idJ (Step.toPar s) (.refl _)
  | .idJWitness _ s         => .idJ (.refl _) (Step.toPar s)
  | .iotaIdJRefl base       => .iotaIdJRefl (.refl base)

/-- Transport a parallel reduction across the same type equality on
both endpoints. -/
theorem Step.par.castBoth
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    (parallelStep : Step.par beforeTerm afterTerm) :
    Step.par (typeEquality ▸ beforeTerm) (typeEquality ▸ afterTerm) := by
  cases typeEquality
  exact parallelStep

/-- Replace the source endpoint of a same-typed parallel reduction by
propositionally equal syntax. -/
theorem Step.par.castSource
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm beforeTerm' afterTerm : Term ctx termType}
    (sourceEquality : beforeTerm = beforeTerm')
    (parallelStep : Step.par beforeTerm afterTerm) :
    Step.par beforeTerm' afterTerm := by
  cases sourceEquality
  exact parallelStep

/-- Replace the target endpoint of a same-typed parallel reduction by
propositionally equal syntax. -/
theorem Step.par.castTarget
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm afterTerm afterTerm' : Term ctx termType}
    (targetEquality : afterTerm = afterTerm')
    (parallelStep : Step.par beforeTerm afterTerm) :
    Step.par beforeTerm afterTerm' := by
  cases targetEquality
  exact parallelStep


end LeanFX.Syntax
