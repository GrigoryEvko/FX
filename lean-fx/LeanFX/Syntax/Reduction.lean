import LeanFX.Syntax.ToRaw

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Typed reduction (`Step`, `StepStar`).

`Step t₁ t₂` is `Prop`-valued and shares its `{ctx} {T}` indices
between sides — so subject reduction is **structural**: every
`Step` proof produces a same-typed reduct by signature alone, no
preservation theorem needed.  Covers congruence, β (`betaApp`,
`betaAppPi`), Σ projections (`betaFstPair`, `betaSndPair`),
η contractions, and boolean ι rules. -/

/-- Single-step reduction between terms of the same type. -/
inductive Step :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Step inside the function position of a non-dependent application. -/
  | appLeft  :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm functionTerm' :
          Term ctx (.arrow domainType codomainType)}
        {argumentTerm : Term ctx domainType},
      Step functionTerm functionTerm' →
      Step (Term.app functionTerm argumentTerm)
           (Term.app functionTerm' argumentTerm)
  /-- Step inside the argument position of a non-dependent application. -/
  | appRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm : Term ctx (.arrow domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType},
      Step argumentTerm argumentTerm' →
      Step (Term.app functionTerm argumentTerm)
           (Term.app functionTerm argumentTerm')
  /-- Step inside the body of a non-dependent λ-abstraction. -/
  | lamBody  :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken},
      Step body body' →
      Step (Term.lam (codomainType := codomainType) body)
           (Term.lam (codomainType := codomainType) body')
  /-- Step inside the function position of a dependent application. -/
  | appPiLeft :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {functionTerm functionTerm' :
          Term ctx (.piTy domainType codomainType)}
        {argumentTerm : Term ctx domainType},
      Step functionTerm functionTerm' →
      Step (Term.appPi functionTerm argumentTerm)
           (Term.appPi functionTerm' argumentTerm)
  /-- Step inside the argument position of a dependent application. -/
  | appPiRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {functionTerm : Term ctx (.piTy domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType},
      Step argumentTerm argumentTerm' →
      Step (Term.appPi functionTerm argumentTerm)
           (Term.appPi functionTerm argumentTerm')
  /-- Step inside the body of a dependent λ-abstraction. -/
  | lamPiBody :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType},
      Step body body' →
      Step (Term.lamPi (domainType := domainType) body)
           (Term.lamPi (domainType := domainType) body')
  /-- Step inside the first component of a pair. -/
  | pairLeft :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)},
      Step firstVal firstVal' →
      Step (Term.pair (secondType := secondType) firstVal secondVal)
           (Term.pair (secondType := secondType) firstVal' secondVal)
  /-- Step inside the second component of a pair. -/
  | pairRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step secondVal secondVal' →
      Step (Term.pair firstVal secondVal)
           (Term.pair firstVal secondVal')
  /-- Step inside the argument of a first projection. -/
  | fstCong :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (.sigmaTy firstType secondType)},
      Step pairTerm pairTerm' →
      Step (Term.fst pairTerm) (Term.fst pairTerm')
  /-- Step inside the argument of a second projection. -/
  | sndCong :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (.sigmaTy firstType secondType)},
      Step pairTerm pairTerm' →
      Step (Term.snd pairTerm) (Term.snd pairTerm')
  /-- **β-reduction for non-dependent application**: `(λx. body) arg ⟶
  body[arg/x]`.  The result type matches `Term.app`'s codomain because
  `body : Term (ctx.cons domainType) codomainType.weaken` and
  substituting at the type level via `body.subst0 (...)` reduces
  `codomainType.weaken.subst0 _` to `codomainType` per
  `Ty.weaken_subst_singleton`.  We thread the cast through `▸`. -/
  | betaApp :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        (body : Term (ctx.cons domainType) codomainType.weaken)
        (arg : Term ctx domainType),
      Step (Term.app (Term.lam (codomainType := codomainType) body) arg)
           ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body arg)
  /-- **β-reduction for dependent application**: `(λx. body) arg ⟶
  body[arg/x]` where the codomain may depend on `x` via `tyVar 0`.
  No cast needed: `body.subst0 arg : Term ctx (codomainType.subst0
  domainType)` matches `Term.appPi`'s declared result type exactly. -/
  | betaAppPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        (body : Term (ctx.cons domainType) codomainType)
        (arg : Term ctx domainType),
      Step (Term.appPi (Term.lamPi (domainType := domainType) body) arg)
           (Term.subst0 body arg)
  /-- **Σ first projection**: `fst (pair a b) ⟶ a`. -/
  | betaFstPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (firstVal : Term ctx firstType)
        (secondVal : Term ctx (secondType.subst0 firstType)),
      Step (Term.fst
              (Term.pair (firstType := firstType)
                         (secondType := secondType) firstVal secondVal))
           firstVal
  /-- **Σ second projection**: `snd (pair a b) ⟶ b`.  The result type
  is `Term ctx (secondType.subst0 firstType)` — both `Term.snd`'s
  declared result and `secondVal`'s declared type — so no cast is
  needed. -/
  | betaSndPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (firstVal : Term ctx firstType)
        (secondVal : Term ctx (secondType.subst0 firstType)),
      Step (Term.snd
              (Term.pair (firstType := firstType)
                         (secondType := secondType) firstVal secondVal))
           secondVal
  /-- **η-contraction for non-dependent arrow**: `λx. (f.weaken) x ⟶ f`
  whenever `f : Term ctx (arrow A B)`.  The body of the lam is the
  weakened `f` applied to the freshly-bound variable; η says this
  redundant abstraction collapses to `f` itself.  Soundness is
  immediate: `Term.weaken` precludes any use of the bound variable in
  `f`, so contracting cannot lose information. -/
  | etaArrow :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        (f : Term ctx (Ty.arrow domainType codomainType)),
      Step (Term.lam (codomainType := codomainType)
              (Term.app (Term.weaken domainType f)
                        (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
           f
  /-- **η-contraction for Σ-pair**: `pair (fst p) (snd p) ⟶ p`
  whenever `p : Term ctx (sigmaTy A B)`.  Reconstituting a pair from
  its projections collapses to the original pair value.  The result
  type matches because both sides have type `Term ctx (sigmaTy A B)`. -/
  | etaSigma :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (p : Term ctx (Ty.sigmaTy firstType secondType)),
      Step (Term.pair (firstType := firstType)
                       (secondType := secondType)
              (Term.fst p) (Term.snd p))
           p
  /-- Step inside the scrutinee position of a `boolElim`.  Together
  with the two ι-rules below, completes the boolean-evaluation
  story.  v1.14+. -/
  | boolElimScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.bool}
        {thenBr elseBr : Term ctx resultType},
      Step scrutinee scrutinee' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee' thenBr elseBr)
  /-- Step inside the then-branch position of a `boolElim`. -/
  | boolElimThen :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr thenBr' : Term ctx resultType}
        {elseBr : Term ctx resultType},
      Step thenBr thenBr' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee thenBr' elseBr)
  /-- Step inside the else-branch position of a `boolElim`. -/
  | boolElimElse :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr : Term ctx resultType}
        {elseBr elseBr' : Term ctx resultType},
      Step elseBr elseBr' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee thenBr elseBr')
  /-- **ι-reduction for boolElim on `true`**: `boolElim true t e ⟶ t`.
  No cast: both sides have the same `resultType`.  v1.14+. -/
  | iotaBoolElimTrue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (thenBr elseBr : Term ctx resultType),
      Step (Term.boolElim Term.boolTrue thenBr elseBr) thenBr
  /-- **ι-reduction for boolElim on `false`**: `boolElim false t e ⟶ e`.
  No cast: both sides have the same `resultType`.  v1.14+. -/
  | iotaBoolElimFalse :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (thenBr elseBr : Term ctx resultType),
      Step (Term.boolElim Term.boolFalse thenBr elseBr) elseBr
  /-- Step inside the predecessor of a `Term.natSucc`. -/
  | natSuccPred :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {pred pred' : Term ctx Ty.nat},
      Step pred pred' →
      Step (Term.natSucc pred) (Term.natSucc pred')
  /-- Step inside `Term.natElim`'s scrutinee position. -/
  | natElimScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch : Term ctx (Ty.arrow Ty.nat resultType)},
      Step scrutinee scrutinee' →
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.natElim scrutinee' zeroBranch succBranch)
  /-- Step inside `Term.natElim`'s zero-branch position. -/
  | natElimZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch : Term ctx (Ty.arrow Ty.nat resultType)},
      Step zeroBranch zeroBranch' →
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.natElim scrutinee zeroBranch' succBranch)
  /-- Step inside `Term.natElim`'s succ-branch position. -/
  | natElimSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step succBranch succBranch' →
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.natElim scrutinee zeroBranch succBranch')
  /-- **ι-reduction for natElim on `0`**: `natElim 0 z f ⟶ z`.
  No cast: both sides have the same `resultType`. -/
  | iotaNatElimZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch
  /-- **ι-reduction for natElim on `succ n`**: `natElim (succ n) z f ⟶ f n`.
  Result type matches because `f : Ty.nat → resultType` and we apply
  it to the predecessor. -/
  | iotaNatElimSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (predecessor : Term ctx Ty.nat)
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
           (Term.app succBranch predecessor)
  /-- Step inside `Term.natRec`'s scrutinee. -/
  | natRecScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step scrutinee scrutinee' →
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.natRec scrutinee' zeroBranch succBranch)
  /-- Step inside `Term.natRec`'s zero-branch. -/
  | natRecZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step zeroBranch zeroBranch' →
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.natRec scrutinee zeroBranch' succBranch)
  /-- Step inside `Term.natRec`'s succ-branch. -/
  | natRecSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step succBranch succBranch' →
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.natRec scrutinee zeroBranch succBranch')
  /-- **ι-reduction for natRec on `0`**: `natRec 0 z s ⟶ z`.  Same shape
  as `iotaNatElimZero` — the succ-branch is unused on the zero scrutinee. -/
  | iotaNatRecZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch
  /-- **ι-reduction for natRec on `succ n`**:
  `natRec (succ n) z s ⟶ s n (natRec n z s)`.  The reduct contains a
  recursive `natRec` call carrying the IH — this is what makes natRec
  primitive recursion rather than mere case-analysis. -/
  | iotaNatRecSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (predecessor : Term ctx Ty.nat)
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
           (Term.app (Term.app succBranch predecessor)
                     (Term.natRec predecessor zeroBranch succBranch))
  /-- Step inside the head of a `Term.listCons`. -/
  | listConsHead :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {hd hd' : Term ctx elementType}
        {tl : Term ctx (Ty.list elementType)},
      Step hd hd' →
      Step (Term.listCons hd tl) (Term.listCons hd' tl)
  /-- Step inside the tail of a `Term.listCons`. -/
  | listConsTail :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {hd : Term ctx elementType}
        {tl tl' : Term ctx (Ty.list elementType)},
      Step tl tl' →
      Step (Term.listCons hd tl) (Term.listCons hd tl')
  /-- Step inside `Term.listElim`'s scrutinee. -/
  | listElimScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
        {nilBranch : Term ctx resultType}
        {consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step scrutinee scrutinee' →
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.listElim scrutinee' nilBranch consBranch)
  /-- Step inside `Term.listElim`'s nil-branch. -/
  | listElimNil :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        {consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step nilBranch nilBranch' →
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.listElim scrutinee nilBranch' consBranch)
  /-- Step inside `Term.listElim`'s cons-branch. -/
  | listElimCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {nilBranch : Term ctx resultType}
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step consBranch consBranch' →
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.listElim scrutinee nilBranch consBranch')
  /-- **ι-reduction for listElim on `[]`**: `listElim [] n c ⟶ n`. -/
  | iotaListElimNil :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (nilBranch : Term ctx resultType)
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step (Term.listElim (elementType := elementType) Term.listNil
              nilBranch consBranch)
           nilBranch
  /-- **ι-reduction for listElim on `cons`**: `listElim (cons h t) n c ⟶
  c h t` — apply the curried consBranch to head and tail. -/
  | iotaListElimCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (head : Term ctx elementType)
        (tail : Term ctx (Ty.list elementType))
        (nilBranch : Term ctx resultType)
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step (Term.listElim (Term.listCons head tail) nilBranch consBranch)
           (Term.app (Term.app consBranch head) tail)
  /-- Step inside `Term.optionSome`'s value. -/
  | optionSomeValue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {value value' : Term ctx elementType},
      Step value value' →
      Step (Term.optionSome value) (Term.optionSome value')
  /-- Step inside `Term.optionMatch`'s scrutinee. -/
  | optionMatchScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
        {noneBranch : Term ctx resultType}
        {someBranch : Term ctx (Ty.arrow elementType resultType)},
      Step scrutinee scrutinee' →
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.optionMatch scrutinee' noneBranch someBranch)
  /-- Step inside `Term.optionMatch`'s none-branch. -/
  | optionMatchNone :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        {someBranch : Term ctx (Ty.arrow elementType resultType)},
      Step noneBranch noneBranch' →
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.optionMatch scrutinee noneBranch' someBranch)
  /-- Step inside `Term.optionMatch`'s some-branch. -/
  | optionMatchSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {noneBranch : Term ctx resultType}
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)},
      Step someBranch someBranch' →
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.optionMatch scrutinee noneBranch someBranch')
  /-- **ι-reduction for optionMatch on `none`**:
  `optionMatch none n s ⟶ n`. -/
  | iotaOptionMatchNone :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (noneBranch : Term ctx resultType)
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step (Term.optionMatch (elementType := elementType) Term.optionNone
              noneBranch someBranch)
           noneBranch
  /-- **ι-reduction for optionMatch on `some`**:
  `optionMatch (some v) n s ⟶ s v`. -/
  | iotaOptionMatchSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (value : Term ctx elementType)
        (noneBranch : Term ctx resultType)
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step (Term.optionMatch (Term.optionSome value) noneBranch someBranch)
           (Term.app someBranch value)
  /-- Step inside `Term.eitherInl`'s value. -/
  | eitherInlValue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx leftType},
      Step value value' →
      Step (Term.eitherInl (rightType := rightType) value)
           (Term.eitherInl (rightType := rightType) value')
  /-- Step inside `Term.eitherInr`'s value. -/
  | eitherInrValue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx rightType},
      Step value value' →
      Step (Term.eitherInr (leftType := leftType) value)
           (Term.eitherInr (leftType := leftType) value')
  /-- Step inside `Term.eitherMatch`'s scrutinee. -/
  | eitherMatchScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
        {leftBranch : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch : Term ctx (Ty.arrow rightType resultType)},
      Step scrutinee scrutinee' →
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.eitherMatch scrutinee' leftBranch rightBranch)
  /-- Step inside `Term.eitherMatch`'s left-branch. -/
  | eitherMatchLeft :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch : Term ctx (Ty.arrow rightType resultType)},
      Step leftBranch leftBranch' →
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.eitherMatch scrutinee leftBranch' rightBranch)
  /-- Step inside `Term.eitherMatch`'s right-branch. -/
  | eitherMatchRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {leftBranch : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)},
      Step rightBranch rightBranch' →
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.eitherMatch scrutinee leftBranch rightBranch')
  /-- **ι-reduction for eitherMatch on `inl`**:
  `eitherMatch (inl v) lb rb ⟶ lb v`. -/
  | iotaEitherMatchInl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        (value : Term ctx leftType)
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step (Term.eitherMatch (Term.eitherInl (rightType := rightType) value)
              leftBranch rightBranch)
           (Term.app leftBranch value)
  /-- **ι-reduction for eitherMatch on `inr`**:
  `eitherMatch (inr v) lb rb ⟶ rb v`. -/
  | iotaEitherMatchInr :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        (value : Term ctx rightType)
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step (Term.eitherMatch (Term.eitherInr (leftType := leftType) value)
              leftBranch rightBranch)
           (Term.app rightBranch value)
  /-- Step inside `Term.idJ`'s baseCase position. -/
  | idJBase :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {witness : Term ctx (Ty.id carrier leftEnd rightEnd)},
      Step baseCase baseCase' →
      Step (Term.idJ baseCase witness) (Term.idJ baseCase' witness)
  /-- Step inside `Term.idJ`'s witness position. -/
  | idJWitness :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
        {resultType : Ty level scope}
        (baseCase : Term ctx resultType)
        {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)},
      Step witness witness' →
      Step (Term.idJ baseCase witness) (Term.idJ baseCase witness')
  /-- **ι-reduction for J at refl**: `J base (refl rt) ⟶ base`.  The
  defining computational behaviour of identity types: a refl-witness
  collapses to its base case.  In the closed-endpoint regime, this is
  the only canonical J reduction (open-endpoint dependent J adds a
  cast through the path's transport, deferred to v2.3+). -/
  | iotaIdJRefl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {endpoint : RawTerm 0}
        {resultType : Ty level scope}
        (baseCase : Term ctx resultType),
      Step (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                     (rightEnd := endpoint) baseCase
                     (Term.refl (carrier := carrier) endpoint))
           baseCase

/-- Reflexive-transitive closure of `Step` — multi-step reduction.
Captures the eventual reach of the reduction relation. -/
inductive StepStar :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Zero-step: a term reduces to itself. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      StepStar t t
  /-- Prepend a single step to an existing multi-step path. -/
  | step :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ t₃ : Term ctx T},
      Step t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃

/-! Subject reduction is **structural** in this kernel: `Step`,
`StepStar`, and `Conv` (introduced below) all share their
`{ctx} {T}` indices between input and output terms, so every
well-typed input produces a well-typed output by the relations'
signatures alone.  No inductive subject-reduction theorem to state
— the typing is in the relation's type. -/

/-- Single steps lift to multi-step. -/
theorem Step.toStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : StepStar t₁ t₂ :=
  StepStar.step h (StepStar.refl t₂)

/-- Transitivity of multi-step reduction.  Together with `refl` this
makes `StepStar` an equivalence-relation-like object and is
load-bearing for the eventual conversion algorithm — in particular
for showing common-reducts when comparing terms. -/
theorem StepStar.trans
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃
  | .refl _, h         => h
  | .step s rest, h    => .step s (StepStar.trans rest h)

/-! ## StepStar structural congruences.

Multi-step threading through each constructor.  Per-position and
combined forms; induction on `StepStar` with `refl`/`step` arms. -/

/-- Multi-step reduction threads through the function position of `Term.app`. -/
theorem StepStar.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.app f₁ a) (Term.app f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appLeft s) (StepStar.app_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.app`. -/
theorem StepStar.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.app f a₁) (Term.app f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appRight s) (StepStar.app_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.app`. -/
theorem StepStar.app_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  StepStar.trans (StepStar.app_cong_left a₁ h_f)
                 (StepStar.app_cong_right f₂ h_a)

/-- Multi-step reduction threads through the body of `Term.lam`. -/
theorem StepStar.lam_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken} :
    StepStar body₁ body₂ →
    StepStar (Term.lam (codomainType := codomainType) body₁)
             (Term.lam (codomainType := codomainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamBody s) (StepStar.lam_cong rest)

/-- Multi-step reduction threads through the body of `Term.lamPi`. -/
theorem StepStar.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType} :
    StepStar body₁ body₂ →
    StepStar (Term.lamPi (domainType := domainType) body₁)
             (Term.lamPi (domainType := domainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamPiBody s) (StepStar.lamPi_cong rest)

/-- Multi-step reduction threads through the function position of `Term.appPi`. -/
theorem StepStar.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.appPi f₁ a) (Term.appPi f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiLeft s)
        (StepStar.appPi_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.appPi`. -/
theorem StepStar.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.appPi f a₁) (Term.appPi f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiRight s)
        (StepStar.appPi_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.appPi`. -/
theorem StepStar.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  StepStar.trans (StepStar.appPi_cong_left a₁ h_f)
                 (StepStar.appPi_cong_right f₂ h_a)

/-- Multi-step reduction threads through the first component of `Term.pair`. -/
theorem StepStar.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType)) :
    StepStar firstVal₁ firstVal₂ →
    StepStar
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₁ secondVal)
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₂ secondVal)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.pairLeft s)
        (StepStar.pair_cong_first secondVal rest)

/-- Multi-step reduction threads through the second component of `Term.pair`. -/
theorem StepStar.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)} :
    StepStar secondVal₁ secondVal₂ →
    StepStar (Term.pair firstVal secondVal₁)
             (Term.pair firstVal secondVal₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.pairRight s)
        (StepStar.pair_cong_second firstVal rest)

/-- Multi-step reduction threads through both components of `Term.pair`. -/
theorem StepStar.pair_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : StepStar firstVal₁ firstVal₂)
    (h_second : StepStar secondVal₁ secondVal₂) :
    StepStar (Term.pair firstVal₁ secondVal₁)
             (Term.pair firstVal₂ secondVal₂) :=
  StepStar.trans (StepStar.pair_cong_first secondVal₁ h_first)
                 (StepStar.pair_cong_second firstVal₂ h_second)

/-- Multi-step reduction threads through `Term.fst`. -/
theorem StepStar.fst_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.fst p₁) (Term.fst p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.fstCong s) (StepStar.fst_cong rest)

/-- Multi-step reduction threads through `Term.snd`. -/
theorem StepStar.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.snd p₁) (Term.snd p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.sndCong s) (StepStar.snd_cong rest)

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
  /-- Parallel reduction inside a dependent application. -/
  | appPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {f f' : Term ctx (.piTy domainType codomainType)}
        {a a' : Term ctx domainType},
      Step.par f f' → Step.par a a' →
      Step.par (Term.appPi f a) (Term.appPi f' a')
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
  /-- Parallel reduction inside a second projection. -/
  | snd :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {p p' : Term ctx (.sigmaTy firstType secondType)},
      Step.par p p' → Step.par (Term.snd p) (Term.snd p')
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
  body[arg/x]` with parallel reductions in body and arg.  No cast
  needed because `body.subst0 arg : Term ctx (codomainType.subst0
  domainType)` matches `Term.appPi`'s declared result type exactly. -/
  | betaAppPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType}
        {arg arg' : Term ctx domainType},
      Step.par body body' → Step.par arg arg' →
      Step.par (Term.appPi (Term.lamPi (domainType := domainType) body) arg)
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
  `Step.par b b'`. -/
  | betaSndPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (firstVal : Term ctx firstType)
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step.par secondVal secondVal' →
      Step.par (Term.snd
                 (Term.pair (firstType := firstType)
                            (secondType := secondType) firstVal secondVal))
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
  /-- **η-contraction for Σ-pair** at the parallel level. -/
  | etaSigma :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (p : Term ctx (Ty.sigmaTy firstType secondType)),
      Step.par (Term.pair (firstType := firstType)
                           (secondType := secondType)
                  (Term.fst p) (Term.snd p))
               p
  /-- Parallel reduction inside both positions of `Term.idJ`. -/
  | idJ :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
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
        {carrier : Ty level scope} {endpoint : RawTerm 0}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType},
      Step.par baseCase baseCase' →
      Step.par (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                         (rightEnd := endpoint) baseCase
                         (Term.refl (carrier := carrier) endpoint))
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

/-! ## Definitional conversion (`Conv`).

Symmetric / reflexive / transitive closure of `Step`.  Minimal
constructors (`refl`, `sym`, `trans`, `fromStep`); structural-
congruence rules below are derived theorems. -/

/-- The conversion relation: equivalence closure of `Step` over
terms of the same type.  Subject preservation is definitional (the
relation's indices fix the type). -/
inductive Conv :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Reflexivity: every term is convertible with itself. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      Conv t t
  /-- Symmetry: convertibility is bidirectional. -/
  | sym :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₁
  /-- Transitivity: convertibility chains. -/
  | trans :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ t₃ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₃ → Conv t₁ t₃
  /-- Embedding: every single-step reduction is a conversion. -/
  | fromStep :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ : Term ctx T},
      Step t₁ t₂ → Conv t₁ t₂

/-- Multi-step reductions lift to conversions: a sequence of forward
steps is a conversion in the forward direction.  Proven by induction
on `StepStar`: the empty case is reflexivity, the step case composes
`fromStep` with the inductive hypothesis via `trans`. -/
theorem StepStar.toConv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} :
    StepStar t₁ t₂ → Conv t₁ t₂
  | .refl t       => Conv.refl t
  | .step s rest  => Conv.trans (Conv.fromStep s) (StepStar.toConv rest)

/-- Single-step reductions lift to conversions through the multi-step
intermediary.  Direct from `Conv.fromStep`; provided as a named
theorem for symmetry with `Step.toStar`. -/
theorem Step.toConv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : Conv t₁ t₂ :=
  Conv.fromStep h

/-! ## Conv structural congruences.

Make `Conv` a full congruence relation over the term constructors. -/

/-- Convertibility threads through the function position of `Term.app`. -/
theorem Conv.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.app f₁ a) (Term.app f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appLeft s)

/-- Convertibility threads through the argument position of `Term.app`. -/
theorem Conv.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.app f a₁) (Term.app f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appRight s)

/-- Convertibility threads through both positions of `Term.app`. -/
theorem Conv.app_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  Conv.trans (Conv.app_cong_left a₁ h_f) (Conv.app_cong_right f₂ h_a)

/-- Convertibility threads through the body of `Term.lam`. -/
theorem Conv.lam_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken}
    (h : Conv body₁ body₂) :
    Conv (Term.lam (codomainType := codomainType) body₁)
         (Term.lam (codomainType := codomainType) body₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.lamBody s)

/-- Convertibility threads through the body of `Term.lamPi`. -/
theorem Conv.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType}
    (h : Conv body₁ body₂) :
    Conv (Term.lamPi (domainType := domainType) body₁)
         (Term.lamPi (domainType := domainType) body₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.lamPiBody s)

/-- Convertibility threads through the function position of `Term.appPi`. -/
theorem Conv.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.appPi f₁ a) (Term.appPi f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiLeft s)

/-- Convertibility threads through the argument position of `Term.appPi`. -/
theorem Conv.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.appPi f a₁) (Term.appPi f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiRight s)

/-- Convertibility threads through both positions of `Term.appPi`. -/
theorem Conv.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  Conv.trans (Conv.appPi_cong_left a₁ h_f) (Conv.appPi_cong_right f₂ h_a)

/-- Convertibility threads through the first component of `Term.pair`. -/
theorem Conv.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (h : Conv firstVal₁ firstVal₂) :
    Conv (Term.pair (firstType := firstType) (secondType := secondType)
                    firstVal₁ secondVal)
         (Term.pair (firstType := firstType) (secondType := secondType)
                    firstVal₂ secondVal) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.pairLeft s)

/-- Convertibility threads through the second component of `Term.pair`. -/
theorem Conv.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal secondVal₁)
         (Term.pair firstVal secondVal₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.pairRight s)

/-- Convertibility threads through both components of `Term.pair`. -/
theorem Conv.pair_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : Conv firstVal₁ firstVal₂)
    (h_second : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal₁ secondVal₁)
         (Term.pair firstVal₂ secondVal₂) :=
  Conv.trans (Conv.pair_cong_first secondVal₁ h_first)
             (Conv.pair_cong_second firstVal₂ h_second)

/-- Convertibility threads through `Term.fst`. -/
theorem Conv.fst_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.fst p₁) (Term.fst p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.fstCong s)

/-- Convertibility threads through `Term.snd`. -/
theorem Conv.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.snd p₁) (Term.snd p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.sndCong s)

/-! ## η-equivalence in natural direction.

`Step.eta*` are contractions (η-redex → underlying value); these
wrappers state η as `f ≡ λx. f x`, the form conversion algorithms
typically check. -/

/-- **η-equivalence for arrow**: `f ≡ λx. f x`. -/
theorem Term.eta_arrow_eq {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType)) :
    Conv f
         (Term.lam (codomainType := codomainType)
            (Term.app (Term.weaken domainType f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
  Conv.sym (Step.etaArrow f).toConv

/-- **η-equivalence for Σ**: `p ≡ pair (fst p) (snd p)`. -/
theorem Term.eta_sigma_eq {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (p : Term ctx (Ty.sigmaTy firstType secondType)) :
    Conv p
         (Term.pair (firstType := firstType)
                     (secondType := secondType)
            (Term.fst p) (Term.snd p)) :=
  Conv.sym (Step.etaSigma p).toConv

/-- Append a single step to an existing multi-step path — companion
to `StepStar.step` (which prepends).  Both directions are useful for
trace manipulation in conversion algorithms. -/
theorem StepStar.append
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-! ## Boolean reduction congruences.

Multi-step and definitional-equivalence threading through `boolElim`'s
three positions, plus combined three-position congruences. -/

/-- Multi-step reduction threads through `boolElim`'s scrutinee. -/
theorem StepStar.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.boolElim scrutinee₁ thenBr elseBr)
             (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimScrutinee s)
        (StepStar.boolElim_cong_scrutinee thenBr elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s then-branch. -/
theorem StepStar.boolElim_cong_then
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    StepStar thenBr₁ thenBr₂ →
    StepStar (Term.boolElim scrutinee thenBr₁ elseBr)
             (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimThen s)
        (StepStar.boolElim_cong_then scrutinee elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s else-branch. -/
theorem StepStar.boolElim_cong_else
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    StepStar elseBr₁ elseBr₂ →
    StepStar (Term.boolElim scrutinee thenBr elseBr₁)
             (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimElse s)
        (StepStar.boolElim_cong_else scrutinee thenBr rest)

/-- Multi-step reduction threads through all three `boolElim`
positions simultaneously.  Sequenced via three `trans` calls over
the single-position congruences. -/
theorem StepStar.boolElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_then : StepStar thenBr₁ thenBr₂)
    (h_else : StepStar elseBr₁ elseBr₂) :
    StepStar (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
             (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  StepStar.trans
    (StepStar.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (StepStar.trans
      (StepStar.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (StepStar.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-- Definitional equivalence threads through `boolElim`'s scrutinee. -/
theorem Conv.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    Conv scrutinee₁ scrutinee₂ →
    Conv (Term.boolElim scrutinee₁ thenBr elseBr)
         (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_scrutinee thenBr elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₁)
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimScrutinee s)

/-- Definitional equivalence threads through `boolElim`'s then-branch. -/
theorem Conv.boolElim_cong_then
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    Conv thenBr₁ thenBr₂ →
    Conv (Term.boolElim scrutinee thenBr₁ elseBr)
         (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_then scrutinee elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_then scrutinee elseBr h₁)
        (Conv.boolElim_cong_then scrutinee elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimThen s)

/-- Definitional equivalence threads through `boolElim`'s else-branch. -/
theorem Conv.boolElim_cong_else
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    Conv elseBr₁ elseBr₂ →
    Conv (Term.boolElim scrutinee thenBr elseBr₁)
         (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_else scrutinee thenBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_else scrutinee thenBr h₁)
        (Conv.boolElim_cong_else scrutinee thenBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimElse s)

/-- Definitional equivalence threads through all three `boolElim`
positions simultaneously. -/
theorem Conv.boolElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_then : Conv thenBr₁ thenBr₂)
    (h_else : Conv elseBr₁ elseBr₂) :
    Conv (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
         (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  Conv.trans
    (Conv.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (Conv.trans
      (Conv.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (Conv.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-! ## Natural-number reduction congruences.

Multi-step and definitional-equivalence threading through `Term.natSucc`
and `Term.natElim`'s three positions, mirroring the boolean section. -/

/-- Definitional equivalence threads through `Term.natSucc`. -/
theorem Conv.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat}
    (h : Conv pred₁ pred₂) :
    Conv (Term.natSucc pred₁) (Term.natSucc pred₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natSuccPred s)

/-- Definitional equivalence threads through `natElim`'s scrutinee. -/
theorem Conv.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch succBranch)
         (Term.natElim scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimScrutinee s)

/-- Definitional equivalence threads through `natElim`'s zero-branch. -/
theorem Conv.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch₁ succBranch)
         (Term.natElim scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimZero s)

/-- Definitional equivalence threads through `natElim`'s succ-branch. -/
theorem Conv.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch succBranch₁)
         (Term.natElim scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimSucc s)

/-- Definitional equivalence threads through all three `natElim` positions. -/
theorem Conv.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec Conv congruences (parallel to natElim, with the richer
succBranch type `Ty.arrow Ty.nat (Ty.arrow resultType resultType)`). -/

/-- Definitional equivalence threads through `natRec`'s scrutinee. -/
theorem Conv.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch succBranch)
         (Term.natRec scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecScrutinee s)

/-- Definitional equivalence threads through `natRec`'s zero-branch. -/
theorem Conv.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch₁ succBranch)
         (Term.natRec scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecZero s)

/-- Definitional equivalence threads through `natRec`'s succ-branch. -/
theorem Conv.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch succBranch₁)
         (Term.natRec scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecSucc s)

/-- Definitional equivalence threads through all three `natRec` positions. -/
theorem Conv.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## Natural-number Conv congruences end here.

The list-side congruences (Step / StepStar / Conv on listCons / listElim)
mirror the natElim layout but with `elementType` as an extra parametric
implicit. -/

/-- Multi-step reduction threads through `listCons`'s head. -/
theorem StepStar.listCons_cong_head {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    (tl : Term ctx (Ty.list elementType)) :
    StepStar hd₁ hd₂ →
    StepStar (Term.listCons hd₁ tl) (Term.listCons hd₂ tl)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listConsHead s)
        (StepStar.listCons_cong_head tl rest)

/-- Multi-step reduction threads through `listCons`'s tail. -/
theorem StepStar.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} :
    StepStar tl₁ tl₂ →
    StepStar (Term.listCons hd tl₁) (Term.listCons hd tl₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listConsTail s)
        (StepStar.listCons_cong_tail hd rest)

/-- Multi-step reduction threads through both head and tail of `listCons`. -/
theorem StepStar.listCons_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    {tl₁ tl₂ : Term ctx (Ty.list elementType)}
    (h_hd : StepStar hd₁ hd₂) (h_tl : StepStar tl₁ tl₂) :
    StepStar (Term.listCons hd₁ tl₁) (Term.listCons hd₂ tl₂) :=
  StepStar.trans (StepStar.listCons_cong_head tl₁ h_hd)
                 (StepStar.listCons_cong_tail hd₂ h_tl)

/-- Multi-step reduction threads through `listElim`'s scrutinee. -/
theorem StepStar.listElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.listElim scrutinee₁ nilBranch consBranch)
             (Term.listElim scrutinee₂ nilBranch consBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimScrutinee s)
        (StepStar.listElim_cong_scrutinee nilBranch consBranch rest)

/-- Multi-step reduction threads through `listElim`'s nil-branch. -/
theorem StepStar.listElim_cong_nil
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    StepStar nilBranch₁ nilBranch₂ →
    StepStar (Term.listElim scrutinee nilBranch₁ consBranch)
             (Term.listElim scrutinee nilBranch₂ consBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimNil s)
        (StepStar.listElim_cong_nil scrutinee consBranch rest)

/-- Multi-step reduction threads through `listElim`'s cons-branch. -/
theorem StepStar.listElim_cong_cons
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))} :
    StepStar consBranch₁ consBranch₂ →
    StepStar (Term.listElim scrutinee nilBranch consBranch₁)
             (Term.listElim scrutinee nilBranch consBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimCons s)
        (StepStar.listElim_cong_cons scrutinee nilBranch rest)

/-- Multi-step reduction threads through all three `listElim` positions. -/
theorem StepStar.listElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_nil : StepStar nilBranch₁ nilBranch₂)
    (h_cons : StepStar consBranch₁ consBranch₂) :
    StepStar (Term.listElim scrutinee₁ nilBranch₁ consBranch₁)
             (Term.listElim scrutinee₂ nilBranch₂ consBranch₂) :=
  StepStar.trans
    (StepStar.listElim_cong_scrutinee nilBranch₁ consBranch₁ h_scr)
    (StepStar.trans
      (StepStar.listElim_cong_nil scrutinee₂ consBranch₁ h_nil)
      (StepStar.listElim_cong_cons scrutinee₂ nilBranch₂ h_cons))

/-- Definitional equivalence threads through `listCons`'s head. -/
theorem Conv.listCons_cong_head {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    (tl : Term ctx (Ty.list elementType)) (h : Conv hd₁ hd₂) :
    Conv (Term.listCons hd₁ tl) (Term.listCons hd₂ tl) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listConsHead s)

/-- Definitional equivalence threads through `listCons`'s tail. -/
theorem Conv.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} (h : Conv tl₁ tl₂) :
    Conv (Term.listCons hd tl₁) (Term.listCons hd tl₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listConsTail s)

/-- Definitional equivalence threads through both `listCons` positions. -/
theorem Conv.listCons_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    {tl₁ tl₂ : Term ctx (Ty.list elementType)}
    (h_hd : Conv hd₁ hd₂) (h_tl : Conv tl₁ tl₂) :
    Conv (Term.listCons hd₁ tl₁) (Term.listCons hd₂ tl₂) :=
  Conv.trans (Conv.listCons_cong_head tl₁ h_hd)
             (Conv.listCons_cong_tail hd₂ h_tl)

/-- Definitional equivalence threads through `listElim`'s scrutinee. -/
theorem Conv.listElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.listElim scrutinee₁ nilBranch consBranch)
         (Term.listElim scrutinee₂ nilBranch consBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimScrutinee s)

/-- Definitional equivalence threads through `listElim`'s nil-branch. -/
theorem Conv.listElim_cong_nil
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (h : Conv nilBranch₁ nilBranch₂) :
    Conv (Term.listElim scrutinee nilBranch₁ consBranch)
         (Term.listElim scrutinee nilBranch₂ consBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimNil s)

/-- Definitional equivalence threads through `listElim`'s cons-branch. -/
theorem Conv.listElim_cong_cons
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h : Conv consBranch₁ consBranch₂) :
    Conv (Term.listElim scrutinee nilBranch consBranch₁)
         (Term.listElim scrutinee nilBranch consBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimCons s)

/-- Definitional equivalence threads through all three `listElim` positions. -/
theorem Conv.listElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_nil : Conv nilBranch₁ nilBranch₂)
    (h_cons : Conv consBranch₁ consBranch₂) :
    Conv (Term.listElim scrutinee₁ nilBranch₁ consBranch₁)
         (Term.listElim scrutinee₂ nilBranch₂ consBranch₂) :=
  Conv.trans
    (Conv.listElim_cong_scrutinee nilBranch₁ consBranch₁ h_scr)
    (Conv.trans
      (Conv.listElim_cong_nil scrutinee₂ consBranch₁ h_nil)
      (Conv.listElim_cong_cons scrutinee₂ nilBranch₂ h_cons))

/-! ## Option Conv congruences (mirror the list versions). -/

/-- Definitional equivalence threads through `Term.optionSome`'s value. -/
theorem Conv.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} (h : Conv value₁ value₂) :
    Conv (Term.optionSome value₁) (Term.optionSome value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionSomeValue s)

/-- Definitional equivalence threads through `optionMatch`'s scrutinee. -/
theorem Conv.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch someBranch)
         (Term.optionMatch scrutinee₂ noneBranch someBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchScrutinee s)

/-- Definitional equivalence threads through `optionMatch`'s none-branch. -/
theorem Conv.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv noneBranch₁ noneBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch₁ someBranch)
         (Term.optionMatch scrutinee noneBranch₂ someBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchNone s)

/-- Definitional equivalence threads through `optionMatch`'s some-branch. -/
theorem Conv.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch someBranch₁)
         (Term.optionMatch scrutinee noneBranch someBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchSome s)

/-- Definitional equivalence threads through all three `optionMatch` positions. -/
theorem Conv.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_none : Conv noneBranch₁ noneBranch₂)
    (h_some : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
         (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  Conv.trans
    (Conv.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (Conv.trans
      (Conv.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (Conv.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))

/-! ## Either Conv congruences (mirror the option versions). -/

/-- Definitional equivalence threads through `Term.eitherInl`'s value. -/
theorem Conv.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInl (rightType := rightType) value₁)
         (Term.eitherInl (rightType := rightType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInlValue s)

/-- Definitional equivalence threads through `Term.eitherInr`'s value. -/
theorem Conv.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInr (leftType := leftType) value₁)
         (Term.eitherInr (leftType := leftType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInrValue s)

/-- Definitional equivalence threads through `eitherMatch`'s scrutinee. -/
theorem Conv.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
         (Term.eitherMatch scrutinee₂ leftBranch rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchScrutinee s)

/-- Definitional equivalence threads through `eitherMatch`'s left-branch. -/
theorem Conv.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv leftBranch₁ leftBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
         (Term.eitherMatch scrutinee leftBranch₂ rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchLeft s)

/-- Definitional equivalence threads through `eitherMatch`'s right-branch. -/
theorem Conv.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch rightBranch₁)
         (Term.eitherMatch scrutinee leftBranch rightBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchRight s)

/-- Definitional equivalence threads through all three `eitherMatch` positions. -/
theorem Conv.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_left : Conv leftBranch₁ leftBranch₂)
    (h_right : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
         (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  Conv.trans
    (Conv.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (Conv.trans
      (Conv.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (Conv.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))

/-! ## idJ Conv congruences. -/

/-- Definitional equivalence threads through `Term.idJ`'s baseCase. -/
theorem Conv.idJ_cong_base {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd))
    (h : Conv baseCase₁ baseCase₂) :
    Conv (Term.idJ baseCase₁ witness) (Term.idJ baseCase₂ witness) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.idJBase s)

/-- Definitional equivalence threads through `Term.idJ`'s witness. -/
theorem Conv.idJ_cong_witness {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h : Conv witness₁ witness₂) :
    Conv (Term.idJ baseCase witness₁) (Term.idJ baseCase witness₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.idJWitness baseCase s)

/-- Definitional equivalence threads through both `Term.idJ` positions. -/
theorem Conv.idJ_cong {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h_base : Conv baseCase₁ baseCase₂)
    (h_witness : Conv witness₁ witness₂) :
    Conv (Term.idJ baseCase₁ witness₁) (Term.idJ baseCase₂ witness₂) :=
  Conv.trans
    (Conv.idJ_cong_base witness₁ h_base)
    (Conv.idJ_cong_witness baseCase₂ h_witness)

/-! ## StepStar congruences for nat (defined above the Conv versions
because Step.par.toStar consumes them). -/

/-- Multi-step reduction threads through `Term.natSucc`. -/
theorem StepStar.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat} :
    StepStar pred₁ pred₂ →
    StepStar (Term.natSucc pred₁) (Term.natSucc pred₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natSuccPred s)
        (StepStar.natSucc_cong rest)

/-- Multi-step reduction threads through `natElim`'s scrutinee. -/
theorem StepStar.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natElim scrutinee₁ zeroBranch succBranch)
             (Term.natElim scrutinee₂ zeroBranch succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimScrutinee s)
        (StepStar.natElim_cong_scrutinee zeroBranch succBranch rest)

/-- Multi-step reduction threads through `natElim`'s zero-branch. -/
theorem StepStar.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch₁ succBranch)
             (Term.natElim scrutinee zeroBranch₂ succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimZero s)
        (StepStar.natElim_cong_zero scrutinee succBranch rest)

/-- Multi-step reduction threads through `natElim`'s succ-branch. -/
theorem StepStar.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch succBranch₁)
             (Term.natElim scrutinee zeroBranch succBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimSucc s)
        (StepStar.natElim_cong_succ scrutinee zeroBranch rest)

/-- Multi-step reduction threads through all three `natElim` positions. -/
theorem StepStar.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec StepStar congruences (placed before Step.par.toStar
which consumes them, parallel to natElim). -/

/-- Multi-step reduction threads through `natRec`'s scrutinee. -/
theorem StepStar.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natRec scrutinee₁ zeroBranch succBranch)
             (Term.natRec scrutinee₂ zeroBranch succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecScrutinee s)
        (StepStar.natRec_cong_scrutinee zeroBranch succBranch rest)

/-- Multi-step reduction threads through `natRec`'s zero-branch. -/
theorem StepStar.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch₁ succBranch)
             (Term.natRec scrutinee zeroBranch₂ succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecZero s)
        (StepStar.natRec_cong_zero scrutinee succBranch rest)

/-- Multi-step reduction threads through `natRec`'s succ-branch. -/
theorem StepStar.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch succBranch₁)
             (Term.natRec scrutinee zeroBranch succBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecSucc s)
        (StepStar.natRec_cong_succ scrutinee zeroBranch rest)

/-- Multi-step reduction threads through all three `natRec` positions. -/
theorem StepStar.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## Option StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.optionSome`. -/
theorem StepStar.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} :
    StepStar value₁ value₂ →
    StepStar (Term.optionSome value₁) (Term.optionSome value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionSomeValue s)
        (StepStar.optionSome_cong rest)

/-- Multi-step reduction threads through `optionMatch`'s scrutinee. -/
theorem StepStar.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.optionMatch scrutinee₁ noneBranch someBranch)
             (Term.optionMatch scrutinee₂ noneBranch someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchScrutinee s)
        (StepStar.optionMatch_cong_scrutinee noneBranch someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s none-branch. -/
theorem StepStar.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar noneBranch₁ noneBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch₁ someBranch)
             (Term.optionMatch scrutinee noneBranch₂ someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchNone s)
        (StepStar.optionMatch_cong_none scrutinee someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s some-branch. -/
theorem StepStar.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)} :
    StepStar someBranch₁ someBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch someBranch₁)
             (Term.optionMatch scrutinee noneBranch someBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchSome s)
        (StepStar.optionMatch_cong_some scrutinee noneBranch rest)

/-- Multi-step reduction threads through all three `optionMatch` positions. -/
theorem StepStar.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_none : StepStar noneBranch₁ noneBranch₂)
    (h_some : StepStar someBranch₁ someBranch₂) :
    StepStar (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
             (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  StepStar.trans
    (StepStar.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (StepStar.trans
      (StepStar.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (StepStar.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))

/-! ## Either StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.eitherInl`. -/
theorem StepStar.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInl (rightType := rightType) value₁)
             (Term.eitherInl (rightType := rightType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInlValue s)
        (StepStar.eitherInl_cong rest)

/-- Multi-step reduction threads through `Term.eitherInr`. -/
theorem StepStar.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInr (leftType := leftType) value₁)
             (Term.eitherInr (leftType := leftType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInrValue s)
        (StepStar.eitherInr_cong rest)

/-- Multi-step reduction threads through `eitherMatch`'s scrutinee. -/
theorem StepStar.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
             (Term.eitherMatch scrutinee₂ leftBranch rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchScrutinee s)
        (StepStar.eitherMatch_cong_scrutinee leftBranch rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s left-branch. -/
theorem StepStar.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar leftBranch₁ leftBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
             (Term.eitherMatch scrutinee leftBranch₂ rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchLeft s)
        (StepStar.eitherMatch_cong_left scrutinee rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s right-branch. -/
theorem StepStar.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)} :
    StepStar rightBranch₁ rightBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch rightBranch₁)
             (Term.eitherMatch scrutinee leftBranch rightBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchRight s)
        (StepStar.eitherMatch_cong_right scrutinee leftBranch rest)

/-- Multi-step reduction threads through all three `eitherMatch` positions. -/
theorem StepStar.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_left : StepStar leftBranch₁ leftBranch₂)
    (h_right : StepStar rightBranch₁ rightBranch₂) :
    StepStar (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
             (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  StepStar.trans
    (StepStar.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (StepStar.trans
      (StepStar.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (StepStar.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))

/-! ## idJ StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.idJ`'s baseCase. -/
theorem StepStar.idJ_cong_base {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd)) :
    StepStar baseCase₁ baseCase₂ →
    StepStar (Term.idJ baseCase₁ witness) (Term.idJ baseCase₂ witness)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.idJBase s)
        (StepStar.idJ_cong_base witness rest)

/-- Multi-step reduction threads through `Term.idJ`'s witness. -/
theorem StepStar.idJ_cong_witness {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)} :
    StepStar witness₁ witness₂ →
    StepStar (Term.idJ baseCase witness₁) (Term.idJ baseCase witness₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.idJWitness baseCase s)
        (StepStar.idJ_cong_witness baseCase rest)

/-- Multi-step reduction threads through both positions of `Term.idJ`. -/
theorem StepStar.idJ_cong {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm 0}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h_base : StepStar baseCase₁ baseCase₂)
    (h_witness : StepStar witness₁ witness₂) :
    StepStar (Term.idJ baseCase₁ witness₁) (Term.idJ baseCase₂ witness₂) :=
  StepStar.trans
    (StepStar.idJ_cong_base witness₁ h_base)
    (StepStar.idJ_cong_witness baseCase₂ h_witness)

/-! ## `Step.par.toStar` — parallel reduction lifts to multi-step.

Each Step.par constructor decomposes into a sequence of single Step's
chained via StepStar congruences.  Subterm-parallel cases use the
corresponding StepStar congruence directly; β/Σ cases chain congruences
first then append a final Step.beta_* via StepStar.append; ι cases
similarly chain boolElim_cong with Step.iota_*; η cases lift directly
via Step.toStar.

Placed AFTER StepStar.append and the boolean StepStar congruences
(which v1.49 needs but were originally defined later in the file).

Together with Step.toPar (v1.48), this establishes the bridge between
StepStar and the reflexive-transitive closure of Step.par — the
Tait–Martin-Löf reformulation that makes confluence tractable. -/
theorem Step.par.toStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} : Step.par t₁ t₂ → StepStar t₁ t₂
  | .refl t                  => StepStar.refl t
  | .app par_f par_a         =>
      StepStar.app_cong (Step.par.toStar par_f) (Step.par.toStar par_a)
  | .lam par_body            =>
      StepStar.lam_cong (Step.par.toStar par_body)
  | .lamPi par_body          =>
      StepStar.lamPi_cong (Step.par.toStar par_body)
  | .appPi par_f par_a       =>
      StepStar.appPi_cong (Step.par.toStar par_f) (Step.par.toStar par_a)
  | .pair par_v par_w        =>
      StepStar.pair_cong (Step.par.toStar par_v) (Step.par.toStar par_w)
  | .fst par_p               => StepStar.fst_cong (Step.par.toStar par_p)
  | .snd par_p               => StepStar.snd_cong (Step.par.toStar par_p)
  | .boolElim par_s par_t par_e =>
      StepStar.boolElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_t)
        (Step.par.toStar par_e)
  | .betaApp (body' := body') (arg' := arg') par_body par_arg =>
      -- StepStar (app (lam body) arg) (app (lam body') arg')
      --   via app_cong of lam_cong (par_body.toStar) and par_arg.toStar
      -- then Step.betaApp body' arg' completes the β-step.
      StepStar.append
        (StepStar.app_cong
          (StepStar.lam_cong (Step.par.toStar par_body))
          (Step.par.toStar par_arg))
        (Step.betaApp body' arg')
  | .betaAppPi (body' := body') (arg' := arg') par_body par_arg =>
      StepStar.append
        (StepStar.appPi_cong
          (StepStar.lamPi_cong (Step.par.toStar par_body))
          (Step.par.toStar par_arg))
        (Step.betaAppPi body' arg')
  | .betaFstPair (firstVal' := v') secondVal par_v =>
      StepStar.append
        (StepStar.fst_cong
          (StepStar.pair_cong
            (Step.par.toStar par_v) (StepStar.refl secondVal)))
        (Step.betaFstPair v' secondVal)
  | .betaSndPair (secondVal' := w') firstVal par_w =>
      StepStar.append
        (StepStar.snd_cong
          (StepStar.pair_cong
            (StepStar.refl firstVal) (Step.par.toStar par_w)))
        (Step.betaSndPair firstVal w')
  | .iotaBoolElimTrue (thenBr' := t') elseBr par_t =>
      StepStar.append
        (StepStar.boolElim_cong
          (StepStar.refl Term.boolTrue)
          (Step.par.toStar par_t)
          (StepStar.refl elseBr))
        (Step.iotaBoolElimTrue t' elseBr)
  | .iotaBoolElimFalse (elseBr' := e') thenBr par_e =>
      StepStar.append
        (StepStar.boolElim_cong
          (StepStar.refl Term.boolFalse)
          (StepStar.refl thenBr)
          (Step.par.toStar par_e))
        (Step.iotaBoolElimFalse thenBr e')
  | .natSucc par_pred        =>
      StepStar.natSucc_cong (Step.par.toStar par_pred)
  | .natElim par_s par_z par_f =>
      StepStar.natElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_z)
        (Step.par.toStar par_f)
  | .iotaNatElimZero (zeroBranch' := z') succBranch par_z =>
      StepStar.append
        (StepStar.natElim_cong
          (StepStar.refl Term.natZero)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatElimZero z' succBranch)
  | .iotaNatElimSucc
        (predecessor' := n') (succBranch' := f')
        zeroBranch par_n par_f =>
      StepStar.trans
        (StepStar.natElim_cong
          (StepStar.natSucc_cong (Step.par.toStar par_n))
          (StepStar.refl zeroBranch)
          (Step.par.toStar par_f))
        (Step.toStar (Step.iotaNatElimSucc n' zeroBranch f'))
  | .natRec par_s par_z par_f =>
      StepStar.natRec_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_z)
        (Step.par.toStar par_f)
  | .iotaNatRecZero (zeroBranch' := z') succBranch par_z =>
      StepStar.append
        (StepStar.natRec_cong
          (StepStar.refl Term.natZero)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatRecZero z' succBranch)
  | .iotaNatRecSucc
        (predecessor' := n') (zeroBranch' := z') (succBranch' := s')
        par_n par_z par_s =>
      StepStar.trans
        (StepStar.natRec_cong
          (StepStar.natSucc_cong (Step.par.toStar par_n))
          (Step.par.toStar par_z)
          (Step.par.toStar par_s))
        (Step.toStar (Step.iotaNatRecSucc n' z' s'))
  | .listCons par_hd par_tl  =>
      StepStar.listCons_cong (Step.par.toStar par_hd) (Step.par.toStar par_tl)
  | .listElim par_s par_n par_c =>
      StepStar.listElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_n)
        (Step.par.toStar par_c)
  | .iotaListElimNil (nilBranch' := n') consBranch par_n =>
      StepStar.append
        (StepStar.listElim_cong
          (StepStar.refl Term.listNil)
          (Step.par.toStar par_n)
          (StepStar.refl consBranch))
        (Step.iotaListElimNil n' consBranch)
  | .iotaListElimCons
        (head' := h') (tail' := t') (consBranch' := c')
        nilBranch par_h par_t par_c =>
      StepStar.trans
        (StepStar.listElim_cong
          (StepStar.listCons_cong (Step.par.toStar par_h) (Step.par.toStar par_t))
          (StepStar.refl nilBranch)
          (Step.par.toStar par_c))
        (Step.toStar (Step.iotaListElimCons h' t' nilBranch c'))
  | .optionSome par_value    =>
      StepStar.optionSome_cong (Step.par.toStar par_value)
  | .optionMatch par_s par_n par_sm =>
      StepStar.optionMatch_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_n)
        (Step.par.toStar par_sm)
  | .iotaOptionMatchNone (noneBranch' := n') someBranch par_n =>
      StepStar.append
        (StepStar.optionMatch_cong
          (StepStar.refl Term.optionNone)
          (Step.par.toStar par_n)
          (StepStar.refl someBranch))
        (Step.iotaOptionMatchNone n' someBranch)
  | .iotaOptionMatchSome
        (value' := v') (someBranch' := sm')
        noneBranch par_value par_some =>
      StepStar.trans
        (StepStar.optionMatch_cong
          (StepStar.optionSome_cong (Step.par.toStar par_value))
          (StepStar.refl noneBranch)
          (Step.par.toStar par_some))
        (Step.toStar (Step.iotaOptionMatchSome v' noneBranch sm'))
  | .eitherInl par_value     =>
      StepStar.eitherInl_cong (Step.par.toStar par_value)
  | .eitherInr par_value     =>
      StepStar.eitherInr_cong (Step.par.toStar par_value)
  | .eitherMatch par_s par_l par_r =>
      StepStar.eitherMatch_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_l)
        (Step.par.toStar par_r)
  | .iotaEitherMatchInl
        (value' := v') (leftBranch' := lb')
        rightBranch par_value par_left =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (StepStar.eitherInl_cong (Step.par.toStar par_value))
          (Step.par.toStar par_left)
          (StepStar.refl rightBranch))
        (Step.toStar (Step.iotaEitherMatchInl v' lb' rightBranch))
  | .iotaEitherMatchInr
        (value' := v') (rightBranch' := rb')
        leftBranch par_value par_right =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (StepStar.eitherInr_cong (Step.par.toStar par_value))
          (StepStar.refl leftBranch)
          (Step.par.toStar par_right))
        (Step.toStar (Step.iotaEitherMatchInr v' leftBranch rb'))
  | .etaArrow f              => Step.toStar (Step.etaArrow f)
  | .etaSigma p              => Step.toStar (Step.etaSigma p)
  | .idJ par_base par_witness =>
      StepStar.idJ_cong (Step.par.toStar par_base) (Step.par.toStar par_witness)
  | .iotaIdJRefl (baseCase' := base') par_base =>
      StepStar.append
        (StepStar.idJ_cong_base _ (Step.par.toStar par_base))
        (Step.iotaIdJRefl base')

end LeanFX.Syntax
