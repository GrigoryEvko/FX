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
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {witness : Term ctx (Ty.id carrier leftEnd rightEnd)},
      Step baseCase baseCase' →
      Step (Term.idJ baseCase witness) (Term.idJ baseCase' witness)
  /-- Step inside `Term.idJ`'s witness position. -/
  | idJWitness :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
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
        {carrier : Ty level scope} {endpoint : RawTerm scope}
        {resultType : Ty level scope}
        (baseCase : Term ctx resultType),
      Step (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                     (rightEnd := endpoint) baseCase
                     (Term.refl (carrier := carrier) endpoint))
           baseCase

/-- Transport a single-step reduction across the same type equality on
both endpoints.  This is the reduction-level analogue of the repeated
`Eq.rec` bridges used in term substitution proofs: when a constructor
such as `Term.rename` inserts the same cast on both sides of a
congruence, the reduction proof itself is unchanged after eliminating
the equality. -/
theorem Step.castBoth
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    (singleStep : Step beforeTerm afterTerm) :
    Step (typeEquality ▸ beforeTerm) (typeEquality ▸ afterTerm) := by
  cases typeEquality
  exact singleStep

/-- Replace the source endpoint of a same-typed single-step reduction
by propositionally equal syntax.  β/η preservation proofs use this
after exposing a renamed redex as the source expected by a primitive
`Step` constructor. -/
theorem Step.castSource
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm beforeTerm' afterTerm : Term ctx termType}
    (sourceEquality : beforeTerm = beforeTerm')
    (singleStep : Step beforeTerm afterTerm) :
    Step beforeTerm' afterTerm := by
  cases sourceEquality
  exact singleStep

/-- Replace the target endpoint of a same-typed single-step reduction
by propositionally equal syntax.  β/ι preservation proofs use this
after the primitive reduction constructor produces the canonical
renamed reduct and a commute lemma identifies it with the renamed
original reduct. -/
theorem Step.castTarget
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm afterTerm afterTerm' : Term ctx termType}
    (targetEquality : afterTerm = afterTerm')
    (singleStep : Step beforeTerm afterTerm) :
    Step beforeTerm afterTerm' := by
  cases targetEquality
  exact singleStep

end LeanFX.Syntax
