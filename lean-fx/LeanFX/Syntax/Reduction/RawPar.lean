import LeanFX.Syntax.RawSubst

namespace LeanFX.Syntax

variable {level : Nat}

/-! ## Raw-level parallel reduction (`RawStep.par`).

This is the workhorse for confluence work.  It mirrors the typed
`Step.par`'s structure but at the type-erased raw level (`RawTerm`),
where indices are just `Nat` (the scope) — so dependent elimination
always succeeds and `cases` produces sensible inversions for every
constructor.

## Why a separate raw-level relation

Typed `Step.par`'s β/ι constructors have conclusion types involving
`▸`-casts over Ty equations (e.g., `betaApp` produces a value at
`(Ty.weaken_subst_singleton …) ▸ Term.subst0 …`).  Lean's pattern
matcher needs to solve type-level equations like `Ty.arrow d c =
codomainType.subst (Subst.singleton domainType)` to invert
`Step.par (Term.lam body) target`, and these are unsolvable in
general.  The raw-level relation has no such equations; inversion is
mechanical.

## Bridge to typed Step.par

`Reduction/RawParBridge.lean` proves `Step.par t t' →
RawStep.par (Term.toRaw t) (Term.toRaw t')` (forward direction; uses
toRaw_subst0).  `cd_lemma` is then proved at raw level (where
inversion works) and lifted to typed via the bridge plus
`Term.toRaw (Term.cd t) = RawTerm.cd (Term.toRaw t)`.

## Structure

  * 1 reflexivity rule.
  * 17 congruence rules — one per Term constructor that has subterms.
    `lam`/`lamPi` collapse to `RawTerm.lam` (Curry-style), so a
    single `lam` cong covers both.  Same for `app`/`appPi`.
  * 3 shallow β rules (`betaApp`, `betaFstPair`, `betaSndPair`).
    `betaAppPi` is unified with `betaApp` since the lam-shapes
    coincide at raw level.
  * 13 shallow ι rules (Bool×2, Nat-elim×2, Nat-rec×2, List×2,
    Option×2, Either×2, Id-J×1).
  * 16 deep variants — `betaXxxDeep` and `iotaXxxDeep` — accepting
    "inner term parallel-reduces to redex shape" as the premise.
    These mirror typed `Step.par`'s deep family (Phase 1) and are
    what `cd_lemma`'s deep cases fire.

Total: 50 constructors. -/

inductive RawStep.par : {scope : Nat} → RawTerm scope → RawTerm scope → Prop
  /-- Reflexivity. -/
  | refl : ∀ {scope : Nat} (term : RawTerm scope), RawStep.par term term

  -- Congruence rules (parallel reduction inside subterms).

  /-- Parallel reduction inside a λ-abstraction's body. -/
  | lam :
      ∀ {scope : Nat} {body body' : RawTerm (scope + 1)},
      RawStep.par body body' →
      RawStep.par (RawTerm.lam body) (RawTerm.lam body')
  /-- Parallel reduction inside both sides of an application. -/
  | app :
      ∀ {scope : Nat} {function function' argument argument' : RawTerm scope},
      RawStep.par function function' →
      RawStep.par argument argument' →
      RawStep.par (RawTerm.app function argument)
                  (RawTerm.app function' argument')
  /-- Parallel reduction inside both sides of a pair. -/
  | pair :
      ∀ {scope : Nat} {firstVal firstVal' secondVal secondVal' : RawTerm scope},
      RawStep.par firstVal firstVal' →
      RawStep.par secondVal secondVal' →
      RawStep.par (RawTerm.pair firstVal secondVal)
                  (RawTerm.pair firstVal' secondVal')
  /-- Parallel reduction inside `fst`. -/
  | fst :
      ∀ {scope : Nat} {pairTerm pairTerm' : RawTerm scope},
      RawStep.par pairTerm pairTerm' →
      RawStep.par (RawTerm.fst pairTerm) (RawTerm.fst pairTerm')
  /-- Parallel reduction inside `snd`. -/
  | snd :
      ∀ {scope : Nat} {pairTerm pairTerm' : RawTerm scope},
      RawStep.par pairTerm pairTerm' →
      RawStep.par (RawTerm.snd pairTerm) (RawTerm.snd pairTerm')
  /-- Parallel reduction inside all three positions of `boolElim`. -/
  | boolElim :
      ∀ {scope : Nat}
        {scrutinee scrutinee' thenBranch thenBranch'
         elseBranch elseBranch' : RawTerm scope},
      RawStep.par scrutinee scrutinee' →
      RawStep.par thenBranch thenBranch' →
      RawStep.par elseBranch elseBranch' →
      RawStep.par (RawTerm.boolElim scrutinee thenBranch elseBranch)
                  (RawTerm.boolElim scrutinee' thenBranch' elseBranch')
  /-- Parallel reduction inside a `natSucc`. -/
  | natSucc :
      ∀ {scope : Nat} {predecessor predecessor' : RawTerm scope},
      RawStep.par predecessor predecessor' →
      RawStep.par (RawTerm.natSucc predecessor) (RawTerm.natSucc predecessor')
  /-- Parallel reduction inside all three positions of `natElim`. -/
  | natElim :
      ∀ {scope : Nat}
        {scrutinee scrutinee' zeroBranch zeroBranch'
         succBranch succBranch' : RawTerm scope},
      RawStep.par scrutinee scrutinee' →
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par succBranch succBranch' →
      RawStep.par (RawTerm.natElim scrutinee zeroBranch succBranch)
                  (RawTerm.natElim scrutinee' zeroBranch' succBranch')
  /-- Parallel reduction inside all three positions of `natRec`. -/
  | natRec :
      ∀ {scope : Nat}
        {scrutinee scrutinee' zeroBranch zeroBranch'
         succBranch succBranch' : RawTerm scope},
      RawStep.par scrutinee scrutinee' →
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par succBranch succBranch' →
      RawStep.par (RawTerm.natRec scrutinee zeroBranch succBranch)
                  (RawTerm.natRec scrutinee' zeroBranch' succBranch')
  /-- Parallel reduction inside both sides of a `listCons`. -/
  | listCons :
      ∀ {scope : Nat} {head head' tail tail' : RawTerm scope},
      RawStep.par head head' →
      RawStep.par tail tail' →
      RawStep.par (RawTerm.listCons head tail) (RawTerm.listCons head' tail')
  /-- Parallel reduction inside all three positions of `listElim`. -/
  | listElim :
      ∀ {scope : Nat}
        {scrutinee scrutinee' nilBranch nilBranch'
         consBranch consBranch' : RawTerm scope},
      RawStep.par scrutinee scrutinee' →
      RawStep.par nilBranch nilBranch' →
      RawStep.par consBranch consBranch' →
      RawStep.par (RawTerm.listElim scrutinee nilBranch consBranch)
                  (RawTerm.listElim scrutinee' nilBranch' consBranch')
  /-- Parallel reduction inside an `optionSome`. -/
  | optionSome :
      ∀ {scope : Nat} {value value' : RawTerm scope},
      RawStep.par value value' →
      RawStep.par (RawTerm.optionSome value) (RawTerm.optionSome value')
  /-- Parallel reduction inside all three positions of `optionMatch`. -/
  | optionMatch :
      ∀ {scope : Nat}
        {scrutinee scrutinee' noneBranch noneBranch'
         someBranch someBranch' : RawTerm scope},
      RawStep.par scrutinee scrutinee' →
      RawStep.par noneBranch noneBranch' →
      RawStep.par someBranch someBranch' →
      RawStep.par (RawTerm.optionMatch scrutinee noneBranch someBranch)
                  (RawTerm.optionMatch scrutinee' noneBranch' someBranch')
  /-- Parallel reduction inside an `eitherInl`. -/
  | eitherInl :
      ∀ {scope : Nat} {value value' : RawTerm scope},
      RawStep.par value value' →
      RawStep.par (RawTerm.eitherInl value) (RawTerm.eitherInl value')
  /-- Parallel reduction inside an `eitherInr`. -/
  | eitherInr :
      ∀ {scope : Nat} {value value' : RawTerm scope},
      RawStep.par value value' →
      RawStep.par (RawTerm.eitherInr value) (RawTerm.eitherInr value')
  /-- Parallel reduction inside all three positions of `eitherMatch`. -/
  | eitherMatch :
      ∀ {scope : Nat}
        {scrutinee scrutinee' leftBranch leftBranch'
         rightBranch rightBranch' : RawTerm scope},
      RawStep.par scrutinee scrutinee' →
      RawStep.par leftBranch leftBranch' →
      RawStep.par rightBranch rightBranch' →
      RawStep.par (RawTerm.eitherMatch scrutinee leftBranch rightBranch)
                  (RawTerm.eitherMatch scrutinee' leftBranch' rightBranch')
  /-- Parallel reduction inside both positions of `idJ`. -/
  | idJ :
      ∀ {scope : Nat} {baseCase baseCase' witness witness' : RawTerm scope},
      RawStep.par baseCase baseCase' →
      RawStep.par witness witness' →
      RawStep.par (RawTerm.idJ baseCase witness)
                  (RawTerm.idJ baseCase' witness')

  -- Shallow β rules (literal-redex contraction).

  /-- β-reduction on a literal lam-app: parallel reductions in body
  and argument before substitution. -/
  | betaApp :
      ∀ {scope : Nat}
        {body body' : RawTerm (scope + 1)} {arg arg' : RawTerm scope},
      RawStep.par body body' → RawStep.par arg arg' →
      RawStep.par (RawTerm.app (RawTerm.lam body) arg)
                  (body'.subst0 arg')
  /-- π₁-reduction on a literal pair. -/
  | betaFstPair :
      ∀ {scope : Nat}
        {firstVal firstVal' : RawTerm scope} (secondVal : RawTerm scope),
      RawStep.par firstVal firstVal' →
      RawStep.par (RawTerm.fst (RawTerm.pair firstVal secondVal)) firstVal'
  /-- π₂-reduction on a literal pair. -/
  | betaSndPair :
      ∀ {scope : Nat}
        (firstVal : RawTerm scope) {secondVal secondVal' : RawTerm scope},
      RawStep.par secondVal secondVal' →
      RawStep.par (RawTerm.snd (RawTerm.pair firstVal secondVal)) secondVal'

  -- Shallow ι rules (literal-redex eliminator contraction).

  /-- ι-reduction on `boolElim true`. -/
  | iotaBoolElimTrue :
      ∀ {scope : Nat}
        {thenBranch thenBranch' : RawTerm scope}
        (elseBranch : RawTerm scope),
      RawStep.par thenBranch thenBranch' →
      RawStep.par
        (RawTerm.boolElim RawTerm.boolTrue thenBranch elseBranch)
        thenBranch'
  /-- ι-reduction on `boolElim false`. -/
  | iotaBoolElimFalse :
      ∀ {scope : Nat}
        (thenBranch : RawTerm scope)
        {elseBranch elseBranch' : RawTerm scope},
      RawStep.par elseBranch elseBranch' →
      RawStep.par
        (RawTerm.boolElim RawTerm.boolFalse thenBranch elseBranch)
        elseBranch'
  /-- ι-reduction on `natElim natZero`. -/
  | iotaNatElimZero :
      ∀ {scope : Nat}
        {zeroBranch zeroBranch' : RawTerm scope}
        (succBranch : RawTerm scope),
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par
        (RawTerm.natElim RawTerm.natZero zeroBranch succBranch)
        zeroBranch'
  /-- ι-reduction on `natElim (natSucc n)`. -/
  | iotaNatElimSucc :
      ∀ {scope : Nat}
        (zeroBranch : RawTerm scope)
        {predecessor : RawTerm scope}
        {succBranch succBranch' : RawTerm scope},
      RawStep.par succBranch succBranch' →
      RawStep.par
        (RawTerm.natElim (RawTerm.natSucc predecessor)
          zeroBranch succBranch)
        (RawTerm.app succBranch' predecessor)
  /-- ι-reduction on `natRec natZero`. -/
  | iotaNatRecZero :
      ∀ {scope : Nat}
        {zeroBranch zeroBranch' : RawTerm scope}
        (succBranch : RawTerm scope),
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par
        (RawTerm.natRec RawTerm.natZero zeroBranch succBranch)
        zeroBranch'
  /-- ι-reduction on `natRec (natSucc n)`. -/
  | iotaNatRecSucc :
      ∀ {scope : Nat}
        {predecessor : RawTerm scope}
        {zeroBranch zeroBranch' : RawTerm scope}
        {succBranch succBranch' : RawTerm scope},
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par succBranch succBranch' →
      RawStep.par
        (RawTerm.natRec (RawTerm.natSucc predecessor)
          zeroBranch succBranch)
        (RawTerm.app (RawTerm.app succBranch' predecessor)
          (RawTerm.natRec predecessor zeroBranch' succBranch'))
  /-- ι-reduction on `listElim listNil`. -/
  | iotaListElimNil :
      ∀ {scope : Nat}
        {nilBranch nilBranch' : RawTerm scope}
        (consBranch : RawTerm scope),
      RawStep.par nilBranch nilBranch' →
      RawStep.par
        (RawTerm.listElim RawTerm.listNil nilBranch consBranch)
        nilBranch'
  /-- ι-reduction on `listElim (listCons head tail)`. -/
  | iotaListElimCons :
      ∀ {scope : Nat}
        (nilBranch : RawTerm scope)
        {head tail consBranch consBranch' : RawTerm scope},
      RawStep.par consBranch consBranch' →
      RawStep.par
        (RawTerm.listElim (RawTerm.listCons head tail)
          nilBranch consBranch)
        (RawTerm.app (RawTerm.app consBranch' head) tail)
  /-- ι-reduction on `optionMatch optionNone`. -/
  | iotaOptionMatchNone :
      ∀ {scope : Nat}
        {noneBranch noneBranch' : RawTerm scope}
        (someBranch : RawTerm scope),
      RawStep.par noneBranch noneBranch' →
      RawStep.par
        (RawTerm.optionMatch RawTerm.optionNone noneBranch someBranch)
        noneBranch'
  /-- ι-reduction on `optionMatch (optionSome value)`. -/
  | iotaOptionMatchSome :
      ∀ {scope : Nat}
        (noneBranch : RawTerm scope)
        {value someBranch someBranch' : RawTerm scope},
      RawStep.par someBranch someBranch' →
      RawStep.par
        (RawTerm.optionMatch (RawTerm.optionSome value)
          noneBranch someBranch)
        (RawTerm.app someBranch' value)
  /-- ι-reduction on `eitherMatch (eitherInl value)`. -/
  | iotaEitherMatchInl :
      ∀ {scope : Nat}
        {value leftBranch leftBranch' : RawTerm scope}
        (rightBranch : RawTerm scope),
      RawStep.par leftBranch leftBranch' →
      RawStep.par
        (RawTerm.eitherMatch (RawTerm.eitherInl value)
          leftBranch rightBranch)
        (RawTerm.app leftBranch' value)
  /-- ι-reduction on `eitherMatch (eitherInr value)`. -/
  | iotaEitherMatchInr :
      ∀ {scope : Nat}
        (leftBranch : RawTerm scope)
        {value rightBranch rightBranch' : RawTerm scope},
      RawStep.par rightBranch rightBranch' →
      RawStep.par
        (RawTerm.eitherMatch (RawTerm.eitherInr value)
          leftBranch rightBranch)
        (RawTerm.app rightBranch' value)
  /-- ι-reduction on `idJ (refl rawTerm) baseCase`. -/
  | iotaIdJRefl :
      ∀ {scope : Nat}
        {baseCase baseCase' : RawTerm scope}
        (rawTerm : RawTerm scope),
      RawStep.par baseCase baseCase' →
      RawStep.par
        (RawTerm.idJ baseCase (RawTerm.refl rawTerm))
        baseCase'

  -- Deep β/ι rules — accept "inner reduces to redex shape".

  /-- Deep β-application: function reduces to a literal lam. -/
  | betaAppDeep :
      ∀ {scope : Nat}
        {function : RawTerm scope}
        {body body' : RawTerm (scope + 1)}
        {argument argument' : RawTerm scope},
      RawStep.par function (RawTerm.lam body') →
      RawStep.par argument argument' →
      RawStep.par (RawTerm.app function argument)
                  (body'.subst0 argument')
  /-- Deep π₁: pair-target reduces to a literal pair. -/
  | betaFstPairDeep :
      ∀ {scope : Nat}
        {pairTerm : RawTerm scope}
        {firstVal' secondVal' : RawTerm scope},
      RawStep.par pairTerm (RawTerm.pair firstVal' secondVal') →
      RawStep.par (RawTerm.fst pairTerm) firstVal'
  /-- Deep π₂: pair-target reduces to a literal pair. -/
  | betaSndPairDeep :
      ∀ {scope : Nat}
        {pairTerm : RawTerm scope}
        {firstVal' secondVal' : RawTerm scope},
      RawStep.par pairTerm (RawTerm.pair firstVal' secondVal') →
      RawStep.par (RawTerm.snd pairTerm) secondVal'
  /-- Deep ι on `boolElim`/`true`: scrutinee reduces to literal `true`. -/
  | iotaBoolElimTrueDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {thenBranch thenBranch' : RawTerm scope}
        (elseBranch : RawTerm scope),
      RawStep.par scrutinee RawTerm.boolTrue →
      RawStep.par thenBranch thenBranch' →
      RawStep.par
        (RawTerm.boolElim scrutinee thenBranch elseBranch)
        thenBranch'
  /-- Deep ι on `boolElim`/`false`: scrutinee reduces to literal `false`. -/
  | iotaBoolElimFalseDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        (thenBranch : RawTerm scope)
        {elseBranch elseBranch' : RawTerm scope},
      RawStep.par scrutinee RawTerm.boolFalse →
      RawStep.par elseBranch elseBranch' →
      RawStep.par
        (RawTerm.boolElim scrutinee thenBranch elseBranch)
        elseBranch'
  /-- Deep ι on `natElim`/`zero`. -/
  | iotaNatElimZeroDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {zeroBranch zeroBranch' : RawTerm scope}
        (succBranch : RawTerm scope),
      RawStep.par scrutinee RawTerm.natZero →
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par
        (RawTerm.natElim scrutinee zeroBranch succBranch)
        zeroBranch'
  /-- Deep ι on `natElim`/`succ`. -/
  | iotaNatElimSuccDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        (zeroBranch : RawTerm scope)
        {predecessor : RawTerm scope}
        {succBranch succBranch' : RawTerm scope},
      RawStep.par scrutinee (RawTerm.natSucc predecessor) →
      RawStep.par succBranch succBranch' →
      RawStep.par
        (RawTerm.natElim scrutinee zeroBranch succBranch)
        (RawTerm.app succBranch' predecessor)
  /-- Deep ι on `natRec`/`zero`. -/
  | iotaNatRecZeroDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {zeroBranch zeroBranch' : RawTerm scope}
        (succBranch : RawTerm scope),
      RawStep.par scrutinee RawTerm.natZero →
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par
        (RawTerm.natRec scrutinee zeroBranch succBranch)
        zeroBranch'
  /-- Deep ι on `natRec`/`succ`. -/
  | iotaNatRecSuccDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {predecessor : RawTerm scope}
        {zeroBranch zeroBranch' : RawTerm scope}
        {succBranch succBranch' : RawTerm scope},
      RawStep.par scrutinee (RawTerm.natSucc predecessor) →
      RawStep.par zeroBranch zeroBranch' →
      RawStep.par succBranch succBranch' →
      RawStep.par
        (RawTerm.natRec scrutinee zeroBranch succBranch)
        (RawTerm.app (RawTerm.app succBranch' predecessor)
          (RawTerm.natRec predecessor zeroBranch' succBranch'))
  /-- Deep ι on `listElim`/`nil`. -/
  | iotaListElimNilDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {nilBranch nilBranch' : RawTerm scope}
        (consBranch : RawTerm scope),
      RawStep.par scrutinee RawTerm.listNil →
      RawStep.par nilBranch nilBranch' →
      RawStep.par
        (RawTerm.listElim scrutinee nilBranch consBranch)
        nilBranch'
  /-- Deep ι on `listElim`/`cons`. -/
  | iotaListElimConsDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        (nilBranch : RawTerm scope)
        {head tail : RawTerm scope}
        {consBranch consBranch' : RawTerm scope},
      RawStep.par scrutinee (RawTerm.listCons head tail) →
      RawStep.par consBranch consBranch' →
      RawStep.par
        (RawTerm.listElim scrutinee nilBranch consBranch)
        (RawTerm.app (RawTerm.app consBranch' head) tail)
  /-- Deep ι on `optionMatch`/`none`. -/
  | iotaOptionMatchNoneDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {noneBranch noneBranch' : RawTerm scope}
        (someBranch : RawTerm scope),
      RawStep.par scrutinee RawTerm.optionNone →
      RawStep.par noneBranch noneBranch' →
      RawStep.par
        (RawTerm.optionMatch scrutinee noneBranch someBranch)
        noneBranch'
  /-- Deep ι on `optionMatch`/`some`. -/
  | iotaOptionMatchSomeDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        (noneBranch : RawTerm scope)
        {value : RawTerm scope}
        {someBranch someBranch' : RawTerm scope},
      RawStep.par scrutinee (RawTerm.optionSome value) →
      RawStep.par someBranch someBranch' →
      RawStep.par
        (RawTerm.optionMatch scrutinee noneBranch someBranch)
        (RawTerm.app someBranch' value)
  /-- Deep ι on `eitherMatch`/`inl`. -/
  | iotaEitherMatchInlDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        {value : RawTerm scope}
        {leftBranch leftBranch' : RawTerm scope}
        (rightBranch : RawTerm scope),
      RawStep.par scrutinee (RawTerm.eitherInl value) →
      RawStep.par leftBranch leftBranch' →
      RawStep.par
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch)
        (RawTerm.app leftBranch' value)
  /-- Deep ι on `eitherMatch`/`inr`. -/
  | iotaEitherMatchInrDeep :
      ∀ {scope : Nat}
        {scrutinee : RawTerm scope}
        (leftBranch : RawTerm scope)
        {value : RawTerm scope}
        {rightBranch rightBranch' : RawTerm scope},
      RawStep.par scrutinee (RawTerm.eitherInr value) →
      RawStep.par rightBranch rightBranch' →
      RawStep.par
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch)
        (RawTerm.app rightBranch' value)
  /-- Deep ι on `idJ`/`refl`. -/
  | iotaIdJReflDeep :
      ∀ {scope : Nat}
        {witness : RawTerm scope}
        {rawTerm : RawTerm scope}
        {baseCase baseCase' : RawTerm scope},
      RawStep.par witness (RawTerm.refl rawTerm) →
      RawStep.par baseCase baseCase' →
      RawStep.par (RawTerm.idJ baseCase witness) baseCase'

end LeanFX.Syntax
