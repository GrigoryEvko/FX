import LeanFX2.Term.Subst

/-! # Reduction/Step — single-step βι reduction

`Step source target : Prop` is a typed single-step reduction
between Term values.

## Signature

`Step` carries TWO Ty indices and TWO RawTerm indices:

```lean
Step : ∀ {mode level scope} {ctx : Ctx mode level scope}
        {sourceType targetType : Ty level scope}
        {sourceRaw targetRaw : RawTerm scope},
       Term ctx sourceType sourceRaw →
       Term ctx targetType targetRaw →
       Prop
```

Why two Ty indices?  Lean-fx-2's raw-aware Term threads `RawTerm.fst
pairRaw` into the type of `Term.snd`'s result.  When we step
`Term.snd (Term.pair fv sv)` to `sv`, the source's Ty contains
`RawTerm.fst (RawTerm.pair firstRaw secondRaw)` and the target's
Ty contains `firstRaw` directly — these are NOT equal in Lean's
intensional Eq (only equal up to βι at the raw level).  Two Ty
indices let `Step.betaSndPair` state cleanly without HEq.

The same gap appears in dep cong rules: `Step.appPiRight` steps
the argument of a Π-application, changing the result's Ty (whose
codomain substitutes the argument's raw form); `Step.pairLeft`
steps the first component of a Σ-pair, changing the second
component's required Ty.  Two Ty indices accommodate all of these.

Subject reduction at the Step level is therefore *not* given by
the signature.  Subject reduction modulo βι Conv is recovered at
Layer 3 (Confluence) via Church-Rosser.

## η deliberately omitted

η-reduction has structurally weakened source ctor patterns
(`Term.lam (Term.app (Term.weaken f) (Term.var 0))`) that make
βι confluence proofs harder than they need to be.  βι is the
default at this layer; η lives in `Reduction/Eta.lean` as opt-in.

## Cong rules (one per binder + per eliminator)

Each cong rule lifts an inner Step into the surrounding ctor.

* `appLeft, appRight, lamBody`
* `appPiLeft, appPiRight, lamPiBody`
* `pairLeft, pairRight, fstCong, sndCong`
* `boolElimScrutinee, boolElimThen, boolElimElse`
* `natSuccPred, natElim{Scrutinee,Zero,Succ}, natRec{Scrutinee,Zero,Succ}`
* `listConsHead, listConsTail, listElim{Scrutinee,Nil,Cons}`
* `optionSomeValue, optionMatch{Scrutinee,None,Some}`
* `eitherInlValue, eitherInrValue, eitherMatch{Scrutinee,Left,Right}`
* `idJBase, idJWitness`

## β rules

* `betaApp body arg` — `(λx. body) arg ⟶ body[arg/x]`
  (non-dep; tgt Ty = `cod.weaken.subst0 dom argRaw`, src Ty = `cod`)
* `betaAppPi body arg` — `(λx. body) arg ⟶ body[arg/x]`
  (dep Π; both Tys = `cod.subst0 dom argRaw` ✓)
* `betaFstPair fv sv` — `fst (pair a b) ⟶ a` (both Tys = `firstType` ✓)
* `betaSndPair fv sv` — `snd (pair a b) ⟶ b`
  (src Ty has `fst (pair fr sr)`, tgt Ty has `fr` — DIFFER, allowed by sig)

## ι rules

* `iotaBoolElim{True,False}`
* `iotaNatElim{Zero,Succ}, iotaNatRec{Zero,Succ}`
* `iotaListElim{Nil,Cons}`
* `iotaOptionMatch{None,Some}`
* `iotaEitherMatch{Inl,Inr}`
* `iotaIdJRefl`

## Cast helpers

`Step.castSourceType`, `Step.castTargetType`, `Step.castSourceRaw`,
`Step.castTargetRaw` swap propositionally-equal Ty / RawTerm at
the indices.  Defined as theorems via `cases equality; exact step`.
-/

namespace LeanFX2

/-- Single-step typed βι reduction.  `Step src tgt` witnesses that
`src` reduces in one step to `tgt`.  Two Ty + two RawTerm indices
on src/tgt allow dep cong rules and `betaSndPair` to state
naturally without HEq scaffolding. -/
inductive Step :
    ∀ {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {sourceType targetType : Ty level scope}
      {sourceRaw targetRaw : RawTerm scope},
      Term context sourceType sourceRaw →
      Term context targetType targetRaw →
      Prop
  /-- Step inside the function position of a non-dep application. -/
  | appLeft {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionRawSource functionRawTarget argumentRaw : RawTerm scope}
      {functionTermSource :
        Term context (Ty.arrow domainType codomainType) functionRawSource}
      {functionTermTarget :
        Term context (Ty.arrow domainType codomainType) functionRawTarget}
      {argumentTerm : Term context domainType argumentRaw} :
      Step functionTermSource functionTermTarget →
      Step (Term.app functionTermSource argumentTerm)
           (Term.app functionTermTarget argumentTerm)
  /-- Step inside the argument position of a non-dep application. -/
  | appRight {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionRaw argumentRawSource argumentRawTarget : RawTerm scope}
      {functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw}
      {argumentTermSource : Term context domainType argumentRawSource}
      {argumentTermTarget : Term context domainType argumentRawTarget} :
      Step argumentTermSource argumentTermTarget →
      Step (Term.app functionTerm argumentTermSource)
           (Term.app functionTerm argumentTermTarget)
  /-- Step inside the body of a non-dep λ-abstraction. -/
  | lamBody {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons domainType) codomainType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons domainType) codomainType.weaken bodyRawTarget} :
      Step bodySource bodyTarget →
      Step (Term.lam (codomainType := codomainType) bodySource)
           (Term.lam (codomainType := codomainType) bodyTarget)
  /-- Step inside the function position of a dependent application. -/
  | appPiLeft {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {functionRawSource functionRawTarget argumentRaw : RawTerm scope}
      {functionTermSource :
        Term context (Ty.piTy domainType codomainType) functionRawSource}
      {functionTermTarget :
        Term context (Ty.piTy domainType codomainType) functionRawTarget}
      {argumentTerm : Term context domainType argumentRaw} :
      Step functionTermSource functionTermTarget →
      Step (Term.appPi functionTermSource argumentTerm)
           (Term.appPi functionTermTarget argumentTerm)
  /-- Step inside the argument position of a dependent application.
  The result's Ty depends on the argument's raw form, so source and
  target Ty differ — handled by the two-Ty signature. -/
  | appPiRight {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {functionRaw argumentRawSource argumentRawTarget : RawTerm scope}
      {functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw}
      {argumentTermSource : Term context domainType argumentRawSource}
      {argumentTermTarget : Term context domainType argumentRawTarget} :
      Step argumentTermSource argumentTermTarget →
      Step (Term.appPi functionTerm argumentTermSource)
           (Term.appPi functionTerm argumentTermTarget)
  /-- Step inside the body of a dependent λ-abstraction. -/
  | lamPiBody {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons domainType) codomainType bodyRawSource}
      {bodyTarget :
        Term (context.cons domainType) codomainType bodyRawTarget} :
      Step bodySource bodyTarget →
      Step (Term.lamPi (domainType := domainType) bodySource)
           (Term.lamPi (domainType := domainType) bodyTarget)
  /-- Step inside the second component of a Σ-pair.  First's raw
  is fixed, so secondValueSource and secondValueTarget share Ty. -/
  | pairRight {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw secondRawSource secondRawTarget : RawTerm scope}
      {firstValue : Term context firstType firstRaw}
      {secondValueSource :
        Term context (secondType.subst0 firstType firstRaw) secondRawSource}
      {secondValueTarget :
        Term context (secondType.subst0 firstType firstRaw) secondRawTarget} :
      Step secondValueSource secondValueTarget →
      Step (Term.pair (secondType := secondType) firstValue secondValueSource)
           (Term.pair (secondType := secondType) firstValue secondValueTarget)
  /-- Step inside the argument of a first projection. -/
  | fstCong {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRawSource pairRawTarget : RawTerm scope}
      {pairTermSource :
        Term context (Ty.sigmaTy firstType secondType) pairRawSource}
      {pairTermTarget :
        Term context (Ty.sigmaTy firstType secondType) pairRawTarget} :
      Step pairTermSource pairTermTarget →
      Step (Term.fst (secondType := secondType) pairTermSource)
           (Term.fst (secondType := secondType) pairTermTarget)
  /-- Step inside the argument of a second projection.  Source and
  target Ty differ via `RawTerm.fst pairRawSource` vs
  `RawTerm.fst pairRawTarget` — accommodated by two-Ty signature. -/
  | sndCong {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRawSource pairRawTarget : RawTerm scope}
      {pairTermSource :
        Term context (Ty.sigmaTy firstType secondType) pairRawSource}
      {pairTermTarget :
        Term context (Ty.sigmaTy firstType secondType) pairRawTarget} :
      Step pairTermSource pairTermTarget →
      Step (Term.snd (secondType := secondType) pairTermSource)
           (Term.snd (secondType := secondType) pairTermTarget)
  /-- β-reduction non-dep arrow: `(λx. body) arg ⟶ body[arg/x]`.
  Source Ty = `codomainType`; target Ty =
  `codomainType.weaken.subst0 domainType argumentRaw` — these are
  propositionally equal (`Ty.weaken_subst_singleton`) but differ
  syntactically; two-Ty Step makes the rule clean. -/
  | betaApp {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
      (bodyTerm :
        Term (context.cons domainType) codomainType.weaken bodyRaw)
      (argumentTerm : Term context domainType argumentRaw) :
      Step (Term.app (Term.lam (codomainType := codomainType) bodyTerm) argumentTerm)
           (Term.subst0 bodyTerm argumentTerm)
  /-- β-reduction dependent Π: `(λx. body) arg ⟶ body[arg/x]`.
  Source and target Ty both equal `codomainType.subst0 domainType argumentRaw`. -/
  | betaAppPi {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
      (bodyTerm : Term (context.cons domainType) codomainType bodyRaw)
      (argumentTerm : Term context domainType argumentRaw) :
      Step (Term.appPi (Term.lamPi (domainType := domainType) bodyTerm) argumentTerm)
           (Term.subst0 bodyTerm argumentTerm)
  /-- β-reduction Σ first projection: `fst (pair a b) ⟶ a`.  Both
  sides have Ty `firstType`. -/
  | betaFstPair {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw secondRaw : RawTerm scope}
      (firstValue : Term context firstType firstRaw)
      (secondValue :
        Term context (secondType.subst0 firstType firstRaw) secondRaw) :
      Step (Term.fst (Term.pair (secondType := secondType) firstValue secondValue))
           firstValue
  /-- β-reduction Σ second projection: `snd (pair a b) ⟶ b`.  Source
  Ty = `secondType.subst0 firstType (RawTerm.fst (RawTerm.pair fr sr))`;
  target Ty = `secondType.subst0 firstType firstRaw`.  These differ
  via the un-fired raw fst-of-pair redex; two-Ty Step admits it. -/
  | betaSndPair {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw secondRaw : RawTerm scope}
      (firstValue : Term context firstType firstRaw)
      (secondValue :
        Term context (secondType.subst0 firstType firstRaw) secondRaw) :
      Step (Term.snd (Term.pair (secondType := secondType) firstValue secondValue))
           secondValue
  /-- Step inside the scrutinee of a `boolElim`. -/
  | boolElimScrutinee {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget thenRaw elseRaw : RawTerm scope}
      {scrutineeSource : Term context Ty.bool scrutineeRawSource}
      {scrutineeTarget : Term context Ty.bool scrutineeRawTarget}
      {thenBranch : Term context motiveType thenRaw}
      {elseBranch : Term context motiveType elseRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.boolElim scrutineeSource thenBranch elseBranch)
           (Term.boolElim scrutineeTarget thenBranch elseBranch)
  /-- Step inside the then-branch of a `boolElim`. -/
  | boolElimThen {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw thenRawSource thenRawTarget elseRaw : RawTerm scope}
      {scrutinee : Term context Ty.bool scrutineeRaw}
      {thenSource : Term context motiveType thenRawSource}
      {thenTarget : Term context motiveType thenRawTarget}
      {elseBranch : Term context motiveType elseRaw} :
      Step thenSource thenTarget →
      Step (Term.boolElim scrutinee thenSource elseBranch)
           (Term.boolElim scrutinee thenTarget elseBranch)
  /-- Step inside the else-branch of a `boolElim`. -/
  | boolElimElse {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw thenRaw elseRawSource elseRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.bool scrutineeRaw}
      {thenBranch : Term context motiveType thenRaw}
      {elseSource : Term context motiveType elseRawSource}
      {elseTarget : Term context motiveType elseRawTarget} :
      Step elseSource elseTarget →
      Step (Term.boolElim scrutinee thenBranch elseSource)
           (Term.boolElim scrutinee thenBranch elseTarget)
  /-- ι-reduction `boolElim true t e ⟶ t`. -/
  | iotaBoolElimTrue {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {thenRaw elseRaw : RawTerm scope}
      (thenBranch : Term context motiveType thenRaw)
      (elseBranch : Term context motiveType elseRaw) :
      Step (Term.boolElim Term.boolTrue thenBranch elseBranch) thenBranch
  /-- ι-reduction `boolElim false t e ⟶ e`. -/
  | iotaBoolElimFalse {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {thenRaw elseRaw : RawTerm scope}
      (thenBranch : Term context motiveType thenRaw)
      (elseBranch : Term context motiveType elseRaw) :
      Step (Term.boolElim Term.boolFalse thenBranch elseBranch) elseBranch
  /-- Step inside the predecessor of `Term.natSucc`. -/
  | natSuccPred {mode level scope} {context : Ctx mode level scope}
      {predecessorRawSource predecessorRawTarget : RawTerm scope}
      {predecessorSource : Term context Ty.nat predecessorRawSource}
      {predecessorTarget : Term context Ty.nat predecessorRawTarget} :
      Step predecessorSource predecessorTarget →
      Step (Term.natSucc predecessorSource) (Term.natSucc predecessorTarget)
  /-- Step inside `natElim`'s scrutinee. -/
  | natElimScrutinee {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget zeroRaw succRaw : RawTerm scope}
      {scrutineeSource : Term context Ty.nat scrutineeRawSource}
      {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
      {zeroBranch : Term context motiveType zeroRaw}
      {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.natElim scrutineeSource zeroBranch succBranch)
           (Term.natElim scrutineeTarget zeroBranch succBranch)
  /-- Step inside `natElim`'s zero-branch. -/
  | natElimZero {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRawSource zeroRawTarget succRaw : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw} :
      Step zeroSource zeroTarget →
      Step (Term.natElim scrutinee zeroSource succBranch)
           (Term.natElim scrutinee zeroTarget succBranch)
  /-- Step inside `natElim`'s succ-branch. -/
  | natElimSucc {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRaw succRawSource succRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {zeroBranch : Term context motiveType zeroRaw}
      {succSource : Term context (Ty.arrow Ty.nat motiveType) succRawSource}
      {succTarget : Term context (Ty.arrow Ty.nat motiveType) succRawTarget} :
      Step succSource succTarget →
      Step (Term.natElim scrutinee zeroBranch succSource)
           (Term.natElim scrutinee zeroBranch succTarget)
  /-- ι-reduction `natElim 0 z s ⟶ z`. -/
  | iotaNatElimZero {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {zeroRaw succRaw : RawTerm scope}
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      Step (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch
  /-- ι-reduction `natElim (succ n) z s ⟶ s n`. -/
  | iotaNatElimSucc {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {predecessorRaw zeroRaw succRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predecessorRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      Step (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
           (Term.app succBranch predecessor)
  /-- Step inside `natRec`'s scrutinee. -/
  | natRecScrutinee {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget zeroRaw succRaw : RawTerm scope}
      {scrutineeSource : Term context Ty.nat scrutineeRawSource}
      {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
      {zeroBranch : Term context motiveType zeroRaw}
      {succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.natRec scrutineeSource zeroBranch succBranch)
           (Term.natRec scrutineeTarget zeroBranch succBranch)
  /-- Step inside `natRec`'s zero-branch. -/
  | natRecZero {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRawSource zeroRawTarget succRaw : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      {succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw} :
      Step zeroSource zeroTarget →
      Step (Term.natRec scrutinee zeroSource succBranch)
           (Term.natRec scrutinee zeroTarget succBranch)
  /-- Step inside `natRec`'s succ-branch. -/
  | natRecSucc {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRaw succRawSource succRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {zeroBranch : Term context motiveType zeroRaw}
      {succSource :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
      {succTarget :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget} :
      Step succSource succTarget →
      Step (Term.natRec scrutinee zeroBranch succSource)
           (Term.natRec scrutinee zeroBranch succTarget)
  /-- ι-reduction `natRec 0 z s ⟶ z`. -/
  | iotaNatRecZero {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {zeroRaw succRaw : RawTerm scope}
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      Step (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch
  /-- ι-reduction `natRec (succ n) z s ⟶ s n (natRec n z s)`. -/
  | iotaNatRecSucc {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {predecessorRaw zeroRaw succRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predecessorRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      Step (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
           (Term.app (Term.app succBranch predecessor)
                     (Term.natRec predecessor zeroBranch succBranch))
  /-- Step inside the head of `Term.listCons`. -/
  | listConsHead {mode level scope} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headRawSource headRawTarget tailRaw : RawTerm scope}
      {headSource : Term context elementType headRawSource}
      {headTarget : Term context elementType headRawTarget}
      {tailTerm : Term context (Ty.listType elementType) tailRaw} :
      Step headSource headTarget →
      Step (Term.listCons headSource tailTerm)
           (Term.listCons headTarget tailTerm)
  /-- Step inside the tail of `Term.listCons`. -/
  | listConsTail {mode level scope} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headRaw tailRawSource tailRawTarget : RawTerm scope}
      {headTerm : Term context elementType headRaw}
      {tailSource : Term context (Ty.listType elementType) tailRawSource}
      {tailTarget : Term context (Ty.listType elementType) tailRawTarget} :
      Step tailSource tailTarget →
      Step (Term.listCons headTerm tailSource)
           (Term.listCons headTerm tailTarget)
  /-- Step inside `listElim`'s scrutinee. -/
  | listElimScrutinee {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget nilRaw consRaw : RawTerm scope}
      {scrutineeSource :
        Term context (Ty.listType elementType) scrutineeRawSource}
      {scrutineeTarget :
        Term context (Ty.listType elementType) scrutineeRawTarget}
      {nilBranch : Term context motiveType nilRaw}
      {consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.listElim scrutineeSource nilBranch consBranch)
           (Term.listElim scrutineeTarget nilBranch consBranch)
  /-- Step inside `listElim`'s nil-branch. -/
  | listElimNil {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw nilRawSource nilRawTarget consRaw : RawTerm scope}
      {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
      {nilSource : Term context motiveType nilRawSource}
      {nilTarget : Term context motiveType nilRawTarget}
      {consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw} :
      Step nilSource nilTarget →
      Step (Term.listElim scrutinee nilSource consBranch)
           (Term.listElim scrutinee nilTarget consBranch)
  /-- Step inside `listElim`'s cons-branch. -/
  | listElimCons {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw nilRaw consRawSource consRawTarget : RawTerm scope}
      {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
      {nilBranch : Term context motiveType nilRaw}
      {consSource :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawSource}
      {consTarget :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawTarget} :
      Step consSource consTarget →
      Step (Term.listElim scrutinee nilBranch consSource)
           (Term.listElim scrutinee nilBranch consTarget)
  /-- ι-reduction `listElim [] n c ⟶ n`. -/
  | iotaListElimNil {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {nilRaw consRaw : RawTerm scope}
      (nilBranch : Term context motiveType nilRaw)
      (consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      Step (Term.listElim (elementType := elementType) Term.listNil
              nilBranch consBranch)
           nilBranch
  /-- ι-reduction `listElim (cons h t) n c ⟶ c h t`. -/
  | iotaListElimCons {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {headRaw tailRaw nilRaw consRaw : RawTerm scope}
      (headTerm : Term context elementType headRaw)
      (tailTerm : Term context (Ty.listType elementType) tailRaw)
      (nilBranch : Term context motiveType nilRaw)
      (consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      Step (Term.listElim (Term.listCons headTerm tailTerm) nilBranch consBranch)
           (Term.app (Term.app consBranch headTerm) tailTerm)
  /-- Step inside `Term.optionSome`'s value. -/
  | optionSomeValue {mode level scope} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {valueRawSource valueRawTarget : RawTerm scope}
      {valueSource : Term context elementType valueRawSource}
      {valueTarget : Term context elementType valueRawTarget} :
      Step valueSource valueTarget →
      Step (Term.optionSome valueSource) (Term.optionSome valueTarget)
  /-- Step inside `optionMatch`'s scrutinee. -/
  | optionMatchScrutinee {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget noneRaw someRaw : RawTerm scope}
      {scrutineeSource :
        Term context (Ty.optionType elementType) scrutineeRawSource}
      {scrutineeTarget :
        Term context (Ty.optionType elementType) scrutineeRawTarget}
      {noneBranch : Term context motiveType noneRaw}
      {someBranch : Term context (Ty.arrow elementType motiveType) someRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.optionMatch scrutineeSource noneBranch someBranch)
           (Term.optionMatch scrutineeTarget noneBranch someBranch)
  /-- Step inside `optionMatch`'s none-branch. -/
  | optionMatchNone {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw noneRawSource noneRawTarget someRaw : RawTerm scope}
      {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
      {noneSource : Term context motiveType noneRawSource}
      {noneTarget : Term context motiveType noneRawTarget}
      {someBranch : Term context (Ty.arrow elementType motiveType) someRaw} :
      Step noneSource noneTarget →
      Step (Term.optionMatch scrutinee noneSource someBranch)
           (Term.optionMatch scrutinee noneTarget someBranch)
  /-- Step inside `optionMatch`'s some-branch. -/
  | optionMatchSome {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw noneRaw someRawSource someRawTarget : RawTerm scope}
      {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
      {noneBranch : Term context motiveType noneRaw}
      {someSource : Term context (Ty.arrow elementType motiveType) someRawSource}
      {someTarget : Term context (Ty.arrow elementType motiveType) someRawTarget} :
      Step someSource someTarget →
      Step (Term.optionMatch scrutinee noneBranch someSource)
           (Term.optionMatch scrutinee noneBranch someTarget)
  /-- ι-reduction `optionMatch none n s ⟶ n`. -/
  | iotaOptionMatchNone {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {noneRaw someRaw : RawTerm scope}
      (noneBranch : Term context motiveType noneRaw)
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      Step (Term.optionMatch (elementType := elementType) Term.optionNone
              noneBranch someBranch)
           noneBranch
  /-- ι-reduction `optionMatch (some v) n s ⟶ s v`. -/
  | iotaOptionMatchSome {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {valueRaw noneRaw someRaw : RawTerm scope}
      (valueTerm : Term context elementType valueRaw)
      (noneBranch : Term context motiveType noneRaw)
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      Step (Term.optionMatch (Term.optionSome valueTerm) noneBranch someBranch)
           (Term.app someBranch valueTerm)
  /-- Step inside `Term.eitherInl`'s value. -/
  | eitherInlValue {mode level scope} {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueRawSource valueRawTarget : RawTerm scope}
      {valueSource : Term context leftType valueRawSource}
      {valueTarget : Term context leftType valueRawTarget} :
      Step valueSource valueTarget →
      Step (Term.eitherInl (rightType := rightType) valueSource)
           (Term.eitherInl (rightType := rightType) valueTarget)
  /-- Step inside `Term.eitherInr`'s value. -/
  | eitherInrValue {mode level scope} {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueRawSource valueRawTarget : RawTerm scope}
      {valueSource : Term context rightType valueRawSource}
      {valueTarget : Term context rightType valueRawTarget} :
      Step valueSource valueTarget →
      Step (Term.eitherInr (leftType := leftType) valueSource)
           (Term.eitherInr (leftType := leftType) valueTarget)
  /-- Step inside `eitherMatch`'s scrutinee. -/
  | eitherMatchScrutinee {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget leftRaw rightRaw : RawTerm scope}
      {scrutineeSource :
        Term context (Ty.eitherType leftType rightType) scrutineeRawSource}
      {scrutineeTarget :
        Term context (Ty.eitherType leftType rightType) scrutineeRawTarget}
      {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
      {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.eitherMatch scrutineeSource leftBranch rightBranch)
           (Term.eitherMatch scrutineeTarget leftBranch rightBranch)
  /-- Step inside `eitherMatch`'s left-branch. -/
  | eitherMatchLeft {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRaw leftRawSource leftRawTarget rightRaw : RawTerm scope}
      {scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw}
      {leftSource : Term context (Ty.arrow leftType motiveType) leftRawSource}
      {leftTarget : Term context (Ty.arrow leftType motiveType) leftRawTarget}
      {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw} :
      Step leftSource leftTarget →
      Step (Term.eitherMatch scrutinee leftSource rightBranch)
           (Term.eitherMatch scrutinee leftTarget rightBranch)
  /-- Step inside `eitherMatch`'s right-branch. -/
  | eitherMatchRight {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRaw leftRaw rightRawSource rightRawTarget : RawTerm scope}
      {scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw}
      {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
      {rightSource : Term context (Ty.arrow rightType motiveType) rightRawSource}
      {rightTarget : Term context (Ty.arrow rightType motiveType) rightRawTarget} :
      Step rightSource rightTarget →
      Step (Term.eitherMatch scrutinee leftBranch rightSource)
           (Term.eitherMatch scrutinee leftBranch rightTarget)
  /-- ι-reduction `eitherMatch (inl v) lb rb ⟶ lb v`. -/
  | iotaEitherMatchInl {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {valueRaw leftRaw rightRaw : RawTerm scope}
      (valueTerm : Term context leftType valueRaw)
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      Step (Term.eitherMatch (Term.eitherInl (rightType := rightType) valueTerm)
              leftBranch rightBranch)
           (Term.app leftBranch valueTerm)
  /-- ι-reduction `eitherMatch (inr v) lb rb ⟶ rb v`. -/
  | iotaEitherMatchInr {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {valueRaw leftRaw rightRaw : RawTerm scope}
      (valueTerm : Term context rightType valueRaw)
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      Step (Term.eitherMatch (Term.eitherInr (leftType := leftType) valueTerm)
              leftBranch rightBranch)
           (Term.app rightBranch valueTerm)
  /-- Step inside `idJ`'s baseCase. -/
  | idJBase {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget witnessRaw : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessTerm : Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw} :
      Step baseSource baseTarget →
      Step (Term.idJ baseSource witnessTerm)
           (Term.idJ baseTarget witnessTerm)
  /-- Step inside `idJ`'s witness. -/
  | idJWitness {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRaw witnessRawSource witnessRawTarget : RawTerm scope}
      (baseCase : Term context motiveType baseRaw)
      {witnessSource :
        Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSource}
      {witnessTarget :
        Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawTarget} :
      Step witnessSource witnessTarget →
      Step (Term.idJ baseCase witnessSource)
           (Term.idJ baseCase witnessTarget)
  /-- ι-reduction `J base (refl rt) ⟶ base`. -/
  | iotaIdJRefl {mode level scope} {context : Ctx mode level scope}
      (carrier : Ty level scope) (endpoint : RawTerm scope)
      {motiveType : Ty level scope}
      {baseRaw : RawTerm scope}
      (baseCase : Term context motiveType baseRaw) :
      Step (Term.idJ (carrier := carrier)
                     (leftEndpoint := endpoint)
                     (rightEndpoint := endpoint)
              baseCase
              (Term.refl carrier endpoint))
           baseCase
  /-- Cong rule for `Term.cumulUp`: a Step inside the lower payload
  lifts to a Step on the wrapping `cumulUp`.  The lower payload sits
  at its own context `ctxLow` and scope `scopeLow` (decoupled per
  Phase 12.A.B1.5 from the outer `ctxHigh`/`scope`); the inner
  `Step` therefore lives at parameters distinct from the outer one.

  This is the FIRST Step ctor that bridges different scope/context
  parameterizations.  The Step's parameterization picks up
  `context, level, scope` — single context throughout (Design D).

  The Step lifts the inner reduction `Step typeCodeSource
  typeCodeTarget` to the corresponding outer reduction between the
  two `cumulUp _ _ _ _ _ typeCodeSource` and `cumulUp _ _ _ _ _
  typeCodeTarget` Terms.  Output raw shape `RawTerm.cumulUpMarker
  (codeSourceRaw / codeTargetRaw)` matches the typed Term ctor's
  output. -/
  | cumulUpInner {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeSourceRaw codeTargetRaw : RawTerm scope}
      {typeCodeSource :
        Term context (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
      {typeCodeTarget :
        Term context (Ty.universe lowerLevel levelLeLow) codeTargetRaw} :
      Step typeCodeSource typeCodeTarget →
      Step (Term.cumulUp (context := context)
                         lowerLevel higherLevel cumulMonotone
                         levelLeLow levelLeHigh typeCodeSource)
           (Term.cumulUp (context := context)
                         lowerLevel higherLevel cumulMonotone
                         levelLeLow levelLeHigh typeCodeTarget)
  /-- **Univalence rfl-fragment as a definitional reduction.**
      `Step.eqType` reduces the canonical Id-typed identity-equivalence
      proof at the universe (`Term.equivReflIdAtId ... carrier carrierRaw :
      Ty.id (Ty.universe ...) carrierRaw carrierRaw`) to the canonical
      identity equivalence (`Term.equivReflId carrier : Ty.equiv carrier
      carrier`).  Both Terms project to the SAME raw form
      `RawTerm.equivIntro (lam (var 0)) (lam (var 0))`, so the rule
      changes the type only — the data is preserved.
      ## Architectural significance
      This is the single Step constructor that makes Univalence (rfl-
      fragment) DEFINITIONAL in lean-fx-2: vanilla MLTT cannot prove
      `Id Universe A B ~ Equiv A B`, but lean-fx-2 BUILDS it into the
      kernel's reduction relation.  The downstream theorem
      `Univalence : Conv (equivReflIdAtId ...) (equivReflId ...)` is
      then `Conv.fromStep Step.eqType` — zero axioms.
      ## Why source raw = target raw
      The toRawBridge (Bridge.lean) projects each typed Step.par to a
      raw-side step.  Designing this rule with matching raw forms means
      the bridge arm is `RawStep.par.refl _` — no cascade through
      RawCd / RawCdLemma / RawDiamond required.  Same trick as
      `cumulUpInner` (both source/target project to the same raw).
      Phase 12.A.B8.1 (CUMUL-8.1). -/
  | eqType {mode : Mode} {level scope : Nat}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {context : Ctx mode level scope}
      (carrier : Ty level scope)
      (carrierRaw : RawTerm scope) :
      Step (Term.equivReflIdAtId (context := context)
                                 innerLevel innerLevelLt carrier carrierRaw)
           (Term.equivReflId (context := context) carrier)
  /-- **Funext rfl-fragment as a definitional reduction.**
      `Step.eqArrow` reduces the canonical Id-typed funext witness at
      arrow types (`Term.funextReflAtId ... domainTy codomainTy applyRaw :
      Ty.id (Ty.arrow domainTy codomainTy) (lam (refl applyRaw))
      (lam (refl applyRaw))`) to the canonical pointwise-refl funext
      witness (`Term.funextRefl domainTy codomainTy applyRaw :
      Ty.piTy domainTy (Ty.id codomainTy.weaken applyRaw applyRaw)`).
      Both Terms project to the SAME raw form
      `RawTerm.lam (RawTerm.refl applyRaw)`.
      ## Architectural significance
      This is the Step constructor that makes funext (rfl-fragment)
      DEFINITIONAL in lean-fx-2.  Vanilla MLTT requires funext as an
      axiom (or via cubical machinery); lean-fx-2 builds the rfl-
      fragment into the kernel's reduction.  The downstream theorem
      `funext : Conv (funextReflAtId ...) (funextRefl ...)` is
      `Conv.fromStep Step.eqArrow` — zero axioms.
      Phase 12.A.B8.2 (CUMUL-8.2). -/
  | eqArrow {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyRaw : RawTerm (scope + 1)) :
      Step (Term.funextReflAtId (context := context)
                                domainType codomainType applyRaw)
           (Term.funextRefl (context := context)
                            domainType codomainType applyRaw)
  /-- **Heterogeneous Univalence as a definitional reduction.**
      `Step.eqTypeHet` reduces the canonical heterogeneous-carrier
      path-from-equivalence proof at the universe
      (`Term.uaIntroHet ... equivWitness :
      Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw carrierBRaw`)
      to the underlying packaged equivalence
      (`equivWitness : Ty.equiv carrierA carrierB`).  Both Terms project
      to the SAME raw form `RawTerm.equivIntro forwardRaw backwardRaw`
      (the architectural raw-alignment trick of `Term.uaIntroHet`):
      the rule changes the type only — `Ty.id (Ty.universe ...)
      carrierARaw carrierBRaw` reduces to `Ty.equiv carrierA carrierB`
      while the raw data is preserved.
      ## Architectural significance
      This is the Step constructor that makes Univalence DEFINITIONAL
      at heterogeneous carriers in lean-fx-2.  `Step.eqType` (CUMUL-8.1)
      handles only the rfl-fragment (`equivReflIdAtId → equivReflId`,
      where both carriers are the SAME `carrier`); `Step.eqTypeHet`
      generalises to ANY equivalence between two distinct carrier
      type-codes.  The downstream theorem
      `UnivalenceHet : Conv (uaIntroHet ... equivWitness) equivWitness`
      is `Conv.fromStep Step.eqTypeHet` — zero axioms.
      ## Why source raw = target raw
      Both `Term.uaIntroHet ... equivWitness` and `equivWitness`
      project to `RawTerm.equivIntro forwardRaw backwardRaw` — the
      `uaIntroHet` ctor's raw is by construction the same as its
      packaged `equivWitness`'s raw (see `Term.uaIntroHet` docstring).
      Therefore the `Step.par.toRawBridge` arm collapses to
      `RawStep.par.refl _` — no cascade through `RawCd` / `RawCdLemma`
      / `RawDiamond` required, mirroring `cumulUpInner` / `eqType` /
      `eqArrow`.
      Phase 12.A.B8.6 (heterogeneous Univalence reduction). -/
  | eqTypeHet {mode : Mode} {level scope : Nat}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRaw backwardRaw : RawTerm scope}
      (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw)) :
      Step (Term.uaIntroHet (context := context)
                            innerLevel innerLevelLt
                            carrierARaw carrierBRaw equivWitness)
           equivWitness
  /-- **Heterogeneous funext as a definitional reduction.**
      `Step.eqArrowHet` reduces the canonical heterogeneous-carrier
      funext-introduction Term at Id-of-arrow
      (`Term.funextIntroHet ... applyARaw applyBRaw :
      Ty.id (Ty.arrow domainType codomainType)
            (RawTerm.lam applyARaw) (RawTerm.lam applyBRaw)`)
      to the canonical pointwise-refl funext witness instantiated at
      `applyARaw` (`Term.funextRefl ... applyARaw :
      Ty.piTy domainType (Ty.id codomainType.weaken applyARaw applyARaw)`).
      Both Terms project to the SAME raw form
      `RawTerm.lam (RawTerm.refl applyARaw)` (the architectural raw-
      alignment trick of `Term.funextIntroHet`): the rule changes the
      type only — `Ty.id (Ty.arrow ...) (lam applyARaw) (lam applyBRaw)`
      reduces to `Ty.piTy domainType (Ty.id codomainType.weaken
      applyARaw applyARaw)` while the raw data is preserved.
      ## Architectural significance
      This is the Step constructor that makes funext DEFINITIONAL at
      heterogeneous lambda payloads in lean-fx-2.  `Step.eqArrow`
      (CUMUL-8.2) handles only the rfl-fragment (`funextReflAtId →
      funextRefl`, where source has `applyARaw = applyBRaw = applyRaw`);
      `Step.eqArrowHet` generalises to ANY two distinct apply payloads
      `applyARaw, applyBRaw` packaged through `Term.funextIntroHet`.
      The downstream theorem
      `FunextHet : Conv (funextIntroHet ... applyARaw applyBRaw)
                        (funextRefl ... applyARaw)`
      is `Conv.fromStep Step.eqArrowHet` — zero axioms.
      ## Why source raw = target raw
      Both `Term.funextIntroHet ... applyARaw applyBRaw` and
      `Term.funextRefl ... applyARaw` project to
      `RawTerm.lam (RawTerm.refl applyARaw)` — the `funextIntroHet`
      ctor's raw is by construction the same as `funextRefl`'s raw at
      the `applyARaw` payload (see `Term.funextIntroHet` docstring).
      Therefore the `Step.par.toRawBridge` arm collapses to
      `RawStep.par.refl _` — no cascade through `RawCd` / `RawCdLemma`
      / `RawDiamond` required, mirroring `cumulUpInner` / `eqType` /
      `eqArrow` / `eqTypeHet`.
      ## Asymmetric target collapse to applyARaw
      The target instantiates `funextRefl` at `applyARaw` (the LEFT
      apply payload of the source `Ty.id`).  This is forced by raw
      alignment: `funextIntroHet`'s raw uses `applyARaw` (not
      `applyBRaw`), so the rfl-collapse target must also pick
      `applyARaw`.  The dual variant collapsing to `applyBRaw` would
      require `funextIntroHet`'s raw to be `RawTerm.lam (RawTerm.refl
      applyBRaw)` — a different ctor design.  The current design picks
      `applyARaw` consistently throughout, sufficient for the
      heterogeneous funext theorem.
      Phase 12.A.B8.B (heterogeneous funext reduction). -/
  | eqArrowHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyARaw applyBRaw : RawTerm (scope + 1)) :
      Step (Term.funextIntroHet (context := context)
                                domainType codomainType applyARaw applyBRaw)
           (Term.funextRefl (context := context)
                            domainType codomainType applyARaw)

/-! ## Cast helpers

When source/target indices need to be transported across propositional
equalities (e.g., when bridging Step proofs through Ty/RawTerm
commute lemmas), these helpers swap the indexed Term values without
touching the underlying Step witness.  Each is `cases equality;
exact step`. -/

/-- Replace the source Ty by a propositionally equal Ty. -/
theorem Step.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact singleStep

/-- Replace the target Ty by a propositionally equal Ty. -/
theorem Step.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact singleStep

/-- Replace the source Term by a propositionally equal Term (same Ty). -/
theorem Step.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (singleStep : Step sourceOriginal targetTerm) :
    Step sourceReplacement targetTerm := by
  cases sourceEquality
  exact singleStep

/-- Replace the target Term by a propositionally equal Term (same Ty). -/
theorem Step.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (singleStep : Step sourceTerm targetOriginal) :
    Step sourceTerm targetReplacement := by
  cases targetEquality
  exact singleStep

end LeanFX2
