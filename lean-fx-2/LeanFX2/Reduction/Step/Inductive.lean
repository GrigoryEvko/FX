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
      {motiveType : Ty level (scope + 1)}
      {scrutineeRawSource scrutineeRawTarget thenRaw elseRaw : RawTerm scope}
      {scrutineeSource : Term context Ty.bool scrutineeRawSource}
      {scrutineeTarget : Term context Ty.bool scrutineeRawTarget}
      {thenBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
      {elseBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw} :
      Step scrutineeSource scrutineeTarget →
      Step (Term.boolElim scrutineeSource thenBranch elseBranch)
           (Term.boolElim scrutineeTarget thenBranch elseBranch)
  /-- Step inside the then-branch of a `boolElim`. -/
  | boolElimThen {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      {scrutineeRaw thenRawSource thenRawTarget elseRaw : RawTerm scope}
      {scrutinee : Term context Ty.bool scrutineeRaw}
      {thenSource :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawSource}
      {thenTarget :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawTarget}
      {elseBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw} :
      Step thenSource thenTarget →
      Step (Term.boolElim scrutinee thenSource elseBranch)
           (Term.boolElim scrutinee thenTarget elseBranch)
  /-- Step inside the else-branch of a `boolElim`. -/
  | boolElimElse {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      {scrutineeRaw thenRaw elseRawSource elseRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.bool scrutineeRaw}
      {thenBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
      {elseSource :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawSource}
      {elseTarget :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawTarget} :
      Step elseSource elseTarget →
      Step (Term.boolElim scrutinee thenBranch elseSource)
           (Term.boolElim scrutinee thenBranch elseTarget)
  /-- ι-reduction `boolElim true t e ⟶ t`. -/
  | iotaBoolElimTrue {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      {thenRaw elseRaw : RawTerm scope}
      (thenBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
      (elseBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
      Step (Term.boolElim Term.boolTrue thenBranch elseBranch) thenBranch
  /-- ι-reduction `boolElim false t e ⟶ e`. -/
  | iotaBoolElimFalse {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      {thenRaw elseRaw : RawTerm scope}
      (thenBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
      (elseBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
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
  /-- Step inside `oeqJ`'s baseCase. -/
  | oeqJBase {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget witnessRaw : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessTerm :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw} :
      Step baseSource baseTarget →
      Step (Term.oeqJ baseSource witnessTerm)
           (Term.oeqJ baseTarget witnessTerm)
  /-- Step inside `oeqJ`'s witness. -/
  | oeqJWitness {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRaw witnessRawSource witnessRawTarget : RawTerm scope}
      (baseCase : Term context motiveType baseRaw)
      {witnessSource :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessRawSource}
      {witnessTarget :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessRawTarget} :
      Step witnessSource witnessTarget →
      Step (Term.oeqJ baseCase witnessSource)
           (Term.oeqJ baseCase witnessTarget)
  /-- Step inside OEq funext's pointwise equality proof function. -/
  | oeqFunextPointwise {mode level scope}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (leftFunctionRaw rightFunctionRaw : RawTerm scope)
      {pointwiseRawSource pointwiseRawTarget : RawTerm scope}
      {pointwiseSource :
        Term context
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRawSource}
      {pointwiseTarget :
        Term context
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRawTarget} :
      Step pointwiseSource pointwiseTarget →
      Step
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseSource)
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseTarget)
  /-- Step inside `idStrictRec`'s baseCase. -/
  | idStrictRecBase {mode level scope} {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget witnessRaw : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessTerm :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw} :
      Step baseSource baseTarget →
      Step (Term.idStrictRec modeIsStrict baseSource witnessTerm)
           (Term.idStrictRec modeIsStrict baseTarget witnessTerm)
  /-- Step inside `idStrictRec`'s witness. -/
  | idStrictRecWitness {mode level scope} {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRaw witnessRawSource witnessRawTarget : RawTerm scope}
      (baseCase : Term context motiveType baseRaw)
      {witnessSource :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessRawSource}
      {witnessTarget :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessRawTarget} :
      Step witnessSource witnessTarget →
      Step (Term.idStrictRec modeIsStrict baseCase witnessSource)
           (Term.idStrictRec modeIsStrict baseCase witnessTarget)
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
  /-- Strict-identity ι-reduction
      `idStrictRec base (idStrictRefl rt) ⟶ base`. -/
  | iotaIdStrictRecRefl {mode level scope} {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      (carrier : Ty level scope) (endpoint : RawTerm scope)
      {motiveType : Ty level scope}
      {baseRaw : RawTerm scope}
      (baseCase : Term context motiveType baseRaw) :
      Step (Term.idStrictRec (carrier := carrier)
                             (leftEndpoint := endpoint)
                             (rightEndpoint := endpoint)
              modeIsStrict
              baseCase
              (Term.idStrictRefl modeIsStrict carrier endpoint))
           baseCase
  /-- Step inside `modIntro`'s payload. -/
  | modIntroInner {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context innerType innerRawSource}
      {innerTarget : Term context innerType innerRawTarget} :
      Step innerSource innerTarget →
      Step (Term.modIntro innerSource) (Term.modIntro innerTarget)
  /-- Step inside `modElim`'s payload. -/
  | modElimInner {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context innerType innerRawSource}
      {innerTarget : Term context innerType innerRawTarget} :
      Step innerSource innerTarget →
      Step (Term.modElim innerSource) (Term.modElim innerTarget)
  /-- Modal β-reduction: eliminating a freshly introduced modal value
  returns the payload.  This is type-preserving in the current Layer 1
  modal scaffold, where `modIntro` and `modElim` both preserve
  `innerType`. -/
  | betaModElimIntro {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw) :
      Step (Term.modElim (Term.modIntro innerTerm)) innerTerm
  /-- Step inside `subsume`'s payload. -/
  | subsumeInner {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context innerType innerRawSource}
      {innerTarget : Term context innerType innerRawTarget} :
      Step innerSource innerTarget →
      Step (Term.subsume innerSource) (Term.subsume innerTarget)
  /-- Step inside a cubical path lambda body. -/
  | pathLamBody {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget} :
      Step bodySource bodyTarget →
      Step (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodySource)
           (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodyTarget)
  /-- Step inside the path position of cubical path application. -/
  | pathAppPath {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {pathRawSource pathRawTarget intervalRaw : RawTerm scope}
      {pathSource :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawSource}
      {pathTarget :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawTarget}
      {intervalTerm : Term context Ty.interval intervalRaw} :
      Step pathSource pathTarget →
      Step (Term.pathApp modeIsUnivalent pathSource intervalTerm)
           (Term.pathApp modeIsUnivalent pathTarget intervalTerm)
  /-- Step inside the interval argument of cubical path application. -/
  | pathAppInterval {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint pathRaw : RawTerm scope}
      {intervalRawSource intervalRawTarget : RawTerm scope}
      {pathTerm :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRaw}
      {intervalSource : Term context Ty.interval intervalRawSource}
      {intervalTarget : Term context Ty.interval intervalRawTarget} :
      Step intervalSource intervalTarget →
      Step (Term.pathApp modeIsUnivalent pathTerm intervalSource)
           (Term.pathApp modeIsUnivalent pathTerm intervalTarget)
  /-- Cubical β-reduction: `(pathLam body) @ interval ⟶ body[interval]`.
  Source type is `carrierType`; target type is
  `carrierType.weaken.subst0 Ty.interval intervalRaw`, so this uses
  the two-Ty Step signature just like `betaApp`. -/
  | betaPathApp {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyRaw : RawTerm (scope + 1)}
      {intervalRaw : RawTerm scope}
      (bodyTerm :
        Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
      (intervalTerm : Term context Ty.interval intervalRaw) :
      Step
        (Term.pathApp modeIsUnivalent
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodyTerm)
          intervalTerm)
        (Term.subst0 bodyTerm intervalTerm)
  /-- Cubical path β at a syntactically constant path body:
  `pathApp (pathLam value.weaken) interval ⟶ value`.

  This is the Step-layer mirror of `RawStep.par.betaPathReflApp` and
  `Step.par.betaPathReflApp`.  When the pathLam's body is literally
  `value.weaken` (mentions no interval binder), pathApp gives back
  the original value irrespective of the interval — the cubical
  analog of "(λ i ⇒ value) @ i ⟶ value" for value independent of i.

  ## Why this is a primitive Step ctor (matches transpReflBeta)

  At the typed Step layer, `Term.subst0 (Term.weaken value) interval`
  is propositionally — but not definitionally — equal to `value`
  (cancellation via `Ty.weaken_subst_singleton` and
  `RawTerm.weaken_subst_singleton`).  Defining `betaPathReflApp` as a
  primitive Step ctor with the cancelled-form target lets `Conv.fromStep`
  consumers and the downstream cd cascade reach `value` directly
  without threading a propositional Eq cast through every site.  This
  matches the existing `transpReflBeta` discipline. -/
  | betaPathReflApp {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (carrierType : Ty level scope)
      (leftEndpoint rightEndpoint : RawTerm scope)
      {valueRaw intervalRaw : RawTerm scope}
      (valueTerm : Term context carrierType valueRaw)
      (intervalTerm : Term context Ty.interval intervalRaw) :
      Step
        (Term.pathApp modeIsUnivalent
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
            (Term.weaken Ty.interval valueTerm))
          intervalTerm)
        valueTerm
  /-- Step inside `glueIntro`'s base value. -/
  | glueIntroBase {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRawSource baseRawTarget partialRaw : RawTerm scope}
      {baseSource : Term context baseType baseRawSource}
      {baseTarget : Term context baseType baseRawTarget}
      {partialValue : Term context baseType partialRaw} :
      Step baseSource baseTarget →
      Step (Term.glueIntro modeIsUnivalent baseType boundaryWitness
              baseSource partialValue)
           (Term.glueIntro modeIsUnivalent baseType boundaryWitness
              baseTarget partialValue)
  /-- Step inside `glueIntro`'s partial value. -/
  | glueIntroPartial {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRaw partialRawSource partialRawTarget : RawTerm scope}
      {baseValue : Term context baseType baseRaw}
      {partialSource : Term context baseType partialRawSource}
      {partialTarget : Term context baseType partialRawTarget} :
      Step partialSource partialTarget →
      Step (Term.glueIntro modeIsUnivalent baseType boundaryWitness
              baseValue partialSource)
           (Term.glueIntro modeIsUnivalent baseType boundaryWitness
              baseValue partialTarget)
  /-- Step inside `glueElim`'s glued value. -/
  | glueElimValue {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {gluedRawSource gluedRawTarget : RawTerm scope}
      {gluedSource :
        Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
      {gluedTarget :
        Term context (Ty.glue baseType boundaryWitness) gluedRawTarget} :
      Step gluedSource gluedTarget →
      Step (Term.glueElim modeIsUnivalent gluedSource)
           (Term.glueElim modeIsUnivalent gluedTarget)
  /-- Cubical Glue β-reduction: `glueElim (glueIntro base partial) ⟶ base`. -/
  | betaGlueElimIntro {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRaw partialRaw : RawTerm scope}
      (baseValue : Term context baseType baseRaw)
      (partialValue : Term context baseType partialRaw) :
      Step
        (Term.glueElim modeIsUnivalent
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue))
        baseValue
  /-- Step inside interval negation. -/
  | intervalOppInner {mode level scope} {context : Ctx mode level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context Ty.interval innerRawSource}
      {innerTarget : Term context Ty.interval innerRawTarget} :
      Step innerSource innerTarget →
      Step (Term.intervalOpp innerSource)
           (Term.intervalOpp innerTarget)
  /-- Step inside the left argument of interval meet. -/
  | intervalMeetLeft {mode level scope} {context : Ctx mode level scope}
      {leftRawSource leftRawTarget rightRaw : RawTerm scope}
      {leftSource : Term context Ty.interval leftRawSource}
      {leftTarget : Term context Ty.interval leftRawTarget}
      {rightValue : Term context Ty.interval rightRaw} :
      Step leftSource leftTarget →
      Step (Term.intervalMeet leftSource rightValue)
           (Term.intervalMeet leftTarget rightValue)
  /-- Step inside the right argument of interval meet. -/
  | intervalMeetRight {mode level scope} {context : Ctx mode level scope}
      {leftRaw rightRawSource rightRawTarget : RawTerm scope}
      {leftValue : Term context Ty.interval leftRaw}
      {rightSource : Term context Ty.interval rightRawSource}
      {rightTarget : Term context Ty.interval rightRawTarget} :
      Step rightSource rightTarget →
      Step (Term.intervalMeet leftValue rightSource)
           (Term.intervalMeet leftValue rightTarget)
  /-- Step inside the left argument of interval join. -/
  | intervalJoinLeft {mode level scope} {context : Ctx mode level scope}
      {leftRawSource leftRawTarget rightRaw : RawTerm scope}
      {leftSource : Term context Ty.interval leftRawSource}
      {leftTarget : Term context Ty.interval leftRawTarget}
      {rightValue : Term context Ty.interval rightRaw} :
      Step leftSource leftTarget →
      Step (Term.intervalJoin leftSource rightValue)
           (Term.intervalJoin leftTarget rightValue)
  /-- Step inside the right argument of interval join. -/
  | intervalJoinRight {mode level scope} {context : Ctx mode level scope}
      {leftRaw rightRawSource rightRawTarget : RawTerm scope}
      {leftValue : Term context Ty.interval leftRaw}
      {rightSource : Term context Ty.interval rightRawSource}
      {rightTarget : Term context Ty.interval rightRawTarget} :
      Step rightSource rightTarget →
      Step (Term.intervalJoin leftValue rightSource)
           (Term.intervalJoin leftValue rightTarget)
  /-- Step inside a single-field record introduction. -/
  | recordIntroField {mode level scope} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRawSource firstRawTarget : RawTerm scope}
      {firstSource : Term context singleFieldType firstRawSource}
      {firstTarget : Term context singleFieldType firstRawTarget} :
      Step firstSource firstTarget →
      Step (Term.recordIntro firstSource)
           (Term.recordIntro firstTarget)
  /-- Step inside a single-field record projection. -/
  | recordProjRecord {mode level scope} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {recordRawSource recordRawTarget : RawTerm scope}
      {recordSource : Term context (Ty.record singleFieldType) recordRawSource}
      {recordTarget : Term context (Ty.record singleFieldType) recordRawTarget} :
      Step recordSource recordTarget →
      Step (Term.recordProj recordSource)
           (Term.recordProj recordTarget)
  /-- Single-field record β-reduction: projecting an introduced field yields
  that field. -/
  | betaRecordProjIntro {mode level scope} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRaw : RawTerm scope}
      (firstField : Term context singleFieldType firstRaw) :
      Step (Term.recordProj (Term.recordIntro firstField)) firstField
  /-- Step inside a refinement introduction value. -/
  | refineIntroValue {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {valueRawSource valueRawTarget proofRaw : RawTerm scope}
      {valueSource : Term context baseType valueRawSource}
      {valueTarget : Term context baseType valueRawTarget}
      {predicateProof : Term context Ty.unit proofRaw} :
      Step valueSource valueTarget →
      Step (Term.refineIntro predicate valueSource predicateProof)
           (Term.refineIntro predicate valueTarget predicateProof)
  /-- Step inside a refinement proof certificate. -/
  | refineIntroProof {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {valueRaw proofRawSource proofRawTarget : RawTerm scope}
      {baseValue : Term context baseType valueRaw}
      {proofSource : Term context Ty.unit proofRawSource}
      {proofTarget : Term context Ty.unit proofRawTarget} :
      Step proofSource proofTarget →
      Step (Term.refineIntro predicate baseValue proofSource)
           (Term.refineIntro predicate baseValue proofTarget)
  /-- Step inside refinement elimination. -/
  | refineElimValue {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {refinedRawSource refinedRawTarget : RawTerm scope}
      {refinedSource : Term context (Ty.refine baseType predicate) refinedRawSource}
      {refinedTarget : Term context (Ty.refine baseType predicate) refinedRawTarget} :
      Step refinedSource refinedTarget →
      Step (Term.refineElim refinedSource)
           (Term.refineElim refinedTarget)
  /-- Refinement β-reduction: eliminating an introduced refinement
  yields the base value. -/
  | betaRefineElimIntro {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      (predicate : RawTerm (scope + 1))
      {valueRaw proofRaw : RawTerm scope}
      (baseValue : Term context baseType valueRaw)
      (predicateProof : Term context Ty.unit proofRaw) :
      Step (Term.refineElim (Term.refineIntro predicate baseValue predicateProof))
           baseValue
  /-- Step inside codata unfold's initial state. -/
  | codataUnfoldState {mode level scope} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {stateRawSource stateRawTarget transitionRaw : RawTerm scope}
      {stateSource : Term context stateType stateRawSource}
      {stateTarget : Term context stateType stateRawTarget}
      {transition : Term context (Ty.arrow stateType outputType) transitionRaw} :
      Step stateSource stateTarget →
      Step (Term.codataUnfold stateSource transition)
           (Term.codataUnfold stateTarget transition)
  /-- Step inside codata unfold's transition. -/
  | codataUnfoldTransition {mode level scope} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {stateRaw transitionRawSource transitionRawTarget : RawTerm scope}
      {initialState : Term context stateType stateRaw}
      {transitionSource :
        Term context (Ty.arrow stateType outputType) transitionRawSource}
      {transitionTarget :
        Term context (Ty.arrow stateType outputType) transitionRawTarget} :
      Step transitionSource transitionTarget →
      Step (Term.codataUnfold initialState transitionSource)
           (Term.codataUnfold initialState transitionTarget)
  /-- Step inside codata destruction. -/
  | codataDestValue {mode level scope} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {codataRawSource codataRawTarget : RawTerm scope}
      {codataSource :
        Term context (Ty.codata stateType outputType) codataRawSource}
      {codataTarget :
        Term context (Ty.codata stateType outputType) codataRawTarget} :
      Step codataSource codataTarget →
      Step (Term.codataDest codataSource)
           (Term.codataDest codataTarget)
  /-- Codata β-reduction: observing an unfold applies the transition to
  the current state. -/
  | betaCodataDestUnfold {mode level scope} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {stateRaw transitionRaw : RawTerm scope}
      (initialState : Term context stateType stateRaw)
      (transition : Term context (Ty.arrow stateType outputType) transitionRaw) :
      Step
        (Term.codataDest (Term.codataUnfold initialState transition))
        (Term.app transition initialState)
  /-- Step inside a session-send channel. -/
  | sessionSendChannel {mode level scope} {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {payloadType : Ty level scope}
      {channelRawSource channelRawTarget payloadRaw : RawTerm scope}
      {channelSource : Term context (Ty.session protocolStep) channelRawSource}
      {channelTarget : Term context (Ty.session protocolStep) channelRawTarget}
      {payload : Term context payloadType payloadRaw} :
      Step channelSource channelTarget →
      Step (Term.sessionSend protocolStep channelSource payload)
           (Term.sessionSend protocolStep channelTarget payload)
  /-- Step inside a session-send payload. -/
  | sessionSendPayload {mode level scope} {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {payloadType : Ty level scope}
      {channelRaw payloadRawSource payloadRawTarget : RawTerm scope}
      {channel : Term context (Ty.session protocolStep) channelRaw}
      {payloadSource : Term context payloadType payloadRawSource}
      {payloadTarget : Term context payloadType payloadRawTarget} :
      Step payloadSource payloadTarget →
      Step (Term.sessionSend protocolStep channel payloadSource)
           (Term.sessionSend protocolStep channel payloadTarget)
  /-- Step inside a session-receive channel. -/
  | sessionRecvChannel {mode level scope} {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {channelRawSource channelRawTarget : RawTerm scope}
      {channelSource : Term context (Ty.session protocolStep) channelRawSource}
      {channelTarget : Term context (Ty.session protocolStep) channelRawTarget} :
      Step channelSource channelTarget →
      Step (Term.sessionRecv channelSource)
           (Term.sessionRecv channelTarget)
  /-- Step inside an effect operation tag. -/
  | effectPerformOperation {mode level scope} {context : Ctx mode level scope}
      {effectTag : RawTerm scope}
      {effectRow : Effects.EffectRow}
      {operationSignature : Effects.OperationSignature (Ty level scope)}
      {canPerformOperation :
        Effects.CanPerform effectRow operationSignature}
      {operationRawSource operationRawTarget argumentsRaw : RawTerm scope}
      {operationSource :
        Term context
          (Ty.effect operationSignature.argumentCarrier effectTag)
          operationRawSource}
      {operationTarget :
        Term context
          (Ty.effect operationSignature.argumentCarrier effectTag)
          operationRawTarget}
      {arguments :
        Term context operationSignature.argumentCarrier argumentsRaw} :
      Step operationSource operationTarget →
      Step (Term.effectPerform effectTag effectRow operationSignature
              canPerformOperation operationSource arguments)
           (Term.effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTarget arguments)
  /-- Step inside effect arguments. -/
  | effectPerformArguments {mode level scope} {context : Ctx mode level scope}
      {effectTag : RawTerm scope}
      {effectRow : Effects.EffectRow}
      {operationSignature : Effects.OperationSignature (Ty level scope)}
      {canPerformOperation :
        Effects.CanPerform effectRow operationSignature}
      {operationRaw argumentsRawSource argumentsRawTarget : RawTerm scope}
      {operationTag :
        Term context
          (Ty.effect operationSignature.argumentCarrier effectTag)
          operationRaw}
      {argumentsSource :
        Term context operationSignature.argumentCarrier argumentsRawSource}
      {argumentsTarget :
        Term context operationSignature.argumentCarrier argumentsRawTarget} :
      Step argumentsSource argumentsTarget →
      Step (Term.effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag argumentsSource)
           (Term.effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag argumentsTarget)
  /-- Step inside cubical transport's type path. -/
  | transpPath {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : RawTerm scope)
      {pathRawSource pathRawTarget sourceRaw : RawTerm scope}
      {typePathSource :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRawSource}
      {typePathTarget :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRawTarget}
      {sourceValue : Term context sourceType sourceRaw} :
      Step typePathSource typePathTarget →
      Step
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValue)
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValue)
  /-- Step inside cubical transport's source value. -/
  | transpSource {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : RawTerm scope)
      {pathRaw sourceRawSource sourceRawTarget : RawTerm scope}
      {typePath :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRaw}
      {sourceValueSource : Term context sourceType sourceRawSource}
      {sourceValueTarget : Term context sourceType sourceRawTarget} :
      Step sourceValueSource sourceValueTarget →
      Step
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePath sourceValueSource)
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePath sourceValueTarget)
  /-- β-reduction for cubical transport along a syntactically constant
  type path: `transp (pathLam typeRaw.weaken) value ⟶ value`.

  This is the Step-layer lift of `ConvCumul.betaTranspConstantTypeCumul`
  (`Reduction/Cumul.lean`).  When the type path is the canonical
  constant path (i.e. its body is a weakened type code, mentioning
  no interval binder), transport across it must be the identity.

  ## D2.5.x roadmap status (Phase G complete; v1.1 deferred items below)

  D2.5.1 (transpBeta — generic transp β at non-constant path):
    SUPERSEDED by D2.5.4.  The original D2.5.1 description ("transp β
    currently only in Step.par") referred to a `Step.par.transpBeta`
    that does not exist in this kernel — `transp` reduction at a
    constant path lands here as `transpReflBeta` (D2.5.4) and at a
    non-constant path requires the binder-aware `transpPi` /
    `transpSigma` cascade (D2.5.5–D2.5.7) which are v1.1 deferred.
    No action required.

  D2.5.2 (hcompBeta — homogeneous composition β):
    SHIPPED via Term.hcompPath rep (Option B path-shaped ctor at
    Term.lean:472).  Raw layer ships RawStep.par.hcompBeta +
    hcompBetaDeep with full cd cascade; typed layer ships
    Step.hcompBeta firing on Term.hcompPath at constant-path
    sides (`pathLam capRaw.weaken`).  Mirrors transpReflBeta
    template — the path body and cap are syntactically tied,
    so one par premise suffices.

  D2.5.3 (pathBeta — `(pathLam body) @ i ⟶ body[i/0]`):
    SHIPPED as `Step.betaPathApp` and `RawStep.par.betaPathApp` /
    `RawStep.par.betaPathAppDeep`.

  D2.5.4 (transpReflBeta — this rule):
    SHIPPED.  See documentation below.

  D2.5.5 (transpPi — binder-aware transp Π β rule):
    Path A foundation SHIPPED: `Foundation/RawPartialRename/
    UnweakenSubstCommute.lean` (commute headline) +
    `UnweakenSubstDispatch.lean` (forward dispatch corollaries).
    Cascade Phases E-K remain pending.  Per J37 2026-05-15 analysis,
    Phase E-K cannot ship via Path 2 split-ctor alone: the "cd erases
    interval mention" case (concretely witnessed by codomain
    `B = app (lam (var 1)) (var 1)`) produces an eta-shape contractum
    `λ. ((cd f).weaken @ var 0)` that par-reduction cannot collapse
    to `cd f` without `Step.eta`.  Required co-prerequisite: ship
    `RawStep.par.eta` + `etaDeep` plus the cd cascade extension
    recognizing eta-shape lambdas (~450 LoC).  See memory
    `feedback_d255_d256_blocker_2026_05_15.md` for the concrete
    eta-trap derivation.

    2026-05-16 update: re-attempt revealed the eta cascade requires
    a TYPED `Step.par.eta` extension too, not just raw.  Reason:
    `RawStep.par.lift_lam` / `lift_lamPi` (typed Term.lam preservation
    in `Term/PreservesTerm/TierZeroAndUnary.lean:362-398`) become
    unprovable in the `Or.inr` (eta) case of the updated `lam_inv`
    — the goal `∃ targetTerm : Term ctx (Ty.arrow ...) targetRaw,
    Step.par (Term.lam body) targetTerm` cannot be discharged because
    typed kernel has no Step.par rule that produces non-lam output
    from `Term.lam` input.  Full D2.5.5 cascade scope therefore
    extends to ~1500+ LoC across raw + typed layers.  See memory
    `feedback_d255_eta_typed_cascade_2026_05_16.md`.  Partial Phase A
    work (eta + etaDeep raw ctors, rename + subst compat arms,
    lam_inv disjunction) preserved in stash
    `wt-eta-cascade-phase-A-partial+compat-arm-WIP-2026-05-16` (and
    a deeper revision in `wt-eta-cascade-with-typed-ParInductive-
    2026-05-16` that adds typed `Step.par.eta` + `Step.par.etaDeep`
    ctors but still blocks at `TierZeroAndUnary`'s `lift_lam` Or.inr
    discharge — needs typed Term.app + Term.weaken inversion ~150 LoC
    + `HeadlineRenameInjInv:787` Or.inr structural rename inversion
    ~250 LoC).

  D2.5.6 (transpSigma — transp through dependent pair):
    BLOCKED on the same `cd_lemma` dispatch ambiguity (Barrier D)
    PLUS three Σ-specific barriers: (A) no `Term.transpFill`
    ctor for inner-snd transp path argument, (B) `Term.transp`'s
    sourceType/targetType are independent schematic data per
    `Term.lean:397-405` docstring, (C) `Term.snd`'s typing pulls
    FST of whole pair, not FST after transport.  Unblocker
    deliverables: Term.transpFill (~800 LoC) OR Term.transp
    redesign (~1500 LoC).  Defer pending kernel milestone.

  D2.5.7 (closed-type transps — list/option/either/record):
    PENDING.  Closed-type case is structurally simpler than
    binder-aware D2.5.5/6 (no binder/scope shift on body),
    but still requires a cd cascade extension per closed type
    introducer.  Note: Lane B's prior transpListBeta Phase A
    work persists as `stash@{0}` (210 LoC across 6 files) —
    review before launching a fresh agent.

  D2.5.8 (betaPathReflApp — `pathApp (pathLam value.weaken) i ⟶ value`):
    LANDED in this batch (Step ctor + raw mirror + cd cascade).
    See `Step.betaPathReflApp` below.

  D2.5.9 (glueAtFace — Glue β at face cofibration):
    BLOCKED ON PREREQUISITE.  Needs a face-system predicate that is
    not in the raw kernel.  Deferred to v1.1 cubical-cofib extension.

  ## Why this is the cubical analog of "transp refl = id"

  In cubical type theory, the constant path `λ i ⇒ A` (built here as
  `Term.pathLam ... typeRaw.weaken` and helper-named
  `constantTypePath`) plays the role of `refl A`.  Transporting along
  this path leaves the value unchanged.  This rule makes that fact
  definitional at the Step layer.

  ## Why both source and target carriers are pinned to `sourceType`

  The Step's source position is a `Term context targetType raw`; for
  the rule to type-check both sides at the same `Ty`, the typed
  source and target carriers must coincide (`sourceType` for both).
  This matches the existing `betaTranspConstantTypeCumul` shape and
  is the strictest form of "transp at constant path is identity"
  that survives intrinsic typing.

  ## Step.par mirror lives in `Reduction/ParRed.lean`

  The matching `Step.par.transpReflBeta` mirror is shipped alongside
  this Step ctor in `Reduction/ParRed.lean`; the cd cascade for it
  is in `Confluence/RawCdLemma.lean`.  Phase G activation completed
  the cascade including the deep variant `transpReflBetaDeep`. -/
  | transpReflBeta {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType : Ty level scope)
      {typeRaw sourceRaw : RawTerm scope}
      (typePath :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            typeRaw typeRaw)
          (RawTerm.pathLam typeRaw.weaken))
      (sourceValue : Term context sourceType sourceRaw) :
      Step
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType sourceType
          typeRaw typeRaw typePath sourceValue)
        sourceValue
  /-- D2.5.2 Phase B: typed cubical-β for homogeneous composition at
  constant-path sides.

  `hcomp [φ → λi. cap] cap ⟶ cap` — homogeneous composition with
  sides equal to the constant path `λi. cap.weaken` at the endpoints
  reduces to the cap.  This is the typed mirror of
  `RawStep.par.hcompBeta` and the typed lift of the kernel-internal
  CCHM cubical rule "hcomp at a trivially filled box equals its cap".

  ## Structural shape

  Fires on `Term.hcompPath` (the path-shaped hcomp ctor in
  `Term.lean:472`) with both `leftEndpoint` and `rightEndpoint`
  pinned to `capRaw` and the sides path's body equal to
  `RawTerm.pathLam capRaw.weaken` (the syntactic constant path at the
  cap).  Reduces to the `capValue` itself.

  ## ConvCumul mirror lives in `Reduction/Cumul/Relation.lean`

  `ConvCumul.betaHcompPathCumul` ships alongside this Step ctor;
  bridge arm in `Reduction/ConvBridge.lean`. -/
  | hcompBeta {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {capRaw : RawTerm scope}
      (capValue : Term context carrierType capRaw)
      (sidesPath :
        Term context
          (Ty.path carrierType capRaw capRaw)
          (RawTerm.pathLam capRaw.weaken)) :
      Step
        (Term.hcompPath modeIsUnivalent
          (leftEndpoint := capRaw) (rightEndpoint := capRaw)
          sidesPath capValue)
        capValue
  /-- Step inside homogeneous composition's side system. -/
  | hcompSides {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {sidesRawSource sidesRawTarget capRaw : RawTerm scope}
      {sidesSource : Term context carrierType sidesRawSource}
      {sidesTarget : Term context carrierType sidesRawTarget}
      {capValue : Term context carrierType capRaw} :
      Step sidesSource sidesTarget →
      Step (Term.hcomp modeIsUnivalent sidesSource capValue)
           (Term.hcomp modeIsUnivalent sidesTarget capValue)
  /-- Step inside homogeneous composition's cap. -/
  | hcompCap {mode level scope} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {sidesRaw capRawSource capRawTarget : RawTerm scope}
      {sidesValue : Term context carrierType sidesRaw}
      {capSource : Term context carrierType capRawSource}
      {capTarget : Term context carrierType capRawTarget} :
      Step capSource capTarget →
      Step (Term.hcomp modeIsUnivalent sidesValue capSource)
           (Term.hcomp modeIsUnivalent sidesValue capTarget)
  /-- Step inside the forward map of a heterogeneous equivalence. -/
  | equivIntroHetForward {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardRawSource forwardRawTarget backwardRaw : RawTerm scope}
      {forwardSource :
        Term context (Ty.arrow carrierA carrierB) forwardRawSource}
      {forwardTarget :
        Term context (Ty.arrow carrierA carrierB) forwardRawTarget}
      {backwardTerm : Term context (Ty.arrow carrierB carrierA) backwardRaw}
      {leftInvSourceRaw rightInvSourceRaw
       leftInvTargetRaw rightInvTargetRaw : RawTerm scope}
      {leftInvSource :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRaw)
          leftInvSourceRaw}
      {rightInvSource :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRawSource backwardRaw)
          rightInvSourceRaw}
      {leftInvTarget :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRaw)
          leftInvTargetRaw}
      {rightInvTarget :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRaw)
          rightInvTargetRaw} :
      Step forwardSource forwardTarget →
      Step (Term.equivIntroHet forwardSource backwardTerm leftInvSource rightInvSource)
           (Term.equivIntroHet forwardTarget backwardTerm leftInvTarget rightInvTarget)
  /-- Step inside the backward map of a heterogeneous equivalence. -/
  | equivIntroHetBackward {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardRaw backwardRawSource backwardRawTarget : RawTerm scope}
      {forwardTerm : Term context (Ty.arrow carrierA carrierB) forwardRaw}
      {backwardSource :
        Term context (Ty.arrow carrierB carrierA) backwardRawSource}
      {backwardTarget :
        Term context (Ty.arrow carrierB carrierA) backwardRawTarget}
      {leftInvSourceRaw rightInvSourceRaw
       leftInvTargetRaw rightInvTargetRaw : RawTerm scope}
      {leftInvSource :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRaw backwardRawSource)
          leftInvSourceRaw}
      {rightInvSource :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRaw backwardRawSource)
          rightInvSourceRaw}
      {leftInvTarget :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRaw backwardRawTarget)
          leftInvTargetRaw}
      {rightInvTarget :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRaw backwardRawTarget)
          rightInvTargetRaw} :
      Step backwardSource backwardTarget →
      Step (Term.equivIntroHet forwardTerm backwardSource leftInvSource rightInvSource)
           (Term.equivIntroHet forwardTerm backwardTarget leftInvTarget rightInvTarget)
  /-- Step inside the equivalence position of an equivalence application. -/
  | equivAppEquiv {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivRawSource equivRawTarget argumentRaw : RawTerm scope}
      {equivSource : Term context (Ty.equiv carrierA carrierB) equivRawSource}
      {equivTarget : Term context (Ty.equiv carrierA carrierB) equivRawTarget}
      {argumentTerm : Term context carrierA argumentRaw} :
      Step equivSource equivTarget →
      Step (Term.equivApp equivSource argumentTerm)
           (Term.equivApp equivTarget argumentTerm)
  /-- Step inside the argument position of an equivalence application. -/
  | equivAppArgument {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivRaw argumentRawSource argumentRawTarget : RawTerm scope}
      (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
      {argumentSource : Term context carrierA argumentRawSource}
      {argumentTarget : Term context carrierA argumentRawTarget} :
      Step argumentSource argumentTarget →
      Step (Term.equivApp equivTerm argumentSource)
           (Term.equivApp equivTerm argumentTarget)
  /-- Step inside the equivalence witness carried by heterogeneous ua. -/
  | uaIntroHetWitness {mode level scope}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRawSource forwardRawTarget
       backwardRawSource backwardRawTarget : RawTerm scope}
      {equivSource :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardRawSource backwardRawSource)}
      {equivTarget :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardRawTarget backwardRawTarget)} :
      Step equivSource equivTarget →
      Step
        (Term.uaIntroHet innerLevel innerLevelLt
          carrierARaw carrierBRaw equivSource)
        (Term.uaIntroHet innerLevel innerLevelLt
          carrierARaw carrierBRaw equivTarget)
  /-- Step inside the path-at-the-universe proof carried by univalence-β
  extractor (`Term.uaToEquiv`).  Phase D3.6-P3 — single-subterm
  cong rule mirroring `uaIntroHetWitness`. -/
  | uaToEquivProof {mode level scope}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (leftTy rightTy : Ty level scope)
      (leftTyRaw rightTyRaw : RawTerm scope)
      {proofRawSource proofRawTarget : RawTerm scope}
      {proofSource :
        Term context
          (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
          proofRawSource}
      {proofTarget :
        Term context
          (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
          proofRawTarget} :
      Step proofSource proofTarget →
      Step
        (Term.uaToEquiv innerLevel innerLevelLt
          leftTy rightTy leftTyRaw rightTyRaw proofSource)
        (Term.uaToEquiv innerLevel innerLevelLt
          leftTy rightTy leftTyRaw rightTyRaw proofTarget)
  /-- Step inside the equivalence position of a univalence-β
  application (`Term.equivApply`).  Phase D3.6-P4 — binary cong rule
  mirroring `Step.equivAppEquiv` for the new `equivApply` ctor. -/
  | equivApplyEquiv {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivRawSource equivRawTarget argumentRaw : RawTerm scope}
      {equivSource : Term context (Ty.equiv carrierA carrierB) equivRawSource}
      {equivTarget : Term context (Ty.equiv carrierA carrierB) equivRawTarget}
      {argumentTerm : Term context carrierA argumentRaw} :
      Step equivSource equivTarget →
      Step (Term.equivApply equivSource argumentTerm)
           (Term.equivApply equivTarget argumentTerm)
  /-- Step inside the argument position of a univalence-β application
  (`Term.equivApply`).  Phase D3.6-P4 — binary cong rule mirroring
  `Step.equivAppArgument` for the new `equivApply` ctor. -/
  | equivApplyArgument {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivRaw argumentRawSource argumentRawTarget : RawTerm scope}
      (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
      {argumentSource : Term context carrierA argumentRawSource}
      {argumentTarget : Term context carrierA argumentRawTarget} :
      Step argumentSource argumentTarget →
      Step (Term.equivApply equivTerm argumentSource)
           (Term.equivApply equivTerm argumentTarget)
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

end LeanFX2
