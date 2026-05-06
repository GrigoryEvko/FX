import LeanFX2.Term

/-! # Algo/Synth — atomic synthesis for individual constructors

Per-ctor synth helpers wrap each typed-Term constructor with a
named, signature-explicit form.  Each helper is a 1-line wrapper
around the corresponding Term ctor; they exist as a reference
card of typing rules and provide consistent calling conventions
for the future `Algo/Infer` algorithm.

In lean-fx-2's raw-aware Term encoding, "synthesis" IS
"construction" — each Term ctor produces a typed Term whose raw
form appears as the third type index.  These helpers make the
typing rules visually explicit at the call site.

## What's NOT here

* `Term.infer` (in `Algo/Infer`) — given a raw term + context,
  reconstructs the typed Term by recursively invoking these
  synth helpers.  Currently a stub.
* `Term.check` (in `Algo/Check`) — bidirectional check.

## Zero-axiom

All helpers compose via `rfl`-style construction and inherit the
zero-axiom guarantee from the underlying Term ctors.
-/

namespace LeanFX2.Algo

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Variable + canonical leaf values -/

/-- Variable lookup synthesis: a `Fin scope` index + Ctx gives a
typed `Term.var`. -/
@[reducible] def Term.synthVar (index : Fin scope) :
    Term context (LeanFX2.varType context index) (RawTerm.var index) :=
  Term.var index

/-- Unit value synthesis. -/
@[reducible] def Term.synthUnit :
    Term context Ty.unit (RawTerm.unit (scope := scope)) :=
  Term.unit

/-- Boolean `true` synthesis. -/
@[reducible] def Term.synthBoolTrue :
    Term context Ty.bool (RawTerm.boolTrue (scope := scope)) :=
  Term.boolTrue

/-- Boolean `false` synthesis. -/
@[reducible] def Term.synthBoolFalse :
    Term context Ty.bool (RawTerm.boolFalse (scope := scope)) :=
  Term.boolFalse

/-- Natural zero synthesis. -/
@[reducible] def Term.synthNatZero :
    Term context Ty.nat (RawTerm.natZero (scope := scope)) :=
  Term.natZero

/-- List nil synthesis: gives a `nil` at any element type. -/
@[reducible] def Term.synthListNil {elementType : Ty level scope} :
    Term context (Ty.listType elementType)
      (RawTerm.listNil (scope := scope)) :=
  Term.listNil

/-- Option none synthesis. -/
@[reducible] def Term.synthOptionNone {elementType : Ty level scope} :
    Term context (Ty.optionType elementType)
      (RawTerm.optionNone (scope := scope)) :=
  Term.optionNone

/-! ## Eliminator + introduction synthesis (binary ctors) -/

/-- App synthesis (non-dep arrow): `fn : A → B`, `arg : A`,
result `: B`. -/
@[reducible] def Term.synthApp
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term context codomainType (RawTerm.app functionRaw argumentRaw) :=
  Term.app functionTerm argumentTerm

/-- Π-app synthesis: dependent application substitutes the
argument's raw into the codomain type. -/
@[reducible] def Term.synthAppPi
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term context (codomainType.subst0 domainType argumentRaw)
      (RawTerm.app functionRaw argumentRaw) :=
  Term.appPi functionTerm argumentTerm

/-- Σ first projection synthesis. -/
@[reducible] def Term.synthFst
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term context firstType (RawTerm.fst pairRaw) :=
  Term.fst pairTerm

/-- Successor synthesis. -/
@[reducible] def Term.synthNatSucc
    {predecessorRaw : RawTerm scope}
    (predecessorTerm : Term context Ty.nat predecessorRaw) :
    Term context Ty.nat (RawTerm.natSucc predecessorRaw) :=
  Term.natSucc predecessorTerm

/-- List cons synthesis. -/
@[reducible] def Term.synthListCons
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw) :
    Term context (Ty.listType elementType)
      (RawTerm.listCons headRaw tailRaw) :=
  Term.listCons headTerm tailTerm

/-- Option some synthesis. -/
@[reducible] def Term.synthOptionSome
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw) :
    Term context (Ty.optionType elementType)
      (RawTerm.optionSome valueRaw) :=
  Term.optionSome valueTerm

/-- Either inl synthesis. -/
@[reducible] def Term.synthEitherInl
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw) :
    Term context (Ty.eitherType leftType rightType)
      (RawTerm.eitherInl valueRaw) :=
  Term.eitherInl valueTerm

/-- Either inr synthesis. -/
@[reducible] def Term.synthEitherInr
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw) :
    Term context (Ty.eitherType leftType rightType)
      (RawTerm.eitherInr valueRaw) :=
  Term.eitherInr valueTerm

/-! ## Eliminator synthesis (n-ary)

Eliminator helpers package the scrutinee + each branch.  The
motive type is propagated explicitly so the result type is
visible at the call site. -/

/-- Boolean elim synthesis. -/
@[reducible] def Term.synthBoolElim
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term context (motiveType.subst0 Ty.bool scrutineeRaw)
      (RawTerm.boolElim scrutineeRaw thenRaw elseRaw) :=
  Term.boolElim scrutinee thenBranch elseBranch

/-- Nat elim synthesis (case analysis on `nat`). -/
@[reducible] def Term.synthNatElim
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Term context motiveType
      (RawTerm.natElim scrutineeRaw zeroRaw succRaw) :=
  Term.natElim scrutinee zeroBranch succBranch

/-- Nat recursion synthesis (recursive case analysis). -/
@[reducible] def Term.synthNatRec
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
                    succRaw) :
    Term context motiveType
      (RawTerm.natRec scrutineeRaw zeroRaw succRaw) :=
  Term.natRec scrutinee zeroBranch succBranch

/-- List elim synthesis. -/
@[reducible] def Term.synthListElim
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context
                    (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType))
                    consRaw) :
    Term context motiveType
      (RawTerm.listElim scrutineeRaw nilRaw consRaw) :=
  Term.listElim scrutinee nilBranch consBranch

/-- Option match synthesis. -/
@[reducible] def Term.synthOptionMatch
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    Term context motiveType
      (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) :=
  Term.optionMatch scrutinee noneBranch someBranch

/-- Either match synthesis. -/
@[reducible] def Term.synthEitherMatch
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    Term context motiveType
      (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) :=
  Term.eitherMatch scrutinee leftBranch rightBranch

/-- Identity J synthesis (non-dep motive). -/
@[reducible] def Term.synthIdJ
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    Term context motiveType (RawTerm.idJ baseRaw witnessRaw) :=
  Term.idJ baseCase witness

/-! ## Binders + Σ pair + identity refl synthesis

Round out the Synth API so every Term constructor has a synth
helper.  These wrap the constructor with named arguments to make
the typing rule visible at the call site. -/

/-- Lambda synthesis (non-dep arrow). -/
@[reducible] def Term.synthLam
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw) :
    Term context (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw) :=
  Term.lam body

/-- Π lambda synthesis (dependent). -/
@[reducible] def Term.synthLamPi
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType bodyRaw) :
    Term context (Ty.piTy domainType codomainType) (RawTerm.lam bodyRaw) :=
  Term.lamPi body

/-- Σ pair synthesis. -/
@[reducible] def Term.synthPair
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Term context (Ty.sigmaTy firstType secondType)
                 (RawTerm.pair firstRaw secondRaw) :=
  Term.pair firstValue secondValue

/-- Σ second projection synthesis. -/
@[reducible] def Term.synthSnd
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term context (secondType.subst0 firstType (RawTerm.fst pairRaw))
                 (RawTerm.snd pairRaw) :=
  Term.snd pairTerm

/-- Identity refl synthesis. -/
@[reducible] def Term.synthRefl
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Term context (Ty.id carrier rawWitness rawWitness)
                 (RawTerm.refl rawWitness) :=
  Term.refl carrier rawWitness

/-- Modal intro synthesis (Layer 1 raw scaffolding — preserves inner type). -/
@[reducible] def Term.synthModIntro
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term context innerType (RawTerm.modIntro innerRaw) :=
  Term.modIntro innerTerm

/-- Modal elim synthesis (Layer 1 raw scaffolding). -/
@[reducible] def Term.synthModElim
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term context innerType (RawTerm.modElim innerRaw) :=
  Term.modElim innerTerm

/-- Subsume synthesis (Layer 1 raw scaffolding). -/
@[reducible] def Term.synthSubsume
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term context innerType (RawTerm.subsume innerRaw) :=
  Term.subsume innerTerm

end LeanFX2.Algo
