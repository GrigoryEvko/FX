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

end LeanFX2.Algo
