import LeanFX.Syntax.Identity

namespace LeanFX.Syntax
open LeanFX.Mode

/-! ## Dependent J motive shape.

This module records the dependent-J signature as checked Lean data.
It intentionally does not add a `Term` constructor or a reduction rule:
task v2.7 uses this shape when the kernel is ready to extend intrinsic
identity elimination.
-/

/-- A dependent-J motive over raw identity endpoints and an identity
witness between them. -/
abbrev DependentJMotive {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (carrier : Ty level scope) : Type :=
  (leftEndpoint rightEndpoint : RawTerm scope) →
    Term context (Ty.id carrier leftEndpoint rightEndpoint) →
      Ty level scope

namespace DependentJ

/-- Type expected for the reflexive base case of dependent J. -/
def baseCaseType {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    (motive : DependentJMotive context carrier)
    (endpoint : RawTerm scope) :
    Ty level scope :=
  motive endpoint endpoint (Term.refl (carrier := carrier) endpoint)

/-- Result type of dependent J at a specific witness. -/
def resultType {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    (motive : DependentJMotive context carrier)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)) :
    Ty level scope :=
  motive leftEndpoint rightEndpoint witness

/-- Fully typed input package for a future intrinsic dependent-J
constructor. -/
structure Input {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) where
  motive : DependentJMotive context carrier
  baseCase : Term context (baseCaseType motive leftEndpoint)
  witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)

/-- The target type selected by a dependent-J input package. -/
def Input.resultType {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    (input : Input context carrier leftEndpoint rightEndpoint) :
    Ty level scope :=
  DependentJ.resultType input.motive input.witness

/-- Reflexive dependent-J inputs have the base-case result type. -/
example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    (motive : DependentJMotive context carrier)
    (endpoint : RawTerm scope)
    (baseCase : Term context (baseCaseType motive endpoint)) :
    (DependentJ.Input.resultType
      {
        motive := motive,
        baseCase := baseCase,
        witness := Term.refl (carrier := carrier) endpoint
      } :
      Ty level scope) =
        baseCaseType motive endpoint := rfl

end DependentJ

end LeanFX.Syntax
