import LeanFX.Syntax.Ty

namespace LeanFX.Syntax

/-! ## Tarski codes

`Code level scope` is the axiom-free substrate for a small internal
universe.  It mirrors `Ty level scope` constructor-for-constructor but
stays syntactic: interpretation into `Ty` lands in the next task. -/

/-- Tarski code syntax for the small FX type universe. -/
inductive Code : Nat → Nat → Type
  /-- Code for the unit type. -/
  | codeUnit : {level scope : Nat} → Code level scope
  /-- Code for the boolean type. -/
  | codeBool : {level scope : Nat} → Code level scope
  /-- Code for the natural-number type. -/
  | codeNat : {level scope : Nat} → Code level scope
  /-- Code for a non-dependent arrow type. -/
  | codeArrow : {level scope : Nat} →
      (domain : Code level scope) →
      (codomain : Code level scope) →
      Code level scope
  /-- Code for a dependent function type. -/
  | codePiTy : {level scope : Nat} →
      (domain : Code level scope) →
      (codomain : Code level (scope + 1)) →
      Code level scope
  /-- Code for a type variable. -/
  | codeTyVar : {level scope : Nat} → (position : Fin scope) → Code level scope
  /-- Code for a dependent pair type. -/
  | codeSigma : {level scope : Nat} →
      (firstType : Code level scope) →
      (secondType : Code level (scope + 1)) →
      Code level scope
  /-- Code for a universe type. -/
  | codeUniverse : {level scope : Nat} →
      (universeLevel : Nat) →
      (levelEq : level = universeLevel + 1) →
      Code level scope
  /-- Code for lists. -/
  | codeList : {level scope : Nat} →
      (elementType : Code level scope) →
      Code level scope
  /-- Code for optional values. -/
  | codeOption : {level scope : Nat} →
      (elementType : Code level scope) →
      Code level scope
  /-- Code for tagged sums. -/
  | codeEither : {level scope : Nat} →
      (leftType : Code level scope) →
      (rightType : Code level scope) →
      Code level scope
  /-- Code for identity types with open raw endpoints. -/
  | codeId : {level scope : Nat} →
      (carrier : Code level scope) →
      (leftEndpoint : RawTerm scope) →
      (rightEndpoint : RawTerm scope) →
      Code level scope

deriving instance DecidableEq for Code

namespace SmokeTestCode

/-- Closed code for unit. -/
example : Code 0 0 := Code.codeUnit

/-- Closed code for bool. -/
example : Code 0 0 := Code.codeBool

/-- Closed code for nat. -/
example : Code 0 0 := Code.codeNat

/-- Closed code for a simple arrow. -/
example : Code 0 0 :=
  Code.codeArrow Code.codeUnit Code.codeBool

/-- Code for a dependent function whose codomain references its binder. -/
example : Code 0 0 :=
  Code.codePiTy Code.codeUnit
    (Code.codeTyVar ⟨0, Nat.zero_lt_succ 0⟩)

/-- Code for a type variable at scope one. -/
example : Code 0 1 :=
  Code.codeTyVar ⟨0, Nat.zero_lt_succ 0⟩

/-- Code for a dependent pair whose second component references its binder. -/
example : Code 0 0 :=
  Code.codeSigma Code.codeUnit
    (Code.codeTyVar ⟨0, Nat.zero_lt_succ 0⟩)

/-- Code for `Type 0 : Type 1`. -/
example : Code 1 0 :=
  Code.codeUniverse 0 rfl

/-- Code for a list. -/
example : Code 0 0 :=
  Code.codeList Code.codeNat

/-- Code for an option. -/
example : Code 0 0 :=
  Code.codeOption Code.codeBool

/-- Code for a tagged sum. -/
example : Code 0 0 :=
  Code.codeEither Code.codeBool Code.codeNat

/-- Code for a closed identity type. -/
example : Code 0 0 :=
  Code.codeId Code.codeBool RawTerm.boolTrue RawTerm.boolTrue

/-- Code for an open identity type under one raw binder. -/
example : Code 0 1 :=
  Code.codeId Code.codeUnit
    (RawTerm.var ⟨0, Nat.zero_lt_succ 0⟩)
    (RawTerm.var ⟨0, Nat.zero_lt_succ 0⟩)

end SmokeTestCode

end LeanFX.Syntax
