import FX1Poly.Typed.HasTypeDescPiConsistency

/-! # FX1Poly/Typed/HasTypeFormationNoLambdaApplication
    - lambda/application exclusion for the native and description formation engines

The native pi/sigma-formation `HasType` core and the equivalent description formation engine
`HasTypeDesc` are formation-only judgments: they type variables, universe codes, and Pi/Sigma type-code
formers, but not lambda or application subjects.  The grown engine `HasTypeDescPi` is the separate judgment
that adds `lamCell` and `appCell`.

This file records that separation as kernel theorems.  It is the precise counterpart of the informal
"formation-only" scope note: any `HasType` or `HasTypeDesc` derivation has subject root
`gen_var` / `gen_universeCode` / `gen_piTyCode` / `gen_sigmaTyCode`, hence never `gen_lam` or `gen_app`.

## Zero-axiom verification

`HasTypeDesc` uses the already-gated root characterization from `HasTypeDescPiConsistency`; `HasType`
transports through `HasType.toHasTypeDesc`.  Cell-level exclusions close because `lamCell` and `appCell`
have definitional root generators `gen_lam` and `gen_app`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- A description-formation subject never has lambda root.  Lambda subjects live only in the grown
`HasTypeDescPi` judgment. -/
theorem HasTypeDesc.subjectRootGenerator_ne_lam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    subject.rootGenerator ≠ Generator.gen_lam := by
  intro rootIsLam
  rcases typed.subjectRootGenerator with rootIsVar | rootIsUniverse | rootIsPi | rootIsSigma
  · rw [rootIsVar] at rootIsLam
    cases rootIsLam
  · rw [rootIsUniverse] at rootIsLam
    cases rootIsLam
  · rw [rootIsPi] at rootIsLam
    cases rootIsLam
  · rw [rootIsSigma] at rootIsLam
    cases rootIsLam

/-- A description-formation subject never has application root.  Application subjects live only in the grown
`HasTypeDescPi` judgment. -/
theorem HasTypeDesc.subjectRootGenerator_ne_app {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    subject.rootGenerator ≠ Generator.gen_app := by
  intro rootIsApp
  rcases typed.subjectRootGenerator with rootIsVar | rootIsUniverse | rootIsPi | rootIsSigma
  · rw [rootIsVar] at rootIsApp
    cases rootIsApp
  · rw [rootIsUniverse] at rootIsApp
    cases rootIsApp
  · rw [rootIsPi] at rootIsApp
    cases rootIsApp
  · rw [rootIsSigma] at rootIsApp
    cases rootIsApp

/-- The description formation engine cannot type a lambda subject. -/
theorem HasTypeDesc.subjectCannotBeLambda {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (lamCell body) classifier) :
    False :=
  typed.subjectRootGenerator_ne_lam rfl

/-- The description formation engine cannot type an application subject. -/
theorem HasTypeDesc.subjectCannotBeApplication {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (appCell functionTerm argument) classifier) :
    False :=
  typed.subjectRootGenerator_ne_app rfl

/-- A native pi/sigma-formation `HasType` subject never has lambda root. -/
theorem HasType.subjectRootGenerator_ne_lam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    subject.rootGenerator ≠ Generator.gen_lam :=
  (HasType.toHasTypeDesc typed).subjectRootGenerator_ne_lam

/-- A native pi/sigma-formation `HasType` subject never has application root. -/
theorem HasType.subjectRootGenerator_ne_app {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    subject.rootGenerator ≠ Generator.gen_app :=
  (HasType.toHasTypeDesc typed).subjectRootGenerator_ne_app

/-- The native pi/sigma-formation `HasType` core cannot type a lambda subject. -/
theorem HasType.subjectCannotBeLambda {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed : HasType profile context (lamCell body) classifier) :
    False :=
  typed.subjectRootGenerator_ne_lam rfl

/-- The native pi/sigma-formation `HasType` core cannot type an application subject. -/
theorem HasType.subjectCannotBeApplication {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument classifier : RawTerm scope}
    (typed : HasType profile context (appCell functionTerm argument) classifier) :
    False :=
  typed.subjectRootGenerator_ne_app rfl

end FX1Poly.Typed
