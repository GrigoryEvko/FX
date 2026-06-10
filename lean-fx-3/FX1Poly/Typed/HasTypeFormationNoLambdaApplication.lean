import FX1Poly.Typed.HasTypeDescPiConsistency
import FX1Poly.Typed.HasTypeDescPiRootGeneric

/-! # FX1Poly/Typed/HasTypeFormationNoLambdaApplication
    - lambda/application exclusion for the description formation engine

The description formation engine `HasTypeDesc` is a formation-only judgment: it types variables, universe
codes, and Pi/Sigma type-code formers, but not lambda or application subjects.  The grown engine
`HasTypeDescPi` is the separate judgment that adds `lamCell` and `appCell`.

This file records that separation as kernel theorems.  It is the precise counterpart of the informal
"formation-only" scope note: any `HasTypeDesc` derivation has subject root
`gen_var` / `gen_universeCode` / `gen_piTyCode` / `gen_sigmaTyCode`, hence never `gen_lam` or `gen_app`.

## Zero-axiom verification

`HasTypeDesc` uses the already-gated root characterization from `HasTypeDescPiConsistency`.  Cell-level
exclusions close because `lamCell` and `appCell` have definitional root generators `gen_lam` and `gen_app`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
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
  rcases typed.subjectRootGeneratorGeneric with rootIsVar | rootIsUniverse | ⟨_rule, isFormer⟩
  · rw [rootIsVar] at rootIsLam
    cases rootIsLam
  · rw [rootIsUniverse] at rootIsLam
    cases rootIsLam
  · -- the root carries a formation rule, but `gen_lam` has `typingRuleDescOf = none`
    rw [rootIsLam] at isFormer
    cases isFormer

/-- A description-formation subject never has application root.  Application subjects live only in the grown
`HasTypeDescPi` judgment. -/
theorem HasTypeDesc.subjectRootGenerator_ne_app {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    subject.rootGenerator ≠ Generator.gen_app := by
  intro rootIsApp
  rcases typed.subjectRootGeneratorGeneric with rootIsVar | rootIsUniverse | ⟨_rule, isFormer⟩
  · rw [rootIsVar] at rootIsApp
    cases rootIsApp
  · rw [rootIsUniverse] at rootIsApp
    cases rootIsApp
  · -- the root carries a formation rule, but `gen_app` has `typingRuleDescOf = none`
    rw [rootIsApp] at isFormer
    cases isFormer

/-- The description formation engine cannot type a lambda subject. -/
theorem HasTypeDesc.subjectCannotBeLambda {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (lamCell domainAnn body) classifier) :
    False :=
  typed.subjectRootGenerator_ne_lam rfl

/-- The description formation engine cannot type an application subject. -/
theorem HasTypeDesc.subjectCannotBeApplication {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (appCell functionTerm argument) classifier) :
    False :=
  typed.subjectRootGenerator_ne_app rfl

end FX1Poly.Typed
