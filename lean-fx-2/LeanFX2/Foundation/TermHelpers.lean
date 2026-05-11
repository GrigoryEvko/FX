import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Ty

/-! # Foundation/TermHelpers — proof-obligation types for HoTT/HOTT
ctors at Layer 0.

Three `@[reducible]` defs (plus their codomain helpers) that name the
typed-proof-witness signatures for `equivIntroHet` (HoTT heterogeneous
equivalence) and `oeqFunext` (observational equality funext).

## Why at Layer 0 (Foundation) rather than Layer 1 (Term.lean)

These helpers only depend on `Ty`, `Ty.weaken`, `Ty.id`, `Ty.oeq`,
`Ty.arrow`, `Ty.piTy`, `RawTerm`, `RawTerm.app`, `RawTerm.weaken`,
`RawTerm.var` — all Foundation primitives.  Living at Layer 0 lets BOTH
`LeanFX2.Term` (Layer 1) AND `LeanFX2.Foundation.Polygraph.PolyTerm`
(Layer 0) reference them in their `equivIntroHet` / `oeqFunext` ctor
signatures.  Without this migration, PolyTerm could only ship those
ctors with OPAQUE motive types — losing the strict-bijection guarantee
that Term ⇌ PolyTerm is lossless.

Migrated from `LeanFX2/Term.lean` lines 91-151 (preserved verbatim,
namespaced identically). -/

namespace LeanFX2

/-- Codomain of the left-inverse law for `equivIntroHet`.

Under one fresh `carrierA` binder, this is the identity type
`backward (forward x) = x`. -/
@[reducible] def equivIntroHetLeftInverseCodomain {level scope : Nat}
    (carrierA : Ty level scope)
    (forwardRaw backwardRaw : RawTerm scope) : Ty level (scope + 1) :=
  Ty.id carrierA.weaken
    (RawTerm.app backwardRaw.weaken
      (RawTerm.app forwardRaw.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
    (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)

/-- Proof-function type for the left-inverse law of `equivIntroHet`. -/
@[reducible] def equivIntroHetLeftInverseType {level scope : Nat}
    (carrierA : Ty level scope)
    (forwardRaw backwardRaw : RawTerm scope) : Ty level scope :=
  Ty.piTy carrierA
    (equivIntroHetLeftInverseCodomain carrierA forwardRaw backwardRaw)

/-- Codomain of the right-inverse law for `equivIntroHet`. -/
@[reducible] def equivIntroHetRightInverseCodomain {level scope : Nat}
    (carrierB : Ty level scope)
    (forwardRaw backwardRaw : RawTerm scope) : Ty level (scope + 1) :=
  Ty.id carrierB.weaken
    (RawTerm.app forwardRaw.weaken
      (RawTerm.app backwardRaw.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
    (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)

/-- Proof-function type for the right-inverse law of `equivIntroHet`. -/
@[reducible] def equivIntroHetRightInverseType {level scope : Nat}
    (carrierB : Ty level scope)
    (forwardRaw backwardRaw : RawTerm scope) : Ty level scope :=
  Ty.piTy carrierB
    (equivIntroHetRightInverseCodomain carrierB forwardRaw backwardRaw)

/-- Codomain of the pointwise equality law for `oeqFunext`. -/
@[reducible] def oeqFunextPointwiseCodomain {level scope : Nat}
    (codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope) : Ty level (scope + 1) :=
  Ty.oeq codomainType.weaken
    (RawTerm.app leftFunctionRaw.weaken
      (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
    (RawTerm.app rightFunctionRaw.weaken
      (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))

/-- Proof-function type for `oeqFunext`: pointwise equality over the domain. -/
@[reducible] def oeqFunextPointwiseType {level scope : Nat}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope) : Ty level scope :=
  Ty.piTy domainType
    (oeqFunextPointwiseCodomain codomainType leftFunctionRaw rightFunctionRaw)

end LeanFX2
