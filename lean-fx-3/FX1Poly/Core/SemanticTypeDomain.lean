import FX1Poly.Core.ReducibilityCandidate

/-! # Foundation/PolyCell/Core/SemanticTypeDomain
    — the kind-indexed semantic domain for the reducibility logical relation

The Girard-Tait reducibility interpretation assigns to every type-code a **reducibility candidate**
(a predicate on terms).  For a FIRST-ORDER system (type variables `A : Type` only) a candidate is
enough.  But `HasTypeDescPi` is genuinely higher-order: `piIntro` types `lamCell body :
piTyCodeCell A codomainCode` with `codomainCode` itself living in a universe, so one can form a
**type family** `F : A → Type` and then `piElim` makes `appCell F arg` a well-typed *type*.  A plain
candidate cannot interpret a type-FAMILY variable `F`: its interpretation must be a *function* from
the argument to the result candidate.

This file gives the domain that carries exactly that, **kind-indexed**:

  `SemanticType scope .star                = RawTerm scope → Prop`   (a candidate — a proper type)
  `SemanticType scope (.arrow k1 k2)       = SemanticType scope k1 → SemanticType scope k2`  (an operator)

`SemanticType` is a **recursion on the kind** (a `def`, not an inductive over itself), which is why
it sidesteps the reflexive-domain positivity trap that kills `inductive D | … (D → D)`: the operator
arrow is a plain function space at a *structurally smaller* kind.  Predicativity of FX makes the kind
hierarchy well-founded.

Two foundational operations land alongside the domain:

* `SemanticType.IsReducible` — the candidate-hood predicate lifted to every kind (a candidate at
  `.star`; an operator that maps reducible inputs to reducible outputs at `.arrow`).  This is the
  Girard saturation condition, kind-generalised.
* `SemanticType.witness` / `witness_isReducible` — a reducible inhabitant at EVERY kind (the strongly
  normalizing candidate at `.star`; the constant operator returning the codomain witness at `.arrow`),
  so a semantic environment can always be populated — the higher-kinded CR1 inhabitedness witness.

## Zero-axiom verification

Structural recursion on the two-constructor `SemanticKind` (full enumeration, no wildcards), closing
the `.star` cases by the shipped `isStronglyNormalizing_isReducibilityCandidate`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- Simple kinds for the type-level fragment: a proper type (`star`), or an operator from one kind to
another (`arrow`).  Type families `A → Type` inhabit `arrow star star`; higher operators nest further.
A two-constructor inductive — the structural measure the semantic domain recurses on. -/
inductive SemanticKind where
  | star : SemanticKind
  | arrow (domainKind codomainKind : SemanticKind) : SemanticKind

/-- The kind-indexed semantic domain.  At `.star` a type interprets to a **reducibility candidate**
(a predicate on terms of the same scope); at `.arrow` a type operator interprets to a function from
the domain interpretation to the codomain interpretation.  Defined by recursion on the kind, so no
positivity obligation (the operator arrow is a plain function space at a smaller kind). -/
def SemanticType (scope : Nat) : SemanticKind → Type
  | .star => RawTerm scope → Prop
  | .arrow domainKind codomainKind => SemanticType scope domainKind → SemanticType scope codomainKind

/-- Candidate-hood at every kind (the Girard saturation condition, kind-generalised): at `.star` the
value is a reducibility candidate; at `.arrow` the operator maps every reducible input to a reducible
output.  This is the predicate a semantic environment's entries must satisfy. -/
def SemanticType.IsReducible (scope : Nat) :
    (kind : SemanticKind) → SemanticType scope kind → Prop
  | .star, candidate => IsReducibilityCandidate candidate
  | .arrow domainKind codomainKind, operator =>
      ∀ input : SemanticType scope domainKind, SemanticType.IsReducible scope domainKind input →
        SemanticType.IsReducible scope codomainKind (operator input)

/-- A reducible inhabitant at EVERY kind — the higher-kinded CR1 inhabitedness witness, so a semantic
environment can always be populated.  At `.star` it is the strongly normalizing candidate; at `.arrow`
it is the constant operator returning the codomain witness (ignoring its input). -/
def SemanticType.witness (scope : Nat) : (kind : SemanticKind) → SemanticType scope kind
  | .star => IsStronglyNormalizing
  | .arrow _domainKind codomainKind => fun _input => SemanticType.witness scope codomainKind

/-- The witness inhabitant is reducible at every kind.  At `.star` the strongly normalizing terms form
a reducibility candidate; at `.arrow` the constant operator sends any input (reducible or not) to the
codomain witness, reducible by the induction hypothesis. -/
theorem SemanticType.witness_isReducible (scope : Nat) : (kind : SemanticKind) →
    SemanticType.IsReducible scope kind (SemanticType.witness scope kind)
  | .star => isStronglyNormalizing_isReducibilityCandidate
  | .arrow _domainKind codomainKind => fun _input _inputReducible =>
      SemanticType.witness_isReducible scope codomainKind

end FX1Poly.Core
