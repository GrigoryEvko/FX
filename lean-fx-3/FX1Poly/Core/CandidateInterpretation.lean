import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.ReducibilityCandidate

/-! # Foundation/PolyCell/Core/CandidateInterpretation
    — the candidate-environment reducibility interpretation (Girard-Tait, for polymorphism)

A simply-typed skeleton can prove SN only for the simply-typed
λ-calculus, NOT the full dependent kernel: `HasTypeDescPi` is polymorphic
(`f : (A : Type) → A` is typeable), and a term like `(f (Nat → Nat)) 5` instantiates a type
variable with a function type and then applies the result.  The skeleton erases `f (Nat → Nat)`
to the base sort and can no longer apply it — the classical reason System F SN needs Girard's
**reducibility candidates with a candidate environment**, not simple types.

This file builds that engine.  A `CandidateEnv` assigns a reducibility candidate (over target-scope
terms) to each type variable.  `InterpretsType env typeCode candidate` interprets a type-code as a
candidate under the environment:

  * a type variable looks up its candidate in the environment;
  * a Π-type code denotes the **arrow candidate** (`IsArrowReducible`, Girard's function space) of
    its children's interpretations, with the codomain interpreted in the environment extended by the
    domain's candidate;
  * every other code denotes the SN candidate.

The headline `InterpretsType.isReducibilityCandidate` proves every interpreted type-code is a
genuine reducibility candidate — the arrow case discharges CR1's inhabitedness obligation with
variable 0 (`containsVariable`), so the target scope is taken non-empty (`targetScopePred + 1`); the
closed case is reached later by weakening.

## Soundness scope

Correct for the current `HasTypeDescPi` fragment (Π-formation + Π-intro/elim, NO data eliminators):
with no large elimination, a type's candidate never depends on a term value, so the single-candidate
interpretation per Π is sound.  When data eliminators with type-valued motives land, the
interpretation gains the value-tracking refinement — additive, flagged here.

## Zero-axiom verification

A plain inductive `Prop` (indexed by the candidate predicate, a `Type` index — well-formed) +
induction discharging to the shipped candidate combinators (`isArrowReducible_isReducibilityCandidate`,
`isStronglyNormalizing_isReducibilityCandidate`, `containsVariable`).  `Fin` positions split by the
blessed `⟨0, _⟩` / `⟨k + 1, _⟩` match.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A candidate environment assigns a reducibility-candidate predicate (over `targetScope` terms) to
each type variable in the source `scope`. -/
@[reducible] def CandidateEnv (scope targetScope : Nat) : Type :=
  Fin scope → (RawTerm targetScope → Prop)

/-- Extend a candidate environment with a fresh candidate at position 0; prior variables shift up. -/
def CandidateEnv.cons {scope targetScope : Nat}
    (headCandidate : RawTerm targetScope → Prop)
    (tailEnv : CandidateEnv scope targetScope) : CandidateEnv (scope + 1) targetScope :=
  fun position =>
    match position with
    | ⟨0, _⟩ => headCandidate
    | ⟨priorValue + 1, hBound⟩ => tailEnv ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- The candidate-environment reducibility interpretation: a type-code denotes a reducibility
candidate under an environment of candidates for its type variables.  Type variables look up the
environment; a Π-type code denotes the arrow candidate of its children's interpretations (codomain
interpreted in the environment extended by the domain's candidate); every other code denotes the SN
candidate. -/
inductive InterpretsType {targetScope : Nat} :
    {scope : Nat} → CandidateEnv scope targetScope → RawTerm scope →
      (RawTerm targetScope → Prop) → Prop where
  /-- A type variable interprets to its environment candidate. -/
  | typeVariable {scope : Nat} (env : CandidateEnv scope targetScope) (index : Fin scope) :
      InterpretsType env (.mkGen .gen_var index .childNil) (env index)
  /-- A Π-type code interprets to the arrow candidate; the codomain is interpreted in the environment
  extended by the domain's candidate. -/
  | piType {scope : Nat} {env : CandidateEnv scope targetScope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainCandidate codomainCandidate : RawTerm targetScope → Prop} :
      InterpretsType env domainCode domainCandidate →
      InterpretsType (env.cons domainCandidate) codomainCode codomainCandidate →
      InterpretsType env
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)))
        (IsArrowReducible domainCandidate codomainCandidate)
  /-- Every non-variable, non-Π code interprets to the SN candidate. -/
  | baseType {scope : Nat} (env : CandidateEnv scope targetScope) {term : RawTerm scope} :
      term.rootGenerator ≠ Generator.gen_var →
      term.rootGenerator ≠ Generator.gen_piTyCode →
      InterpretsType env term IsStronglyNormalizing

/-- A candidate environment is well-formed when every entry is a reducibility candidate. -/
@[reducible] def IsCandidateEnv {scope targetScope : Nat}
    (env : CandidateEnv scope targetScope) : Prop :=
  ∀ index : Fin scope, IsReducibilityCandidate (env index)

/-- Consing a candidate onto a well-formed environment stays well-formed. -/
theorem isCandidateEnv_cons {scope targetScope : Nat}
    {headCandidate : RawTerm targetScope → Prop} {tailEnv : CandidateEnv scope targetScope}
    (headIsCandidate : IsReducibilityCandidate headCandidate)
    (tailIsCandidateEnv : IsCandidateEnv tailEnv) :
    IsCandidateEnv (CandidateEnv.cons headCandidate tailEnv) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact headIsCandidate
  | ⟨priorValue + 1, hBound⟩ => exact tailIsCandidateEnv ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- **Every interpreted type-code is a reducibility candidate**, given a well-formed environment.
Induction on the interpretation: a type variable's candidate comes from the environment, the SN
candidate is shipped (`isStronglyNormalizing_isReducibilityCandidate`), and the arrow candidate is a
candidate by `isArrowReducible_isReducibilityCandidate` — its CR1 inhabitedness obligation discharged
by variable 0 (`containsVariable`), so the target scope is taken non-empty.  This is what makes the
interpretation meaningful: an interpreted type is a real candidate, so the eventual fundamental
theorem extracts SN from membership (CR1). -/
theorem InterpretsType.isReducibilityCandidate {targetScopePred scope : Nat}
    {env : CandidateEnv scope (targetScopePred + 1)} {typeCode : RawTerm scope}
    {candidate : RawTerm (targetScopePred + 1) → Prop}
    (interprets : InterpretsType env typeCode candidate) :
    IsCandidateEnv env → IsReducibilityCandidate candidate := by
  induction interprets with
  | typeVariable environment index =>
      intro envIsCandidate
      exact envIsCandidate index
  | piType _domainInterprets _codomainInterprets domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro envIsCandidate
      have domainCandidate := domainInductiveHypothesis envIsCandidate
      have codomainCandidate :=
        codomainInductiveHypothesis (isCandidateEnv_cons domainCandidate envIsCandidate)
      exact isArrowReducible_isReducibilityCandidate domainCandidate codomainCandidate
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ targetScopePred⟩ .childNil)
        (domainCandidate.containsVariable ⟨0, Nat.zero_lt_succ targetScopePred⟩)
  | baseType environment _notVariable _notPiType =>
      intro _envIsCandidate
      exact isStronglyNormalizing_isReducibilityCandidate

end FX1Poly.Core
