import FX1Poly.Core.CandidateInterpretation
import FX1Poly.Core.HeadExpansionClosure

/-! # Foundation/PolyCell/Core/CandidateInterpretationHeadExpansion
    — every interpreted type is head-expansion-closed

The Girard-Tait fundamental theorem's Π-introduction case must show a λ-abstraction is reducible at
its arrow candidate: for every reducible argument, the β-redex `app (lam body) argument` lies in the
codomain candidate.  That β-redex inherits codomain membership from its contractum `subst0 body
argument` exactly when the codomain candidate is **head-expansion-closed**.  So, alongside
`InterpretsType.isReducibilityCandidate`, every interpreted type must carry this second property.

This file proves it: `InterpretsType.headExpansionClosed` — if the environment's candidates are all
head-expansion-closed, so is every candidate the environment interprets.  Unlike
`isReducibilityCandidate`, the arrow case needs no inhabitedness witness (the arrow former preserves
head-expansion closure with no domain hypothesis, `isArrowReducible_headExpansionClosed`), so this
holds at every target scope.

## Zero-axiom verification

Induction on the interpretation, discharging to the shipped closures
(`isStronglyNormalizing_headExpansionClosed`, `isArrowReducible_headExpansionClosed`); the Π case keeps
the codomain environment closed by `isHeadExpansionClosedEnv_cons` from the domain closure.  `Fin`
positions split by the blessed `⟨0, _⟩` / `⟨k + 1, _⟩` match.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A candidate environment is head-expansion-closed when every entry is. -/
@[reducible] def IsHeadExpansionClosedEnv {scope targetScope : Nat}
    (env : CandidateEnv scope targetScope) : Prop :=
  ∀ index : Fin scope, HeadExpansionClosed (env index)

/-- Consing a head-expansion-closed candidate onto a head-expansion-closed environment stays
head-expansion-closed. -/
theorem isHeadExpansionClosedEnv_cons {scope targetScope : Nat}
    {headCandidate : RawTerm targetScope → Prop} {tailEnv : CandidateEnv scope targetScope}
    (headClosed : HeadExpansionClosed headCandidate)
    (tailClosed : IsHeadExpansionClosedEnv tailEnv) :
    IsHeadExpansionClosedEnv (CandidateEnv.cons headCandidate tailEnv) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      show HeadExpansionClosed headCandidate
      exact headClosed
  | ⟨priorValue + 1, hBound⟩ =>
      show HeadExpansionClosed (tailEnv ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩)
      exact tailClosed ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- **Every interpreted type is head-expansion-closed**, given a head-expansion-closed environment.
Induction on the interpretation: a type variable's candidate comes from the environment, the SN
candidate is closed (`isStronglyNormalizing_headExpansionClosed`), and the arrow candidate is closed
by `isArrowReducible_headExpansionClosed` (the codomain environment kept closed by
`isHeadExpansionClosedEnv_cons` from the domain closure).  Together with
`InterpretsType.isReducibilityCandidate`, this is the second property the fundamental theorem's λ case
consumes. -/
theorem InterpretsType.headExpansionClosed {scope targetScope : Nat}
    {env : CandidateEnv scope targetScope} {typeCode : RawTerm scope}
    {candidate : RawTerm targetScope → Prop}
    (interpretation : InterpretsType env typeCode candidate) :
    IsHeadExpansionClosedEnv env → HeadExpansionClosed candidate := by
  induction interpretation with
  | typeVariable environment index =>
      intro envClosed
      exact envClosed index
  | piType _domainInterp _codomainInterp domainInductiveHypothesis codomainInductiveHypothesis =>
      intro envClosed
      refine isArrowReducible_headExpansionClosed ?_
      exact codomainInductiveHypothesis
        (isHeadExpansionClosedEnv_cons (domainInductiveHypothesis envClosed) envClosed)
  | baseType environment _notVariable _notPiType =>
      intro _envClosed
      exact isStronglyNormalizing_headExpansionClosed

end FX1Poly.Core
