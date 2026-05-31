import FX1Poly.Core.CandidateInterpretation
import FX1Poly.Core.RawTermSubst

/-! # Foundation/PolyCell/Core/CandidateReducibleSubst
    — the reducible term-substitution environment for the fundamental theorem

The Girard-Tait fundamental theorem applies a term-substitution `ρ` to the subject and concludes
`subst ρ subject` lies in the subject's classifier candidate.  For that it threads an environment
hypothesis: each context variable's substituent must lie in that variable's *candidate*.  This file
provides that environment as a relation over an explicit per-variable candidate assignment (a
`CandidateEnv`), so it is independent of how the interpretation assigns those candidates — robust to
the interpretation's internals:

  `ReducibleSubst varCandidates ρ  :=  ∀ i, varCandidates i (ρ i)`

with the two operations the fundamental theorem needs: consing a fresh reducible argument (the
Π-introduction binder extension) and the reducible identity substitution (each variable lies in its
own candidate by `containsVariable`, turning the theorem into the closed-term reducibility corollary).

`RawTermSubst.cons` (the term-level substitution extension, dual to `lift`) is redefined here.

## Zero-axiom verification

A reducible def + two `Fin`-position inductions split by the blessed `⟨0, _⟩` / `⟨k + 1, _⟩` match.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- Extend a parallel substitution with a fresh substituent `headTerm` at position 0 — the term-level
dual of `RawTermSubst.lift` (lift weakens; cons substitutes) and of `CandidateEnv.cons`. -/
def RawTermSubst.cons {scope targetScope : Nat} (headTerm : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) : RawTermSubst (scope + 1) targetScope :=
  fun position =>
    match position with
    | ⟨0, _⟩ => headTerm
    | ⟨priorValue + 1, hBound⟩ => tailSubst ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- A term substitution is reducible for a per-variable candidate assignment when each variable's
substituent lies in that variable's candidate. -/
@[reducible] def ReducibleSubst {scope targetScope : Nat}
    (varCandidates : CandidateEnv scope targetScope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope, varCandidates index (substitution index)

/-- Consing a reducible argument onto a reducible substitution stays reducible for the consed
candidate assignment — the environment extension the Π-introduction case performs. -/
theorem reducibleSubst_cons {scope targetScope : Nat}
    {varCandidates : CandidateEnv scope targetScope}
    {substitution : RawTermSubst scope targetScope}
    {headCandidate : RawTerm targetScope → Prop} {headTerm : RawTerm targetScope}
    (headReducible : headCandidate headTerm)
    (tailReducible : ReducibleSubst varCandidates substitution) :
    ReducibleSubst (CandidateEnv.cons headCandidate varCandidates)
      (RawTermSubst.cons headTerm substitution) := by
  intro index
  match index with
  | ⟨0, _⟩ => exact headReducible
  | ⟨priorValue + 1, hBound⟩ => exact tailReducible ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- The identity substitution is reducible for any well-formed candidate assignment: each variable
lies in its own candidate by `containsVariable` (CR3 over the variable, which has no reducts).  This
is the base environment that turns the fundamental theorem into the closed-term reducibility
corollary. -/
theorem reducibleSubst_identity {scope : Nat} {varCandidates : CandidateEnv scope scope}
    (allCandidates : IsCandidateEnv varCandidates) :
    ReducibleSubst varCandidates (RawTermSubst.identity : RawTermSubst scope scope) := by
  intro index
  exact (allCandidates index).containsVariable index

end FX1Poly.Core
