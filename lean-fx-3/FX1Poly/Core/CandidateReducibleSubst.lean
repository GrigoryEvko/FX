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

`RawTermSubst.cons` (the term-level substitution extension, dual to `lift`) now lives in
`FX1Poly/Core/RawTermSubst.lean` (relocated so the reduction substrate can reference it) and is in
scope here via the `RawTermSubst` import.

## Zero-axiom verification

A reducible def + two `Fin`-position inductions split by the blessed `⟨0, _⟩` / `⟨k + 1, _⟩` match.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

-- `RawTermSubst.cons` (the term-level substitution extension, dual to `lift`) was relocated to
-- `FX1Poly/Core/RawTermSubst.lean` so the low-level reduction substrate (`Step`'s natElim/natRec
-- succ-iota) can reference it; it is in scope here via the `RawTermSubst` import above.

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
