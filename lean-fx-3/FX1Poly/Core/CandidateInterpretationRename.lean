import FX1Poly.Core.CandidateInterpretation
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.SubstPreservationProbes

/-! # Foundation/PolyCell/Core/CandidateInterpretationRename
    — the candidate-environment interpretation commutes with renaming

The semantic substitution lemma (the crux of polymorphic SN, coming next) needs the interpretation
to commute with **weakening**: when the codomain of a Π is interpreted under a lifted substitution,
the `k + 1` case of the lift weakens the substituent, and the interpretation must be stable under
that weakening.  Weakening is a renaming, so this file proves the general statement:

  `InterpretsType (env ∘ renaming) typeCode candidate →
     InterpretsType env (rename renaming typeCode) candidate`

— renaming the type variables in a type-code (and pre-composing the environment with the same
renaming) leaves the denoted candidate unchanged.  The candidate is literally the same predicate; no
pointwise slack is needed because renaming only reindexes variables.

The proof is an induction on the interpretation, with a foundational head-preservation lemma
`RawTerm.rename_rootGenerator` (renaming never changes a cell's head generator) discharging the
non-variable case.

## Zero-axiom verification

`rename_rootGenerator` reduces the fold's non-variable branch with `dsimp only [fold]` (NOT
`unfold`, which would pull `Quot.sound` through the mutual-def equation lemmas).  The main induction
threads a pointwise environment-equality hypothesis (`∀ index, sourceEnv index = env (renaming index)`)
so no `funext` is needed.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Renaming preserves the head generator.**  `rename` is `fold` with the canonical algebra: the
variable branch re-emits a `gen_var` cell, the non-variable branch rebuilds with the same generator,
so the root generator is unchanged.  Foundational and reusable beyond the interpretation. -/
theorem RawTerm.rename_rootGenerator {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (term : RawTerm sourceScope) :
    (RawTerm.rename rawRenaming term).rootGenerator = term.rootGenerator := by
  match term with
  | .mkGen generator _payload _children =>
      by_cases hVar : generator = .gen_var
      · subst hVar; rfl
      · show (fold GenAlgebra.canonical rawRenaming
            (.mkGen generator _payload _children)).rootGenerator = generator
        dsimp only [fold]
        rw [dif_neg hVar]
        rfl

/-- Renaming a Π-type code distributes: the domain is renamed by `renaming`, the codomain (under one
binder) by `renaming.lift`. -/
theorem RawTerm.rename_piTyCode {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) =
      .mkGen .gen_piTyCode ()
        (.childCons (RawTerm.rename rawRenaming domainCode)
          (.childCons (RawTerm.rename (RawRenaming.lift rawRenaming) codomainCode) .childNil)) :=
  rfl

/-- The environment-consing/renaming-lift coherence the Π binder case needs: extending the renamed
environment by a head candidate agrees pointwise with renaming the extended environment by the lifted
renaming. -/
theorem candidateEnv_cons_lift_eq {sourceScope renamedScope targetScope : Nat}
    {sourceEnv : CandidateEnv sourceScope targetScope}
    {env : CandidateEnv renamedScope targetScope}
    {rawRenaming : RawRenaming sourceScope renamedScope}
    {headCandidate : RawTerm targetScope → Prop}
    (envEquality : ∀ index, sourceEnv index = env (rawRenaming index)) :
    ∀ index, (CandidateEnv.cons headCandidate sourceEnv) index =
      (CandidateEnv.cons headCandidate env) (RawRenaming.lift rawRenaming index) := by
  intro index
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨priorValue + 1, hBound⟩ => exact envEquality ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- **The interpretation commutes with renaming.**  If a type-code interprets to a candidate under
the environment pre-composed with a renaming, then the renamed type-code interprets to the same
candidate under the original environment.  Induction on the interpretation: a variable reads the
renamed position, a Π distributes (codomain under the lifted renaming, environments kept coherent by
`candidateEnv_cons_lift_eq`), and a non-Π/non-variable code keeps its head by `rename_rootGenerator`. -/
theorem InterpretsType.rename {sourceScope targetScope : Nat}
    {sourceEnv : CandidateEnv sourceScope targetScope} {typeCode : RawTerm sourceScope}
    {candidate : RawTerm targetScope → Prop}
    (interpretation : InterpretsType sourceEnv typeCode candidate) :
    ∀ {renamedScope : Nat} {env : CandidateEnv renamedScope targetScope}
      (rawRenaming : RawRenaming sourceScope renamedScope),
      (∀ index, sourceEnv index = env (rawRenaming index)) →
      InterpretsType env (RawTerm.rename rawRenaming typeCode) candidate := by
  induction interpretation with
  | typeVariable environment index =>
      intro renamedScope env rawRenaming envEquality
      rw [RawTerm.rename_var_reduces, envEquality index]
      exact InterpretsType.typeVariable env (rawRenaming index)
  | piType _domainInterp _codomainInterp domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro renamedScope env rawRenaming envEquality
      rw [RawTerm.rename_piTyCode]
      exact InterpretsType.piType
        (domainInductiveHypothesis rawRenaming envEquality)
        (codomainInductiveHypothesis (RawRenaming.lift rawRenaming)
          (candidateEnv_cons_lift_eq envEquality))
  | baseType environment notVariable notPiType =>
      intro renamedScope env rawRenaming _envEquality
      refine InterpretsType.baseType env ?_ ?_
      · rw [RawTerm.rename_rootGenerator]; exact notVariable
      · rw [RawTerm.rename_rootGenerator]; exact notPiType

end FX1Poly.Core
