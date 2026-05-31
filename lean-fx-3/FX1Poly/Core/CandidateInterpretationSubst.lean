import FX1Poly.Core.CandidateInterpretationRename
import FX1Poly.Core.RawTermSubst
import FX1Poly.Core.RawTermWeaken

/-! # Foundation/PolyCell/Core/CandidateInterpretationSubst
    — the semantic substitution lemma (the crux of polymorphic SN)

The Girard-Tait fundamental theorem's Π-elimination case needs the interpretation to commute with
**type substitution**: the result type of `f a` is `codomain[a]`, and its candidate must be the
codomain's candidate.  This file proves the general semantic substitution lemma, in a form that needs
neither totality nor determinism in its statement:

  `InterpretsType env₁ T cand → (∀ i, InterpretsType env₂ (σ i) (env₁ i)) →
     InterpretsType env₂ (subst σ T) cand`

— if `T` interprets to `cand` under `env₁`, and each type variable's substituent `σ i` interprets
under `env₂` to that variable's `env₁`-candidate, then `subst σ T` interprets to the SAME candidate
under `env₂`.  The bound-variable candidate that handles a *polymorphic* codomain (e.g. `codomain = X`,
where `subst σ X = σ X` interprets to whatever `σ X` denotes) is exactly `env₁ X`, threaded through the
hypothesis — this is what dissolves the dependency that the simply-typed skeleton could not.

The Π case interprets the codomain under the **lifted** substitution; the lift's `k + 1` case weakens
the substituent, discharged by `InterpretsType.rename` (the renaming-commutation lemma).

## Zero-axiom verification

Induction on the first interpretation + `interpretsLiftSubst` (the lift helper, var-0 = fresh,
`k + 1` = weaken via `InterpretsType.rename`).  `subst_rootGenerator_of_not_var` reduces the fold's
non-variable branch with `dsimp only [fold]` (NOT `unfold`, which pulls `Quot.sound`).  No `funext`
(the substituent hypothesis is pointwise).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- Substituting into a Π-type code distributes: the domain by `σ`, the codomain (under one binder)
by `σ.lift`. -/
theorem RawTerm.subst_piTyCode {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) =
      .mkGen .gen_piTyCode ()
        (.childCons (RawTerm.subst substitution domainCode)
          (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)) :=
  rfl

/-- Substituting preserves the head generator of a NON-variable cell.  (Substitution can change the
head only at a variable, where it replaces the cell wholesale.)  Reduces the non-variable fold branch
with `dsimp only [fold]`. -/
theorem RawTerm.subst_rootGenerator_of_not_var {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) {term : RawTerm sourceScope}
    (notVariable : term.rootGenerator ≠ Generator.gen_var) :
    (RawTerm.subst substitution term).rootGenerator = term.rootGenerator := by
  match term with
  | .mkGen generator _payload _children =>
      have hVar : generator ≠ .gen_var := notVariable
      show (fold GenAlgebra.canonical substitution
            (.mkGen generator _payload _children)).rootGenerator = generator
      dsimp only [fold]
      rw [dif_neg hVar]
      rfl

/-- The lifted-substitution interpretation helper: if each type variable's substituent interprets to
its candidate, then under one more binder each LIFTED substituent interprets to the consed candidate.
Position 0 is the fresh variable (`typeVariable`); position `k + 1` is the weakened original,
discharged by `InterpretsType.rename` at the weakening renaming. -/
theorem interpretsLiftSubst {sourceScope middleScope targetScope : Nat}
    {env1 : CandidateEnv sourceScope targetScope}
    {env2 : CandidateEnv middleScope targetScope}
    {substitution : RawTermSubst sourceScope middleScope}
    {headCandidate : RawTerm targetScope → Prop}
    (substInterprets : ∀ index, InterpretsType env2 (substitution index) (env1 index)) :
    ∀ index, InterpretsType (CandidateEnv.cons headCandidate env2)
      (RawTermSubst.lift substitution index) ((CandidateEnv.cons headCandidate env1) index) := by
  intro index
  match index with
  | ⟨0, _⟩ =>
      exact InterpretsType.typeVariable (CandidateEnv.cons headCandidate env2)
        ⟨0, Nat.zero_lt_succ middleScope⟩
  | ⟨priorValue + 1, hBound⟩ =>
      show InterpretsType (CandidateEnv.cons headCandidate env2)
        (RawTerm.weaken (substitution ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩))
        (env1 ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩)
      rw [RawTerm.weaken_eq_rename]
      exact (substInterprets ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩).rename
        RawRenaming.weaken (fun _index => rfl)

/-- **The semantic substitution lemma** (the crux of polymorphic SN).  If a type-code interprets to a
candidate under `env₁`, and each type variable's substituent interprets under `env₂` to that
variable's `env₁`-candidate, then the substituted type-code interprets to the SAME candidate under
`env₂`.  Induction on the interpretation: a variable becomes its substituent (the hypothesis), a Π
distributes (codomain under the lifted substitution via `interpretsLiftSubst`), and a non-Π/
non-variable code keeps its head (`subst_rootGenerator_of_not_var`). -/
theorem InterpretsType.subst {sourceScope targetScope : Nat}
    {env1 : CandidateEnv sourceScope targetScope} {typeCode : RawTerm sourceScope}
    {candidate : RawTerm targetScope → Prop}
    (interpretation : InterpretsType env1 typeCode candidate) :
    ∀ {middleScope : Nat} {env2 : CandidateEnv middleScope targetScope}
      (substitution : RawTermSubst sourceScope middleScope),
      (∀ index, InterpretsType env2 (substitution index) (env1 index)) →
      InterpretsType env2 (RawTerm.subst substitution typeCode) candidate := by
  induction interpretation with
  | typeVariable environment index =>
      intro middleScope env2 substitution substInterprets
      rw [RawTerm.subst_var_reduces]
      exact substInterprets index
  | piType _domainInterp _codomainInterp domainInductiveHypothesis codomainInductiveHypothesis =>
      intro middleScope env2 substitution substInterprets
      rw [RawTerm.subst_piTyCode]
      exact InterpretsType.piType
        (domainInductiveHypothesis substitution substInterprets)
        (codomainInductiveHypothesis (RawTermSubst.lift substitution)
          (interpretsLiftSubst substInterprets))
  | baseType environment notVariable notPiType =>
      intro middleScope env2 substitution _substInterprets
      refine InterpretsType.baseType env2 ?_ ?_
      · rw [RawTerm.subst_rootGenerator_of_not_var substitution notVariable]; exact notVariable
      · rw [RawTerm.subst_rootGenerator_of_not_var substitution notVariable]; exact notPiType

end FX1Poly.Core
