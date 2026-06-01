import FX1Poly.Core.CandidateReducibleSubst
import FX1Poly.Core.ArrowCandidateMembership
import FX1Poly.Core.SubstPreservationProbes
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Core/CandidateInterpretationFundamental
    — the fundamental-theorem cases under a closing substitution, over the choice-free interpretation

The Girard-Tait fundamental theorem is an induction over the typing derivation, each arm producing
"the closed subject lies in the closed classifier's candidate".  Over the candidate-environment
interpretation `InterpretsType` (`CandidateInterpretation`) — which is CHOICE-FREE (the Π codomain is
interpreted in a candidate ENVIRONMENT extended by the domain's candidate, never an `∀ argument ∃
candidate` family) — the candidate-level operations are all shipped (`IsArrowReducible.application` /
`.abstraction`, `ReducibleSubst`, `InterpretsType.rename` / `.subst` / `.isReducibilityCandidate` /
`.headExpansionClosed`).  This file assembles the LEAF + ELIMINATION spine of that induction as
standalone closed-substitution cases — the `var`, arrow-`piElim`, and `universeFormation` arms — each a
thin composition of the shipped operations through the cell-substitution reductions.

  * `fundamentalVariable` (the `var` arm) — a reducible closing substitution sends a variable to a
    member of that variable's candidate.  `subst ρ (var i) = ρ i` (`subst_var_reduces`) and
    `ReducibleSubst` supplies `varCandidates i (ρ i)`.
  * `fundamentalArrowApplication` (the `piElim` / app arm, non-dependent arrow) — a closed function in
    the arrow candidate, applied to a closed reducible argument, lands in the codomain candidate.  The
    closing substitution pushes through the application cell (rfl), then `IsArrowReducible.application`
    discharges it.  The choice-free dependent-elimination payoff at the candidate level.
  * `fundamentalUniverseFormation` (the `universeFormation` arm) — a universe code is a member of the
    universe's candidate, which (a universe code is a weak-head-normal non-Π leaf) is strong
    normalization; the code is a normal leaf (`noStep_universeCode`), so it is strongly normalizing.

## Zero-axiom verification

Each case is a composition of shipped lemmas through `subst_var_reduces` (rfl), the rfl
application-cell substitution, and a `dsimp only [fold]` + `dif_neg` reduction of the childless
universe-code substitution (NOT `unfold`, which pulls `Quot.sound`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace
FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- **The `var` case of the fundamental theorem under a closing substitution.**  A reducible closing
substitution `substitution` (each variable's substituent lies in that variable's candidate,
`ReducibleSubst`) sends the variable `index` to a member of `index`'s candidate: `subst substitution
(var index) = substitution index` (`subst_var_reduces`) which `ReducibleSubst` places in `varCandidates
index`.  The leaf case turning the theorem into the closed-term corollary at `reducibleSubst_identity`.
The type-code side is the `InterpretsType.typeVariable` constructor (the variable interprets to its
environment candidate). -/
theorem InterpretsType.fundamentalVariable {scope targetScope : Nat}
    {varCandidates : CandidateEnv scope targetScope}
    {substitution : RawTermSubst scope targetScope}
    (reducibleSubst : ReducibleSubst varCandidates substitution) (index : Fin scope) :
    varCandidates index
      (RawTerm.subst substitution (.mkGen .gen_var index .childNil)) := by
  rw [RawTerm.subst_var_reduces]
  exact reducibleSubst index

/-- **The `piElim` (application) case of the fundamental theorem under a closing substitution**, at the
non-dependent arrow candidate `InterpretsType.piType` produces.  Given a closed function that is a member
of the arrow candidate `IsArrowReducible domainCandidate codomainCandidate` and a closed argument that is
a member of the domain candidate, the closed application is a member of the codomain candidate.  The
closing substitution pushes through the application cell (`subst (app f a) = app (subst f) (subst a)`,
rfl), and `IsArrowReducible.application` discharges the result — the choice-free dependent-elimination
payoff.  The `functionReducible` / `argumentReducible` premises are the function's and argument's
fundamental-theorem induction hypotheses, already closed by the same substitution. -/
theorem InterpretsType.fundamentalArrowApplication {scope targetScope : Nat}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    {functionTerm argument : RawTerm scope}
    (substitution : RawTermSubst scope targetScope)
    (functionReducible : IsArrowReducible domainCandidate codomainCandidate
      (RawTerm.subst substitution functionTerm))
    (argumentReducible : domainCandidate (RawTerm.subst substitution argument)) :
    codomainCandidate
      (RawTerm.subst substitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  IsArrowReducible.application functionReducible argumentReducible

/-- **The `universeFormation` case of the fundamental theorem under a closing substitution.**  A universe
code is a member of the universe's candidate, which — a universe code being a weak-head-normal non-Π leaf
— `InterpretsType.baseType` makes the strong-normalization candidate; the closed universe code is a
normal leaf (`noStep_universeCode`), hence strongly normalizing.  The closing substitution leaves the
childless universe code unchanged (the non-variable fold branch rebuilds the same cell, reduced by
`dsimp only [fold]` + `dif_neg`). -/
theorem InterpretsType.fundamentalUniverseFormation {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)) := by
  have substEquation :
      RawTerm.subst substitution
          (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        = .mkGen .gen_universeCode (levelExpr, flag) .childNil := by
    show fold GenAlgebra.canonical substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) = _
    dsimp only [fold]
    rw [dif_neg (by decide : Generator.gen_universeCode ≠ Generator.gen_var)]
    rfl
  rw [substEquation]
  exact isStronglyNormalizing_of_noStep
    (fun _target step => noStep_universeCode (levelExpr, flag) step)

end FX1Poly.Core
