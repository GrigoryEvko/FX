import FX1Poly.Core.StepRename
import FX1Poly.Core.StrongNormalizationRenameForward
import FX1Poly.Core.CandidateInterpretationRename
import FX1Poly.Core.HeadStepRenameReflect
import FX1Poly.Core.RawTermFresh

/-! # FX1Poly/Core/StepRenameReflect — pulling a `Step` BACK along an injective renaming

`Step.rename` (StepRename.lean) pushes a reduction FORWARD along any renaming
(`Step t t' → Step (rename ρ t) (rename ρ t')`).  The Kripke reducibility-candidate CR3 of the
dependent arrow (the deferred Girard case, `KripkeCandidateRenameClosure.lean:63`) needs the CONVERSE
with image:

  `Step (rename ρ f) h → ∃ f', Step f f' ∧ rename ρ f' = h`   (for injective `ρ`).

That full reflection-with-image splits into two halves:

  * the **`Step` half** (this file): recover the SOURCE reduct `f' := rename ρ⁻¹ h` and prove `Step f f'`.
    This half needs NO free-variable confinement — the left-inverse property `ρ⁻¹ ∘ ρ = id` holds at
    EVERY index (not merely on `ρ`'s image), so the round-trip `rename ρ⁻¹ (rename ρ f) = f` collapses
    definitionally exactly as in `isStronglyNormalizing_rename_of_leftInverse`.
  * the **image half** (`rename ρ f' = h`, a separate later brick): this DOES need confinement
    (`h`'s free variables lie in `ρ`'s image), since it is the OTHER composite `ρ ∘ ρ⁻¹`, which is the
    identity only on the image.

This file ships the confinement-free `Step` half (and its `StepStar` chain lift): pull a reduction of a
`ρ`-renamed term back to a reduction of the source, witnessed by the left-inverse renaming.  It is the
`Step`-level analogue of the shipped `isStronglyNormalizing_rename_of_leftInverse` and the full-`Step`
generalization of the existence-only `HeadStep.rename_reflects`.

## Zero-axiom verification

The round-trip `rename leftInverse (rename forward sourceTerm) = sourceTerm` is the verbatim
`rename_compose` + `rename_pointwise` (compose-is-identity from the left-inverse property) +
`rename_identity_apply` chain shipped in `isStronglyNormalizing_rename_of_leftInverse`; then `Step.rename`
(forward, shipped) transports the step and the round-trip rewrites the source side.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open StepStar

/-- **Generic head-recovery for a renamed cell.**  If `rename rho term` is a `gen`-headed cell, then so is
`term` — renaming preserves the head generator (`rename_rootGenerator`), and `RawTerm` is a single `mkGen`
constructor, so `term` is `mkGen gen _ _` with some payload/children.  The generator-generic head-recovery
half of the shipped `rename_eq_app` / `rename_eq_lam` (which additionally expose the renamed children at a
CONCRETE head via the `rfl`-distribution `rename_app_reduces`).  This is the uniform first step of every arm
of full arbitrary-renaming `Step` reflection (`Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u`,
the Kripke-arrow-CR3 ingredient): recover `t`'s head, then a concrete-`gen` `rfl`-distribution + `injection`
exposes the children for the per-arm reconstruction. -/
theorem RawTerm.rename_eq_mkGen {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {gen : Generator} {payloadReduct : gen.payload targetScope}
    {childrenReduct : RawTermChildren gen.binderShifts targetScope}
    (renameEquation : RawTerm.rename rho term = .mkGen gen payloadReduct childrenReduct) :
    ∃ (payload : gen.payload sourceScope) (children : RawTermChildren gen.binderShifts sourceScope),
      term = .mkGen gen payload children := by
  have rootEquation : term.rootGenerator = gen := by
    have congruence := congrArg RawTerm.rootGenerator renameEquation
    rw [RawTerm.rename_rootGenerator] at congruence
    exact congruence
  match term, rootEquation with
  | .mkGen generator payload children, rootEquation =>
      change generator = gen at rootEquation
      subst rootEquation
      exact ⟨payload, children, rfl⟩

/-- **The β arm of arbitrary-renaming `Step` reflection.**  If `rename rho term` is a β-redex `app (lam
renamedBody) renamedArg`, then `term` is the source β-redex `app (lam body) arg` (renaming preserves the
app/lam shape, `rename_eq_app` / `rename_eq_lam`), it β-reduces to `subst0 body arg`, and that source
contractum renames to the redex's contractum `subst0 renamedBody renamedArg` — by the substitution/renaming
commutation `rename_subst0_commute` aligned through the recovered body/argument renamings.  The β leaf arm of
full arbitrary-ρ `Step` reflection (`Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u`): a complete
standalone case needing NO sub-reflection hypothesis (β is a base case), the substitution arm that the
child-projection ι arms and the recursive `cong` arm will join in the eventual mutual assembly. -/
theorem Step.reflectBeta {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedBody : RawTerm (targetScope + 1)} {renamedArg : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_app ()
        (.childCons (.mkGen .gen_lam () (.childCons renamedBody .childNil))
          (.childCons renamedArg .childNil))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct = RawTerm.subst0 renamedBody renamedArg := by
  obtain ⟨functionTerm, argument, termEqApp, functionRename, argumentRename⟩ :=
    RawTerm.rename_eq_app rho renameEquation
  obtain ⟨body, functionEqLam⟩ := RawTerm.rename_eq_lam rho functionRename
  subst termEqApp
  subst functionEqLam
  rw [RawTerm.rename_lam_reduces] at functionRename
  injection functionRename with _scopeEq _generatorEq _payloadEq bodyChildrenEq
  injection bodyChildrenEq with _childScopeEq _childShiftEq _childRestShiftsEq bodyEq _nilEq
  refine ⟨RawTerm.subst0 body argument, Step.beta, ?_⟩
  rw [RawTerm.rename_subst0_commute, bodyEq, argumentRename]

/-- **The `boolElim`-on-`boolTrue` ι arm of arbitrary-renaming `Step` reflection.**  If `rename rho term` is
the ι-redex `boolElim boolTrue thenBranch elseBranch`, then `term` is the source redex `boolElim boolTrue
sourceThen sourceElse` (renaming preserves the `gen_boolElim` head and the nested `gen_boolTrue` scrutinee head,
both recovered by `rename_eq_mkGen`; `gen_boolTrue` has no children so the scrutinee is recovered exactly), it
ι-reduces to its then-branch, and that source then-branch renames to `renamedThen`.  A child-PROJECTION ι leaf
arm: the contractum is a child of the redex (no substitution), so the image equation is the child's own
recovered renaming.  Complete standalone case (ι is a base case, no sub-reflection hypothesis). -/
theorem Step.reflectIotaBoolTrue {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedThen renamedElse : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_boolElim ()
        (.childCons (.mkGen .gen_boolTrue () .childNil)
          (.childCons renamedThen (.childCons renamedElse .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedThen := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_boolElim ()
              (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))) =
            (.mkGen .gen_boolElim ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho thenBranch)
                  (.childCons (RawTerm.rename rho elseBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ thenEq tail2Eq
      injection tail2Eq with _ _ _ _elseEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childNil =>
          exact ⟨thenBranch, Step.iotaBoolTrue, thenEq⟩

/-- **The `boolElim`-on-`boolFalse` ι arm of arbitrary-renaming `Step` reflection.**  The symmetric twin of
`reflectIotaBoolTrue`: a `boolElim boolFalse thenBranch elseBranch` ι-redex reflects to the source redex
projecting its ELSE-branch.  Same child-projection recipe (head recovery + concrete `gen_boolElim`
rfl-distribution + injection + `gen_boolFalse` scrutinee recovery), returning the else-branch with its
recovered renaming as the contractum image. -/
theorem Step.reflectIotaBoolFalse {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedThen renamedElse : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_boolElim ()
        (.childCons (.mkGen .gen_boolFalse () .childNil)
          (.childCons renamedThen (.childCons renamedElse .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedElse := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_boolElim ()
              (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))) =
            (.mkGen .gen_boolElim ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho thenBranch)
                  (.childCons (RawTerm.rename rho elseBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ _thenEq tail2Eq
      injection tail2Eq with _ _ _ elseEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childNil =>
          exact ⟨elseBranch, Step.iotaBoolFalse, elseEq⟩

/-- **Pull a `Step` back along an injective renaming.**  If the `forwardRenaming`-renamed `sourceTerm`
takes a reduction to `renamedReduct`, then `sourceTerm` itself reduces to `rename leftInverseRenaming
renamedReduct` — the source reduct recovered by the left-inverse.  The confinement-free `Step` half of
full rename-reflection (the image equation `rename forwardRenaming (…) = renamedReduct` is a separate
brick needing free-variable confinement).  Witnessed by transporting the step with `Step.rename` along
`leftInverseRenaming` and collapsing the round-trip `rename leftInverse (rename forward sourceTerm) =
sourceTerm` (the same chain as `isStronglyNormalizing_rename_of_leftInverse`). -/
theorem Step.renamePullbackOfLeftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {sourceTerm : RawTerm sourceScope} {renamedReduct : RawTerm targetScope}
    (renamedStep : Step (RawTerm.rename forwardRenaming sourceTerm) renamedReduct) :
    Step sourceTerm (RawTerm.rename leftInverseRenaming renamedReduct) := by
  have pulledStep := Step.rename leftInverseRenaming renamedStep
  have roundTrip :
      RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming sourceTerm) = sourceTerm := by
    rw [RawTerm.rename_compose forwardRenaming leftInverseRenaming sourceTerm]
    have composeIsIdentity :
        RawRenaming.PointwiseEq
          (RawRenaming.compose forwardRenaming leftInverseRenaming)
          (RawRenaming.identity (scope := sourceScope)) := by
      intro position
      simp only [RawRenaming.compose, RawRenaming.identity]
      exact leftInverseProperty position
    rw [RawTerm.rename_pointwise composeIsIdentity sourceTerm]
    exact RawTerm.rename_identity_apply sourceTerm
  rw [roundTrip] at pulledStep
  exact pulledStep

/-- **Existence form of the `Step` pullback.**  A reduction of a `forwardRenaming`-renamed term reflects
to SOME reduction of the source — the full-`Step` generalization of the existence-only
`HeadStep.rename_reflects`, now with the explicit left-inverse witness available via
`renamePullbackOfLeftInverse`. -/
theorem Step.renameReflectsExistsOfLeftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {sourceTerm : RawTerm sourceScope} {renamedReduct : RawTerm targetScope}
    (renamedStep : Step (RawTerm.rename forwardRenaming sourceTerm) renamedReduct) :
    ∃ sourceReduct : RawTerm sourceScope, Step sourceTerm sourceReduct :=
  ⟨RawTerm.rename leftInverseRenaming renamedReduct,
    Step.renamePullbackOfLeftInverse forwardRenaming leftInverseRenaming leftInverseProperty renamedStep⟩

/-- **Pull a `StepStar` chain back along an injective renaming.**  The reflexive-transitive lift of
`Step.renamePullbackOfLeftInverse`: a multi-step reduction of a `forwardRenaming`-renamed term pulls back
to a reduction chain from the source to the left-inverse image of the endpoint.  Each step is reflected
by the single-step pullback; the round-trips on intermediate terms collapse the same way. -/
theorem StepStar.renamePullbackOfLeftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {sourceTerm : RawTerm sourceScope} {renamedReduct : RawTerm targetScope}
    (renamedChain : StepStar (RawTerm.rename forwardRenaming sourceTerm) renamedReduct) :
    StepStar sourceTerm (RawTerm.rename leftInverseRenaming renamedReduct) := by
  have pulledChain := StepStar.rename leftInverseRenaming renamedChain
  have roundTrip :
      RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming sourceTerm) = sourceTerm := by
    rw [RawTerm.rename_compose forwardRenaming leftInverseRenaming sourceTerm]
    have composeIsIdentity :
        RawRenaming.PointwiseEq
          (RawRenaming.compose forwardRenaming leftInverseRenaming)
          (RawRenaming.identity (scope := sourceScope)) := by
      intro position
      simp only [RawRenaming.compose, RawRenaming.identity]
      exact leftInverseProperty position
    rw [RawTerm.rename_pointwise composeIsIdentity sourceTerm]
    exact RawTerm.rename_identity_apply sourceTerm
  rw [roundTrip] at pulledChain
  exact pulledChain

end FX1Poly.Core
