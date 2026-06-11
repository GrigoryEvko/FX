import FX1Poly.Core.WeakHeadStep
import FX1Poly.Core.RawTermSubst0Commute

/-! # Foundation/PolyCell/Core/WeakHeadStepSubst
    — the complete weak-head reduction commutes with substitution

`HeadStep.subst` (`HeadStepCommute`) shows the β-only weak-head step commutes with a parallel
substitution.  The dependent reducibility relation dispatches on the COMPLETE weak-head reduction
`WeakHeadStep` (β + root-ι + scrutinee-congruence), and the fundamental theorem — interpreting a
well-typed term under a reducible closing substitution — reasons about how the substituted term reduces.
This file lifts substitution-commutation to the full relation.

  * `IotaHeadStep.subst` — root-ι commutes with substitution.  Most ι contracta are Church-encoded (a
    reshuffling of the redex's children into nested applications, NO `subst0`; see the redex/contractum
    pairs in `IotaHeadStep`), so substitution distributes through both redex and contractum definitionally
    and those rules transport by a bare constructor application.  The TWO substituting ι rules
    (`iotaNatElimSucc` / `iotaNatRecSucc`, whose Phase-Z contractum substitutes the recursive call and
    predecessor into the two-binder succ-branch) instead rewrite by the two-binder commute helper
    `RawTerm.natSuccElim_subst_commute` before the constructor application.

  * `WeakHeadStep.subst` — the complete weak-head reduction commutes with substitution.  `beta` reshapes
    its contractum by `RawTerm.subst0_subst_commute` (the head β-redex's `subst0` interacts with the outer
    substitution); `appCongruence` and the ten `scrutineeCong` rules transport by the induction hypothesis
    under the substituted application / eliminator; `rootIota` delegates to `IotaHeadStep.subst`.

This is a reduction-substrate prerequisite for the fundamental theorem (and for any substitution lemma on
the dependent reducibility relation).

## Zero-axiom verification

`induction` on the ι / weak-head derivation; the β contractum rewritten by `RawTerm.subst0_subst_commute`,
every other arm a constructor on the induction hypothesis (or `IotaHeadStep.subst`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **A `cons`-extended substitution annihilates an outer weakening.**

`subst (cons head tail) (weaken sourceTerm) = subst tail sourceTerm`: the fresh binder slot the weakening
introduces is exactly the slot `cons` fills, so they cancel.  Proved locally (the `RawTermSubstConsCommute`
analog `RawTerm.weaken_subst_cons` lives above this file's import frontier) by `weaken = rename weaken`,
`rename_subst_commute`, and the `rfl`-pointwise `(cons head tail) ∘ weaken = tail`. -/
theorem RawTerm.weaken_subst_cons_local {scope targetScope : Nat}
    (sourceTerm : RawTerm scope) (headTerm : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons headTerm tailSubst)
        (RawTerm.weaken sourceTerm) =
      RawTerm.subst tailSubst sourceTerm := by
  rw [RawTerm.weaken_eq_rename]
  rw [RawTerm.rename_subst_commute RawRenaming.weaken
    (RawTermSubst.cons headTerm tailSubst) sourceTerm]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound => rfl

/-- **The two-binder succ-iota contractum commutes with an outer substitution.**

The Phase-Z natElim/natRec succ-iota substitutes into a two-binder succ-branch via
`cons recursiveCall (singleton predecessor)` (`var 0 := recursiveCall`, `var 1 := predecessor`).
Pushing an outer parallel substitution `sigma` through that contractum lifts `sigma` twice for the
succ-branch (`iterateLiftRaw sigma 2`) and substitutes `sigma` into each substituent:

  `subst sigma (subst (cons recCall (singleton pred)) succBranch)
     = subst (cons (subst sigma recCall) (singleton (subst sigma pred)))
             (subst (iterateLiftRaw sigma 2) succBranch)`.

The two-binder analog of `RawTerm.subst0_subst_commute` / `RawTerm.subst_cons_eq_subst0_lift`, proved by
the identical `subst_compose` + `subst_pointwise` template: at positions 0 and 1 both sides hit the consed
head / singleton head (`rfl` after unfolding); at `k + 2` both reduce to `sigma k` (the two lifted
weakenings cancel against the cons and singleton heads via `RawTerm.weaken_subst_singleton`). -/
theorem RawTerm.natSuccElim_subst_commute {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (recursiveCall predecessor : RawTerm sourceScope)
    (succBranch : RawTerm (sourceScope + 2)) :
    RawTerm.subst sigma
        (RawTerm.subst
          (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
          succBranch) =
      RawTerm.subst
        (RawTermSubst.cons
          (RawTerm.subst sigma recursiveCall)
          (RawTermSubst.singleton (RawTerm.subst sigma predecessor)))
        (RawTerm.subst (iterateLiftRaw sigma 2) succBranch) := by
  rw [RawTerm.subst_compose
    (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor)) sigma succBranch]
  rw [RawTerm.subst_compose (iterateLiftRaw sigma 2)
    (RawTermSubst.cons
      (RawTerm.subst sigma recursiveCall)
      (RawTermSubst.singleton (RawTerm.subst sigma predecessor)))
    succBranch]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ =>
      -- LHS = subst σ ((cons R (singleton P)) 0) = subst σ R.
      -- RHS = subst (cons (subst σ R) _) ((iterateLiftRaw σ 2) 0)
      --     = subst (cons (subst σ R) _) (var 0) = subst σ R.
      rfl
  | ⟨1, _⟩ =>
      -- LHS = subst σ ((cons R (singleton P)) 1) = subst σ ((singleton P) 0) = subst σ P.
      -- RHS = subst (cons _ (singleton (subst σ P))) ((iterateLiftRaw σ 2) 1)
      --     = subst (cons _ (singleton (subst σ P))) (weaken (var 0))
      --     = subst (cons _ (singleton (subst σ P))) (var 1)
      --     = (singleton (subst σ P)) 0 = subst σ P.
      rfl
  | ⟨priorValue + 2, positionBound⟩ =>
      have innerBound : priorValue < sourceScope :=
        Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ positionBound)
      show RawTerm.subst sigma
            ((RawTermSubst.cons recursiveCall
              (RawTermSubst.singleton predecessor)) ⟨priorValue + 2, positionBound⟩) =
          RawTerm.subst
            (RawTermSubst.cons
              (RawTerm.subst sigma recursiveCall)
              (RawTermSubst.singleton (RawTerm.subst sigma predecessor)))
            ((iterateLiftRaw sigma 2) ⟨priorValue + 2, positionBound⟩)
      have lhsReduces :
          RawTerm.subst sigma
              ((RawTermSubst.cons recursiveCall
                (RawTermSubst.singleton predecessor)) ⟨priorValue + 2, positionBound⟩) =
            sigma ⟨priorValue, innerBound⟩ := rfl
      have rhsLift :
          (iterateLiftRaw sigma 2) ⟨priorValue + 2, positionBound⟩ =
            RawTerm.weaken (RawTerm.weaken (sigma ⟨priorValue, innerBound⟩)) := rfl
      rw [lhsReduces, rhsLift,
        RawTerm.weaken_subst_cons_local
          (RawTerm.weaken (sigma ⟨priorValue, innerBound⟩))
          (RawTerm.subst sigma recursiveCall)
          (RawTermSubst.singleton (RawTerm.subst sigma predecessor)),
        RawTerm.weaken_subst_singleton
          (sigma ⟨priorValue, innerBound⟩) (RawTerm.subst sigma predecessor)]

/-- **Root-ι reduction commutes with substitution.**  Most ι contracta are Church-encoded reshufflings
of the redex's children (no `subst0`), so substitution distributes through both sides and those rules
transport by their own constructor.  The two substituting succ-iotas (`iotaNatElimSucc` /
`iotaNatRecSucc`) rewrite by `RawTerm.natSuccElim_subst_commute` first. -/
theorem IotaHeadStep.subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (iotaStep : IotaHeadStep term reduct) :
    IotaHeadStep (RawTerm.subst substitution term) (RawTerm.subst substitution reduct) := by
  induction iotaStep with
  | iotaBoolTrue => exact IotaHeadStep.iotaBoolTrue
  | iotaBoolFalse => exact IotaHeadStep.iotaBoolFalse
  | iotaFstPair => exact IotaHeadStep.iotaFstPair
  | iotaSndPair => exact IotaHeadStep.iotaSndPair
  | iotaNatElimZero => exact IotaHeadStep.iotaNatElimZero
  | iotaNatRecZero => exact IotaHeadStep.iotaNatRecZero
  | iotaListElimNil => exact IotaHeadStep.iotaListElimNil
  | iotaOptionMatchNone => exact IotaHeadStep.iotaOptionMatchNone
  | iotaOptionMatchSome => exact IotaHeadStep.iotaOptionMatchSome
  | iotaEitherMatchInl => exact IotaHeadStep.iotaEitherMatchInl
  | iotaEitherMatchInr => exact IotaHeadStep.iotaEitherMatchInr
  | iotaNatElimSucc =>
      rw [RawTerm.natSuccElim_subst_commute]; exact IotaHeadStep.iotaNatElimSucc
  | iotaNatRecSucc =>
      rw [RawTerm.natSuccElim_subst_commute]; exact IotaHeadStep.iotaNatRecSucc
  | iotaListElimCons => exact IotaHeadStep.iotaListElimCons
  | iotaIdJRefl => exact IotaHeadStep.iotaIdJRefl
  | iotaIdStrictRecRefl => exact IotaHeadStep.iotaIdStrictRecRefl

/-- **The complete weak-head reduction commutes with substitution.**  `beta` reshapes its `subst0`
contractum by `RawTerm.subst0_subst_commute`; `appCongruence` / `scrutineeCong` transport by the induction
hypothesis; `rootIota` by `IotaHeadStep.subst`. -/
theorem WeakHeadStep.subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (weakHeadStep : WeakHeadStep term reduct) :
    WeakHeadStep (RawTerm.subst substitution term) (RawTerm.subst substitution reduct) := by
  induction weakHeadStep with
  | beta => rw [RawTerm.subst0_subst_commute]; exact WeakHeadStep.beta
  | appCongruence _functionStep functionInductiveHypothesis =>
      exact WeakHeadStep.appCongruence functionInductiveHypothesis
  | rootIota iotaStep => exact WeakHeadStep.rootIota (iotaStep.subst substitution)
  | scrutineeBoolElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeBoolElim scrutineeInductiveHypothesis
  | scrutineeFst _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeFst scrutineeInductiveHypothesis
  | scrutineeSnd _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeSnd scrutineeInductiveHypothesis
  | scrutineeNatElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeNatElim scrutineeInductiveHypothesis
  | scrutineeNatRec _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeNatRec scrutineeInductiveHypothesis
  | scrutineeListElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeListElim scrutineeInductiveHypothesis
  | scrutineeOptionMatch _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeOptionMatch scrutineeInductiveHypothesis
  | scrutineeEitherMatch _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeEitherMatch scrutineeInductiveHypothesis
  | scrutineeIdJ _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeIdJ scrutineeInductiveHypothesis
  | scrutineeIdStrictRec _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeIdStrictRec scrutineeInductiveHypothesis

end FX1Poly.Core
