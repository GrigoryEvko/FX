import FX1Poly.Core.CdLemma
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepBetaEtaPreservesShape

/-! # Foundation/PolyCell/Core/StepEtaCriticalPairs

First betaEta confluence interface for the raw eta cascade.

The current `Step.betaEta` relation is the sum of:

* the existing beta+iota `Step` relation, including its congruence rule;
* root-only `Step.eta`.

It does not add eta congruence under arbitrary generator children.
Consequently, classical examples such as reducing eta under an outer
application are not one-step branchings in this formal relation.
This file provides the foundation: the betaEta join shape, closure
embeddings from beta+iota `StepStar`, and the beta-only fragment of the
betaEta local Church-Rosser theorem.
-/

namespace FX1Poly.Core

-- `RawRenaming` lives in `FX1Poly.Foundation`, which does not enclose
-- `FX1Poly.Core`, so open it explicitly.
open FX1Poly.Foundation

namespace RawTermSubst

/-- Substituting the newest variable after a weakening lifted under one
binder is pointwise identity.

This is the computational heart of the eta-lambda beta-overlap: the
inner lambda body is weakened under the eta binder, then beta substitutes
the eta binder's newest variable back into the body. -/
theorem lift_weaken_then_singleton_newest_pointwise {scope : Nat} :
    RawTermSubst.PointwiseEq
      (RawRenaming.thenSubst
        (RawRenaming.lift (RawRenaming.weaken (scope := scope)))
        (RawTermSubst.singleton
          (RawTerm.newestVar (scope := scope))))
      (RawTermSubst.identity (scope := scope + 1)) := by
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero => rfl
      | succ _priorPosition => rfl

end RawTermSubst

namespace RawTerm

/-- Weakening a lambda preserves the lambda head and lifts weakening under
the lambda binder. -/
theorem weaken_lam {scope : Nat} (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) :
    RawTerm.weaken
        (RawTerm.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) =
      RawTerm.mkGen .gen_lam ()
        (.childCons
          (RawTerm.rename RawRenaming.weaken domainAnn)
          (.childCons
            (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body)
            .childNil)) := by
  rw [RawTerm.weaken_eq_rename]
  rw [RawTerm.rename_nonVar_reduces RawRenaming.weaken
    (by decide : Generator.gen_lam ≠ .gen_var)]
  rfl

/-- If weakening a source-scope term has lambda shape, the source term was
already a lambda and the weakened body is the binder-lifted weakening of its
source body. -/
theorem weaken_eq_lam_implies_source_lam {scope : Nat}
    {innerFunction : RawTerm scope}
    {weakenedDomain : RawTerm (scope + 1)}
    {weakenedBody : RawTerm (scope + 2)}
    (weakenedEq :
      RawTerm.weaken innerFunction =
        RawTerm.mkGen .gen_lam ()
          (.childCons weakenedDomain (.childCons weakenedBody .childNil))) :
    ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
      innerFunction =
          RawTerm.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons body .childNil)) ∧
        weakenedDomain = RawTerm.rename RawRenaming.weaken domainAnn ∧
        weakenedBody =
          RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body := by
  cases innerFunction with
  | mkGen generator payload children =>
      by_cases generatorIsVar : generator = .gen_var
      · subst generator
        dsimp [RawTerm.weaken, RawTerm.rename, fold] at weakenedEq
        cases weakenedEq
      · by_cases generatorIsLam : generator = .gen_lam
        · subst generator
          cases payload
          cases children with
          | childCons domainHead rest =>
              cases rest with
              | childCons bodyHead restTail =>
                  cases restTail
                  rw [RawTerm.weaken_lam] at weakenedEq
                  injection weakenedEq with _ _ _ childrenEq
                  injection childrenEq with _ _ _ childDomainEq childrenTailEq
                  injection childrenTailEq with _ _ _ childBodyEq _
                  exact ⟨domainHead, bodyHead, rfl, childDomainEq.symm, childBodyEq.symm⟩
        · rw [RawTerm.weaken_eq_rename] at weakenedEq
          rw [RawTerm.rename_nonVar_reduces RawRenaming.weaken
            generatorIsVar] at weakenedEq
          injection weakenedEq
          exact False.elim (generatorIsLam (by assumption))

/-- Beta-substitution of the newest variable cancels a one-binder-lifted
weakening.

Used by the eta-lambda beta-overlap diamond. -/
theorem subst0_lift_weaken_newestVar {scope : Nat}
    (body : RawTerm (scope + 1)) :
    RawTerm.subst0
        (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body)
        (RawTerm.newestVar (scope := scope)) =
      body := by
  unfold RawTerm.subst0
  rw [RawTerm.rename_subst_commute]
  rw [RawTerm.subst_pointwise
    RawTermSubst.lift_weaken_then_singleton_newest_pointwise body]
  exact RawTerm.subst_identity_apply body

end RawTerm

namespace Step
namespace betaEtaStar

/-- Embed a beta+iota `StepStar` chain into the beta+iota+eta closure. -/
theorem ofStepStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : StepStar sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm := by
  induction chain with
  | refl term =>
      exact Step.betaEtaStar.refl term
  | trans headStep _ tailIH =>
      exact Step.betaEtaStar.trans (Or.inl headStep) tailIH

/-- Embed an eta-only `etaStar` chain into the beta+iota+eta closure. -/
theorem ofEtaStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.etaStar sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm := by
  induction chain with
  | refl term =>
      exact Step.betaEtaStar.refl term
  | trans headStep _ tailIH =>
      exact Step.betaEtaStar.trans (Or.inr headStep) tailIH

end betaEtaStar
end Step

/-- The local join shape for two one-step beta+iota-or-eta reductions from
the same source. -/
def BetaEtaPairJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (_leftStep : Step.betaEta sourceTerm leftReduct)
    (_rightStep : Step.betaEta sourceTerm rightReduct) : Prop :=
  ∃ commonReduct : RawTerm scope,
    Step.betaEtaStar leftReduct commonReduct ∧
      Step.betaEtaStar rightReduct commonReduct

/-- Target statement for local Church-Rosser over the betaEta
one-step relation.  Intentionally separate from `CdLemmaStatement`,
which is the beta+iota-only theorem. -/
def CdLemmaStatementBetaEta : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    (leftStep : Step.betaEta sourceTerm leftReduct) →
    (rightStep : Step.betaEta sourceTerm rightReduct) →
    BetaEtaPairJoin leftStep rightStep

/-- Mixed local Church-Rosser statement for a beta+iota step against a
root-eta step.  The eta-vs-eta quadrant is deliberately separate. -/
def CdLemmaStatementStepEta : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    (leftStep : Step sourceTerm leftReduct) →
    (rightStep : Step.eta sourceTerm rightReduct) →
    BetaEtaPairJoin (Or.inl leftStep) (Or.inr rightStep)

/-- Reverse mixed local Church-Rosser statement: root eta against a
beta+iota step. -/
def CdLemmaStatementEtaStep : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    (leftStep : Step.eta sourceTerm leftReduct) →
    (rightStep : Step sourceTerm rightReduct) →
    BetaEtaPairJoin (Or.inr leftStep) (Or.inl rightStep)

namespace BetaEtaPairJoin

/-- Same-reduct closure for betaEta local joins. -/
theorem ofReductsEqual {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step.betaEta sourceTerm leftReduct}
    {rightStep : Step.betaEta sourceTerm rightReduct}
    (reductsEqual : leftReduct = rightReduct) :
    BetaEtaPairJoin leftStep rightStep := by
  cases reductsEqual
  exact ⟨leftReduct, Step.betaEtaStar.refl _,
    Step.betaEtaStar.refl _⟩

/-- A betaEta step trivially joins with itself. -/
theorem sameStep {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (sameStepWitness : Step.betaEta sourceTerm targetTerm) :
    BetaEtaPairJoin sameStepWitness sameStepWitness :=
  ofReductsEqual rfl

/-- Reverse the two branches of a betaEta local join. -/
theorem swap {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step.betaEta sourceTerm leftReduct}
    {rightStep : Step.betaEta sourceTerm rightReduct} :
    BetaEtaPairJoin leftStep rightStep →
      BetaEtaPairJoin rightStep leftStep :=
  fun join =>
    Exists.elim join
      (fun commonReduct chains =>
        ⟨commonReduct, chains.2, chains.1⟩)

/-- Lift an existing beta+iota local join into the betaEta join shape. -/
theorem ofStepPairJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct}
    (join : StepPairJoin leftStep rightStep) :
    BetaEtaPairJoin (Or.inl leftStep) (Or.inl rightStep) :=
  Exists.elim join
    (fun commonReduct chains =>
      ⟨ commonReduct
      , Step.betaEtaStar.ofStepStar chains.1
      , Step.betaEtaStar.ofStepStar chains.2 ⟩)

/-- The beta+iota `cd_lemma` covers the beta-only fragment of the
betaEta local Church-Rosser theorem. -/
theorem ofCdLemmaForStepSteps {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    BetaEtaPairJoin (Or.inl leftStep) (Or.inl rightStep) :=
  ofStepPairJoin (cd_lemma leftStep rightStep)

/-- Eta-pair versus a beta+iota step inside the first projected occurrence.

Source:
`pair (fst pairTerm) (snd pairTerm)`.

Left branch reduces the `pairTerm` under `fst`; right branch contracts
eta-pair at the root.  The join first reduces the remaining `pairTerm`
under `snd`, then contracts eta-pair for `updatedPairTerm`. -/
theorem etaPairFirstCong {scope : Nat}
    {pairTerm updatedPairTerm : RawTerm scope}
    (pairStep : Step pairTerm updatedPairTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pair ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons
              (.mkGen .gen_snd ()
                (.childCons pairTerm .childNil))
              .childNil) : RawTermChildren [0] scope)
            (Step.cong .gen_fst ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                pairStep)))))
      (Or.inr (Step.eta.etaPair pairTerm)) := by
  exact
    ⟨ updatedPairTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_pair ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.mkGen .gen_fst ()
                (.childCons updatedPairTerm .childNil)) : RawTerm scope)
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                (Step.cong .gen_snd ()
                  (StepChildren.here
                    (parentScope := scope) (headShift := 0)
                    (restShifts := [])
                    (.childNil : RawTermChildren [] scope)
                    pairStep))))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaPair updatedPairTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl pairStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-pair versus a beta+iota step inside the second projected occurrence.

This is the symmetric sibling of `etaPairFirstCong`: the left branch
reduces under `snd`, while the join replays the same step under `fst`
before contracting eta-pair. -/
theorem etaPairSecondCong {scope : Nat}
    {pairTerm updatedPairTerm : RawTerm scope}
    (pairStep : Step pairTerm updatedPairTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pair ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.mkGen .gen_fst ()
              (.childCons pairTerm .childNil)) : RawTerm scope)
            (StepChildren.here
              (parentScope := scope) (headShift := 0)
              (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.cong .gen_snd ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  pairStep))))))
      (Or.inr (Step.eta.etaPair pairTerm)) := by
  exact
    ⟨ updatedPairTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_pair ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons
                (.mkGen .gen_snd ()
                  (.childCons updatedPairTerm .childNil))
                .childNil) : RawTermChildren [0] scope)
              (Step.cong .gen_fst ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  pairStep)))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaPair updatedPairTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl pairStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-pair versus direct `fst (pair firstValue secondValue)` iota in
the first projected occurrence.

Source:
`pair (fst (pair firstValue secondValue))
      (snd (pair firstValue secondValue))`.

The iota branch reduces the first projection.  The join reduces the
remaining second projection, reaching the same explicit pair as root
eta-pair. -/
theorem etaPairFirstProjectionIota {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pair ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons
              (.mkGen .gen_snd ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons firstValue
                      (.childCons secondValue .childNil)))
                  .childNil))
              .childNil) : RawTermChildren [0] scope)
            (Step.iotaFstPair
              (firstValue := firstValue) (secondValue := secondValue)))))
      (Or.inr
        (Step.eta.etaPair
          (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil))))) := by
  exact
    ⟨ (.mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil)))
      , Step.betaEtaStar.trans
          (Or.inl
            (Step.cong .gen_pair ()
              (StepChildren.there
                (parentScope := scope) (headShift := 0) (restShifts := [0])
                firstValue
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  (Step.iotaSndPair
                    (firstValue := firstValue)
                    (secondValue := secondValue))))))
          (Step.betaEtaStar.refl _)
      , Step.betaEtaStar.refl _ ⟩

/-- Eta-pair versus direct `snd (pair firstValue secondValue)` iota in
the second projected occurrence.

This is the symmetric sibling of `etaPairFirstProjectionIota`: the iota
branch reduces the second projection, and the join reduces the remaining
first projection before meeting the eta branch. -/
theorem etaPairSecondProjectionIota {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pair ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.mkGen .gen_fst ()
              (.childCons
                (.mkGen .gen_pair ()
                  (.childCons firstValue
                    (.childCons secondValue .childNil)))
                .childNil)) : RawTerm scope)
            (StepChildren.here
              (parentScope := scope) (headShift := 0)
              (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.iotaSndPair
                (firstValue := firstValue) (secondValue := secondValue))))))
      (Or.inr
        (Step.eta.etaPair
          (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil))))) := by
  exact
    ⟨ (.mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil)))
      , Step.betaEtaStar.trans
          (Or.inl
            (Step.cong .gen_pair ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [0])
                ((.childCons secondValue .childNil) :
                  RawTermChildren [0] scope)
                (Step.iotaFstPair
                  (firstValue := firstValue)
                  (secondValue := secondValue)))))
          (Step.betaEtaStar.refl _)
      , Step.betaEtaStar.refl _ ⟩

/-- Resolver-facing eta-pair arm for any beta+iota `Step` leaving the
eta-pair source.

The only possible beta+iota steps from
`pair (fst pairTerm) (snd pairTerm)` are:

* a reduction inside the `pairTerm` occurrence under `fst`;
* a reduction inside the `pairTerm` occurrence under `snd`;
* direct `fst (pair firstValue secondValue)` iota;
* direct `snd (pair firstValue secondValue)` iota.

Those four shapes delegate to the audited primitive joins above. -/
theorem etaPairLeftStep {scope : Nat}
    {pairTerm leftReduct : RawTerm scope}
    (leftStep : Step (RawTerm.etaPairSource pairTerm) leftReduct) :
    BetaEtaPairJoin
      (Or.inl leftStep)
      (Or.inr (Step.eta.etaPair pairTerm)) := by
  cases leftStep with
  | cong _ _ pairChildrenStep =>
      cases pairChildrenStep with
      | here _ firstProjectionStep =>
          cases firstProjectionStep with
          | iotaFstPair =>
              exact etaPairFirstProjectionIota _ _
          | cong _ _ firstProjectionChildrenStep =>
              cases firstProjectionChildrenStep with
              | here _ pairStep =>
                  exact etaPairFirstCong pairStep
              | there _ emptyTailStep =>
                  cases emptyTailStep
      | there _ tailStep =>
          cases tailStep with
          | here _ secondProjectionStep =>
              cases secondProjectionStep with
              | iotaSndPair =>
                  exact etaPairSecondProjectionIota _ _
              | cong _ _ secondProjectionChildrenStep =>
                  cases secondProjectionChildrenStep with
                  | here _ pairStep =>
                      exact etaPairSecondCong pairStep
                  | there _ emptyTailStep =>
                      cases emptyTailStep
          | there _ emptyTailStep =>
              cases emptyTailStep

/-- Reverse orientation of `etaPairLeftStep`, for dispatcher arms where
root eta-pair is the left branch and beta+iota `Step` is the right
branch. -/
theorem etaPairRightStep {scope : Nat}
    {pairTerm rightReduct : RawTerm scope}
    (rightStep : Step (RawTerm.etaPairSource pairTerm) rightReduct) :
    BetaEtaPairJoin
      (Or.inr (Step.eta.etaPair pairTerm))
      (Or.inl rightStep) :=
  swap (etaPairLeftStep rightStep)

/-- Eta-modal-intro versus a beta+iota step inside the eliminated modal
occurrence.

Source:
`modIntro (modElim modalTerm)`.

The congruence branch reduces under `modElim`; the eta branch contracts
the source to `modalTerm`.  The join contracts eta for the updated modal
term on the congruence side and replays the original step on the eta side. -/
theorem etaModIntroCong {scope : Nat}
    {modalTerm updatedModalTerm : RawTerm scope}
    (modalStep : Step modalTerm updatedModalTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_modIntro ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_modElim ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                modalStep)))))
      (Or.inr (Step.eta.etaModIntro modalTerm)) := by
  exact
    ⟨ updatedModalTerm
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaModIntro updatedModalTerm))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl modalStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-Glue-intro versus a beta+iota step inside the eliminated Glue
occurrence.

Source:
`glueIntro (glueElim gluedTerm) gluedTerm`.

The left branch reduces the first occurrence under `glueElim`; the join
replays the same step at the second occurrence and then contracts eta for
the updated Glue term. -/
theorem etaGlueIntroFirstCong {scope : Nat}
    {gluedTerm updatedGluedTerm : RawTerm scope}
    (gluedStep : Step gluedTerm updatedGluedTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_glueIntro ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons gluedTerm .childNil) :
              RawTermChildren [0] scope)
            (Step.cong .gen_glueElim ()
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                gluedStep)))))
      (Or.inr (Step.eta.etaGlueIntro gluedTerm)) := by
  exact
    ⟨ updatedGluedTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_glueIntro ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.mkGen .gen_glueElim ()
                (.childCons updatedGluedTerm .childNil)) : RawTerm scope)
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                gluedStep))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaGlueIntro updatedGluedTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl gluedStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-Glue-intro versus a beta+iota step inside the direct Glue
occurrence.

This is the symmetric sibling of `etaGlueIntroFirstCong`: the left branch
reduces the second occurrence, while the join replays the same step under
`glueElim` before contracting eta. -/
theorem etaGlueIntroSecondCong {scope : Nat}
    {gluedTerm updatedGluedTerm : RawTerm scope}
    (gluedStep : Step gluedTerm updatedGluedTerm) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_glueIntro ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.mkGen .gen_glueElim ()
              (.childCons gluedTerm .childNil)) : RawTerm scope)
            (StepChildren.here
              (parentScope := scope) (headShift := 0)
              (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              gluedStep))))
      (Or.inr (Step.eta.etaGlueIntro gluedTerm)) := by
  exact
    ⟨ updatedGluedTerm
    , Step.betaEtaStar.trans
        (Or.inl
          (Step.cong .gen_glueIntro ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons updatedGluedTerm .childNil) :
                RawTermChildren [0] scope)
              (Step.cong .gen_glueElim ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  gluedStep)))))
        (Step.betaEtaStar.trans
          (Or.inr (Step.eta.etaGlueIntro updatedGluedTerm))
          (Step.betaEtaStar.refl _))
    , Step.betaEtaStar.trans (Or.inl gluedStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Resolver-facing eta-modal-intro arm for any beta+iota `Step`
leaving the eta-modal source.

The current raw relation has no root rule for `modElim`, so the only
possible beta+iota step from `modIntro (modElim modalTerm)` reduces
inside `modalTerm` under `modElim`; the primitive join is
`etaModIntroCong`. -/
theorem etaModIntroLeftStep {scope : Nat}
    {modalTerm leftReduct : RawTerm scope}
    (leftStep : Step (RawTerm.etaModIntroSource modalTerm) leftReduct) :
    BetaEtaPairJoin
      (Or.inl leftStep)
      (Or.inr (Step.eta.etaModIntro modalTerm)) := by
  cases leftStep with
  | cong _ _ introChildrenStep =>
      cases introChildrenStep with
      | here _ elimStep =>
          cases elimStep with
          | cong _ _ elimChildrenStep =>
              cases elimChildrenStep with
              | here _ modalStep =>
                  exact etaModIntroCong modalStep
              | there _ emptyTailStep =>
                  cases emptyTailStep
      | there _ emptyTailStep =>
          cases emptyTailStep

/-- Reverse orientation of `etaModIntroLeftStep`. -/
theorem etaModIntroRightStep {scope : Nat}
    {modalTerm rightReduct : RawTerm scope}
    (rightStep : Step (RawTerm.etaModIntroSource modalTerm) rightReduct) :
    BetaEtaPairJoin
      (Or.inr (Step.eta.etaModIntro modalTerm))
      (Or.inl rightStep) :=
  swap (etaModIntroLeftStep rightStep)

/-- Resolver-facing eta-Glue-intro arm for any beta+iota `Step` leaving
the eta-Glue source.

Current `Step` can reduce either the occurrence under `glueElim` or the
direct second occurrence of the same Glue term.  Both are delegated to
the primitive Glue eta/congruence joins above. -/
theorem etaGlueIntroLeftStep {scope : Nat}
    {gluedTerm leftReduct : RawTerm scope}
    (leftStep : Step (RawTerm.etaGlueIntroSource gluedTerm) leftReduct) :
    BetaEtaPairJoin
      (Or.inl leftStep)
      (Or.inr (Step.eta.etaGlueIntro gluedTerm)) := by
  cases leftStep with
  | cong _ _ introChildrenStep =>
      cases introChildrenStep with
      | here _ elimStep =>
          cases elimStep with
          | cong _ _ elimChildrenStep =>
              cases elimChildrenStep with
              | here _ gluedStep =>
                  exact etaGlueIntroFirstCong gluedStep
              | there _ emptyTailStep =>
                  cases emptyTailStep
      | there _ tailStep =>
          cases tailStep with
          | here _ gluedStep =>
              exact etaGlueIntroSecondCong gluedStep
          | there _ emptyTailStep =>
              cases emptyTailStep

/-- Reverse orientation of `etaGlueIntroLeftStep`. -/
theorem etaGlueIntroRightStep {scope : Nat}
    {gluedTerm rightReduct : RawTerm scope}
    (rightStep : Step (RawTerm.etaGlueIntroSource gluedTerm) rightReduct) :
    BetaEtaPairJoin
      (Or.inr (Step.eta.etaGlueIntro gluedTerm))
      (Or.inl rightStep) :=
  swap (etaGlueIntroLeftStep rightStep)

/-- **The Nederpelt diagonal guard.**  IF the eta-expanded function is itself an
annotated lambda, its annotation matches the eta binder's annotation.  Without this
guard the eta-beta overlap is genuinely NON-JOINABLE in the raw calculus: the source
`lam A (app (weaken (lam B b)) var0)` contracts to `lam A b` by the inner beta and to
`lam B b` by the root eta — distinct stuck terms for normal `A != B`.  Church-style
annotations break RAW beta-eta local confluence (Nederpelt); the typed layer is
unaffected, since typing forces the two annotations convertible. -/
def EtaLamAnnotationDiagonal {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) : Prop :=
  ∀ (innerDomainAnn : RawTerm scope) (innerBody : RawTerm (scope + 1)),
    innerFunction =
      .mkGen .gen_lam ()
        (.childCons innerDomainAnn (.childCons innerBody .childNil)) →
    innerDomainAnn = domainAnn

/-- A function that is not lambda-shaped satisfies the diagonal guard vacuously — the
case every iota-headed or neutral-headed eta-expansion consumer needs (the shape
refutation is one `Generator.noConfusion` at the call site). -/
theorem EtaLamAnnotationDiagonal.ofNotLamShape {scope : Nat}
    {domainAnn innerFunction : RawTerm scope}
    (notLamShaped :
      ∀ (innerDomainAnn : RawTerm scope) (innerBody : RawTerm (scope + 1)),
        innerFunction ≠
          .mkGen .gen_lam ()
            (.childCons innerDomainAnn (.childCons innerBody .childNil))) :
    EtaLamAnnotationDiagonal domainAnn innerFunction :=
  fun innerDomainAnn innerBody innerFunctionEq =>
    absurd innerFunctionEq (notLamShaped innerDomainAnn innerBody)

/-- The matching-annotation lambda satisfies the diagonal guard — the joinable
diagonal instance. -/
theorem EtaLamAnnotationDiagonal.ofMatchingLam {scope : Nat}
    {domainAnn : RawTerm scope} {innerBody : RawTerm (scope + 1)} :
    EtaLamAnnotationDiagonal domainAnn
      (.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons innerBody .childNil))) := by
  intro otherDomainAnn otherBody innerFunctionEq
  injection innerFunctionEq with _ _ _ childrenEq
  injection childrenEq with _ _ _ domainEq _
  exact domainEq.symm

/-- Eta-lambda versus beta at the eta body's application root, ON THE DIAGONAL.

When the eta-expanded function is itself a lambda WITH THE SAME annotation, the body
`app (weaken (lam domainAnn body)) newestVar` beta-reduces under the outer eta
lambda to `body`, so the whole reduct is definitionally joined with
the root eta branch after the substitution-cancellation lemma above.  Off the
diagonal the pair is NON-JOINABLE — see `EtaLamAnnotationDiagonal`. -/
theorem etaLamBodyBeta {scope : Nat}
    (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1)) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.there (parentScope := scope) (headShift := 0)
              (restShifts := [1]) domainAnn
            (StepChildren.here
              (parentScope := scope) (headShift := 1) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.beta
                (domainAnn :=
                  RawTerm.rename RawRenaming.weaken domainAnn)
                (body :=
                  RawTerm.rename (RawRenaming.lift RawRenaming.weaken)
                    body)
                (arg := RawTerm.newestVar (scope := scope)))))))
      (Or.inr
        (Step.eta.etaLam domainAnn
          (RawTerm.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons body .childNil))))) := by
  apply ofReductsEqual
  change
    (RawTerm.mkGen .gen_lam ()
      (.childCons domainAnn
        (.childCons
          (RawTerm.subst0
            (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body)
            (RawTerm.newestVar (scope := scope)))
          .childNil))) =
      (RawTerm.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons body .childNil)))
  rw [RawTerm.subst0_lift_weaken_newestVar]

/-- Eta-lambda versus a beta+iota step replayed through the weakened
function occurrence.

Source:
`lam (app (weaken innerFunction) newestVar)`.

When the inner function itself steps, the congruence branch replays that
step under weakening in the function slot of the eta source.  The join
contracts eta for the updated function on the congruence side and replays
the original function step on the eta side. -/
theorem etaLamFunctionCong {scope : Nat}
    (domainAnn : RawTerm scope)
    {innerFunction updatedFunction : RawTerm scope}
    (functionStep : Step innerFunction updatedFunction) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.there (parentScope := scope) (headShift := 0)
              (restShifts := [1]) domainAnn
            (StepChildren.here
              (parentScope := scope) (headShift := 1) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.cong .gen_app ()
                (StepChildren.here
                  (parentScope := scope + 1) (headShift := 0)
                  (restShifts := [0])
                  ((.childCons RawTerm.newestVar .childNil) :
                    RawTermChildren [0] (scope + 1))
                  (Step.weaken functionStep)))))))
      (Or.inr (Step.eta.etaLam domainAnn innerFunction)) := by
  exact
    ⟨ updatedFunction
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaLam domainAnn updatedFunction))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl functionStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-path-lambda versus a beta+iota step replayed through the weakened
path occurrence.

This is the cubical-path sibling of `etaLamFunctionCong`, using the
current raw `pathLam/pathApp` eta source. -/
theorem etaPathLamFunctionCong {scope : Nat}
    {innerPath updatedPath : RawTerm scope}
    (pathStep : Step innerPath updatedPath) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pathLam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_pathApp ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                (Step.weaken pathStep))))))
      (Or.inr (Step.eta.etaPathLam innerPath)) := by
  exact
    ⟨ updatedPath
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaPathLam updatedPath))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl pathStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-lambda versus an arbitrary under-binder function congruence step,
provided that the reduct strengthens back to a source-scope reduct.

This is the resolver-facing version of `etaLamFunctionCong`: it does not
assume the under-binder step was syntactically built by `Step.weaken`.
Instead, it consumes the exact strengthening evidence a future inversion
lemma must produce. -/
theorem etaLamStrengthenedFunctionCong {scope : Nat}
    (domainAnn : RawTerm scope)
    {innerFunction : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    {updatedFunction : RawTerm scope}
    (underBinderStep :
      Step (RawTerm.weaken innerFunction) updatedUnderBinder)
    (strengthenSuccess :
      RawTerm.strengthen updatedUnderBinder = some updatedFunction)
    (functionStep : Step innerFunction updatedFunction) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.there (parentScope := scope) (headShift := 0)
              (restShifts := [1]) domainAnn
            (StepChildren.here
              (parentScope := scope) (headShift := 1) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.cong .gen_app ()
                (StepChildren.here
                  (parentScope := scope + 1) (headShift := 0)
                  (restShifts := [0])
                  ((.childCons RawTerm.newestVar .childNil) :
                    RawTermChildren [0] (scope + 1))
                  underBinderStep))))))
      (Or.inr (Step.eta.etaLam domainAnn innerFunction)) := by
  have underBinderEq :
      updatedUnderBinder = RawTerm.weaken updatedFunction :=
    (RawTerm.strengthen_sound updatedUnderBinder updatedFunction
      strengthenSuccess).symm
  cases underBinderEq
  exact
    ⟨ updatedFunction
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaLam domainAnn updatedFunction))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl functionStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-path-lambda sibling of `etaLamStrengthenedFunctionCong`.

The premise shape is the same: an arbitrary step under the weakened path
slot is accepted once strengthening identifies a source-scope reduct and
the source-level path step is supplied. -/
theorem etaPathLamStrengthenedFunctionCong {scope : Nat}
    {innerPath : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    {updatedPath : RawTerm scope}
    (underBinderStep :
      Step (RawTerm.weaken innerPath) updatedUnderBinder)
    (strengthenSuccess :
      RawTerm.strengthen updatedUnderBinder = some updatedPath)
    (pathStep : Step innerPath updatedPath) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pathLam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_pathApp ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                underBinderStep)))))
      (Or.inr (Step.eta.etaPathLam innerPath)) := by
  have underBinderEq :
      updatedUnderBinder = RawTerm.weaken updatedPath :=
    (RawTerm.strengthen_sound updatedUnderBinder updatedPath
      strengthenSuccess).symm
  cases underBinderEq
  exact
    ⟨ updatedPath
    , Step.betaEtaStar.trans
        (Or.inr (Step.eta.etaPathLam updatedPath))
        (Step.betaEtaStar.refl _)
    , Step.betaEtaStar.trans (Or.inl pathStep)
        (Step.betaEtaStar.refl _) ⟩

/-- Eta-lambda resolver arm with the source-level step derived from the
under-binder step.

This consumes only the remaining freshness witness
`RawTerm.strengthen updatedUnderBinder = some updatedFunction`; the
source-scope step itself is reconstructed by substituting a canonical unit
term for the fresh variable in `Step.weaken_substTarget`. -/
theorem etaLamStrengthenedFunctionCongFromUnderStep {scope : Nat}
    (domainAnn : RawTerm scope)
    {innerFunction : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    {updatedFunction : RawTerm scope}
    (underBinderStep :
      Step (RawTerm.weaken innerFunction) updatedUnderBinder)
    (strengthenSuccess :
      RawTerm.strengthen updatedUnderBinder = some updatedFunction) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.there (parentScope := scope) (headShift := 0)
              (restShifts := [1]) domainAnn
            (StepChildren.here
              (parentScope := scope) (headShift := 1) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.cong .gen_app ()
                (StepChildren.here
                  (parentScope := scope + 1) (headShift := 0)
                  (restShifts := [0])
                  ((.childCons RawTerm.newestVar .childNil) :
                    RawTermChildren [0] (scope + 1))
                  underBinderStep))))))
      (Or.inr (Step.eta.etaLam domainAnn innerFunction)) := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have targetBySubstitution :
      RawTerm.subst (RawTermSubst.singleton unitTerm) updatedUnderBinder =
        updatedFunction := by
    have weakenedTarget :=
      RawTerm.strengthen_sound updatedUnderBinder updatedFunction
        strengthenSuccess
    rw [← weakenedTarget]
    exact RawTerm.weaken_subst_singleton updatedFunction unitTerm
  have functionStep :
      Step innerFunction updatedFunction := by
    have replayedStep := Step.weaken_substTarget underBinderStep
    dsimp only [unitTerm] at targetBySubstitution
    rw [targetBySubstitution] at replayedStep
    exact replayedStep
  exact etaLamStrengthenedFunctionCong domainAnn underBinderStep
    strengthenSuccess functionStep

/-- Cubical path-lambda sibling of
`etaLamStrengthenedFunctionCongFromUnderStep`. -/
theorem etaPathLamStrengthenedFunctionCongFromUnderStep {scope : Nat}
    {innerPath : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    {updatedPath : RawTerm scope}
    (underBinderStep :
      Step (RawTerm.weaken innerPath) updatedUnderBinder)
    (strengthenSuccess :
      RawTerm.strengthen updatedUnderBinder = some updatedPath) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pathLam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_pathApp ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                underBinderStep)))))
      (Or.inr (Step.eta.etaPathLam innerPath)) := by
  let unitTerm : RawTerm scope := .mkGen .gen_unit () .childNil
  have targetBySubstitution :
      RawTerm.subst (RawTermSubst.singleton unitTerm) updatedUnderBinder =
        updatedPath := by
    have weakenedTarget :=
      RawTerm.strengthen_sound updatedUnderBinder updatedPath
        strengthenSuccess
    rw [← weakenedTarget]
    exact RawTerm.weaken_subst_singleton updatedPath unitTerm
  have pathStep : Step innerPath updatedPath := by
    have replayedStep := Step.weaken_substTarget underBinderStep
    dsimp only [unitTerm] at targetBySubstitution
    rw [targetBySubstitution] at replayedStep
    exact replayedStep
  exact etaPathLamStrengthenedFunctionCong underBinderStep
    strengthenSuccess pathStep

/-- Eta-lambda resolver arm for an arbitrary beta+iota step under the
weakened function occurrence.

The strengthening evidence is now derived from `Step.weaken_strengthenTarget`,
so callers only supply the under-binder `Step`. -/
theorem etaLamArbitraryUnderBinderCong {scope : Nat}
    (domainAnn : RawTerm scope)
    {innerFunction : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    (underBinderStep :
      Step (RawTerm.weaken innerFunction) updatedUnderBinder) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.there (parentScope := scope) (headShift := 0)
              (restShifts := [1]) domainAnn
            (StepChildren.here
              (parentScope := scope) (headShift := 1) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              (Step.cong .gen_app ()
                (StepChildren.here
                  (parentScope := scope + 1) (headShift := 0)
                  (restShifts := [0])
                  ((.childCons RawTerm.newestVar .childNil) :
                    RawTermChildren [0] (scope + 1))
                  underBinderStep))))))
      (Or.inr (Step.eta.etaLam domainAnn innerFunction)) :=
  etaLamStrengthenedFunctionCongFromUnderStep domainAnn underBinderStep
    (Step.weaken_strengthenTarget underBinderStep)

/-- Cubical path-lambda sibling of `etaLamArbitraryUnderBinderCong`. -/
theorem etaPathLamArbitraryUnderBinderCong {scope : Nat}
    {innerPath : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    (underBinderStep :
      Step (RawTerm.weaken innerPath) updatedUnderBinder) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_pathLam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_pathApp ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                underBinderStep)))))
      (Or.inr (Step.eta.etaPathLam innerPath)) :=
  etaPathLamStrengthenedFunctionCongFromUnderStep underBinderStep
    (Step.weaken_strengthenTarget underBinderStep)

/-- Resolver-facing eta-lambda arm for every beta+iota step leaving an
eta-lambda source.

The application body has three possible one-step exits: beta at the
application root, congruence in the weakened function slot, or congruence in
the newest-variable argument.  The root-beta case uses the lambda-shape
inversion for weakened terms plus the lifted-weakening cancellation lemma; the
argument case is impossible because the newest variable has an empty child
spine. -/
theorem etaLamLeftStep {scope : Nat}
    {domainAnn : RawTerm scope}
    {innerFunction leftReduct : RawTerm scope}
    (diagonal : EtaLamAnnotationDiagonal domainAnn innerFunction)
    (leftStep : Step (RawTerm.etaLamSource domainAnn innerFunction) leftReduct) :
    BetaEtaPairJoin
      (Or.inl leftStep)
      (Or.inr (Step.eta.etaLam domainAnn innerFunction)) := by
  cases Step.from_lam leftStep with
  | inl domainBranch =>
      -- The domain annotation itself steps; eta discards it, so the
      -- stepped source eta-contracts to the same `innerFunction`.
      obtain ⟨domainAfter, leftReductEq, _domainStep⟩ := domainBranch
      cases leftReductEq
      exact
        ⟨ innerFunction
        , Step.betaEtaStar.trans
            (Or.inr (Step.eta.etaLam domainAfter innerFunction))
            (Step.betaEtaStar.refl _)
        , Step.betaEtaStar.refl _ ⟩
  | inr bodyBranch =>
      obtain ⟨bodyAfter, leftReductEq, bodyStep⟩ := bodyBranch
      cases Step.from_app bodyStep with
      | inl betaBranch =>
          obtain ⟨weakenedDomain, weakenedBody, weakenedFunctionEq, bodyAfterEq⟩ :=
            betaBranch
          obtain ⟨innerDomainAnn, body, innerFunctionEq, _weakenedDomainEq, weakenedBodyEq⟩ :=
            RawTerm.weaken_eq_lam_implies_source_lam weakenedFunctionEq
          have annotationEq := diagonal innerDomainAnn body innerFunctionEq
          subst annotationEq
          apply ofReductsEqual
          rw [leftReductEq, bodyAfterEq, innerFunctionEq, weakenedBodyEq]
          rw [RawTerm.subst0_lift_weaken_newestVar]
      | inr congruenceBranch =>
          cases congruenceBranch with
          | inl functionBranch =>
              obtain ⟨updatedUnderBinder, bodyAfterEq, underBinderStep⟩ :=
                functionBranch
              cases leftReductEq
              cases bodyAfterEq
              exact etaLamArbitraryUnderBinderCong domainAnn underBinderStep
          | inr argumentBranch =>
              obtain ⟨_argumentAfter, _bodyAfterEq, argumentStep⟩ :=
                argumentBranch
              cases argumentStep with
              | cong _ _ childStep =>
                  cases childStep

/-- Reverse orientation of `etaLamLeftStep` (same Nederpelt diagonal guard). -/
theorem etaLamRightStep {scope : Nat}
    {domainAnn : RawTerm scope}
    {innerFunction rightReduct : RawTerm scope}
    (diagonal : EtaLamAnnotationDiagonal domainAnn innerFunction)
    (rightStep : Step (RawTerm.etaLamSource domainAnn innerFunction) rightReduct) :
    BetaEtaPairJoin
      (Or.inr (Step.eta.etaLam domainAnn innerFunction))
      (Or.inl rightStep) :=
  swap (etaLamLeftStep diagonal rightStep)

/-- Resolver-facing eta-path-lambda arm for every beta+iota step leaving a
path-eta source.

There is no raw `pathApp` beta constructor in the current `Step` relation, so
the only live branch is congruence in the weakened path slot.  A step in the
newest-variable argument is impossible because the variable has no children. -/
theorem etaPathLamLeftStep {scope : Nat}
    {innerPath leftReduct : RawTerm scope}
    (leftStep : Step (RawTerm.etaPathLamSource innerPath) leftReduct) :
    BetaEtaPairJoin
      (Or.inl leftStep)
      (Or.inr (Step.eta.etaPathLam innerPath)) := by
  cases leftStep with
  | cong _ _ pathLamChildrenStep =>
      cases pathLamChildrenStep with
      | here _ bodyStep =>
          cases bodyStep with
          | cong _ _ pathAppChildrenStep =>
              cases pathAppChildrenStep with
              | here _ underBinderStep =>
                  exact etaPathLamArbitraryUnderBinderCong underBinderStep
              | there _ tailStep =>
                  cases tailStep with
                  | here _ argumentStep =>
                      cases argumentStep with
                      | cong _ _ childStep =>
                          cases childStep
                  | there _ emptyStep =>
                      cases emptyStep
      | there _ emptyStep =>
          cases emptyStep

/-- Reverse orientation of `etaPathLamLeftStep`. -/
theorem etaPathLamRightStep {scope : Nat}
    {innerPath rightReduct : RawTerm scope}
    (rightStep : Step (RawTerm.etaPathLamSource innerPath) rightReduct) :
    BetaEtaPairJoin
      (Or.inr (Step.eta.etaPathLam innerPath))
      (Or.inl rightStep) :=
  swap (etaPathLamLeftStep rightStep)

/-- Mixed beta+iota-vs-eta local Church-Rosser dispatcher for all current
root eta rules, GUARDED at the lambda root by the Nederpelt diagonal.

Under Church-style annotations the UNGUARDED statement (`CdLemmaStatementStepEta`)
is FALSE: the eta-beta overlap `lam A (app (weaken (lam B b)) var0)` contracts to
`lam A b` (inner beta) and to `lam B b` (root eta) — non-joinable for normal
`A != B`.  The guard quantifies over the (forced) lambda decomposition of the
source; non-lambda eta roots discharge it vacuously.  The eta-vs-eta quadrant
remains a separate M8g task; the TYPED beta-eta CR is unaffected (typing forces
the annotations convertible). -/
theorem cd_lemma_step_eta {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step.eta sourceTerm rightReduct)
    (lamDiagonal :
      ∀ {domainAnn innerFunction : RawTerm scope},
        sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
        EtaLamAnnotationDiagonal domainAnn innerFunction) :
    BetaEtaPairJoin (Or.inl leftStep) (Or.inr rightStep) := by
  cases rightStep with
  | etaLam domainAnn innerFunction =>
      exact etaLamLeftStep (lamDiagonal rfl) leftStep
  | etaPair pairTerm =>
      exact etaPairLeftStep leftStep
  | etaPathLam innerPath =>
      exact etaPathLamLeftStep leftStep
  | etaModIntro modalTerm =>
      exact etaModIntroLeftStep leftStep
  | etaGlueIntro gluedTerm =>
      exact etaGlueIntroLeftStep leftStep

/-- Reverse mixed eta-vs-beta+iota local Church-Rosser dispatcher (same guard). -/
theorem cd_lemma_eta_step {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.eta sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct)
    (lamDiagonal :
      ∀ {domainAnn innerFunction : RawTerm scope},
        sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
        EtaLamAnnotationDiagonal domainAnn innerFunction) :
    BetaEtaPairJoin (Or.inr leftStep) (Or.inl rightStep) := by
  exact swap (cd_lemma_step_eta rightStep leftStep lamDiagonal)

end BetaEtaPairJoin

/-- Root eta kinds represented by `Step.eta`.

This finite catalog is deliberately limited to constructors whose generators
exist in the `Generator` enum.  Clock, parametricity, and record eta are not
reserved cases here. -/
inductive EtaStepKind : Type where
  | etaLam
  | etaPair
  | etaPathLam
  | etaModIntro
  | etaGlueIntro
  deriving DecidableEq

namespace EtaStepKind

/-- Complete current eta-root catalog. -/
def all : List EtaStepKind :=
  [ .etaLam
  , .etaPair
  , .etaPathLam
  , .etaModIntro
  , .etaGlueIntro
  ]

/-- Source-head generator for a current root eta rule. -/
def sourceGenerator : EtaStepKind → Generator
  | .etaLam => .gen_lam
  | .etaPair => .gen_pair
  | .etaPathLam => .gen_pathLam
  | .etaModIntro => .gen_modIntro
  | .etaGlueIntro => .gen_glueIntro

/-- Does this eta root share beta's source-head generator? -/
def hasBetaSourceGenerator (etaKind : EtaStepKind) : Bool :=
  if etaKind.sourceGenerator = RootStepKind.beta.sourceGenerator then
    true
  else
    false

theorem all_length :
    all.length = 5 := rfl

theorem sourceGenerator_etaLam :
    sourceGenerator .etaLam = .gen_lam := rfl

theorem sourceGenerator_etaPair :
    sourceGenerator .etaPair = .gen_pair := rfl

theorem sourceGenerator_etaPathLam :
    sourceGenerator .etaPathLam = .gen_pathLam := rfl

theorem sourceGenerator_etaModIntro :
    sourceGenerator .etaModIntro = .gen_modIntro := rfl

theorem sourceGenerator_etaGlueIntro :
    sourceGenerator .etaGlueIntro = .gen_glueIntro := rfl

/-- Root beta has source generator `gen_app`, while every current root eta
rule has a different source generator.  Any beta/eta interaction in the
current relation therefore goes through `Step.cong` on the beta+iota side,
not through a same-root beta/eta overlap. -/
theorem currentEtaRoots_doNotShareBetaSource :
    all.map hasBetaSourceGenerator =
      [false, false, false, false, false] := rfl

end EtaStepKind

end FX1Poly.Core
