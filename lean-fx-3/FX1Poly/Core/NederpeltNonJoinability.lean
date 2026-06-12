import FX1Poly.Core.StepEtaCriticalPairs
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.HeadStep

/-! # Foundation/PolyCell/Core/NederpeltNonJoinability
    — the Church-annotation eta-beta overlap is NOT joinable (L1 refutation)

Under Church-style lambda annotations the classic Nederpelt overlap breaks
raw beta-eta local confluence.  The source
`lam A (app (weaken (lam B b)) newestVar)` contracts BOTH

  * by the inner beta to `lam A b` — the OUTER annotation survives, and
  * by the root eta to `lam B b` — the INNER annotation survives,

and for normal `A != B` the two reducts are distinct beta-eta normal forms,
hence non-joinable.  This file pins that as a permanent refutation in the
known-unsoundness corpus: the UNGUARDED mixed cd-lemma statements
(`CdLemmaStatementStepEta`, `CdLemmaStatementEtaStep`,
`CdLemmaStatementBetaEta`) are all FALSE.  The proved replacements are the
`EtaLamAnnotationDiagonal`-guarded forms in `StepEtaCriticalPairs` /
`StepEtaEtaCriticalPairs`, and the hereditary-guarded Newman bridge in
`StepBetaEtaConfluence`.  Typed terms satisfy the guard because typing
forces the two annotations convertible, so the TYPED beta-eta theory is
unaffected.

## Zero-axiom verification

Constructor reasoning only: `Step.beta` + `Step.cong` for the inner-beta
leg, `weaken_lam` + `subst0_lift_weaken_newestVar` for the contractum
shape, `isStepNormalForm_blocks_step` + eta shape analysis for normal-form
rigidity.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- The inner-beta BODY step of the Nederpelt overlap: inside the eta
source's binder, `app (weaken (lam innerDomain innerBody)) newestVar`
beta-contracts to `innerBody` — the lifted weakening cancels against the
newest variable, and Church-style beta DISCARDS the inner annotation. -/
theorem Step.nederpeltInnerBetaBody {scope : Nat}
    (innerDomain : RawTerm scope) (innerBody : RawTerm (scope + 1)) :
    Step
      (.mkGen .gen_app ()
        (.childCons
          (RawTerm.weaken
            (.mkGen .gen_lam ()
              (.childCons innerDomain (.childCons innerBody .childNil))))
          (.childCons RawTerm.newestVar .childNil)))
      innerBody := by
  rw [RawTerm.weaken_lam]
  have betaStep :
      Step
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam ()
              (.childCons (RawTerm.rename RawRenaming.weaken innerDomain)
                (.childCons
                  (RawTerm.rename (RawRenaming.lift RawRenaming.weaken)
                    innerBody)
                  .childNil)))
            (.childCons RawTerm.newestVar .childNil)))
        (RawTerm.subst0
          (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) innerBody)
          RawTerm.newestVar) :=
    HeadStep.beta.toStep
  rw [RawTerm.subst0_lift_weaken_newestVar innerBody] at betaStep
  exact betaStep

/-- The full inner-beta leg: the eta source one-steps (congruence-lifted
beta) to the lambda that keeps the OUTER annotation around the inner
body. -/
theorem Step.nederpeltInnerBeta {scope : Nat}
    (outerDomain innerDomain : RawTerm scope)
    (innerBody : RawTerm (scope + 1)) :
    Step
      (RawTerm.etaLamSource outerDomain
        (.mkGen .gen_lam ()
          (.childCons innerDomain (.childCons innerBody .childNil))))
      (.mkGen .gen_lam ()
        (.childCons outerDomain (.childCons innerBody .childNil))) :=
  Step.cong .gen_lam ()
    (StepChildren.there (parentScope := scope) (headShift := 0)
      (restShifts := [1]) outerDomain
      (StepChildren.here .childNil
        (Step.nederpeltInnerBetaBody innerDomain innerBody)))

/-- No root eta step fires from a lambda whose body is the bare newest
variable: the etaLam source shape needs an application body, and every
other eta constructor has a non-lambda head. -/
theorem Step.eta.not_from_varBodyLam {scope : Nat}
    {annotation : RawTerm scope} {targetTerm : RawTerm scope}
    (etaStep :
      Step.eta
        (.mkGen .gen_lam ()
          (.childCons annotation (.childCons RawTerm.newestVar .childNil)))
        targetTerm) :
    False := by
  generalize sourceEq :
    (RawTerm.mkGen .gen_lam ()
        (.childCons annotation
          (.childCons RawTerm.newestVar .childNil)) :
      RawTerm scope) = sourceTerm at etaStep
  cases etaStep with
  | etaLam => cases sourceEq
  | etaPair => cases sourceEq
  | etaPathLam => cases sourceEq
  | etaModIntro => cases sourceEq
  | etaGlueIntro => cases sourceEq

/-- A beta-eta chain from a source blocking both single-step relations is
reflexive. -/
theorem Step.betaEtaStar.eq_of_blockedSource {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.betaEtaStar sourceTerm targetTerm)
    (sourceNormal : RawTerm.isStepNormalForm sourceTerm)
    (sourceBlocksEta :
      ∀ {nextTerm : RawTerm scope}, ¬ Step.eta sourceTerm nextTerm) :
    sourceTerm = targetTerm := by
  cases chain with
  | refl _ => rfl
  | trans headStep _tailChain =>
      cases headStep with
      | inl betaStep =>
          exact absurd betaStep
            (RawTerm.isStepNormalForm_blocks_step sourceNormal _)
      | inr etaStep => exact absurd etaStep sourceBlocksEta

/-- Outer annotation of the concrete Nederpelt witness: the unit value. -/
@[reducible] def nederpeltOuterAnnotation : RawTerm 0 :=
  .mkGen .gen_unit () .childNil

/-- Inner annotation of the concrete Nederpelt witness: the true boolean —
any closed normal cell distinct from the outer annotation works. -/
@[reducible] def nederpeltInnerAnnotation : RawTerm 0 :=
  .mkGen .gen_boolTrue () .childNil

/-- The beta reduct `lam unit newestVar` — the outer annotation survives. -/
@[reducible] def nederpeltBetaReduct : RawTerm 0 :=
  .mkGen .gen_lam ()
    (.childCons nederpeltOuterAnnotation
      (.childCons RawTerm.newestVar .childNil))

/-- The eta reduct `lam boolTrue newestVar` — the inner annotation
survives. -/
@[reducible] def nederpeltEtaReduct : RawTerm 0 :=
  .mkGen .gen_lam ()
    (.childCons nederpeltInnerAnnotation
      (.childCons RawTerm.newestVar .childNil))

/-- The beta reduct is a beta/iota normal form. -/
theorem nederpeltBetaReduct_isStepNormalForm :
    RawTerm.isStepNormalForm nederpeltBetaReduct := by
  rfl

/-- The eta reduct is a beta/iota normal form. -/
theorem nederpeltEtaReduct_isStepNormalForm :
    RawTerm.isStepNormalForm nederpeltEtaReduct := by
  rfl

/-- **The Nederpelt reducts do not join.**  Both are beta-eta normal forms
(no beta/iota step by structural normality, no eta step by shape), so any
join chains are reflexive — but the reducts differ in their surviving
annotation. -/
theorem nederpeltReductsNonJoinable :
    ¬ ∃ commonReduct : RawTerm 0,
        Step.betaEtaStar nederpeltBetaReduct commonReduct ∧
          Step.betaEtaStar nederpeltEtaReduct commonReduct := by
  intro joinWitness
  obtain ⟨commonReduct, betaReductChain, etaReductChain⟩ := joinWitness
  have betaReductEq :=
    Step.betaEtaStar.eq_of_blockedSource betaReductChain
      nederpeltBetaReduct_isStepNormalForm
      (fun etaStep => Step.eta.not_from_varBodyLam etaStep)
  have etaReductEq :=
    Step.betaEtaStar.eq_of_blockedSource etaReductChain
      nederpeltEtaReduct_isStepNormalForm
      (fun etaStep => Step.eta.not_from_varBodyLam etaStep)
  cases betaReductEq.trans etaReductEq.symm

/-- **REFUTATION: the unguarded beta-vs-eta cd-lemma is FALSE** under
Church-style annotations.  The guarded `cd_lemma_step_eta` (with the
`EtaLamAnnotationDiagonal` hypothesis) is the honest replacement. -/
theorem cdLemmaStatementStepEta_isFalse : ¬ CdLemmaStatementStepEta := by
  intro unguardedStatement
  exact nederpeltReductsNonJoinable
    (unguardedStatement
      (Step.nederpeltInnerBeta nederpeltOuterAnnotation
        nederpeltInnerAnnotation RawTerm.newestVar)
      (Step.eta.etaLam nederpeltOuterAnnotation
        (.mkGen .gen_lam ()
          (.childCons nederpeltInnerAnnotation
            (.childCons RawTerm.newestVar .childNil)))))

/-- **REFUTATION: the unguarded eta-vs-beta cd-lemma is FALSE** (mirror
orientation of `cdLemmaStatementStepEta_isFalse`). -/
theorem cdLemmaStatementEtaStep_isFalse : ¬ CdLemmaStatementEtaStep := by
  intro unguardedStatement
  obtain ⟨commonReduct, etaReductChain, betaReductChain⟩ :=
    unguardedStatement
      (Step.eta.etaLam nederpeltOuterAnnotation
        (.mkGen .gen_lam ()
          (.childCons nederpeltInnerAnnotation
            (.childCons RawTerm.newestVar .childNil))))
      (Step.nederpeltInnerBeta nederpeltOuterAnnotation
        nederpeltInnerAnnotation RawTerm.newestVar)
  exact nederpeltReductsNonJoinable
    ⟨commonReduct, betaReductChain, etaReductChain⟩

/-- **REFUTATION: the unguarded full beta-eta cd-lemma is FALSE** —
the Nederpelt pair instantiates its mixed quadrant.  The guarded
`cd_lemma_betaEta` (in `StepEtaEtaCriticalPairs`) is the honest
replacement. -/
theorem cdLemmaStatementBetaEta_isFalse : ¬ CdLemmaStatementBetaEta := by
  intro unguardedStatement
  exact nederpeltReductsNonJoinable
    (unguardedStatement
      (Or.inl
        (Step.nederpeltInnerBeta nederpeltOuterAnnotation
          nederpeltInnerAnnotation RawTerm.newestVar))
      (Or.inr
        (Step.eta.etaLam nederpeltOuterAnnotation
          (.mkGen .gen_lam ()
            (.childCons nederpeltInnerAnnotation
              (.childCons RawTerm.newestVar .childNil))))))

end FX1Poly.Core
