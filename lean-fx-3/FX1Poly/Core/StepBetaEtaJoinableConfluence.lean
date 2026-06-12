import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.StepEtaEtaCriticalPairs
import FX1Poly.Core.StepBetaEtaConfluence
import FX1Poly.Core.WeakHeadStepCommute

/-! # FX1Poly/Core/StepBetaEtaJoinableConfluence
    — the JOINABILITY-guarded beta+iota+eta local join + Newman bridge

The shipped `cd_lemma_betaEta` / `confluence_of_localJoin_and_accessible` carry the Nederpelt
diagonal guard as a syntactic EQUALITY: at every reachable lambda eta root
`lam A (app (weaken (lam B b)) var0)` the inner annotation must EQUAL the outer one (`B = A`).
That guard is the honest raw-layer statement (off the diagonal the eta-beta pair is
non-joinable, `NederpeltNonJoinability`) — but it is TOO STRONG for typed subjects: typing
forces the two annotations CONVERTIBLE, not syntactically equal, so the equality guard can
fail on a well-typed term.

This file weakens the guard from equality to `StepStar`-JOINABILITY
(`EtaLamAnnotationJoinable`): the two annotations need only meet at a common beta+iota reduct.
The single guarded critical pair then closes by a JOIN instead of an equality — the two
reducts `lam A b` and `lam B b` reduce to `lam C b` (where `A ↝* C ↜* B`) by replaying the
annotation chains through the lambda's domain child via `Step.cong`.  Crucially the
annotation chains are BETA+IOTA chains (`StepStar`), which DO have congruence closure —
root-only `Step.eta` chains would not lift into the domain child.

Joinability is exactly what typing supplies: convertible annotations ARE `StepStar`-joinable
(`Conv` is DEFINED as `StepStar.Join`).  The typed discharge lives in
`FX1Poly/Typed/WfContextBetaEtaConfluenceUnconditional.lean`.

Shipped here:
  * `StepStar.lamDomainCong` — replay an annotation chain through the lambda domain child.
  * `BetaEtaPairJoin.EtaLamAnnotationJoinable` + `.ofDiagonal` — the weakened guard; the
    equality guard implies it (reflexive join).
  * `BetaEtaPairJoin.etaLamLeftStepJoinable` / `etaLamRightStepJoinable` — the guarded
    critical pair re-proved under joinability (the beta branch produces a genuine join).
  * `BetaEtaPairJoin.cd_lemma_step_eta_joinable` / `cd_lemma_eta_step_joinable` /
    `cd_lemma_betaEta_joinable` — the four-quadrant local dispatcher under the weak guard.
  * `Step.betaEtaStar.LamJoinableGuard` / `HereditaryLamJoinable` (+ `alongStep`,
    `ofHereditaryDiagonal`) — the hereditary form the Newman recursion consumes.
  * `Step.betaEtaStar.confluence_of_localJoin_and_accessibleJoinable` — the Newman bridge
    over the weak guard (same `Acc` recursion as the diagonal version).

## Zero-axiom verification

Every proof is structural (`cases` / `obtain` / `rw` with shipped equations / `Acc.ndrec`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- Replay a beta+iota `StepStar` chain on a lambda's domain annotation through the lambda
cell (body fixed) — the one-hole-context instance of `StepStar.congAt` at the `gen_lam` head
child (shift `0`, rest shifts `[1]`). -/
theorem StepStar.lamDomainCong {scope : Nat} (body : RawTerm (scope + 1))
    {domainStart domainEnd : RawTerm scope}
    (annotationChain : StepStar domainStart domainEnd) :
    StepStar
      (RawTerm.mkGen .gen_lam ()
        (.childCons domainStart (.childCons body .childNil)))
      (RawTerm.mkGen .gen_lam ()
        (.childCons domainEnd (.childCons body .childNil))) :=
  StepStar.congAt
    (fun annotation =>
      RawTerm.mkGen .gen_lam () (.childCons annotation (.childCons body .childNil)))
    (fun annotationStep =>
      Step.cong .gen_lam ()
        (StepChildren.here (parentScope := scope) (headShift := 0) (restShifts := [1])
          (.childCons body .childNil) annotationStep))
    annotationChain

namespace BetaEtaPairJoin

/-- **The weakened Nederpelt guard: annotation JOINABILITY.**  IF the eta-expanded function is
itself an annotated lambda, its annotation joins the eta binder's annotation at a common
beta+iota reduct.  Strictly weaker than `EtaLamAnnotationDiagonal` (equality), and exactly
what typing supplies — typed eta sources have CONVERTIBLE annotations, and `Conv` IS
`StepStar.Join`. -/
def EtaLamAnnotationJoinable {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) : Prop :=
  ∀ (innerDomainAnn : RawTerm scope) (innerBody : RawTerm (scope + 1)),
    innerFunction =
      .mkGen .gen_lam ()
        (.childCons innerDomainAnn (.childCons innerBody .childNil)) →
    StepStar.Join innerDomainAnn domainAnn

/-- The syntactic diagonal guard implies the joinability guard — equal annotations join
reflexively. -/
theorem EtaLamAnnotationJoinable.ofDiagonal {scope : Nat}
    {domainAnn innerFunction : RawTerm scope}
    (diagonal : EtaLamAnnotationDiagonal domainAnn innerFunction) :
    EtaLamAnnotationJoinable domainAnn innerFunction := by
  intro innerDomainAnn innerBody innerFunctionEq
  rw [diagonal innerDomainAnn innerBody innerFunctionEq]
  exact ⟨domainAnn, StepStar.refl _, StepStar.refl _⟩

/-- Eta-lambda versus every beta+iota step leaving an eta-lambda source, under the
JOINABILITY guard.  Mirror of `etaLamLeftStep` with one changed branch: when the body fires
the inner beta (the Nederpelt overlap), the two reducts `lam domainAnn body` and
`lam innerDomainAnn body` are no longer forced EQUAL — they JOIN at `lam commonAnn body` by
replaying the annotation chains through the domain child (`StepStar.lamDomainCong`). -/
theorem etaLamLeftStepJoinable {scope : Nat}
    {domainAnn : RawTerm scope}
    {innerFunction leftReduct : RawTerm scope}
    (joinable : EtaLamAnnotationJoinable domainAnn innerFunction)
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
          obtain ⟨commonAnn, innerToCommon, outerToCommon⟩ :=
            joinable innerDomainAnn body innerFunctionEq
          refine
            ⟨ RawTerm.mkGen .gen_lam ()
                (.childCons commonAnn (.childCons body .childNil)), ?_, ?_ ⟩
          · rw [leftReductEq, bodyAfterEq, weakenedBodyEq,
              RawTerm.subst0_lift_weaken_newestVar]
            exact Step.betaEtaStar.ofStepStar (StepStar.lamDomainCong body outerToCommon)
          · rw [innerFunctionEq]
            exact Step.betaEtaStar.ofStepStar (StepStar.lamDomainCong body innerToCommon)
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

/-- Reverse orientation of `etaLamLeftStepJoinable` (same joinability guard). -/
theorem etaLamRightStepJoinable {scope : Nat}
    {domainAnn : RawTerm scope}
    {innerFunction rightReduct : RawTerm scope}
    (joinable : EtaLamAnnotationJoinable domainAnn innerFunction)
    (rightStep : Step (RawTerm.etaLamSource domainAnn innerFunction) rightReduct) :
    BetaEtaPairJoin
      (Or.inr (Step.eta.etaLam domainAnn innerFunction))
      (Or.inl rightStep) :=
  swap (etaLamLeftStepJoinable joinable rightStep)

/-- Mixed beta+iota-vs-eta local Church-Rosser dispatcher under the JOINABILITY guard —
the weak-guard twin of `cd_lemma_step_eta`. -/
theorem cd_lemma_step_eta_joinable {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step.eta sourceTerm rightReduct)
    (lamJoinable :
      ∀ {domainAnn innerFunction : RawTerm scope},
        sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
        EtaLamAnnotationJoinable domainAnn innerFunction) :
    BetaEtaPairJoin (Or.inl leftStep) (Or.inr rightStep) := by
  cases rightStep with
  | etaLam domainAnn innerFunction =>
      exact etaLamLeftStepJoinable (lamJoinable rfl) leftStep
  | etaPair pairTerm =>
      exact etaPairLeftStep leftStep
  | etaPathLam innerPath =>
      exact etaPathLamLeftStep leftStep
  | etaModIntro modalTerm =>
      exact etaModIntroLeftStep leftStep
  | etaGlueIntro gluedTerm =>
      exact etaGlueIntroLeftStep leftStep

/-- Reverse mixed eta-vs-beta+iota dispatcher under the JOINABILITY guard. -/
theorem cd_lemma_eta_step_joinable {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.eta sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct)
    (lamJoinable :
      ∀ {domainAnn innerFunction : RawTerm scope},
        sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
        EtaLamAnnotationJoinable domainAnn innerFunction) :
    BetaEtaPairJoin (Or.inr leftStep) (Or.inl rightStep) :=
  swap (cd_lemma_step_eta_joinable rightStep leftStep lamJoinable)

/-- Full local Church-Rosser dispatcher for the beta+iota+root-eta single-step relation
under the JOINABILITY guard — the weak-guard twin of `cd_lemma_betaEta`. -/
theorem cd_lemma_betaEta_joinable {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.betaEta sourceTerm leftReduct)
    (rightStep : Step.betaEta sourceTerm rightReduct)
    (lamJoinable :
      ∀ {domainAnn innerFunction : RawTerm scope},
        sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
        EtaLamAnnotationJoinable domainAnn innerFunction) :
    BetaEtaPairJoin leftStep rightStep := by
  cases leftStep with
  | inl leftStepOnly =>
      cases rightStep with
      | inl rightStepOnly =>
          exact ofStepStepLocalJoin leftStepOnly rightStepOnly
      | inr rightEtaOnly =>
          exact cd_lemma_step_eta_joinable leftStepOnly rightEtaOnly lamJoinable
  | inr leftEtaOnly =>
      cases rightStep with
      | inl rightStepOnly =>
          exact cd_lemma_eta_step_joinable leftEtaOnly rightStepOnly lamJoinable
      | inr rightEtaOnly =>
          exact cd_lemma_eta_eta leftEtaOnly rightEtaOnly

end BetaEtaPairJoin

namespace Step
namespace betaEtaStar

/-- The joinability guard at one source term — the weak-guard twin of `LamDiagonalGuard`. -/
def LamJoinableGuard {scope : Nat} (sourceTerm : RawTerm scope) : Prop :=
  ∀ {domainAnn innerFunction : RawTerm scope},
    sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
    BetaEtaPairJoin.EtaLamAnnotationJoinable domainAnn innerFunction

/-- Hereditary joinability guard: the joinable guard holds at every beta+iota+eta reachable
reduct of the source — the weak-guard twin of `HereditaryLamDiagonal`, and what the Newman
recursion consumes. -/
def HereditaryLamJoinable {scope : Nat} (sourceTerm : RawTerm scope) : Prop :=
  ∀ {reachedTerm : RawTerm scope},
    Step.betaEtaStar sourceTerm reachedTerm → LamJoinableGuard reachedTerm

/-- The hereditary joinability guard transfers along a single beta+iota+eta step. -/
theorem HereditaryLamJoinable.alongStep {scope : Nat}
    {sourceTerm nextTerm : RawTerm scope}
    (hereditaryJoinable : HereditaryLamJoinable sourceTerm)
    (headStep : Step.betaEta sourceTerm nextTerm) :
    HereditaryLamJoinable nextTerm :=
  fun reachChain =>
    hereditaryJoinable (Step.betaEtaStar.trans headStep reachChain)

/-- The hereditary DIAGONAL guard implies the hereditary JOINABILITY guard — at every
reachable term the equality guard weakens to the reflexive join. -/
theorem HereditaryLamJoinable.ofHereditaryDiagonal {scope : Nat}
    {sourceTerm : RawTerm scope}
    (hereditaryDiagonal : HereditaryLamDiagonal sourceTerm) :
    HereditaryLamJoinable sourceTerm := by
  intro reachedTerm reachChain domainAnn innerFunction sourceShapeEq
  exact BetaEtaPairJoin.EtaLamAnnotationJoinable.ofDiagonal
    (hereditaryDiagonal reachChain sourceShapeEq)

/-- The weak-guard local one-step join for the beta+iota+eta relation. -/
theorem localJoin_of_cdLemmaBetaEtaJoinable {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.betaEta sourceTerm leftReduct)
    (rightStep : Step.betaEta sourceTerm rightReduct)
    (lamJoinable : LamJoinableGuard sourceTerm) :
    Join leftReduct rightReduct :=
  BetaEtaPairJoin.cd_lemma_betaEta_joinable leftStep rightStep lamJoinable

/-- Newman's lift from the weak-guard local join plus source accessibility to global
Church-Rosser — the joinability twin of `confluence_of_localJoin_and_accessible`.  The
hereditary joinability guard is consumed at every node of the two chains. -/
theorem confluence_of_localJoin_and_accessibleJoinable {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing sourceTerm)
    (hereditaryJoinable : HereditaryLamJoinable sourceTerm)
    (leftChain : Step.betaEtaStar sourceTerm leftReduct)
    (rightChain : Step.betaEtaStar sourceTerm rightReduct) :
    Join leftReduct rightReduct := by
  exact
    (Acc.ndrec
      (r := Step.betaEtaSuccessor)
      (C := fun currentTerm =>
        HereditaryLamJoinable currentTerm →
        ∀ {leftReduct rightReduct : RawTerm scope},
          Step.betaEtaStar currentTerm leftReduct →
          Step.betaEtaStar currentTerm rightReduct →
          Join leftReduct rightReduct)
      (m := fun currentTerm _ currentIH => by
        intro hereditaryHere leftReduct rightReduct leftChain rightChain
        cases leftChain with
        | refl _ =>
            exact ⟨rightReduct, rightChain, Step.betaEtaStar.refl _⟩
        | trans leftHeadStep leftTailChain =>
            cases rightChain with
            | refl _ =>
                exact
                  ⟨ leftReduct
                  , Step.betaEtaStar.refl _
                  , Step.betaEtaStar.trans leftHeadStep leftTailChain ⟩
            | trans rightHeadStep rightTailChain =>
                obtain
                  ⟨localReduct, leftHeadToLocal, rightHeadToLocal⟩ :=
                    localJoin_of_cdLemmaBetaEtaJoinable leftHeadStep rightHeadStep
                      (hereditaryHere (Step.betaEtaStar.refl _))
                obtain
                  ⟨leftCommon, leftTailToCommon, localToLeftCommon⟩ :=
                    currentIH _ leftHeadStep
                      (HereditaryLamJoinable.alongStep hereditaryHere
                        leftHeadStep)
                      leftTailChain leftHeadToLocal
                obtain
                  ⟨finalCommon, rightTailToCommon, leftCommonToFinal⟩ :=
                    currentIH _ rightHeadStep
                      (HereditaryLamJoinable.alongStep hereditaryHere
                        rightHeadStep)
                      rightTailChain
                      (Step.betaEtaStar.trans_compose rightHeadToLocal
                        localToLeftCommon)
                exact
                  ⟨ finalCommon
                  , Step.betaEtaStar.trans_compose leftTailToCommon
                      leftCommonToFinal
                  , rightTailToCommon ⟩)
      sourceTerminates)
      hereditaryJoinable
      leftChain
      rightChain

end betaEtaStar
end Step

end FX1Poly.Core
