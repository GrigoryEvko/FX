import FX1Poly.Core.StepEtaEtaCriticalPairs

/-! # Foundation/PolyCell/Core/StepBetaEtaConfluence
    - Newman bridge for the beta+iota+eta raw relation

The eta cascade extends the raw one-step relation by opt-in union:
`Step.betaEta = Step ∪ Step.eta`.  The local one-step join theorem for
that union is `BetaEtaPairJoin.cd_lemma_betaEta`; this file supplies the
matching Newman bridge.

The confluence machinery here is conditional on global strong
normalization for beta+iota+eta, which is supplied separately.
-/

namespace FX1Poly.Core

namespace Step

/-- The one-step-successor relation for beta+iota+eta accessibility:
`laterTerm` is below `earlierTerm` when `earlierTerm` takes one
`Step.betaEta` step to `laterTerm`. -/
def betaEtaSuccessor {scope : Nat}
    (laterTerm earlierTerm : RawTerm scope) : Prop :=
  Step.betaEta earlierTerm laterTerm

namespace betaEtaStar

/-- Two raw terms join when they reduce to a common reduct by
`Step.betaEtaStar`. -/
def Join {scope : Nat} (leftTerm rightTerm : RawTerm scope) : Prop :=
  ∃ commonTerm : RawTerm scope,
    Step.betaEtaStar leftTerm commonTerm ∧
      Step.betaEtaStar rightTerm commonTerm

/-- The Nederpelt lambda-annotation guard at one source term: whenever the
source is a root lambda eta redex, the inner function's annotation sits on
the diagonal (matches the outer binder's annotation).  Under Church-style
annotations the UNGUARDED local join is false: `lam A (app (weaken (lam B b))
var0)` contracts to `lam A b` (inner beta) and `lam B b` (root eta),
non-joinable for normal `A != B`. -/
def LamDiagonalGuard {scope : Nat} (sourceTerm : RawTerm scope) : Prop :=
  ∀ {domainAnn innerFunction : RawTerm scope},
    sourceTerm = RawTerm.etaLamSource domainAnn innerFunction →
    BetaEtaPairJoin.EtaLamAnnotationDiagonal domainAnn innerFunction

/-- Hereditary Nederpelt guard: the diagonal guard holds at every
beta+iota+eta reachable reduct of the source.  This is what the Newman
recursion needs, since local joins fire at every node of the two chains. -/
def HereditaryLamDiagonal {scope : Nat} (sourceTerm : RawTerm scope) :
    Prop :=
  ∀ {reachedTerm : RawTerm scope},
    Step.betaEtaStar sourceTerm reachedTerm → LamDiagonalGuard reachedTerm

/-- The hereditary guard transfers along a single beta+iota+eta step. -/
theorem HereditaryLamDiagonal.alongStep {scope : Nat}
    {sourceTerm nextTerm : RawTerm scope}
    (hereditaryDiagonal : HereditaryLamDiagonal sourceTerm)
    (headStep : Step.betaEta sourceTerm nextTerm) :
    HereditaryLamDiagonal nextTerm :=
  fun reachChain =>
    hereditaryDiagonal (Step.betaEtaStar.trans headStep reachChain)

/-- Global Church-Rosser for the beta+iota+eta raw relation on the
Nederpelt-guarded fragment.  The unguarded statement is FALSE under
Church-style lambda annotations; typed terms satisfy the guard because
typing forces the annotations convertible. -/
def HasConfluence : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    HereditaryLamDiagonal sourceTerm →
    Step.betaEtaStar sourceTerm leftReduct →
    Step.betaEtaStar sourceTerm rightReduct →
    Join leftReduct rightReduct

/-- A raw term is strongly normalizing for beta+iota+eta when there is no
infinite chain of one-step beta+iota+eta reducts below it. -/
def IsStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Prop :=
  Acc Step.betaEtaSuccessor sourceTerm

/-- Strong normalization for beta+iota+eta at every scope.  This is the
input needed to close beta+eta confluence globally. -/
def HasStrongNormalization : Prop :=
  ∀ {scope : Nat} (sourceTerm : RawTerm scope),
    IsStronglyNormalizing sourceTerm

/-- The beta+eta local critical-pair dispatcher gives the
one-step/one-step local join for the beta+iota+eta relation, on sources
satisfying the Nederpelt diagonal guard. -/
theorem localJoin_of_cdLemmaBetaEta {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.betaEta sourceTerm leftReduct)
    (rightStep : Step.betaEta sourceTerm rightReduct)
    (lamDiagonal : LamDiagonalGuard sourceTerm) :
    Join leftReduct rightReduct :=
  BetaEtaPairJoin.cd_lemma_betaEta leftStep rightStep lamDiagonal

/-- A beta+iota+eta single step joins with a reflexive right chain. -/
theorem joinStepWithReflRight {scope : Nat}
    {sourceTerm leftReduct : RawTerm scope}
    (leftStep : Step.betaEta sourceTerm leftReduct) :
    Join leftReduct sourceTerm :=
  ⟨leftReduct, Step.betaEtaStar.refl _,
    Step.betaEtaStar.single leftStep⟩

/-- Two beta+iota+eta single steps from the same diagonal-guarded source
join by the local beta+eta critical-pair dispatcher. -/
theorem joinStepWithSingleRight {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step.betaEta sourceTerm leftReduct)
    (rightStep : Step.betaEta sourceTerm rightReduct)
    (lamDiagonal : LamDiagonalGuard sourceTerm) :
    Join leftReduct rightReduct :=
  localJoin_of_cdLemmaBetaEta leftStep rightStep lamDiagonal

/-- Newman's lift from beta+eta local one-step confluence plus source
accessibility to global Church-Rosser for two chains from that source.
The hereditary Nederpelt guard is consumed at every node of the two
chains (local joins fire at every reachable term). -/
theorem confluence_of_localJoin_and_accessible {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing sourceTerm)
    (hereditaryDiagonal : HereditaryLamDiagonal sourceTerm)
    (leftChain : Step.betaEtaStar sourceTerm leftReduct)
    (rightChain : Step.betaEtaStar sourceTerm rightReduct) :
    Join leftReduct rightReduct := by
  exact
    (Acc.ndrec
      (r := Step.betaEtaSuccessor)
      (C := fun currentTerm =>
        HereditaryLamDiagonal currentTerm →
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
                    localJoin_of_cdLemmaBetaEta leftHeadStep rightHeadStep
                      (hereditaryHere (Step.betaEtaStar.refl _))
                obtain
                  ⟨leftCommon, leftTailToCommon, localToLeftCommon⟩ :=
                    currentIH _ leftHeadStep
                      (HereditaryLamDiagonal.alongStep hereditaryHere
                        leftHeadStep)
                      leftTailChain leftHeadToLocal
                obtain
                  ⟨finalCommon, rightTailToCommon, leftCommonToFinal⟩ :=
                    currentIH _ rightHeadStep
                      (HereditaryLamDiagonal.alongStep hereditaryHere
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
      hereditaryDiagonal
      leftChain
      rightChain

/-- Strong normalization plus the beta+eta local critical-pair dispatcher
gives global beta+iota+eta Church-Rosser on the Nederpelt-guarded
fragment. -/
theorem confluence_of_strongNormalization
    (hasStrongNormalization : HasStrongNormalization) :
    HasConfluence := by
  intro scope sourceTerm leftReduct rightReduct hereditaryDiagonal
    leftChain rightChain
  exact
    confluence_of_localJoin_and_accessible
      (hasStrongNormalization sourceTerm)
      hereditaryDiagonal
      leftChain
      rightChain

end betaEtaStar
end Step

end FX1Poly.Core
