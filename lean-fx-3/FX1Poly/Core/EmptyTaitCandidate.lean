import FX1Poly.Core.EmptyCanonicalFormsCandidate
import FX1Poly.Core.HeadExpansionClosure
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.NeutralStepClosure
import FX1Poly.Core.StrongNormalizationSpineExpansion
import FX1Poly.Core.StratifiedReducibleTypeHeadExpansion
import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Core/EmptyTaitCandidate
    — the HEAD-EXPANSION-CLOSED empty (bottom) Tait candidate, zero-axiom

The empty type (`never` / `Empty`) needs a reducibility candidate to participate in the §5 reducibility
model (the candidate-bridge edit pins `emptyTypeCell` to it).  The naive choice `CanonicalFormsPredicate
emptyIsValue` (= strongly-normalizing terms that are themselves neutral, since the empty type has no values)
is a reducibility candidate and has no closed members — but it is NOT closed under weak-head / β expansion:
a β-redex `(λ.body) arg` whose contractum is a neutral member is itself NOT neutral (its head is a λ), so it
is not in `CanonicalFormsPredicate emptyIsValue`.  That breaks the fundamental theorem's Π-INTRODUCTION arm,
which needs every codomain candidate to be head-expansion-closed (`HeadExpansionClosed`) — and the empty type
genuinely appears as a Π codomain after a polymorphic instantiation `X ↦ Empty`.

`emptyTaitCandidate` is the CORRECT empty candidate: "strongly normalizing AND every reachable normal form is
neutral".  It is the Girard-style bottom candidate with the WIDE neutral notion (an application is neutral
regardless of its head), expressed via the reduction-stable property "no reachable normal form is an
introduction" (equivalently, every reachable normal form is `IsNeutral`):

  * **No closed member** — a closed strongly-normalizing term reaches a closed normal form, which the candidate
    forces neutral, but closed neutrals do not exist (`IsNeutral.noClosed`).  This is the consistency core:
    `emptyTypeCell`'s candidate has no closed inhabitant.
  * **Reducibility candidate** (CR1/CR2/CR3) — CR1 is the first conjunct; CR2 (forward `Step` closure) prepends
    the step to each reachable-normal-form chain; CR3 (neutral expansion) splits the reduction chain at its
    head (refl gives the term's own neutrality, trans delegates to a reduct member).
  * **Head-expansion-closed** (`HeadExpansionClosed`) — a spined β-redex inherits membership from its
    contractum: the redex is strongly normalizing (`betaSpineHeadExpansion`), and any reachable normal form,
    by confluence (`confluence_of_localJoin_and_accessible`) with the single betaSpine step to the contractum
    plus the normal form's rigidity (`eq_of_noStep`), is also reachable from the contractum, hence neutral.
  * **Member weak-head expansion** — the general-`WeakHeadStep` analogue, by the same confluence argument; the
    member weak-head-expansion engine consumes it.

This is what makes the candidate-bridge edit VIABLE through the whole fundamental theorem: `emptyTaitCandidate`
behaves like every other reducibility candidate (it is head-expansion-closed), so the Π-intro / member /
forward / determinism machinery all flow mechanically when `emptyTypeCell` is pinned to it.

## Zero-axiom verification

CR1/CR2/CR3 are projections + a two-arm `cases` on `StepStar`; head-expansion and member weak-head expansion
are per-term confluence (`Acc.ndrec`, axiom-clean) + `eq_of_noStep`.  No `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The head-expansion-closed empty (bottom) Tait candidate.**  "Strongly normalizing AND every reachable
normal form is neutral."  The Girard bottom candidate (wide-neutral notion), expressed reduction-stably so it
is head-expansion-closed.  Contrast `CanonicalFormsPredicate emptyIsValue` (members must be neutral
THEMSELVES), which is not head-expansion-closed. -/
def emptyTaitCandidate {scope : Nat} (term : RawTerm scope) : Prop :=
  IsStronglyNormalizing term ∧
    ∀ normalForm : RawTerm scope, StepStar term normalForm →
      RawTerm.isStepNormalForm normalForm → IsNeutral normalForm

/-- **CR1: every member is strongly normalizing** — the first conjunct. -/
theorem emptyTaitCandidate.stronglyNormalizing {scope : Nat} {term : RawTerm scope}
    (member : emptyTaitCandidate term) : IsStronglyNormalizing term := member.1

/-- **No closed member — the consistency core.**  A closed member reaches a closed normal form
(`exists_normalForm_of_isStronglyNormalizing`), which the candidate forces `IsNeutral`; but no closed term is
neutral (`IsNeutral.noClosed`).  So the empty Tait candidate has no closed inhabitant: combined with the
candidate bridge (`emptyTypeCell`'s reducibility candidate IS this), no closed term inhabits the empty type. -/
theorem emptyTaitCandidate.noClosedMember {term : RawTerm 0}
    (member : emptyTaitCandidate term) : False := by
  obtain ⟨normalForm, reachesNF, nfIsNormal⟩ := exists_normalForm_of_isStronglyNormalizing member.1
  exact IsNeutral.noClosed (member.2 normalForm reachesNF nfIsNormal)

/-- **CR2: forward closure under one `Step`.**  A reduct is strongly normalizing (`Acc.inv`), and any normal
form reachable from the reduct is reachable from the term (prepend the step), hence neutral. -/
theorem emptyTaitCandidate.closedUnderStep {scope : Nat} {term reduct : RawTerm scope}
    (member : emptyTaitCandidate term) (step : Step term reduct) : emptyTaitCandidate reduct := by
  refine ⟨member.1.inv step, ?_⟩
  intro normalForm reductToNF nfIsNormal
  exact member.2 normalForm (StepStar.trans step reductToNF) nfIsNormal

/-- **CR3: neutral expansion.**  A neutral term whose every one-step reduct is a member is a member: it is
strongly normalizing (all reducts are, `Acc.intro`), and any reachable normal form chain splits at the head —
the reflexive chain gives the term's own neutrality, a `trans` chain delegates to the reduct member. -/
theorem emptyTaitCandidate.neutralExpansion {scope : Nat} {term : RawTerm scope}
    (termIsNeutral : IsNeutral term)
    (reductsMembers : ∀ reduct : RawTerm scope, Step term reduct → emptyTaitCandidate reduct) :
    emptyTaitCandidate term := by
  refine ⟨?stronglyNormalizing, ?reachableNeutral⟩
  case stronglyNormalizing =>
    exact Acc.intro term (fun reduct stepToReduct => (reductsMembers reduct stepToReduct).1)
  case reachableNeutral =>
    intro normalForm termToNF nfIsNormal
    cases termToNF with
    | refl _ => exact termIsNeutral
    | trans termHeadStep tailChain =>
        exact (reductsMembers _ termHeadStep).2 normalForm tailChain nfIsNormal

/-- **The empty Tait candidate IS a Girard reducibility candidate** (CR1+CR2+CR3). -/
theorem emptyTaitCandidate_isReducibilityCandidate {scope : Nat} :
    IsReducibilityCandidate (emptyTaitCandidate (scope := scope)) :=
  ⟨emptyTaitCandidate.stronglyNormalizing,
   emptyTaitCandidate.closedUnderStep,
   emptyTaitCandidate.neutralExpansion⟩

/-- **Head-expansion-closed — the property `CanonicalFormsPredicate emptyIsValue` lacks.**  A spined β-redex
inherits membership from its contractum: it is strongly normalizing (`betaSpineHeadExpansion`), and any
reachable normal form — by per-term confluence with the single `betaSpine` step to the contractum, plus the
normal form's rigidity (`eq_of_noStep`) collapsing the join apex onto it — is reachable from the contractum,
hence neutral.  This is exactly what the fundamental theorem's Π-introduction arm needs of every codomain
candidate (`DependentArrowCandidate.abstraction`). -/
theorem emptyTaitCandidate_headExpansionClosed {scope : Nat} :
    HeadExpansionClosed (emptyTaitCandidate (scope := scope)) := by
  intro body argument spine argumentSN contractumMember
  refine ⟨betaSpineHeadExpansion argumentSN contractumMember.1, ?_⟩
  intro normalForm redexToNF nfIsNormal
  have redexToContractum : StepStar
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine)
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    StepStar.single (WeakHeadStep.betaSpine).toStep
  obtain ⟨commonReduct, normalFormToCommon, contractumToCommon⟩ :=
    confluence_of_localJoin_and_accessible
      (betaSpineHeadExpansion argumentSN contractumMember.1) redexToNF redexToContractum
  have commonEqNormalForm : commonReduct = normalForm :=
    StepStar.eq_of_noStep (fun reduct step =>
      (RawTerm.isStepNormalForm_blocks_step nfIsNormal reduct step).elim) normalFormToCommon
  rw [commonEqNormalForm] at contractumToCommon
  exact contractumMember.2 normalForm contractumToCommon nfIsNormal

/-- **Member weak-head expansion (general `WeakHeadStep`).**  A term that weak-head-steps to a member is a
member (given it is strongly normalizing): by the same confluence argument as `headExpansionClosed`, any
reachable normal form is reachable from the contractum, hence neutral.  The general-`WeakHeadStep` analogue
of head-expansion closure that the member weak-head-expansion engine consumes. -/
theorem emptyTaitCandidate_memberWeakHeadExpansion {scope : Nat}
    {source reduct : RawTerm scope} (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source) (reductMember : emptyTaitCandidate reduct) :
    emptyTaitCandidate source := by
  refine ⟨sourceStronglyNormalizing, ?_⟩
  intro normalForm sourceToNF nfIsNormal
  obtain ⟨commonReduct, normalFormToCommon, reductToCommon⟩ :=
    confluence_of_localJoin_and_accessible sourceStronglyNormalizing sourceToNF
      (StepStar.single weakHeadStep.toStep)
  have commonEqNormalForm : commonReduct = normalForm :=
    StepStar.eq_of_noStep (fun reduct step =>
      (RawTerm.isStepNormalForm_blocks_step nfIsNormal reduct step).elim) normalFormToCommon
  rw [commonEqNormalForm] at reductToCommon
  exact reductMember.2 normalForm reductToCommon nfIsNormal

end FX1Poly.Core
