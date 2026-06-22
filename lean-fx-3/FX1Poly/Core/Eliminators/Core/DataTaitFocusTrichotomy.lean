import FX1Poly.Core.Rewriting.Normalize.NeutralReflectAlongStep
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/DataTaitFocusTrichotomy
    — the candidate-agnostic per-focus trichotomy shared by EVERY dependent data-eliminator general-candidate member

Every dependent data eliminator's general-candidate reducibility member (`boolElimDependentReducibleMember` and
its `option` / `either` / `nat` / `list` / `id` / `proj` siblings) drives the shared
`dependentDataEliminatorMemberFromValueDispatch` skeleton, whose `focusTrichotomy` premise asks: a member of the
scrutinee's head-expansion-closed `dataTaitCandidate` is EITHER a value, OR has a weak-head step, OR is neutral.
`boolDataTaitFocusTrichotomy` was the first instance, proved by a bool-specific `boolReachesValue…` lemma whose
value case refuted the congruence reduct by `cases childStep` — sound only because `true`/`false` are CHILDLESS,
so a congruence reduct (which steps a child) can never equal the value.

That refutation does NOT generalize to child-bearing value constructors (`some`, `cons`, `succ`, `pair`,
`inl`/`inr`, `refl`): a congruence reduct of `some payload` is `some payload'` — STILL a value.  The genuinely
general argument is cleaner and uses no childlessness: a congruence (non-weak-head) `Step` steps a CHILD, so it
PRESERVES the root generator (`Step.weakHeadStep_or_cong` exposes the shared `generator`).  Hence a term reaching
a value-HEADED normal form either already has that value head (it is a value) or its head must have changed —
which only a weak-head step can do.  This file factors that root-preservation argument OUT, keyed on an abstract
`valueHead : Generator → Prop` (the data constructor heads), so every eliminator's trichotomy is a one-liner:
reach the normal form (SN), read off value-or-neutral (`dataTaitCandidate`'s second projection), and reflect the
status back — `reachesValueHead_isValueHead_or_hasWeakHeadStep` for the value case, `IsNeutral.reflectAlongStepStar`
for the neutral case.

This is the FTGEN-11 unification on the dependent elimination side: the candidate-formation side already went
generic via `descriptorClosedCandidate`, the dispatch control flow via `dependentDataEliminatorMemberFromValue\
Dispatch`; the per-focus classifier is the last shared ingredient, and it lands here ONCE.

## Zero-axiom verification

`reachesValueHead_isValueHead_or_hasWeakHeadStep` is an `induction` on `StepStar` + `Step.weakHeadStep_or_cong` +
`WeakHeadStep.reflectAlongStep`, closing the congruence-value case by root-generator preservation (the reduct's
root equals the start's, both `mkGen generator …`).  `dataTaitFocusTrichotomyOfValueHead` composes
`exists_normalForm_of_isStronglyNormalizing` with it and `IsNeutral.reflectAlongStepStar`.  No `induction` on
data, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **A term reaching a value-HEADED normal form is value-headed or has a weak-head step.**  If `start ↠ finish`
and `finish`'s root generator is a `valueHead` (a data constructor), then either `start`'s root generator is
already that `valueHead` (so `start` is a value) or `start` has a weak-head redex.  Induction on the reduction: a
weak-head first step gives the redex directly; a congruence (internal child) first step PRESERVES the root
generator (`Step.weakHeadStep_or_cong` exposes the shared `generator` on both sides), so the reduct's value-head
status transfers straight back to `start`; and a reduct that instead has a weak-head step pulls one back to
`start` via `WeakHeadStep.reflectAlongStep`.  Generic over `valueHead` — no childlessness assumption (the bool
instance's `cases childStep` refutation is the childless special case of root preservation). -/
theorem reachesValueHead_isValueHead_or_hasWeakHeadStep {scope : Nat} {valueHead : Generator → Prop} :
    ∀ {start finish : RawTerm scope}, StepStar start finish → valueHead finish.rootGenerator →
      valueHead start.rootGenerator ∨ (∃ reduct : RawTerm scope, WeakHeadStep start reduct) := by
  intro start finish chain
  induction chain with
  | refl _ => intro finishValueHead; exact Or.inl finishValueHead
  | trans firstStep _restChain restInductiveHypothesis =>
      intro finishValueHead
      rcases Step.weakHeadStep_or_cong firstStep with
        ⟨weakHeadReduct, weakHeadOnStart⟩
        | ⟨generator, payload, children, childrenAfter, startEquation, midEquation, _childStep⟩
      · exact Or.inr ⟨weakHeadReduct, weakHeadOnStart⟩
      · rcases restInductiveHypothesis finishValueHead with midValueHead | ⟨_midReduct, midWeakHead⟩
        · -- The congruence step preserves the root generator: `start` and the reduct are both
          -- `mkGen generator payload …`, so the reduct's value head transfers straight back.
          refine Or.inl ?_
          rw [startEquation]
          rw [midEquation] at midValueHead
          exact midValueHead
        · exact Or.inr (WeakHeadStep.reflectAlongStep midWeakHead firstStep)

/-- **The generic per-focus trichotomy for a `dataTaitCandidate candidateValue` member.**  A member of the data
candidate is EITHER `conclusionValue`, OR has a weak-head step, OR is neutral — the classification the dependent
eliminator's SN-induction dispatches on at each focus.  TWO value predicates, bridged by the abstract `valueHead`
on the root generator: `candidateValue` is what the candidate's reachable normal forms satisfy (read off via
`valueHeadOfCandidateValue`), and `conclusionValue` is the (possibly weaker) constructor-head predicate the
dispatch fires the ι on (recovered via `conclusionValueOfValueHead`).  They DIFFER for child-bearing constructors
— e.g. option's candidate predicate `isOptionValue` requires a normal payload, but the conclusion
`isOptionConstructorHead` does not (a `some(redex)` focus is constructor-headed yet not a value, and is neither
weak-head-reducible nor neutral).  For childless constructors they coincide (pass one predicate twice).  Proof:
reach the member's normal form (SN), read off value-or-neutral (`dataTaitCandidate`'s second projection), then
reflect — `reachesValueHead_isValueHead_or_hasWeakHeadStep` for the value case (root preserved under congruence),
`IsNeutral.reflectAlongStepStar` for the neutral case. -/
theorem dataTaitFocusTrichotomyOfValueHead {scope : Nat} {valueHead : Generator → Prop}
    {candidateValue conclusionValue : RawTerm scope → Prop}
    (valueHeadOfCandidateValue : ∀ {term : RawTerm scope}, candidateValue term → valueHead term.rootGenerator)
    (conclusionValueOfValueHead : ∀ {term : RawTerm scope}, valueHead term.rootGenerator → conclusionValue term)
    {focus : RawTerm scope} (member : dataTaitCandidate candidateValue focus) :
    conclusionValue focus ∨ (∃ reduct : RawTerm scope, WeakHeadStep focus reduct) ∨ IsNeutral focus := by
  obtain ⟨normalForm, focusToNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.stronglyNormalizing
  rcases member.2 normalForm focusToNormalForm normalFormIsNormal with
    normalFormIsValue | normalFormIsNeutral
  · rcases reachesValueHead_isValueHead_or_hasWeakHeadStep (valueHead := valueHead) focusToNormalForm
      (valueHeadOfCandidateValue normalFormIsValue) with
      focusValueHead | weakHead
    · exact Or.inl (conclusionValueOfValueHead focusValueHead)
    · exact Or.inr (Or.inl weakHead)
  · rcases IsNeutral.reflectAlongStepStar focusToNormalForm normalFormIsNeutral with
      weakHead | focusNeutral
    · exact Or.inr (Or.inl weakHead)
    · exact Or.inr (Or.inr focusNeutral)

end FX1Poly.Core
