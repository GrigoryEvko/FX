import FX1Poly.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Rewriting.Normalize.NeutralReflectAlongStep

/-! # FX1Poly/Core/BoolElimGeneralCandidateMember
    — dependent `boolElim` over a `dataTaitCandidate` scrutinee lands in the candidate of the motive at the scrutinee

The native bounded data-eliminator fundamental-theorem rows need `boolElim` to land in an ARBITRARY reducibility
candidate (the dependent motive's instantiated output type `motive(scrutinee)` — possibly Π, universe, or another
data candidate), whose membership is NOT backward-closed under arbitrary reduction, only along a WEAK-HEAD step
(its `headExpand` interface).  AND the scrutinee arrives as a member of the HEAD-EXPANSION-CLOSED `dataTaitCandidate
boolIsValue` (the candidate the §5 reducibility model pins `boolTypeCell` to — "SN ∧ every reachable normal form is
a value or neutral"), NOT the older `CanonicalFormsPredicate boolIsValue`: `dataTaitCandidate ⊋ CanonicalFormsPredicate`
(a β-redex reducing to a neutral satisfies the former but not the latter — its head is a λ, not stuck, and it never
reaches a value), so the bounded bool member cannot be downgraded.

The standard Tait dispatch (value → fire ι, weak-head-reducible → head-expand the IH on the smaller reduct, neutral
→ CR3) drives a well-founded `Acc` induction on the scrutinee, peeling its WEAK-HEAD steps one at a time (the only
reduction the general result candidate absorbs backward).  The per-focus classifier is the trichotomy
`boolDataTaitFocusTrichotomy`: a `dataTaitCandidate boolIsValue` member is a boolean value, OR has a weak-head step,
OR is neutral.  Its proof reaches the member's normal form (SN), reads off value-or-neutral
(`dataTaitCandidate`'s second projection), and reflects that status BACK to the focus —
`boolReachesValue_isValue_or_hasWeakHeadStep` for the value case, `IsNeutral.reflectAlongStepStar` for the neutral
case (a term reaching a neutral is neutral or has a weak-head step).

## Zero-axiom verification

`boolReachesValue_…` is an `induction` on `StepStar` + `Step.weakHeadStep_or_cong` + `WeakHeadStep.reflectAlongStep`
+ the childless-constructor `cases childStep` refutation.  `boolDataTaitFocusTrichotomy` composes
`exists_normalForm_of_isStronglyNormalizing` with `boolReachesValue_…` / `IsNeutral.reflectAlongStepStar`.
`boolElimDependentReducibleMember` is a well-founded `Acc` induction on the scrutinee's strong normalization
threading `StepStar scrutinee focus`, feeding `IotaHeadStep.iotaBool…` head expansion / the candidate's CR3 +
weak-head-expansion interface; the IH recurses on the weak-head reduct via `dataTaitCandidate.closedUnderStep`.  No
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
open StepStar

/-- **A term reaching a boolean value is that value or has a weak-head step.**  If `start ↠ finish` and `finish`
is `true`/`false`, then either `start` already is a boolean value or `start` has a weak-head redex.  Induction on
the reduction: a weak-head first step gives the redex directly; a congruence (internal) first step recurses — the
reduct cannot itself be the value (a value is a childless constructor, but a congruence reduct has a stepped child,
refuted by `cases childStep`), so the reduct has a weak-head step that `WeakHeadStep.reflectAlongStep` pulls back to
`start`.  No decidable weak-head-normal-form oracle is used. -/
theorem boolReachesValue_isValue_or_hasWeakHeadStep {scope : Nat} :
    ∀ {start finish : RawTerm scope}, StepStar start finish → boolIsValue finish →
      boolIsValue start ∨ (∃ reduct : RawTerm scope, WeakHeadStep start reduct) := by
  intro start finish chain
  induction chain with
  | refl _ => intro finishIsBool; exact Or.inl finishIsBool
  | trans firstStep _restChain restInductiveHypothesis =>
      intro finishIsBool
      rcases Step.weakHeadStep_or_cong firstStep with
        ⟨weakHeadReduct, weakHeadOnStart⟩
        | ⟨generator, payload, children, childrenAfter, _startEquation, midEquation, childStep⟩
      · exact Or.inr ⟨weakHeadReduct, weakHeadOnStart⟩
      · rcases restInductiveHypothesis finishIsBool with midIsValue | ⟨_midReduct, midWeakHead⟩
        · exfalso
          rw [midEquation] at midIsValue
          rcases midIsValue with valueEquation | valueEquation
          · have generatorEquation : generator = Generator.gen_boolTrue :=
              congrArg RawTerm.rootGenerator valueEquation
            subst generatorEquation
            injection valueEquation with _scopeEquation _generatorEquation _payloadEquation childrenEquation
            subst childrenEquation
            cases childStep
          · have generatorEquation : generator = Generator.gen_boolFalse :=
              congrArg RawTerm.rootGenerator valueEquation
            subst generatorEquation
            injection valueEquation with _scopeEquation _generatorEquation _payloadEquation childrenEquation
            subst childrenEquation
            cases childStep
        · exact Or.inr (WeakHeadStep.reflectAlongStep midWeakHead firstStep)

/-- **The per-focus trichotomy for a `dataTaitCandidate boolIsValue` member.**  A member of the bool data
candidate is EITHER a boolean value, OR has a weak-head step, OR is neutral — the classification the dependent
eliminator's SN-induction dispatches on at each focus.  Proof: reach the member's normal form (SN), read off
value-or-neutral (`dataTaitCandidate`'s second projection), then reflect that status BACK to the focus —
`boolReachesValue_isValue_or_hasWeakHeadStep` for the value case (a term reaching a boolean value is the value or
weak-head-steps), `IsNeutral.reflectAlongStepStar` for the neutral case (a term reaching a neutral is neutral or
weak-head-steps). -/
theorem boolDataTaitFocusTrichotomy {scope : Nat} {focus : RawTerm scope}
    (member : dataTaitCandidate boolIsValue focus) :
    boolIsValue focus ∨ (∃ reduct : RawTerm scope, WeakHeadStep focus reduct) ∨ IsNeutral focus := by
  obtain ⟨normalForm, focusToNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.stronglyNormalizing
  rcases member.2 normalForm focusToNormalForm normalFormIsNormal with
    normalFormIsBool | normalFormIsNeutral
  · rcases boolReachesValue_isValue_or_hasWeakHeadStep focusToNormalForm normalFormIsBool with
      focusIsValue | weakHead
    · exact Or.inl focusIsValue
    · exact Or.inr (Or.inl weakHead)
  · rcases IsNeutral.reflectAlongStepStar focusToNormalForm normalFormIsNeutral with
      weakHead | focusNeutral
    · exact Or.inr (Or.inl weakHead)
    · exact Or.inr (Or.inr focusNeutral)

/-- **Dependent `boolElim` reducibility: the cell lands in the candidate of the motive at the scrutinee.**  The
genuinely-dependent strengthening: the result type is `motive(scrutinee)`, so the branches inhabit DIFFERENT
types — `thenBranch : motive(true)`, `elseBranch : motive(false)` — and the cell `motive(scrutinee)`.  By
conversion-invariance of reducibility, `candidate(motive(scrutinee)) = candidate(motive(value))` for any `value`
the scrutinee reaches, so a SINGLE `resultCandidate` (= the cell's) suffices, and the ι-selected branch lands in
it WHEN the scrutinee reaches the matching value.  That conditioning is exactly the two `…IfReaches…`
hypotheses, which the bounded data-eliminator row discharges from the motive's reducibility (the per-value
candidate equals `resultCandidate` because `motive(scrutinee) ↠ motive(value)` and reducibility is
forward-closed).

The scrutinee arrives as a member of the head-expansion-closed `dataTaitCandidate boolIsValue` (the candidate the
§5 model pins `boolTypeCell` to), NOT `CanonicalFormsPredicate` (`dataTaitCandidate ⊋ CanonicalFormsPredicate`).
A well-founded `Acc` induction on the scrutinee, with the scrutinee's reachability of the current focus
(`StepStar scrutinee focus`) THREADED so the value case can invoke the right conditional branch membership (the
focus, being a reduct of the scrutinee that is a value, reaches that value from the scrutinee).  Per-focus
classification is `boolDataTaitFocusTrichotomy`; the weak-head-reducible case recurses on the smaller reduct via
`dataTaitCandidate.closedUnderStep`.  Motive strong-normalization is a genuine hypothesis (the dependent motive
carries a well-formedness obligation — a type family is a reducible type, hence SN), which is what the cell's
strong normalization needs. -/
theorem boolElimDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (thenBranchStronglyNormalizing : IsStronglyNormalizing thenBranch)
    (elseBranchStronglyNormalizing : IsStronglyNormalizing elseBranch)
    (scrutineeMember : dataTaitCandidate boolIsValue scrutinee)
    (thenBranchMemberIfReachesTrue :
      StepStar scrutinee boolTrueCell → resultCandidate thenBranch)
    (elseBranchMemberIfReachesFalse :
      StepStar scrutinee boolFalseCell → resultCandidate elseBranch) :
    resultCandidate (boolElimSpine motive scrutinee thenBranch elseBranch) := by
  suffices general : ∀ {focus : RawTerm scope}, Acc StepSuccessor focus →
      dataTaitCandidate boolIsValue focus → StepStar scrutinee focus →
      resultCandidate (boolElimSpine motive focus thenBranch elseBranch) from
    general scrutineeMember.stronglyNormalizing scrutineeMember (StepStar.refl scrutinee)
  intro focus accessible
  induction accessible with
  | intro currentFocus _predecessorsAccessible inductiveHypothesis =>
      intro member reaches
      have cellStronglyNormalizing :
          IsStronglyNormalizing (boolElimSpine motive currentFocus thenBranch elseBranch) :=
        boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
          member.stronglyNormalizing motiveStronglyNormalizing
          thenBranchStronglyNormalizing elseBranchStronglyNormalizing
      rcases boolDataTaitFocusTrichotomy member with
        focusIsValue | ⟨focusReduct, focusWeakHead⟩ | focusNeutral
      · rcases focusIsValue with focusEquation | focusEquation
        · subst focusEquation
          exact headExpand IotaHeadStep.iotaBoolTrue.toWeakHeadStep
            (thenBranchMemberIfReachesTrue reaches) cellStronglyNormalizing
        · subst focusEquation
          exact headExpand IotaHeadStep.iotaBoolFalse.toWeakHeadStep
            (elseBranchMemberIfReachesFalse reaches) cellStronglyNormalizing
      · have reductMember : dataTaitCandidate boolIsValue focusReduct :=
          member.closedUnderStep focusWeakHead.toStep
        have reductReaches : StepStar scrutinee focusReduct :=
          StepStar.trans_compose reaches (StepStar.single focusWeakHead.toStep)
        have cellReductMember :
            resultCandidate (boolElimSpine motive focusReduct thenBranch elseBranch) :=
          inductiveHypothesis focusReduct focusWeakHead.toStep reductMember reductReaches
        exact headExpand (WeakHeadStep.scrutineeBoolElim focusWeakHead) cellReductMember
          cellStronglyNormalizing
      · exact memberOfStronglyNormalizingNeutral cellStronglyNormalizing (IsNeutral.boolElim focusNeutral)

end FX1Poly.Core
