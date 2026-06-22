import FX1Poly.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember
import FX1Poly.Core.Metatheory.Canonicity.BoolCanonicalFormsCandidate
import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation

/-! # FX1Poly/Core/BoolElimGeneralCandidateMember
    — `boolElim` over a reducible scrutinee lands in ANY reducibility candidate (the data-eliminator FT core)

`boolElimReducibleScrutineeMember` (DataEliminatorReducibleScrutineeMember) brought `boolElim` to general-scrutinee
reducibility but ONLY into a `CanonicalFormsPredicate` result candidate: its value-case lift-back
(`ofStepStarReachingValue`) is canonical-forms-specific (membership IS "reaches a value", trivially backward-closed
under the scrutinee's general `StepStar`).  The native bounded data-eliminator fundamental-theorem rows need
`boolElim` to land in an ARBITRARY reducibility candidate (the motive's instantiated output type — possibly Π,
universe, or another data candidate), whose membership is NOT backward-closed under arbitrary reduction.

The standard Tait dispatch (neutral → CR3, value → fire ι, reducible → head-expand) supplies the answer, but its
"reducible" branch must reduce the scrutinee by a WEAK-HEAD step (the only reduction a candidate absorbs backward,
via the shipped member weak-head expansion).  The crux is a clean, dichotomy-free fact:

`boolReachesValue_isValue_or_hasWeakHeadStep`: a term that reduces (multi-step) to a boolean value is EITHER
already that value OR has a weak-head step.  No decidable "has-a-weak-head-step" oracle is needed — the proof is an
induction on the reduction whose only non-trivial move pulls a downstream weak-head step back across one step by
`WeakHeadStep.reflectAlongStep` (a single step never destroys a weak-head redex), with the "reached value is a
cong-reduct" sub-case refuted because a boolean value is a CHILDLESS constructor (no child can have stepped).

With it, `boolElimReducibleMemberGeneral` is the textbook SN-induction on the scrutinee for a general candidate:
NEUTRAL scrutinee → the cell is neutral+SN (CR3); a scrutinee that REACHES A VALUE is either the value (fire ι by
`boolElimValueReducibility`) or weak-head-reduces (lift the inductive hypothesis on the smaller weak-head reduct
back to the cell through `WeakHeadStep.scrutineeBoolElim` + the candidate's weak-head expansion `headExpand`).

## Zero-axiom verification

`boolReachesValue_…` is an `induction` on `StepStar` + `Step.weakHeadStep_or_cong` + `WeakHeadStep.reflectAlongStep`
+ the childless-constructor `cases childStep` refutation (the proven nullary-cong-impossible idiom of
`WeakHeadNormalPreservation`).  `boolElimReducibleMemberGeneral` is a well-founded `Acc` induction on the
scrutinee's strong normalization feeding the shipped `boolElimValueReducibility` /
`memberOfStronglyNormalizingNeutral` (passed as the candidate's CR1/CR3 + weak-head-expansion interface).  No
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

/-- **`boolElim` over a reducible scrutinee is a member of an ARBITRARY reducibility candidate.**  Given a result
candidate with CR1 (`candidateMembersStronglyNormalizing`), member weak-head expansion (`headExpand`), and CR3
(`memberOfStronglyNormalizingNeutral`), a strongly-normalizing motive, reducible branches, and a scrutinee that is
a member of the bool data candidate, the `boolElim` cell is a member of the result candidate.  Well-founded
induction on the scrutinee's strong normalization: NEUTRAL scrutinee → the cell is neutral and SN (CR3); a
scrutinee that reaches a value is, by `boolReachesValue_isValue_or_hasWeakHeadStep`, either the value (fire the ι by
`boolElimValueReducibility`) or has a weak-head reduct (a smaller bool member; lift its cell membership — the
inductive hypothesis — back through `WeakHeadStep.scrutineeBoolElim` by `headExpand`).  The general-candidate
strengthening of `boolElimReducibleScrutineeMember` the native bounded data-eliminator FT row consumes. -/
theorem boolElimReducibleMemberGeneral {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersStronglyNormalizing :
      ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (thenBranchMember : resultCandidate thenBranch)
    (elseBranchMember : resultCandidate elseBranch)
    {scrutinee : RawTerm scope}
    (scrutineeMember : CanonicalFormsPredicate boolIsValue scrutinee) :
    resultCandidate (boolElimSpine motive scrutinee thenBranch elseBranch) := by
  have thenBranchStronglyNormalizing := candidateMembersStronglyNormalizing thenBranchMember
  have elseBranchStronglyNormalizing := candidateMembersStronglyNormalizing elseBranchMember
  have redexStronglyNormalizing : ∀ {value : RawTerm scope}, boolIsValue value →
      IsStronglyNormalizing (boolElimSpine motive value thenBranch elseBranch) :=
    fun valueIsBool =>
      boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
        (boolValue_isStronglyNormalizing valueIsBool) motiveStronglyNormalizing
        thenBranchStronglyNormalizing elseBranchStronglyNormalizing
  suffices general : ∀ {currentScrutinee : RawTerm scope}, Acc StepSuccessor currentScrutinee →
      CanonicalFormsPredicate boolIsValue currentScrutinee →
      resultCandidate (boolElimSpine motive currentScrutinee thenBranch elseBranch) from
    general scrutineeMember.stronglyNormalizing scrutineeMember
  intro currentScrutinee accessible
  induction accessible with
  | intro focus _predecessorsAccessible inductiveHypothesis =>
      intro member
      have cellStronglyNormalizing :
          IsStronglyNormalizing (boolElimSpine motive focus thenBranch elseBranch) :=
        boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
          member.stronglyNormalizing motiveStronglyNormalizing
          thenBranchStronglyNormalizing elseBranchStronglyNormalizing
      rcases member.2 with focusNeutral | ⟨_value, focusReachesValue, valueIsBool⟩
      · exact memberOfStronglyNormalizingNeutral cellStronglyNormalizing (IsNeutral.boolElim focusNeutral)
      · rcases boolReachesValue_isValue_or_hasWeakHeadStep focusReachesValue valueIsBool with
          focusIsValue | ⟨focusReduct, focusWeakHead⟩
        · exact boolElimValueReducibility resultCandidate headExpand thenBranchMember
            elseBranchMember redexStronglyNormalizing focusIsValue
        · have reductMember : CanonicalFormsPredicate boolIsValue focusReduct :=
            boolCanonicalFormsCandidate.closedUnderStep member focusWeakHead.toStep
          have cellReductMember :
              resultCandidate (boolElimSpine motive focusReduct thenBranch elseBranch) :=
            inductiveHypothesis focusReduct focusWeakHead.toStep reductMember
          exact headExpand (WeakHeadStep.scrutineeBoolElim focusWeakHead) cellReductMember
            cellStronglyNormalizing

/-- **Dependent `boolElim` reducibility: the cell lands in the candidate of the motive at the scrutinee.**  The
genuinely-dependent strengthening: the result type is `motive(scrutinee)`, so the branches inhabit DIFFERENT
types — `thenBranch : motive(true)`, `elseBranch : motive(false)` — and the cell `motive(scrutinee)`.  By
conversion-invariance of reducibility, `candidate(motive(scrutinee)) = candidate(motive(value))` for any `value`
the scrutinee reaches, so a SINGLE `resultCandidate` (= the cell's) suffices, and the ι-selected branch lands in
it WHEN the scrutinee reaches the matching value.  That conditioning is exactly the two `…IfReaches…`
hypotheses, which the bounded data-eliminator row discharges from the motive's reducibility (the per-value
candidate equals `resultCandidate` because `motive(scrutinee) ↠ motive(value)` and reducibility is
forward-closed).

Same dichotomy-free SN-induction as `boolElimReducibleMemberGeneral`, but the scrutinee's reachability of the
current focus (`StepStar scrutinee focus`) is THREADED so the value case can invoke the right conditional branch
membership (the focus, being a reduct of the scrutinee that is a value, reaches that value from the scrutinee).
Motive strong-normalization is a genuine hypothesis now (the dependent motive carries a well-formedness
obligation — a type family is a reducible type, hence SN), which is what the cell's strong normalization needs. -/
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
    (scrutineeMember : CanonicalFormsPredicate boolIsValue scrutinee)
    (thenBranchMemberIfReachesTrue :
      StepStar scrutinee boolTrueCell → resultCandidate thenBranch)
    (elseBranchMemberIfReachesFalse :
      StepStar scrutinee boolFalseCell → resultCandidate elseBranch) :
    resultCandidate (boolElimSpine motive scrutinee thenBranch elseBranch) := by
  suffices general : ∀ {focus : RawTerm scope}, Acc StepSuccessor focus →
      CanonicalFormsPredicate boolIsValue focus → StepStar scrutinee focus →
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
      rcases member.2 with focusNeutral | ⟨_value, focusReachesValue, valueIsBool⟩
      · exact memberOfStronglyNormalizingNeutral cellStronglyNormalizing (IsNeutral.boolElim focusNeutral)
      · rcases boolReachesValue_isValue_or_hasWeakHeadStep focusReachesValue valueIsBool with
          focusIsValue | ⟨focusReduct, focusWeakHead⟩
        · rcases focusIsValue with focusEquation | focusEquation
          · subst focusEquation
            exact headExpand IotaHeadStep.iotaBoolTrue.toWeakHeadStep
              (thenBranchMemberIfReachesTrue reaches) cellStronglyNormalizing
          · subst focusEquation
            exact headExpand IotaHeadStep.iotaBoolFalse.toWeakHeadStep
              (elseBranchMemberIfReachesFalse reaches) cellStronglyNormalizing
        · have reductMember : CanonicalFormsPredicate boolIsValue focusReduct :=
            boolCanonicalFormsCandidate.closedUnderStep member focusWeakHead.toStep
          have reductReaches : StepStar scrutinee focusReduct :=
            StepStar.trans_compose reaches (StepStar.single focusWeakHead.toStep)
          have cellReductMember :
              resultCandidate (boolElimSpine motive focusReduct thenBranch elseBranch) :=
            inductiveHypothesis focusReduct focusWeakHead.toStep reductMember reductReaches
          exact headExpand (WeakHeadStep.scrutineeBoolElim focusWeakHead) cellReductMember
            cellStronglyNormalizing

end FX1Poly.Core
