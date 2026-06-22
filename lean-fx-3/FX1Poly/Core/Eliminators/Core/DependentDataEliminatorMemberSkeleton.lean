import FX1Poly.Core.Rewriting.Confluence.StepStarConfluence
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepSubsumes
import FX1Poly.Core.Substrate.Neutral.NeutralTerm

/-! # FX1Poly/Core/DependentDataEliminatorMemberSkeleton
    — the candidate-agnostic Tait dispatch shared by EVERY dependent data-eliminator reducibility member

Every dependent data eliminator (`boolElim`, `natElim`, `natRec`, `optionMatch`, `eitherMatch`, `idJ`, `fst`,
`snd`, `listElim`) lands its cell in an ARBITRARY result candidate (the motive instantiated at the scrutinee)
by the SAME well-founded `Acc` dispatch: peel the scrutinee's WEAK-HEAD steps one at a time (the only reduction
the general result candidate absorbs backward, via its `headExpand` interface), classifying each focus as a
value (fire the ι, transport the conditioned branch), a weak-head reduct (recurse on the smaller reduct), or a
neutral (CR3).  `boolElimDependentReducibleMember` was the first instance; this file factors its trichotomy
skeleton OUT so each subsequent eliminator supplies only its genuinely-per-eliminator data — the value
predicate, the spine function, that spine's SN / scrutinee-congruence / neutrality lemmas, and the
value-dispatch handler (which fires the ι and transports the matching branch).  The candidate, the SN
machinery, and the dispatch control flow are shared here.

This is the FTGEN-11 unification for the dependent elim-reducibility layer: the candidate-formation side
already went generic via `descriptorClosedCandidate`; this is the matching move on the elimination side.

## Zero-axiom verification

A well-founded `Acc StepSuccessor` induction on the scrutinee threading `StepStar scrutinee focus`, dispatching
on a supplied per-focus trichotomy and routing each branch through the supplied `headExpand` /
`memberOfStronglyNormalizingNeutral` candidate interface, the spine's congruence/neutrality reflections, and
the value handler.  No `induction` on data, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
open StepStar

/-- **The shared dependent data-eliminator Tait dispatch.**  Given a scrutinee that is a member of its data
candidate (`scrutineeCandidate`, closed under `Step` and strongly normalizing), and an eliminator whose cell is
`elimSpine focus` for the focus currently in scrutinee position, the eliminator cell is a member of an
arbitrary `resultCandidate` (the motive at the scrutinee) provided:

* `focusTrichotomy` — every candidate member is a value (`isValue`), or has a weak-head step, or is neutral;
* `spineStronglyNormalizing` — the cell is SN whenever the focus is (the motive/branch SNs are closed over);
* `spineScrutineeCongruence` — a focus weak-head step lifts to a cell weak-head step (scrutinee congruence);
* `spineNeutral` — a neutral focus makes the cell neutral;
* `headExpand` / `memberOfStronglyNormalizingNeutral` — the result candidate's CR-style closures;
* `valueHandler` — fires the ι and transports the matching branch when the focus is a value (the only
  genuinely per-constructor step; it gets the scrutinee-reaches-focus witness to invoke its conditioned
  branch memberships).

The `boolElim` / `natElim` / `optionMatch` / … members each instantiate this once. -/
theorem dependentDataEliminatorMemberFromValueDispatch {scope : Nat}
    {resultCandidate : RawTerm scope → Prop}
    {isValue : RawTerm scope → Prop}
    {scrutineeCandidate : RawTerm scope → Prop}
    {elimSpine : RawTerm scope → RawTerm scope}
    {scrutinee : RawTerm scope}
    (focusTrichotomy : ∀ {focus : RawTerm scope}, scrutineeCandidate focus →
        isValue focus ∨ (∃ reduct : RawTerm scope, WeakHeadStep focus reduct) ∨ IsNeutral focus)
    (candidateStronglyNormalizing : ∀ {focus : RawTerm scope},
        scrutineeCandidate focus → IsStronglyNormalizing focus)
    (candidateClosedUnderStep : ∀ {focus reduct : RawTerm scope},
        scrutineeCandidate focus → Step focus reduct → scrutineeCandidate reduct)
    (spineStronglyNormalizing : ∀ {focus : RawTerm scope},
        IsStronglyNormalizing focus → IsStronglyNormalizing (elimSpine focus))
    (spineScrutineeCongruence : ∀ {focus reduct : RawTerm scope},
        WeakHeadStep focus reduct → WeakHeadStep (elimSpine focus) (elimSpine reduct))
    (spineNeutral : ∀ {focus : RawTerm scope}, IsNeutral focus → IsNeutral (elimSpine focus))
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    (valueHandler : ∀ {focus : RawTerm scope}, isValue focus → StepStar scrutinee focus →
        IsStronglyNormalizing (elimSpine focus) → resultCandidate (elimSpine focus))
    (scrutineeMember : scrutineeCandidate scrutinee) :
    resultCandidate (elimSpine scrutinee) := by
  suffices general : ∀ {focus : RawTerm scope}, Acc StepSuccessor focus →
      scrutineeCandidate focus → StepStar scrutinee focus →
      resultCandidate (elimSpine focus) from
    general (candidateStronglyNormalizing scrutineeMember) scrutineeMember (StepStar.refl scrutinee)
  intro focus accessible
  induction accessible with
  | intro currentFocus _predecessorsAccessible inductiveHypothesis =>
      intro member reaches
      have cellStronglyNormalizing : IsStronglyNormalizing (elimSpine currentFocus) :=
        spineStronglyNormalizing (candidateStronglyNormalizing member)
      rcases focusTrichotomy member with
        focusIsValue | ⟨focusReduct, focusWeakHead⟩ | focusNeutral
      · exact valueHandler focusIsValue reaches cellStronglyNormalizing
      · have reductMember : scrutineeCandidate focusReduct :=
          candidateClosedUnderStep member focusWeakHead.toStep
        have reductReaches : StepStar scrutinee focusReduct :=
          StepStar.trans_compose reaches (StepStar.single focusWeakHead.toStep)
        have cellReductMember : resultCandidate (elimSpine focusReduct) :=
          inductiveHypothesis focusReduct focusWeakHead.toStep reductMember reductReaches
        exact headExpand (spineScrutineeCongruence focusWeakHead) cellReductMember
          cellStronglyNormalizing
      · exact memberOfStronglyNormalizingNeutral cellStronglyNormalizing (spineNeutral focusNeutral)

end FX1Poly.Core
