import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Core/StrongNormalizationModalEliminators
    — structural SN closure for the modal elimination + subsumption operators (modal-core β+ι coverage)

`StrongNormalizationConstructors.lean` ships the one-child congruence SN closure for the modal box
INTRODUCTION (`modIntro_isStronglyNormalizing_of_value`).  This file completes the modal-core β+ι strong-
normalization coverage with the two remaining one-child modal operators: the modal ELIMINATION `gen_modElim`
and the modality SUBSUMPTION `gen_subsume`.

Both are congruence-only under the β+ι reduction relation `Step`: the `Step` inductive has iota rules for
beta / boolElim / fst / snd / natElim / natRec / listElim / optionMatch / eitherMatch / idJ / idStrictRec, but
NONE for `gen_modElim` or `gen_subsume`.  The modal collapse `modIntro (modElim m) ↝ m` lives in the separate
raw-η relation `Step.eta`, not in β+ι.  So under `Step` a reduction out of a `modElim`- or `subsume`-rooted
term reduces exactly its single child, and accessibility of that child lifts to the wrapped term via the
shipped `isStronglyNormalizing_of_oneChildCong` — exactly as for `modIntro` and the one-child data
constructors.

Together with `modIntro_isStronglyNormalizing_of_value` and `ModIntroCanonicalFormsCandidate.lean` (the modal
box reducibility candidate), this covers the β+ι metatheory of the three modal-core operators
(`gen_modIntro` / `gen_modElim` / `gen_subsume`) at the strong-normalization layer.

## Zero-axiom verification

The inversions are `cases reduction` (only the `cong` constructor matches a `modElim`/`subsume` head — no iota
rule does) + `cases childStep` down the one-child `StepChildren` spine, closing the empty-spine tail with
`StepChildren.no_step_at_empty_spine`; the SN closures are direct `isStronglyNormalizing_of_oneChildCong`
applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `modElim`-rooted Step.**  `gen_modElim` is a one-child modal eliminator with no β+ι root
rule (its only collapse, `modIntro (modElim m) ↝ m`, is raw η), so a `Step` out of it reduces exactly its
child. -/
theorem Step.from_modElim
    {scope : Nat} {modalTerm : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_modElim () (.childCons modalTerm .childNil)) target) :
    ∃ (modalAfter : RawTerm scope),
      target = .mkGen .gen_modElim () (.childCons modalAfter .childNil) ∧
      Step modalTerm modalAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ modalStep =>
          rename_i modalAfter
          exact ⟨modalAfter, rfl, modalStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `subsume`-rooted Step.**  `gen_subsume` is a one-child modality-subsumption operator with
no β+ι root rule, congruence-only. -/
theorem Step.from_subsume
    {scope : Nat} {subsumedTerm : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil)) target) :
    ∃ (subsumedAfter : RawTerm scope),
      target = .mkGen .gen_subsume () (.childCons subsumedAfter .childNil) ∧
      Step subsumedTerm subsumedAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ subsumedStep =>
          rename_i subsumedAfter
          exact ⟨subsumedAfter, rfl, subsumedStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- Modal elimination is strongly normalizing when its child is.  Congruence-only under β+ι
(`Step.from_modElim`), so accessibility of the child lifts via `isStronglyNormalizing_of_oneChildCong`. -/
theorem modElim_isStronglyNormalizing_of_child {scope : Nat}
    {modalTerm : RawTerm scope}
    (modalTerminates : IsStronglyNormalizing modalTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentModal =>
      (.mkGen .gen_modElim () (.childCons currentModal .childNil) : RawTerm scope))
    (fun parentStep => Step.from_modElim parentStep)
    modalTerminates

/-- Modality subsumption is strongly normalizing when its child is.  Congruence-only under β+ι
(`Step.from_subsume`), via `isStronglyNormalizing_of_oneChildCong`. -/
theorem subsume_isStronglyNormalizing_of_child {scope : Nat}
    {subsumedTerm : RawTerm scope}
    (subsumedTerminates : IsStronglyNormalizing subsumedTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentSubsumed =>
      (.mkGen .gen_subsume () (.childCons currentSubsumed .childNil) : RawTerm scope))
    (fun parentStep => Step.from_subsume parentStep)
    subsumedTerminates

end StepStar
end FX1Poly.Core
