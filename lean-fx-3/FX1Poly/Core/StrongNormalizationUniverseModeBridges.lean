import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Core/StrongNormalizationUniverseModeBridges
    — structural SN closure for the 2LTT universe-mode bridge operators (precursor to their reducibility)

`StrongNormalizationModalEliminators.lean` ships the congruence SN closure for the modal-core operators
(`gen_modElim` / `gen_subsume`).  This file does the same for the two UNIVERSE-MODE bridge operators of the
2-level universe stack: the inner→outer lift `gen_liftInnerToOuter` (one child, the inner term) and the
outer→inner lower `gen_lowerOuterToInner` (two children, the outer term + its cofibrancy witness).

Both are congruence-only under the β+ι reduction relation `Step`: the `Step` inductive has iota rules for
beta / boolElim / fst / snd / natElim / natRec / listElim / optionMatch / eitherMatch / idJ / idStrictRec, but
NONE for `gen_liftInnerToOuter` or `gen_lowerOuterToInner` — their mode-bridge computation rule
(`lower (lift x) ↝ x`) is not part of the current β+ι substrate (cf. `gen_modElim`, whose modal collapse is
raw η).  So under `Step` a reduction out of a `liftInnerToOuter`- or `lowerOuterToInner`-rooted term reduces
exactly its child(ren), and accessibility lifts via the shipped one-child / two-child congruence SN closures.

This is the strong-normalization precursor of universe-mode bridge reducibility; the value-case
reducibility candidate awaits the mode-bridge ι-rule, exactly as the modal `modElim`
reducibility awaits its ι-rule.

## Zero-axiom verification

The inversions are `cases reduction` (only the `cong` constructor matches a bridge head — no iota rule does) +
`cases childStep` down the one-child / two-child `StepChildren` spine, closing the empty-spine tail with
`StepChildren.no_step_at_empty_spine`; the SN closures are direct `isStronglyNormalizing_of_oneChildCong` /
`isStronglyNormalizing_of_twoChildCong` applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `liftInnerToOuter`-rooted Step.**  `gen_liftInnerToOuter` is a one-child universe-mode
bridge with no β+ι root rule (its mode-bridge collapse is not in the current substrate), so a `Step` out of it
reduces exactly its inner-term child. -/
theorem Step.from_liftInnerToOuter
    {scope : Nat} {innerTerm : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_liftInnerToOuter () (.childCons innerTerm .childNil)) target) :
    ∃ (innerAfter : RawTerm scope),
      target = .mkGen .gen_liftInnerToOuter () (.childCons innerAfter .childNil) ∧
      Step innerTerm innerAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ innerStep =>
          rename_i innerAfter
          exact ⟨innerAfter, rfl, innerStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `lowerOuterToInner`-rooted Step.**  `gen_lowerOuterToInner` is a two-child universe-mode
bridge (outer term + cofibrancy witness, both at the ambient scope) with no β+ι root rule, congruence-only: a
`Step` out of it reduces exactly one of its two children. -/
theorem Step.from_lowerOuterToInner
    {scope : Nat} {outerTerm cofibrancy : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_lowerOuterToInner ()
              (.childCons outerTerm (.childCons cofibrancy .childNil))) target) :
    (∃ (outerAfter : RawTerm scope),
        target = .mkGen .gen_lowerOuterToInner ()
          (.childCons outerAfter (.childCons cofibrancy .childNil)) ∧
        Step outerTerm outerAfter)
    ∨
    (∃ (cofibrancyAfter : RawTerm scope),
        target = .mkGen .gen_lowerOuterToInner ()
          (.childCons outerTerm (.childCons cofibrancyAfter .childNil)) ∧
        Step cofibrancy cofibrancyAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ outerStep =>
          rename_i outerAfter
          exact Or.inl ⟨outerAfter, rfl, outerStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ cofibrancyStep =>
              rename_i cofibrancyAfter
              exact Or.inr ⟨cofibrancyAfter, rfl, cofibrancyStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- The inner→outer lift is strongly normalizing when its inner-term child is.  Congruence-only under β+ι
(`Step.from_liftInnerToOuter`), so accessibility of the child lifts via `isStronglyNormalizing_of_oneChildCong`. -/
theorem liftInnerToOuter_isStronglyNormalizing_of_child {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerTerminates : IsStronglyNormalizing innerTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_liftInnerToOuter () (.childCons innerTerm .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentInner =>
      (.mkGen .gen_liftInnerToOuter () (.childCons currentInner .childNil) : RawTerm scope))
    (fun parentStep => Step.from_liftInnerToOuter parentStep)
    innerTerminates

/-- The outer→inner lower is strongly normalizing when both its children (outer term + cofibrancy witness) are.
Congruence-only under β+ι (`Step.from_lowerOuterToInner`), via `isStronglyNormalizing_of_twoChildCong`. -/
theorem lowerOuterToInner_isStronglyNormalizing_of_children {scope : Nat}
    {outerTerm cofibrancy : RawTerm scope}
    (outerTerminates : IsStronglyNormalizing outerTerm)
    (cofibrancyTerminates : IsStronglyNormalizing cofibrancy) :
    IsStronglyNormalizing
      (.mkGen .gen_lowerOuterToInner ()
        (.childCons outerTerm (.childCons cofibrancy .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope)
    (secondScope := scope)
    (parentScope := scope)
    (fun currentOuter currentCofibrancy =>
      (.mkGen .gen_lowerOuterToInner ()
        (.childCons currentOuter (.childCons currentCofibrancy .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_lowerOuterToInner parentStep)
    outerTerminates
    cofibrancyTerminates

end StepStar
end FX1Poly.Core
