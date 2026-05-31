import FX1Poly.Core.StepStarConfluence

/-! # Foundation/PolyCell/Core/ConvNormalForm
    — normal-form rigidity of `StepStar` and the `Conv`-collapses-to-`Eq` seed

A term with no outgoing `Step` is *rigid* under `StepStar`: every reduction
chain out of it reaches only itself.  Consequently, when both endpoints of a
`Conv` (= `StepStar.Join`) have no outgoing `Step`, the shared reduct of the
join must equal each endpoint, so `Conv` collapses to plain equality.

This is the seed of **decidable `Conv` for the normal fragment**: for
terms that are already normal, `Conv` is exactly `Eq`, which the
propext-free `DecidableEq (RawTerm scope)` decides — no normalizer
required.  The general decider (eval + NF comparison) is needed only
for *non-normal* inputs; this file discharges the normal case directly.

The lemmas take the "no outgoing step" hypothesis as data
(`∀ reduct, Step source reduct → False`, the shape `noStep_var` /
`noStep_universeCode` / `isStronglyNormalizing_of_noStep` already produce), so
they are confluence-free and normalizer-free.

## Zero-axiom verification

`StepStar.eq_of_noStep` is a two-arm `cases` on the head-recursive `StepStar`
(`refl` / `trans`) whose indices are plain variables — propext-clean, the same
shape `confluence_of_localJoin_and_accessible` already uses zero-axiom in
`StepStarConfluence.lean`.  The `Conv` lemmas only destructure the `Join`
existential and apply rigidity to each leg.  Swept by
`#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

namespace StepStar

/-- A term with no outgoing one-step reduct is rigid under `StepStar`: any chain
out of `sourceTerm` reaches only `sourceTerm` itself.  The `trans` case is
impossible (its head step contradicts the no-step hypothesis); the `refl` case
is reflexivity. -/
theorem eq_of_noStep {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (sourceHasNoStep : ∀ reduct : RawTerm scope, Step sourceTerm reduct → False)
    (chain : StepStar sourceTerm targetTerm) :
    targetTerm = sourceTerm := by
  cases chain with
  | refl _ => rfl
  | trans headStep _tailChain => exact (sourceHasNoStep _ headStep).elim

end StepStar

namespace Conv

/-- When both endpoints have no outgoing `Step`, conversion collapses to
equality.  `Conv` exposes a common reduct reached from each endpoint; rigidity
forces that reduct to equal each (normal) endpoint, so the endpoints agree. -/
theorem eq_of_noStep {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (leftHasNoStep : ∀ reduct : RawTerm scope, Step leftTerm reduct → False)
    (rightHasNoStep : ∀ reduct : RawTerm scope, Step rightTerm reduct → False)
    (convertibility : Conv leftTerm rightTerm) :
    leftTerm = rightTerm := by
  obtain ⟨commonTerm, leftToCommon, rightToCommon⟩ := convertibility
  have commonIsLeft : commonTerm = leftTerm :=
    StepStar.eq_of_noStep leftHasNoStep leftToCommon
  have commonIsRight : commonTerm = rightTerm :=
    StepStar.eq_of_noStep rightHasNoStep rightToCommon
  exact commonIsLeft.symm.trans commonIsRight

/-- For no-step (normal) endpoints, conversion is exactly equality.  This is the
decidable-`Conv` seed: combined with `DecidableEq (RawTerm scope)` it decides
`Conv` on any pair of normal terms without a normalizer. -/
theorem iff_eq_of_noStep {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (leftHasNoStep : ∀ reduct : RawTerm scope, Step leftTerm reduct → False)
    (rightHasNoStep : ∀ reduct : RawTerm scope, Step rightTerm reduct → False) :
    Conv leftTerm rightTerm ↔ leftTerm = rightTerm := by
  constructor
  · exact Conv.eq_of_noStep leftHasNoStep rightHasNoStep
  · intro termsEqual
    subst termsEqual
    exact Conv.refl _

end Conv

end FX1Poly.Core
