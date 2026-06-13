import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StepTable

/-! # FX1Poly/Core/StrongNormalizationLinearFormers
    — structural SN closure for the linear-logic type formers (linearArrow / tensorProduct)

`StrongNormalizationConstructors.lean` / `StrongNormalizationCodeFormers.lean` cover the data constructors and
the universe-code family.  This file extends the congruence-only former SN coverage to the LINEAR-LOGIC
generator family: the linear function space `gen_linearArrow` (source ⊸ target) and the multiplicative
conjunction `gen_tensorProduct` (leftFactor ⊗ rightFactor).

Both are two-child `[0, 0]` type formers with NO β+ι root rule (the `Step` inductive has no `iotaLinearArrow`
or `iotaTensorProduct` constructor), so they are congruence-only: a `Step` out of either reduces exactly one of
its two same-scope children.  Structurally they are identical to `gen_arrowCode` / `gen_productCode`, so the SN
closures are direct `isStronglyNormalizing_of_twoChildCong` applications over the shipped two-child congruence
combinator.

## Zero-axiom verification

The inversions are `cases reduction` (only `cong` matches a `linearArrow`/`tensorProduct` head — no iota rule
does) + nested `cases childStep` down the two-child `StepChildren` spine, closing the empty-spine tail with
`StepChildren.no_step_at_empty_spine`; the SN closures are direct `isStronglyNormalizing_of_twoChildCong`
applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `linearArrow`-rooted Step.**  `gen_linearArrow` is a two-child linear-function-space type
former with no β+ι root rule, congruence-only: a `Step` out of it reduces exactly the source or the target. -/
theorem Step.from_linearArrow
    {scope : Nat} {source target : RawTerm scope} {reduct : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_linearArrow () (.childCons source (.childCons target .childNil))) reduct) :
    (∃ sourceAfter : RawTerm scope,
        reduct = .mkGen .gen_linearArrow () (.childCons sourceAfter (.childCons target .childNil)) ∧
        Step source sourceAfter)
    ∨ (∃ targetAfter : RawTerm scope,
        reduct = .mkGen .gen_linearArrow () (.childCons source (.childCons targetAfter .childNil)) ∧
        Step target targetAfter) := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
      cases childStep with
      | here _ sourceStep =>
          rename_i sourceAfter
          exact Or.inl ⟨sourceAfter, targetEq, sourceStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ targetStep =>
              rename_i targetAfter
              exact Or.inr ⟨targetAfter, targetEq, targetStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `tensorProduct`-rooted Step.**  `gen_tensorProduct` is a two-child multiplicative
conjunction type former with no β+ι root rule, congruence-only. -/
theorem Step.from_tensorProduct
    {scope : Nat} {leftFactor rightFactor : RawTerm scope} {reduct : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_tensorProduct ()
              (.childCons leftFactor (.childCons rightFactor .childNil))) reduct) :
    (∃ leftAfter : RawTerm scope,
        reduct = .mkGen .gen_tensorProduct () (.childCons leftAfter (.childCons rightFactor .childNil)) ∧
        Step leftFactor leftAfter)
    ∨ (∃ rightAfter : RawTerm scope,
        reduct = .mkGen .gen_tensorProduct () (.childCons leftFactor (.childCons rightAfter .childNil)) ∧
        Step rightFactor rightAfter) := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
      cases childStep with
      | here _ leftStep =>
          rename_i leftAfter
          exact Or.inl ⟨leftAfter, targetEq, leftStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightStep =>
              rename_i rightAfter
              exact Or.inr ⟨rightAfter, targetEq, rightStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- Linear function-space type codes are strongly normalizing when both the source and target type codes are
strongly normalizing.  Congruence-only under β+ι (`Step.from_linearArrow`), via the two-child congruence
combinator. -/
theorem linearArrow_isStronglyNormalizing_of_source_target {scope : Nat}
    {source target : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing source)
    (targetTerminates : IsStronglyNormalizing target) :
    IsStronglyNormalizing
      (.mkGen .gen_linearArrow () (.childCons source (.childCons target .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentSource currentTarget =>
      (.mkGen .gen_linearArrow ()
        (.childCons currentSource (.childCons currentTarget .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_linearArrow parentStep)
    sourceTerminates targetTerminates

/-- Tensor-product (multiplicative conjunction) type codes are strongly normalizing when both factor type
codes are strongly normalizing.  Congruence-only under β+ι (`Step.from_tensorProduct`). -/
theorem tensorProduct_isStronglyNormalizing_of_factors {scope : Nat}
    {leftFactor rightFactor : RawTerm scope}
    (leftTerminates : IsStronglyNormalizing leftFactor)
    (rightTerminates : IsStronglyNormalizing rightFactor) :
    IsStronglyNormalizing
      (.mkGen .gen_tensorProduct ()
        (.childCons leftFactor (.childCons rightFactor .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentLeft currentRight =>
      (.mkGen .gen_tensorProduct ()
        (.childCons currentLeft (.childCons currentRight .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_tensorProduct parentStep)
    leftTerminates rightTerminates

end StepStar
end FX1Poly.Core
