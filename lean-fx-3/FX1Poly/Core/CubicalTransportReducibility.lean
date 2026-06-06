import FX1Poly.Core.StrongNormalizationCodeFormers
import FX1Poly.Core.ModalEliminatorReducibility
import FX1Poly.Core.ReducibilityCandidate

/-! # FX1Poly/Core/CubicalTransportReducibility
    — transport-variant SN coverage (transpHigherDim + transpFill), completing the transport family for SN-146

`CubicalOperatorReducibility.lean` shipped the SN coverage for the two headline CCHM Kan operators `gen_transp`
and `gen_hcomp`.  This file completes the TRANSPORT family with the two remaining shipped transport variants:
`gen_transpHigherDim` (two children: the higher-dimensional path family + the source) and `gen_transpFill` (three
children: the path type, the current interval point, and the source — Kan transport FILLING).

Both are congruence-only under `Step` (their Kan computation rules await M64) and non-neutral, exactly like
`gen_transp`/`gen_hcomp`, so the SN candidate is again the honest ceiling.  The three-child `transpFill` uses the
three-child forward closure `isStronglyNormalizing_of_threeChildCong` and three one-child reflection SLICES (the
generic `isStronglyNormalizing_child_of_oneChildCong` from SN-074, the interval/source slices threading
`StepChildren.there` once/twice past the held earlier children).

With this file, all four shipped transport/composition Kan operators (`transp`, `hcomp`, `transpHigherDim`,
`transpFill`) have congruence-only-stage SN coverage.  The Kan-rule SN robustness + Glue remain for the full
SN-146.

## Zero-axiom verification

Inversions are `cases reduction` (only `cong`) + `cases childStep` down the (two/three)-child spine, empty tail
by `StepChildren.no_step_at_empty_spine`.  Forward closures are `isStronglyNormalizing_of_twoChildCong` /
`isStronglyNormalizing_of_threeChildCong`; reflections instantiate the generic one-child reflection per slice
(the `@StepChildren.there` shifts pinned explicitly since `binderShifts = [0,0]` / `[0,0,0]` do not auto-reduce).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `transpHigherDim`-rooted Step.**  Two-child higher-dimensional transport (path family +
source), congruence-only (no β+ι root rule): a `Step` reduces exactly one child. -/
theorem Step.from_transpHigherDim
    {scope : Nat} {pathFamily source : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_transpHigherDim ()
              (.childCons pathFamily (.childCons source .childNil))) target) :
    (∃ (pathFamilyAfter : RawTerm scope),
        target = .mkGen .gen_transpHigherDim ()
          (.childCons pathFamilyAfter (.childCons source .childNil)) ∧
        Step pathFamily pathFamilyAfter)
    ∨
    (∃ (sourceAfter : RawTerm scope),
        target = .mkGen .gen_transpHigherDim ()
          (.childCons pathFamily (.childCons sourceAfter .childNil)) ∧
        Step source sourceAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ familyStep =>
          rename_i pathFamilyAfter
          exact Or.inl ⟨pathFamilyAfter, rfl, familyStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ sourceStep =>
              rename_i sourceAfter
              exact Or.inr ⟨sourceAfter, rfl, sourceStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `transpFill`-rooted Step.**  Three-child transport filling (path type, current interval,
source), congruence-only (its Kan filling rule awaits M64): a `Step` reduces exactly one of the three children. -/
theorem Step.from_transpFill
    {scope : Nat} {pathTy currentInterval source : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_transpFill ()
              (.childCons pathTy (.childCons currentInterval (.childCons source .childNil)))) target) :
    (∃ (pathTyAfter : RawTerm scope),
        target = .mkGen .gen_transpFill ()
          (.childCons pathTyAfter (.childCons currentInterval (.childCons source .childNil))) ∧
        Step pathTy pathTyAfter)
    ∨ (∃ (intervalAfter : RawTerm scope),
        target = .mkGen .gen_transpFill ()
          (.childCons pathTy (.childCons intervalAfter (.childCons source .childNil))) ∧
        Step currentInterval intervalAfter)
    ∨ (∃ (sourceAfter : RawTerm scope),
        target = .mkGen .gen_transpFill ()
          (.childCons pathTy (.childCons currentInterval (.childCons sourceAfter .childNil))) ∧
        Step source sourceAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ tyStep =>
          rename_i pathTyAfter
          exact Or.inl ⟨pathTyAfter, rfl, tyStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ intervalStep =>
              rename_i intervalAfter
              exact Or.inr (Or.inl ⟨intervalAfter, rfl, intervalStep⟩)
          | there _ tail2Step =>
              cases tail2Step with
              | here _ sourceStep =>
                  rename_i sourceAfter
                  exact Or.inr (Or.inr ⟨sourceAfter, rfl, sourceStep⟩)
              | there _ restStep =>
                  exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- **Higher-dimensional transport is strongly normalizing when both children are.**  Via
`isStronglyNormalizing_of_twoChildCong`. -/
theorem transpHigherDim_isStronglyNormalizing_of_children {scope : Nat}
    {pathFamily source : RawTerm scope}
    (familyTerminates : IsStronglyNormalizing pathFamily)
    (sourceTerminates : IsStronglyNormalizing source) :
    IsStronglyNormalizing
      (.mkGen .gen_transpHigherDim ()
        (.childCons pathFamily (.childCons source .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentFamily currentSource =>
      (.mkGen .gen_transpHigherDim ()
        (.childCons currentFamily (.childCons currentSource .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_transpHigherDim parentStep)
    familyTerminates sourceTerminates

/-- **Transport filling is strongly normalizing when all three children are.**  Via
`isStronglyNormalizing_of_threeChildCong`. -/
theorem transpFill_isStronglyNormalizing_of_children {scope : Nat}
    {pathTy currentInterval source : RawTerm scope}
    (tyTerminates : IsStronglyNormalizing pathTy)
    (intervalTerminates : IsStronglyNormalizing currentInterval)
    (sourceTerminates : IsStronglyNormalizing source) :
    IsStronglyNormalizing
      (.mkGen .gen_transpFill ()
        (.childCons pathTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope) :=
  isStronglyNormalizing_of_threeChildCong
    (firstScope := scope) (secondScope := scope) (thirdScope := scope) (parentScope := scope)
    (fun currentTy currentIntervalValue currentSource =>
      (.mkGen .gen_transpFill ()
        (.childCons currentTy
          (.childCons currentIntervalValue (.childCons currentSource .childNil))) : RawTerm scope))
    (fun parentStep => Step.from_transpFill parentStep)
    tyTerminates intervalTerminates sourceTerminates

/-- **`transpHigherDim`'s family child reflects strong normalization (SN-146 installment).** -/
theorem transpHigherDim_family_isStronglyNormalizing_of_parent {scope : Nat}
    {pathFamily source : RawTerm scope}
    (parentTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transpHigherDim ()
          (.childCons pathFamily (.childCons source .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing pathFamily :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentFamily =>
      (.mkGen .gen_transpHigherDim ()
        (.childCons currentFamily (.childCons source .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transpHigherDim ()
        (StepChildren.here (.childCons source .childNil : RawTermChildren [0] scope) childStep))
    parentTerminates

/-- **`transpHigherDim`'s source child reflects strong normalization (SN-146 installment).** -/
theorem transpHigherDim_source_isStronglyNormalizing_of_parent {scope : Nat}
    {pathFamily source : RawTerm scope}
    (parentTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transpHigherDim ()
          (.childCons pathFamily (.childCons source .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing source :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentSource =>
      (.mkGen .gen_transpHigherDim ()
        (.childCons pathFamily (.childCons currentSource .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transpHigherDim ()
        (@StepChildren.there scope 0 [0] pathFamily _ _
          (StepChildren.here (.childNil : RawTermChildren [] scope) childStep)))
    parentTerminates

/-- **`transpFill`'s path-type child reflects strong normalization (SN-146 installment).**  The first of three
one-child slices; the path type is child 0. -/
theorem transpFill_ty_isStronglyNormalizing_of_parent {scope : Nat}
    {pathTy currentInterval source : RawTerm scope}
    (parentTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transpFill ()
          (.childCons pathTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope)) :
    IsStronglyNormalizing pathTy :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentTy =>
      (.mkGen .gen_transpFill ()
        (.childCons currentTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transpFill ()
        (StepChildren.here
          (.childCons currentInterval (.childCons source .childNil) : RawTermChildren [0, 0] scope)
          childStep))
    parentTerminates

/-- **`transpFill`'s interval child reflects strong normalization (SN-146 installment).**  The middle slice; the
interval is child 1, reached by one `StepChildren.there` past the held path type. -/
theorem transpFill_interval_isStronglyNormalizing_of_parent {scope : Nat}
    {pathTy currentInterval source : RawTerm scope}
    (parentTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transpFill ()
          (.childCons pathTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope)) :
    IsStronglyNormalizing currentInterval :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentIntervalValue =>
      (.mkGen .gen_transpFill ()
        (.childCons pathTy (.childCons currentIntervalValue (.childCons source .childNil))) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transpFill ()
        (@StepChildren.there scope 0 [0, 0] pathTy _ _
          (StepChildren.here (.childCons source .childNil : RawTermChildren [0] scope) childStep)))
    parentTerminates

/-- **`transpFill`'s source child reflects strong normalization (SN-146 installment).**  The last slice; the
source is child 2, reached by two `StepChildren.there` past the held path type and interval. -/
theorem transpFill_source_isStronglyNormalizing_of_parent {scope : Nat}
    {pathTy currentInterval source : RawTerm scope}
    (parentTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transpFill ()
          (.childCons pathTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope)) :
    IsStronglyNormalizing source :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentSource =>
      (.mkGen .gen_transpFill ()
        (.childCons pathTy (.childCons currentInterval (.childCons currentSource .childNil))) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transpFill ()
        (@StepChildren.there scope 0 [0, 0] pathTy _ _
          (@StepChildren.there scope 0 [0] currentInterval _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) childStep))))
    parentTerminates

/-- **`transpHigherDim`'s strong-normalization characterization (SN-146 installment).**  SN iff both children
are. -/
theorem transpHigherDim_isStronglyNormalizing_iff {scope : Nat} {pathFamily source : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_transpHigherDim ()
          (.childCons pathFamily (.childCons source .childNil)) : RawTerm scope)
      ↔ (IsStronglyNormalizing pathFamily ∧ IsStronglyNormalizing source) :=
  ⟨fun terminates =>
      ⟨transpHigherDim_family_isStronglyNormalizing_of_parent terminates,
       transpHigherDim_source_isStronglyNormalizing_of_parent terminates⟩,
   fun ⟨familyTerminates, sourceTerminates⟩ =>
      transpHigherDim_isStronglyNormalizing_of_children familyTerminates sourceTerminates⟩

/-- **`transpFill`'s strong-normalization characterization (SN-146 installment).**  SN iff all three children
are. -/
theorem transpFill_isStronglyNormalizing_iff {scope : Nat}
    {pathTy currentInterval source : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_transpFill ()
          (.childCons pathTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope)
      ↔ (IsStronglyNormalizing pathTy ∧ IsStronglyNormalizing currentInterval ∧
          IsStronglyNormalizing source) :=
  ⟨fun terminates =>
      ⟨transpFill_ty_isStronglyNormalizing_of_parent terminates,
       transpFill_interval_isStronglyNormalizing_of_parent terminates,
       transpFill_source_isStronglyNormalizing_of_parent terminates⟩,
   fun ⟨tyTerminates, intervalTerminates, sourceTerminates⟩ =>
      transpFill_isStronglyNormalizing_of_children tyTerminates intervalTerminates sourceTerminates⟩

/-- **`transpHigherDim` sends reducibility-candidate members to SN-candidate members (SN-146 installment).** -/
theorem transpHigherDim_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {familyPredicate sourcePredicate : RawTerm scope → Prop}
    (familyCandidate : IsReducibilityCandidate familyPredicate)
    (sourceCandidate : IsReducibilityCandidate sourcePredicate)
    {pathFamily source : RawTerm scope}
    (familyMember : familyPredicate pathFamily) (sourceMember : sourcePredicate source) :
    IsStronglyNormalizing
      (.mkGen .gen_transpHigherDim ()
        (.childCons pathFamily (.childCons source .childNil)) : RawTerm scope) :=
  transpHigherDim_isStronglyNormalizing_of_children
    (familyCandidate.stronglyNormalizing familyMember)
    (sourceCandidate.stronglyNormalizing sourceMember)

/-- **`transpFill` sends reducibility-candidate members to SN-candidate members (SN-146 installment).** -/
theorem transpFill_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {tyPredicate intervalPredicate sourcePredicate : RawTerm scope → Prop}
    (tyCandidate : IsReducibilityCandidate tyPredicate)
    (intervalCandidate : IsReducibilityCandidate intervalPredicate)
    (sourceCandidate : IsReducibilityCandidate sourcePredicate)
    {pathTy currentInterval source : RawTerm scope}
    (tyMember : tyPredicate pathTy) (intervalMember : intervalPredicate currentInterval)
    (sourceMember : sourcePredicate source) :
    IsStronglyNormalizing
      (.mkGen .gen_transpFill ()
        (.childCons pathTy (.childCons currentInterval (.childCons source .childNil))) : RawTerm scope) :=
  transpFill_isStronglyNormalizing_of_children
    (tyCandidate.stronglyNormalizing tyMember)
    (intervalCandidate.stronglyNormalizing intervalMember)
    (sourceCandidate.stronglyNormalizing sourceMember)

end StepStar
end FX1Poly.Core
