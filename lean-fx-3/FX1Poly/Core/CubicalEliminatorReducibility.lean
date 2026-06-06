import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.ModalEliminatorReducibility
import FX1Poly.Core.ReducibilityCandidate

/-! # FX1Poly/Core/CubicalEliminatorReducibility
    — cubical path + Glue eliminator SN coverage, zero-axiom

`CubicalOperatorReducibility.lean` + `CubicalTransportReducibility.lean` cover the four Kan transport/composition
operators (transp / hcomp / transpHigherDim / transpFill).  This file covers the two cubical ELIMINATORS: the
path application `gen_pathApp` (two children: the path term + the interval argument) and the Glue elimination
`gen_glueElim` (one child: the glued value).  Together with the already-shipped glue INTRODUCTION SN
(`glueIntro_isStronglyNormalizing_of_components`), this advances the "Glue" coverage and adds the path
eliminator.

Both are congruence-only under `Step` (their computation rules — path-β `pathApp (pathLam b) r ↝ b[r]` and the
Glue collapse — are not part of the substrate) and non-neutral (`NeutralTerm.lean` lists the cubical eliminators
as forming no neutrals yet), so the SN candidate is the honest ceiling, exactly as for `gen_modElim` and the Kan
operators.

## Contents

* `Step.from_pathApp` (two-child) / `Step.from_glueElim` (one-child) — the inversions.
* `pathApp_isStronglyNormalizing_of_children` (twoChildCong) / `glueElim_isStronglyNormalizing_of_child`
  (oneChildCong) — forward SN closures.
* `glueElim_…child_of_parent` / `pathApp_pathTerm_…` / `pathApp_intervalArg_…` — the reflections (one-child
  slices reusing the generic `isStronglyNormalizing_child_of_oneChildCong`).
* `…_isStronglyNormalizing_iff` — the biconditionals.
* `…_of_candidateMember(s)` — the reducibility-framing.

## Zero-axiom verification

Inversions are `cases reduction` (only `cong`) + `cases childStep` down the spine, empty tail by
`StepChildren.no_step_at_empty_spine`.  Forward closures are the shipped one/two-child congruence closures;
reflections instantiate the generic one-child reflection per slice (the pathApp interval slice threads
`StepChildren.there` past the held path term).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `glueElim`-rooted Step.**  `gen_glueElim` is a one-child Glue eliminator with no β+ι root
rule (its Glue collapse is not part of the substrate), congruence-only: a `Step` reduces exactly its glued-value child. -/
theorem Step.from_glueElim
    {scope : Nat} {gluedValue : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_glueElim () (.childCons gluedValue .childNil)) target) :
    ∃ (gluedAfter : RawTerm scope),
      target = .mkGen .gen_glueElim () (.childCons gluedAfter .childNil) ∧
      Step gluedValue gluedAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ gluedStep =>
          rename_i gluedAfter
          exact ⟨gluedAfter, rfl, gluedStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `pathApp`-rooted Step.**  `gen_pathApp` is a two-child cubical path application (path term +
interval argument) with no β+ι root rule (its path-β rule is not part of the substrate), congruence-only: a `Step` reduces exactly
one child. -/
theorem Step.from_pathApp
    {scope : Nat} {pathTerm intervalArg : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_pathApp ()
              (.childCons pathTerm (.childCons intervalArg .childNil))) target) :
    (∃ (pathTermAfter : RawTerm scope),
        target = .mkGen .gen_pathApp ()
          (.childCons pathTermAfter (.childCons intervalArg .childNil)) ∧
        Step pathTerm pathTermAfter)
    ∨
    (∃ (intervalAfter : RawTerm scope),
        target = .mkGen .gen_pathApp ()
          (.childCons pathTerm (.childCons intervalAfter .childNil)) ∧
        Step intervalArg intervalAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ pathStep =>
          rename_i pathTermAfter
          exact Or.inl ⟨pathTermAfter, rfl, pathStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ intervalStep =>
              rename_i intervalAfter
              exact Or.inr ⟨intervalAfter, rfl, intervalStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- **Glue elimination is strongly normalizing when its child is.**  Congruence-only under β+ι
(`Step.from_glueElim`), via `isStronglyNormalizing_of_oneChildCong`. -/
theorem glueElim_isStronglyNormalizing_of_child {scope : Nat}
    {gluedValue : RawTerm scope}
    (gluedTerminates : IsStronglyNormalizing gluedValue) :
    IsStronglyNormalizing
      (.mkGen .gen_glueElim () (.childCons gluedValue .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentGlued =>
      (.mkGen .gen_glueElim () (.childCons currentGlued .childNil) : RawTerm scope))
    (fun parentStep => Step.from_glueElim parentStep)
    gluedTerminates

/-- **Glue elimination's child reflects strong normalization.**  The converse of the
forward closure, via the generic one-child reflection lemma. -/
theorem glueElim_isStronglyNormalizing_child_of_parent {scope : Nat}
    {gluedValue : RawTerm scope}
    (glueElimTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_glueElim () (.childCons gluedValue .childNil) : RawTerm scope)) :
    IsStronglyNormalizing gluedValue :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentGlued =>
      (.mkGen .gen_glueElim () (.childCons currentGlued .childNil) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_glueElim ()
        (StepChildren.here (.childNil : RawTermChildren [] scope) childStep))
    glueElimTerminates

/-- **Glue elimination's strong-normalization characterization.**  SN iff the child is. -/
theorem glueElim_isStronglyNormalizing_iff {scope : Nat} {gluedValue : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_glueElim () (.childCons gluedValue .childNil) : RawTerm scope)
      ↔ IsStronglyNormalizing gluedValue :=
  ⟨glueElim_isStronglyNormalizing_child_of_parent, glueElim_isStronglyNormalizing_of_child⟩

/-- **Glue elimination sends reducibility-candidate members to SN-candidate members.** -/
theorem glueElim_isStronglyNormalizing_of_candidateMember {scope : Nat}
    {memberPredicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate memberPredicate)
    {gluedValue : RawTerm scope} (gluedMember : memberPredicate gluedValue) :
    IsStronglyNormalizing
      (.mkGen .gen_glueElim () (.childCons gluedValue .childNil) : RawTerm scope) :=
  glueElim_isStronglyNormalizing_of_child (candidate.stronglyNormalizing gluedMember)

/-- **Path application is strongly normalizing when both children are.**  Congruence-only under β+ι
(`Step.from_pathApp`), via `isStronglyNormalizing_of_twoChildCong`. -/
theorem pathApp_isStronglyNormalizing_of_children {scope : Nat}
    {pathTerm intervalArg : RawTerm scope}
    (pathTerminates : IsStronglyNormalizing pathTerm)
    (intervalTerminates : IsStronglyNormalizing intervalArg) :
    IsStronglyNormalizing
      (.mkGen .gen_pathApp ()
        (.childCons pathTerm (.childCons intervalArg .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentPath currentInterval =>
      (.mkGen .gen_pathApp ()
        (.childCons currentPath (.childCons currentInterval .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_pathApp parentStep)
    pathTerminates intervalTerminates

/-- **Path application's path-term child reflects strong normalization.** -/
theorem pathApp_pathTerm_isStronglyNormalizing_of_parent {scope : Nat}
    {pathTerm intervalArg : RawTerm scope}
    (pathAppTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_pathApp ()
          (.childCons pathTerm (.childCons intervalArg .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing pathTerm :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentPath =>
      (.mkGen .gen_pathApp ()
        (.childCons currentPath (.childCons intervalArg .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_pathApp ()
        (StepChildren.here (.childCons intervalArg .childNil : RawTermChildren [0] scope) childStep))
    pathAppTerminates

/-- **Path application's interval-argument child reflects strong normalization.**  The
`there` shift is pinned with the explicit `@`-form since `binderShifts = [0, 0]` does not auto-reduce. -/
theorem pathApp_intervalArg_isStronglyNormalizing_of_parent {scope : Nat}
    {pathTerm intervalArg : RawTerm scope}
    (pathAppTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_pathApp ()
          (.childCons pathTerm (.childCons intervalArg .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing intervalArg :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentInterval =>
      (.mkGen .gen_pathApp ()
        (.childCons pathTerm (.childCons currentInterval .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_pathApp ()
        (@StepChildren.there scope 0 [0] pathTerm _ _
          (StepChildren.here (.childNil : RawTermChildren [] scope) childStep)))
    pathAppTerminates

/-- **Path application's strong-normalization characterization.**  SN iff both children
are. -/
theorem pathApp_isStronglyNormalizing_iff {scope : Nat} {pathTerm intervalArg : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_pathApp ()
          (.childCons pathTerm (.childCons intervalArg .childNil)) : RawTerm scope)
      ↔ (IsStronglyNormalizing pathTerm ∧ IsStronglyNormalizing intervalArg) :=
  ⟨fun terminates =>
      ⟨pathApp_pathTerm_isStronglyNormalizing_of_parent terminates,
       pathApp_intervalArg_isStronglyNormalizing_of_parent terminates⟩,
   fun ⟨pathTerminates, intervalTerminates⟩ =>
      pathApp_isStronglyNormalizing_of_children pathTerminates intervalTerminates⟩

/-- **Path application sends reducibility-candidate members to SN-candidate members.** -/
theorem pathApp_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {pathPredicate intervalPredicate : RawTerm scope → Prop}
    (pathCandidate : IsReducibilityCandidate pathPredicate)
    (intervalCandidate : IsReducibilityCandidate intervalPredicate)
    {pathTerm intervalArg : RawTerm scope}
    (pathMember : pathPredicate pathTerm) (intervalMember : intervalPredicate intervalArg) :
    IsStronglyNormalizing
      (.mkGen .gen_pathApp ()
        (.childCons pathTerm (.childCons intervalArg .childNil)) : RawTerm scope) :=
  pathApp_isStronglyNormalizing_of_children
    (pathCandidate.stronglyNormalizing pathMember)
    (intervalCandidate.stronglyNormalizing intervalMember)

end StepStar
end FX1Poly.Core
