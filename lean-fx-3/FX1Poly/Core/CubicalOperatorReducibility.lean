import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.ModalEliminatorReducibility
import FX1Poly.Core.ReducibilityCandidate

/-! # FX1Poly/Core/CubicalOperatorReducibility
    — cubical transport + homogeneous-composition SN coverage (congruence-only stage), zero-axiom

The two headline CCHM cubical Kan operators are shipped generators: transport `gen_transp` (two children: the
path/line and the source term) and homogeneous composition `gen_hcomp` (two children: the sides system and the
cap).  Their Kan COMPUTATION rules (transport reduction, hcomp filling) are not yet part of the β+ι substrate.
Until then both operators are CONGRUENCE-ONLY under `Step` and NON-NEUTRAL
(`NeutralTerm.lean` lists `transp`/`hcomp` among the cubical eliminators that "form no neutrals yet").

This file ships their congruence-only-stage SN coverage — forward SN closures, the reflection direction, and the
reducibility candidate-framing — the pattern shared with the modal core and the 2LTT
universe-mode bridges.  It is the first installment of SN robustness under the cubical
extension: the Kan-rule robustness, plus `gen_transpFill`/`gen_transpHigherDim`/`gen_unglue`/Glue, remain.

## Why the strong-normalization candidate is the honest target

As with `gen_modElim` and the mode bridges: `transp`/`hcomp` have no β+ι ι-rule and are not neutral heads, so
`transp (path) (modIntro …)`-style configurations are simply stuck under `Step` (no Kan rule fires yet), and
neither operator can be claimed a member of an arbitrary classifier candidate via Girard CR3 (which demands
`IsNeutral`).  The honest ceiling is the strong-normalization candidate `IsStronglyNormalizing`: the operators
send candidate members to SN-candidate members.

## Contents (per operator: `transp`, `hcomp`)

* `Step.from_transp` / `Step.from_hcomp` — the two-child inversions (only `cong` matches; a reduction descends
  to exactly one child).
* `transp_isStronglyNormalizing_of_children` / `hcomp_…` — forward SN closures via
  `isStronglyNormalizing_of_twoChildCong`.
* `transp_path_…` / `transp_source_…` / `hcomp_sides_…` / `hcomp_cap_…` — the per-child reflections, each a
  one-child SLICE reusing the generic `isStronglyNormalizing_child_of_oneChildCong`.
* `transp_isStronglyNormalizing_iff` / `hcomp_…` — the biconditionals (parent SN ↔ both children SN).
* `transp_isStronglyNormalizing_of_candidateMembers` / `hcomp_…` — the reducibility-framing.

## Zero-axiom verification

The inversions are `cases reduction` (only `cong`) + `cases childStep` down the two-child `StepChildren` spine,
closing the empty tail with `StepChildren.no_step_at_empty_spine`.  The forward closures are
`isStronglyNormalizing_of_twoChildCong`; the reflections instantiate the generic one-child reflection lemma per
child slice (the second-child slice threads `StepChildren.there` past the held first child with the explicit
`@`-form, since `binderShifts = [0, 0]` does not auto-reduce).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `transp`-rooted Step.**  `gen_transp` is a two-child cubical transport operator with no β+ι
root rule (its Kan transport rule is not part of the substrate), congruence-only: a `Step` out of it reduces
exactly the path child or the source child. -/
theorem Step.from_transp
    {scope : Nat} {path source : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_transp () (.childCons path (.childCons source .childNil))) target) :
    (∃ (pathAfter : RawTerm scope),
        target = .mkGen .gen_transp () (.childCons pathAfter (.childCons source .childNil)) ∧
        Step path pathAfter)
    ∨
    (∃ (sourceAfter : RawTerm scope),
        target = .mkGen .gen_transp () (.childCons path (.childCons sourceAfter .childNil)) ∧
        Step source sourceAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ pathStep =>
          rename_i pathAfter
          exact Or.inl ⟨pathAfter, rfl, pathStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ sourceStep =>
              rename_i sourceAfter
              exact Or.inr ⟨sourceAfter, rfl, sourceStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `hcomp`-rooted Step.**  `gen_hcomp` is a two-child homogeneous-composition operator (sides
system + cap) with no β+ι root rule (its Kan filling rule is not part of the substrate), congruence-only: a
`Step` out of it reduces exactly the sides child or the cap child. -/
theorem Step.from_hcomp
    {scope : Nat} {sides cap : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_hcomp () (.childCons sides (.childCons cap .childNil))) target) :
    (∃ (sidesAfter : RawTerm scope),
        target = .mkGen .gen_hcomp () (.childCons sidesAfter (.childCons cap .childNil)) ∧
        Step sides sidesAfter)
    ∨
    (∃ (capAfter : RawTerm scope),
        target = .mkGen .gen_hcomp () (.childCons sides (.childCons capAfter .childNil)) ∧
        Step cap capAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ sidesStep =>
          rename_i sidesAfter
          exact Or.inl ⟨sidesAfter, rfl, sidesStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ capStep =>
              rename_i capAfter
              exact Or.inr ⟨capAfter, rfl, capStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- **Transport is strongly normalizing when both children are.**  Congruence-only under β+ι
(`Step.from_transp`), via `isStronglyNormalizing_of_twoChildCong`. -/
theorem transp_isStronglyNormalizing_of_children {scope : Nat}
    {path source : RawTerm scope}
    (pathTerminates : IsStronglyNormalizing path)
    (sourceTerminates : IsStronglyNormalizing source) :
    IsStronglyNormalizing
      (.mkGen .gen_transp () (.childCons path (.childCons source .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentPath currentSource =>
      (.mkGen .gen_transp ()
        (.childCons currentPath (.childCons currentSource .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_transp parentStep)
    pathTerminates sourceTerminates

/-- **Homogeneous composition is strongly normalizing when both children are.**  Congruence-only under β+ι
(`Step.from_hcomp`), via `isStronglyNormalizing_of_twoChildCong`. -/
theorem hcomp_isStronglyNormalizing_of_children {scope : Nat}
    {sides cap : RawTerm scope}
    (sidesTerminates : IsStronglyNormalizing sides)
    (capTerminates : IsStronglyNormalizing cap) :
    IsStronglyNormalizing
      (.mkGen .gen_hcomp () (.childCons sides (.childCons cap .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong
    (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun currentSides currentCap =>
      (.mkGen .gen_hcomp ()
        (.childCons currentSides (.childCons currentCap .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_hcomp parentStep)
    sidesTerminates capTerminates

/-- **Transport's PATH child reflects strong normalization.**  The one-child slice in the
path position (source held fixed), via the generic reflection lemma. -/
theorem transp_path_isStronglyNormalizing_of_parent {scope : Nat}
    {path source : RawTerm scope}
    (transpTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transp () (.childCons path (.childCons source .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing path :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentPath =>
      (.mkGen .gen_transp ()
        (.childCons currentPath (.childCons source .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transp ()
        (StepChildren.here (.childCons source .childNil : RawTermChildren [0] scope) childStep))
    transpTerminates

/-- **Transport's SOURCE child reflects strong normalization.**  The one-child slice in the
source position (path held fixed); the `there` shift is pinned with the explicit `@`-form. -/
theorem transp_source_isStronglyNormalizing_of_parent {scope : Nat}
    {path source : RawTerm scope}
    (transpTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_transp () (.childCons path (.childCons source .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing source :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentSource =>
      (.mkGen .gen_transp ()
        (.childCons path (.childCons currentSource .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_transp ()
        (@StepChildren.there scope 0 [0] path _ _
          (StepChildren.here (.childNil : RawTermChildren [] scope) childStep)))
    transpTerminates

/-- **Homogeneous composition's SIDES child reflects strong normalization.**  The one-child
slice in the sides position (cap held fixed). -/
theorem hcomp_sides_isStronglyNormalizing_of_parent {scope : Nat}
    {sides cap : RawTerm scope}
    (hcompTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_hcomp () (.childCons sides (.childCons cap .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing sides :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentSides =>
      (.mkGen .gen_hcomp ()
        (.childCons currentSides (.childCons cap .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_hcomp ()
        (StepChildren.here (.childCons cap .childNil : RawTermChildren [0] scope) childStep))
    hcompTerminates

/-- **Homogeneous composition's CAP child reflects strong normalization.**  The one-child
slice in the cap position (sides held fixed); the `there` shift is pinned with the explicit `@`-form. -/
theorem hcomp_cap_isStronglyNormalizing_of_parent {scope : Nat}
    {sides cap : RawTerm scope}
    (hcompTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_hcomp () (.childCons sides (.childCons cap .childNil)) : RawTerm scope)) :
    IsStronglyNormalizing cap :=
  isStronglyNormalizing_child_of_oneChildCong
    (childScope := scope) (parentScope := scope)
    (fun currentCap =>
      (.mkGen .gen_hcomp ()
        (.childCons sides (.childCons currentCap .childNil)) : RawTerm scope))
    (fun childStep =>
      Step.cong .gen_hcomp ()
        (@StepChildren.there scope 0 [0] sides _ _
          (StepChildren.here (.childNil : RawTermChildren [] scope) childStep)))
    hcompTerminates

/-- **Transport's strong-normalization characterization.**  `transp path source` is
strongly normalizing iff both children are. -/
theorem transp_isStronglyNormalizing_iff {scope : Nat} {path source : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_transp () (.childCons path (.childCons source .childNil)) : RawTerm scope)
      ↔ (IsStronglyNormalizing path ∧ IsStronglyNormalizing source) :=
  ⟨fun terminates =>
      ⟨transp_path_isStronglyNormalizing_of_parent terminates,
       transp_source_isStronglyNormalizing_of_parent terminates⟩,
   fun ⟨pathTerminates, sourceTerminates⟩ =>
      transp_isStronglyNormalizing_of_children pathTerminates sourceTerminates⟩

/-- **Homogeneous composition's strong-normalization characterization.**  `hcomp sides cap`
is strongly normalizing iff both children are. -/
theorem hcomp_isStronglyNormalizing_iff {scope : Nat} {sides cap : RawTerm scope} :
    IsStronglyNormalizing
        (.mkGen .gen_hcomp () (.childCons sides (.childCons cap .childNil)) : RawTerm scope)
      ↔ (IsStronglyNormalizing sides ∧ IsStronglyNormalizing cap) :=
  ⟨fun terminates =>
      ⟨hcomp_sides_isStronglyNormalizing_of_parent terminates,
       hcomp_cap_isStronglyNormalizing_of_parent terminates⟩,
   fun ⟨sidesTerminates, capTerminates⟩ =>
      hcomp_isStronglyNormalizing_of_children sidesTerminates capTerminates⟩

/-- **Transport sends reducibility-candidate members to SN-candidate members.**  Both
children members of (possibly distinct) candidates ⟹ the transport is strongly normalizing, via the two CR1
fields and the forward closure. -/
theorem transp_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {pathPredicate sourcePredicate : RawTerm scope → Prop}
    (pathCandidate : IsReducibilityCandidate pathPredicate)
    (sourceCandidate : IsReducibilityCandidate sourcePredicate)
    {path source : RawTerm scope}
    (pathMember : pathPredicate path) (sourceMember : sourcePredicate source) :
    IsStronglyNormalizing
      (.mkGen .gen_transp () (.childCons path (.childCons source .childNil)) : RawTerm scope) :=
  transp_isStronglyNormalizing_of_children
    (pathCandidate.stronglyNormalizing pathMember)
    (sourceCandidate.stronglyNormalizing sourceMember)

/-- **Homogeneous composition sends reducibility-candidate members to SN-candidate members.**  Both
children members ⟹ the hcomp is strongly normalizing. -/
theorem hcomp_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {sidesPredicate capPredicate : RawTerm scope → Prop}
    (sidesCandidate : IsReducibilityCandidate sidesPredicate)
    (capCandidate : IsReducibilityCandidate capPredicate)
    {sides cap : RawTerm scope}
    (sidesMember : sidesPredicate sides) (capMember : capPredicate cap) :
    IsStronglyNormalizing
      (.mkGen .gen_hcomp () (.childCons sides (.childCons cap .childNil)) : RawTerm scope) :=
  hcomp_isStronglyNormalizing_of_children
    (sidesCandidate.stronglyNormalizing sidesMember)
    (capCandidate.stronglyNormalizing capMember)

end StepStar
end FX1Poly.Core
