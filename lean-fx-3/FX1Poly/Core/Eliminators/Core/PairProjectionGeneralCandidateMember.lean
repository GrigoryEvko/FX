import FX1Poly.Core.Metatheory.Canonicity.PairCanonicalFormsCandidate
import FX1Poly.Core.Eliminators.Core.DependentDataEliminatorMemberSkeleton
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationIotaRedexes
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Core/PairProjectionGeneralCandidateMember
    — dependent `fst` / `snd` over a `dataTaitCandidate` scrutinee land in the motive candidate (Σ-projection)

The Σ-projection companions to `optionMatchDependentReducibleMember`: the native bounded data-eliminator FT rows
need `fst` and `snd` to land in an ARBITRARY reducibility candidate (the dependent motive's instantiated output
type), with the scrutinee arriving as a member of the head-expansion-closed `dataTaitCandidate isPairValue`.

Projection is the PROJECTING shape, structurally simpler than the match eliminators: `gen_fst`/`gen_snd` are
SINGLE-child cells (no motive spine, no branch terms), and the ι contracts to a DIRECT child rather than a branch
application (`fst (pair a b) ↝ a`, `snd (pair a b) ↝ b`).  So the members take no branch-SN or branch-application-
SN premise — only the cell's spine SN (`fst_isStronglyNormalizing_of_argument`) and a single conditioned
component-membership premise (the first / second component is a result member WHEN the scrutinee reaches a pair).
There is exactly one constructor (`pair`), so the trichotomy's value-head set is the singleton `gen_pair`.  As with
option/either, a `pair(redex, _)` focus is a candidate member whose component is a redex — not a value, not
neutral, not weak-head reducible — so the trichotomy concludes the CONSTRUCTOR-HEAD relaxation
`isPairConstructorHead` (head `pair`, components arbitrary), recovered from the root generator by
`isPairConstructorHead_ofValueHead`.

This is the fourth dependent data-eliminator general-candidate family (after `bool`, `option`, `either`), the first
PROJECTING one, confirming `dependentDataEliminatorMemberFromValueDispatch` + `dataTaitFocusTrichotomyOfValueHead`
cover a no-motive no-branch eliminator (`fst` and `snd` share every helper).

## Zero-axiom verification

`isPairConstructorHead_ofValueHead` mirrors `isOptionConstructorHead_ofValueHead`'s head-recovery idiom (match the
cell, `change` the singleton root equation, `subst`), collapsing the `Unit` payload and the two-child GADT (`[0, 0]`).
The members drive the shared skeleton with the projection spine lemmas (`fst`/`snd_isStronglyNormalizing_of_argument`,
`WeakHeadStep.scrutineeFst` / `…Snd`, `IsNeutral.fst` / `…snd`) and fire `iotaFstPair` / `iotaSndPair`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the
`FX1Poly.Core` namespace sweep in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The pair value-head generator predicate.**  The sole Σ data constructor. -/
def isPairValueHead (generator : Generator) : Prop :=
  generator = .gen_pair

/-- **The pair constructor-head predicate.**  A term is Σ-constructor-headed when it is `pairCell first second`
with the components ARBITRARY (no normality side-condition — unlike `isPairValue`).  This is the predicate the
dependent-eliminator value dispatch fires the ι on (the ι fires on `pair(anything, anything)`) and the trichotomy
concludes; `isPairValue ⊆ isPairConstructorHead`. -/
def isPairConstructorHead {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ first second : RawTerm scope, term = pairCell first second

/-- **A pair value is Σ-constructor-headed.**  Drops the component-normality side-condition of `isPairValue` — the
easy inclusion the trichotomy's candidate-side bridge composes with. -/
theorem isPairConstructorHead_ofIsPairValue {scope : Nat} {term : RawTerm scope}
    (valueIsPair : isPairValue term) : isPairConstructorHead term := by
  obtain ⟨first, second, valueEq, _firstNormal, _secondNormal⟩ := valueIsPair
  exact ⟨first, second, valueEq⟩

/-- **A pair value's root generator is the pair value head.**  The candidate-side trichotomy bridge: a normal Σ
value's root is `gen_pair`. -/
theorem isPairValueHead_ofIsPairValue {scope : Nat} {term : RawTerm scope}
    (valueIsPair : isPairValue term) : isPairValueHead term.rootGenerator := by
  obtain ⟨_first, _second, valueEq, _firstNormal, _secondNormal⟩ := valueIsPair
  exact congrArg RawTerm.rootGenerator valueEq

/-- **★ Root-generator reconstruction for pair.**  A term whose root generator is the Σ constructor IS
Σ-constructor-headed — `pairCell first second` structurally.  The conclusion-side trichotomy bridge, recovering the
focus's constructor shape from `reachesValueHead`'s root-generator output.  Mirrors
`isOptionConstructorHead_ofValueHead`'s head-recovery (match the cell, `change`+`subst` the root equation), then
collapses the `Unit` payload and the two-child GADT (`[0, 0]`). -/
theorem isPairConstructorHead_ofValueHead {scope : Nat} {term : RawTerm scope}
    (rootIsPair : isPairValueHead term.rootGenerator) : isPairConstructorHead term := by
  match term, rootIsPair with
  | .mkGen generator payload children, rootIsPair =>
      change generator = .gen_pair at rootIsPair
      subst rootIsPair
      match payload, children with
      | (), .childCons first (.childCons second .childNil) => exact ⟨first, second, rfl⟩

/-- **★ Dependent `fst` reducibility: the cell lands in the candidate of the motive at the scrutinee.**  The
first-projection companion to `optionMatchDependentReducibleMember`.  The scrutinee arrives as a member of the
head-expansion-closed `dataTaitCandidate isPairValue`; the FIRST component is a result member WHEN the scrutinee
reaches `pair first second` (the conditioning the bounded row discharges from the motive's reducibility).  Drives
the shared `dependentDataEliminatorMemberFromValueDispatch` with no motive/branch spine: the per-focus classifier
is `dataTaitFocusTrichotomyOfValueHead` at pair's singleton constructor-head set; the value handler fires
`iotaFstPair` and transports the conditioned first component. -/
theorem fstDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {scrutinee : RawTerm scope}
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (firstMemberIfReachesPair : ∀ first second : RawTerm scope,
        StepStar scrutinee (pairCell first second) → resultCandidate first) :
    resultCandidate (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
  dependentDataEliminatorMemberFromValueDispatch
    (isValue := isPairConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isPairValue)
    (elimSpine := fun focus => .mkGen .gen_fst () (.childCons focus .childNil))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isPairValueHead) (candidateValue := isPairValue)
        (conclusionValue := isPairConstructorHead)
        (fun valueIsPair => isPairValueHead_ofIsPairValue valueIsPair)
        (fun rootIsPair => isPairConstructorHead_ofValueHead rootIsPair)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusStronglyNormalizing =>
      fst_isStronglyNormalizing_of_argument focusStronglyNormalizing)
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeFst focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.fst focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      obtain ⟨first, second, focusIsPair⟩ := focusIsConstructorHead
      subst focusIsPair
      exact headExpand IotaHeadStep.iotaFstPair.toWeakHeadStep
        (firstMemberIfReachesPair first second reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

/-- **★ Dependent `snd` reducibility: the cell lands in the candidate of the motive at the scrutinee.**  Symmetric
to `fstDependentReducibleMember`, projecting the SECOND component: the conditioned premise gives the second
component a result member WHEN the scrutinee reaches `pair first second`, the spine SN is
`snd_isStronglyNormalizing_of_argument`, and the value handler fires `iotaSndPair`.  Shares every pair helper with
`fst` — the single-constructor projecting eliminator's two halves. -/
theorem sndDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {scrutinee : RawTerm scope}
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (secondMemberIfReachesPair : ∀ first second : RawTerm scope,
        StepStar scrutinee (pairCell first second) → resultCandidate second) :
    resultCandidate (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
  dependentDataEliminatorMemberFromValueDispatch
    (isValue := isPairConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isPairValue)
    (elimSpine := fun focus => .mkGen .gen_snd () (.childCons focus .childNil))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isPairValueHead) (candidateValue := isPairValue)
        (conclusionValue := isPairConstructorHead)
        (fun valueIsPair => isPairValueHead_ofIsPairValue valueIsPair)
        (fun rootIsPair => isPairConstructorHead_ofValueHead rootIsPair)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusStronglyNormalizing =>
      snd_isStronglyNormalizing_of_argument focusStronglyNormalizing)
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeSnd focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.snd focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      obtain ⟨first, second, focusIsPair⟩ := focusIsConstructorHead
      subst focusIsPair
      exact headExpand IotaHeadStep.iotaSndPair.toWeakHeadStep
        (secondMemberIfReachesPair first second reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

end FX1Poly.Core
