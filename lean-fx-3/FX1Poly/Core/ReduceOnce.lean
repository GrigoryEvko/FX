import FX1Poly.Core.FireRootRedex

/-! # FX1Poly/Core/ReduceOnce
    — one deterministic reduction step as a total function, with soundness.

`FireRootRedex.lean` computes a ROOT redex's reduct.  This file lifts that to a full one-step reducer
`RawTerm.reduceOnce : RawTerm scope → Option (RawTerm scope)`: fire a root redex if present, otherwise
descend the child spine (leftmost-outermost) to the first reducible child and reduce there.  It is the
computational mirror of `exists_step_of_not_isStepNormalForm` (which only witnessed a `Step`
existentially) — `reduceOnce` produces the reduct as a concrete `RawTerm`.

`reduceOnce_sound` proves every produced reduct is a genuine `Step`: a root firing is
`fireRootRedex_sound`, a child reduction is `Step.cong` over the spine companion `reduceOnceSpine_sound`
(itself `StepChildren.here` for a head reduction, `StepChildren.there` for a tail reduction).  This is the
descent engine the weak-normalization normalizer FUNCTION (eval/quote) iterates along `Acc StepSuccessor`:
each `reduceOnce = some t'` yields `Step t t'`, so `t'` is an accessible successor and the descent provably
shrinks; pairing this with the (forthcoming) completeness direction `reduceOnce = none → isStepNormalForm`
turns the existential `exists_normalForm_of_isStronglyNormalizing` into a real `RawTerm`-valued normalizer.

## Zero-axiom verification

`reduceOnce`/`reduceOnceSpine` are a structural mutual recursion (Option-valued matches over the single-ctor
`RawTerm` and the indexed `RawTermChildren` spine), propext/Quot.sound-free.  The soundness mutual reduces
the single-scrutinee `reduceOnce` with `dsimp only` and the two-scrutinee `reduceOnceSpine` with an
`rfl`-unfold lemma (avoiding the mutual-def equation lemma that would pull `Quot.sound`), then `cases` on the
sub-results, `injection` + the matching `Step`/`StepChildren` constructor, and `nomatch` on the impossible
`none = some` equations.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

mutual

/-- **One reduction step, as a function.**  Fire a root redex (`fireRootRedex`) if present; otherwise
descend the child spine to the first reducible child.  `none` means no redex was found at the root or in
any child (the leftmost-outermost strategy bottomed out). -/
def RawTerm.reduceOnce {scope : Nat} (term : RawTerm scope) : Option (RawTerm scope) :=
  match term with
  | .mkGen generator payload children =>
      match RawTerm.fireRootRedex generator payload children with
      | some reduct => some reduct
      | none =>
          (RawTermChildren.reduceOnceSpine children).map
            (fun reducedChildren => .mkGen generator payload reducedChildren)

/-- **One reduction step inside a child spine.**  Reduce the first reducible child, leaving the rest
fixed; `none` if no child reduces. -/
def RawTermChildren.reduceOnceSpine {binderShifts : List Nat} {scope : Nat}
    (children : RawTermChildren binderShifts scope) :
    Option (RawTermChildren binderShifts scope) :=
  match binderShifts, children with
  | [], .childNil => none
  | _headShift :: _restShifts, .childCons childHead childTail =>
      match RawTerm.reduceOnce childHead with
      | some reducedHead => some (.childCons reducedHead childTail)
      | none =>
          (RawTermChildren.reduceOnceSpine childTail).map
            (fun reducedTail => .childCons childHead reducedTail)

end

mutual

/-- **Soundness of `reduceOnce`.**  Every reduct it produces is a genuine `Step` — a root firing via
`fireRootRedex_sound`, a child reduction via `Step.cong` over the spine companion. -/
theorem RawTerm.reduceOnce_sound {scope : Nat} {term reduct : RawTerm scope}
    (reduced : RawTerm.reduceOnce term = some reduct) :
    Step term reduct := by
  match term with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.reduceOnce] at reduced
      cases hFire : RawTerm.fireRootRedex generator payload children with
      | some rootReduct =>
          rw [hFire] at reduced
          injection reduced with reductEq
          rw [← reductEq]
          exact RawTerm.fireRootRedex_sound hFire
      | none =>
          rw [hFire] at reduced
          cases hSpine : RawTermChildren.reduceOnceSpine children with
          | some reducedChildren =>
              rw [hSpine] at reduced
              dsimp only [Option.map] at reduced
              injection reduced with reductEq
              rw [← reductEq]
              exact Step.cong generator payload (RawTermChildren.reduceOnceSpine_sound hSpine)
          | none =>
              rw [hSpine] at reduced
              nomatch reduced

/-- **Soundness of `reduceOnceSpine`.**  The reduced spine is a genuine `StepChildren` — `StepChildren.here`
for a head reduction, `StepChildren.there` for a tail reduction. -/
theorem RawTermChildren.reduceOnceSpine_sound {binderShifts : List Nat} {scope : Nat}
    {children reducedChildren : RawTermChildren binderShifts scope}
    (reduced : RawTermChildren.reduceOnceSpine children = some reducedChildren) :
    StepChildren children reducedChildren := by
  match binderShifts, children with
  | [], .childNil =>
      nomatch reduced
  | _headShift :: _restShifts, .childCons childHead childTail =>
      have unfoldSpine : RawTermChildren.reduceOnceSpine (.childCons childHead childTail) =
          (match RawTerm.reduceOnce childHead with
            | some reducedHead => some (.childCons reducedHead childTail)
            | none =>
                (RawTermChildren.reduceOnceSpine childTail).map
                  (fun reducedTail => .childCons childHead reducedTail)) := rfl
      rw [unfoldSpine] at reduced
      cases hHead : RawTerm.reduceOnce childHead with
      | some reducedHead =>
          rw [hHead] at reduced
          injection reduced with reductEq
          rw [← reductEq]
          exact StepChildren.here childTail (RawTerm.reduceOnce_sound hHead)
      | none =>
          rw [hHead] at reduced
          cases hTail : RawTermChildren.reduceOnceSpine childTail with
          | some reducedTail =>
              rw [hTail] at reduced
              dsimp only [Option.map] at reduced
              injection reduced with reductEq
              rw [← reductEq]
              exact StepChildren.there childHead (RawTermChildren.reduceOnceSpine_sound hTail)
          | none =>
              rw [hTail] at reduced
              nomatch reduced

end

end FX1Poly.Core
