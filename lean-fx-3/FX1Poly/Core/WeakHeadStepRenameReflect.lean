import FX1Poly.Core.WeakHeadStepRename
import FX1Poly.Core.RawTermRenameComposeFusion
import FX1Poly.Core.RawTermRenamePointwise
import FX1Poly.Core.RawTermStrengthen

/-! # Foundation/PolyCell/Core/WeakHeadStepRenameReflect
    — weak-head reduction is REFLECTED by a left-invertible renaming (head-normality is rename-stable)

`HeadStepRenameReflect` reflects the β-only head step under any renaming by inverting the renamed redex
shape (`rename_eq_app` / `rename_eq_lam`).  The stratified `ReducibleTypeStep` rename-closure needs
the FULL `WeakHeadStep` (β + root-ι + scrutinee-congruence) reflected — its `neutral` arm must carry a
weak-head-NORMAL type (no `WeakHeadStep`) across the renaming.  Re-running the redex-inversion approach
across the full relation would mean a renaming-inversion lemma per eliminator and per ι-constructor.

This file avoids all of that.  For a LEFT-INVERTIBLE renaming (a renaming `leftInverseRenaming` undoing
`forwardRenaming` on every source index — every injective renaming / weakening), reflection follows from
the shipped PRESERVATION lemma `WeakHeadStep.rename` run on the left inverse: a step of
`RawTerm.rename forwardRenaming term` renames once more by `leftInverseRenaming` to a step of
`RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming term)`, which round-trips back to `term`
(`rename_compose` collapses the two renamings into their composition, pointwise the identity by the
left-inverse property, discharged by `rename_identity_apply`).  So the renamed step's source already steps.
This is the same round-trip device the neutral-leaf SN lemma `isStronglyNormalizing_rename_of_leftInverse`
uses, here on `WeakHeadStep.rename` instead of `isStronglyNormalizing_of_rename`.

## Zero-axiom verification

`rename_compose` + `rename_pointwise` + `rename_identity_apply` for the round-trip, feeding the shipped
preservation `WeakHeadStep.rename`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Round-trip of a left-invertible renaming.**  Renaming by `forwardRenaming` then by a left inverse
`leftInverseRenaming` (undoing it on every source index) returns the original term: the two renamings fuse
to their composition (`rename_compose`), which is pointwise the identity renaming by the left-inverse
property, discharged by `rename_identity_apply`. -/
theorem RawTerm.rename_leftInverse_roundTrip {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    (term : RawTerm sourceScope) :
    RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming term) = term := by
  rw [RawTerm.rename_compose forwardRenaming leftInverseRenaming term]
  have composeIsIdentity :
      RawRenaming.PointwiseEq
        (RawRenaming.compose forwardRenaming leftInverseRenaming)
        (RawRenaming.identity (scope := sourceScope)) := by
    intro position
    simp only [RawRenaming.compose, RawRenaming.identity]
    exact leftInverseProperty position
  rw [RawTerm.rename_pointwise composeIsIdentity term]
  exact RawTerm.rename_identity_apply term

/-- **A left-invertible renaming reflects the complete weak-head reduction.**  If `RawTerm.rename
forwardRenaming term` takes a `WeakHeadStep`, then so does `term`.  Run the shipped preservation
`WeakHeadStep.rename` on the left inverse and round-trip the subject back to `term`. -/
theorem WeakHeadStep.rename_reflects_of_leftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {term : RawTerm sourceScope} {reduct : RawTerm targetScope}
    (renamedStep : WeakHeadStep (RawTerm.rename forwardRenaming term) reduct) :
    ∃ sourceReduct : RawTerm sourceScope, WeakHeadStep term sourceReduct := by
  have stepBack :
      WeakHeadStep (RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming term))
        (RawTerm.rename leftInverseRenaming reduct) :=
    WeakHeadStep.rename leftInverseRenaming renamedStep
  rw [RawTerm.rename_leftInverse_roundTrip forwardRenaming leftInverseRenaming leftInverseProperty term]
    at stepBack
  exact ⟨RawTerm.rename leftInverseRenaming reduct, stepBack⟩

/-- **A left-invertible renaming preserves weak-head normality.**  If no `WeakHeadStep` fires on `term`,
none fires on `RawTerm.rename forwardRenaming term` — the contrapositive of
`rename_reflects_of_leftInverse`.  This is the `neutral`-arm ingredient of the stratified
`ReducibleTypeStep` rename-closure: a weak-head-normal (non-Π, non-universe) type stays weak-head-normal
after a left-invertible renaming, so it routes through the same `neutral` arm at the renamed code. -/
theorem WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {term : RawTerm sourceScope}
    (weakHeadNormal : ∀ reduct : RawTerm sourceScope, ¬ WeakHeadStep term reduct) :
    ∀ reduct : RawTerm targetScope, ¬ WeakHeadStep (RawTerm.rename forwardRenaming term) reduct := by
  intro reduct renamedStep
  obtain ⟨sourceReduct, sourceStep⟩ :=
    WeakHeadStep.rename_reflects_of_leftInverse forwardRenaming leftInverseRenaming
      leftInverseProperty renamedStep
  exact weakHeadNormal sourceReduct sourceStep

end FX1Poly.Core
