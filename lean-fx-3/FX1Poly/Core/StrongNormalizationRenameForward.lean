import FX1Poly.Core.StrongNormalizationRename
import FX1Poly.Core.RawTermRenameComposeFusion
import FX1Poly.Core.RawTermRenamePointwise
import FX1Poly.Core.RawTermStrengthen

/-! # Foundation/PolyCell/Core/StrongNormalizationRenameForward
    — strong normalization is PRESERVED forward along a left-invertible renaming

`StrongNormalizationRename` proves the *reflection* direction (`SN (rename rho t) -> SN t`), which needs
only `Step.rename` and holds for every renaming.  Its docstring records that the opposite *forward*
direction (`SN t -> SN (rename rho t)`) "would need Step reflection ... which requires `rho` injective;
that direction is not proved in this file."

This file proves exactly that forward direction, for any renaming that has a LEFT INVERSE — i.e. a
renaming `leftInverseRenaming` with `leftInverseRenaming (forwardRenaming i) = i` for every source index.
Every injective renaming has one (in particular every weakening), so this is the forward SN-preservation
the reducibility-under-renaming development needs for its neutral leaf.

The proof does NOT redo Step reflection by induction.  Instead it runs the SHIPPED reflection lemma
`isStronglyNormalizing_of_rename` on the LEFT INVERSE: renaming `rename forwardRenaming sourceTerm` once
more by `leftInverseRenaming` round-trips back to `sourceTerm` (rename-fusion `rename_compose` collapses the
two renamings into their composition, which is pointwise the identity renaming by the left-inverse property,
and `rename_identity_apply` discharges the identity rename).  So `IsStronglyNormalizing sourceTerm` already
witnesses `IsStronglyNormalizing (rename leftInverseRenaming (rename forwardRenaming sourceTerm))`, and
reflection hands back `IsStronglyNormalizing (rename forwardRenaming sourceTerm)`.

## Zero-axiom verification

Three shipped rewrites (`rename_compose`, `rename_pointwise`, `rename_identity_apply`) feeding the shipped
reflection lemma `isStronglyNormalizing_of_rename`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- **Strong normalization is preserved forward along a left-invertible renaming.**  If `sourceTerm` is
strongly normalizing and `leftInverseRenaming` undoes `forwardRenaming` on every source index, then
`RawTerm.rename forwardRenaming sourceTerm` is strongly normalizing.  Proved by round-tripping through the
left inverse and applying the shipped reflection lemma `isStronglyNormalizing_of_rename`. -/
theorem isStronglyNormalizing_rename_of_leftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    {sourceTerm : RawTerm sourceScope}
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    (sourceTerminates : IsStronglyNormalizing sourceTerm) :
    IsStronglyNormalizing (RawTerm.rename forwardRenaming sourceTerm) := by
  apply isStronglyNormalizing_of_rename leftInverseRenaming
  have roundTrip :
      RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming sourceTerm) = sourceTerm := by
    rw [RawTerm.rename_compose forwardRenaming leftInverseRenaming sourceTerm]
    have composeIsIdentity :
        RawRenaming.PointwiseEq
          (RawRenaming.compose forwardRenaming leftInverseRenaming)
          (RawRenaming.identity (scope := sourceScope)) := by
      intro position
      simp only [RawRenaming.compose, RawRenaming.identity]
      exact leftInverseProperty position
    rw [RawTerm.rename_pointwise composeIsIdentity sourceTerm]
    exact RawTerm.rename_identity_apply sourceTerm
  rw [roundTrip]
  exact sourceTerminates

end StepStar
end FX1Poly.Core
