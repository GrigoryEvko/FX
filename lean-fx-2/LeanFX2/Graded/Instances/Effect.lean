import LeanFX2.Graded.Semiring
import LeanFX2.Effects.Foundation

/-! # Graded/Instances/Effect — effect rows as join-semilattice grades

Effects do not form a nontrivial `GradeSemiring` under FX semantics.
The effect dimension accumulates capabilities by row union:

* `bottom` = `Tot` / empty effect row
* `join` = row union
* `≤` = row subset / subeffect

Sequential and parallel composition both accumulate effects, but
semiring annihilation would require `bottom * effect = bottom`, which
is false for any nonempty effect row.  This file therefore exposes
effects through `GradeJoinSemilattice`, not by pretending they satisfy
the stronger semiring interface.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Effect grade reuses the kernel effect-row carrier. -/
abbrev EffectGrade : Type := LeanFX2.Effects.EffectRow

/-- Effect rows form a bounded join-semilattice under row union and
subset.  The laws are imported from `Effects.Foundation`, where they
are proven directly over the custom membership predicate. -/
instance : GradeJoinSemilattice EffectGrade where
  bottom := LeanFX2.Effects.EffectRow.empty
  join := LeanFX2.Effects.EffectRow.join
  le := LeanFX2.Effects.EffectRow.subset

  le_refl := LeanFX2.Effects.EffectRow.subset_refl

  le_trans := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact LeanFX2.Effects.EffectRow.subset_trans firstSubset secondSubset

  bottom_le := LeanFX2.Effects.EffectRow.empty_subset

  le_join_left := LeanFX2.Effects.EffectRow.join_subset_left

  le_join_right := LeanFX2.Effects.EffectRow.join_subset_right

  join_least_upper_bound := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact LeanFX2.Effects.EffectRow.join_least_upper_bound
      firstSubset secondSubset

  join_idempotent_le := LeanFX2.Effects.EffectRow.join_idempotent_subset

  join_comm_le := LeanFX2.Effects.EffectRow.join_commutes_subset

  join_assoc_le := LeanFX2.Effects.EffectRow.join_associates_subset

/-! ## Smoke samples -/

/-- `Tot` is the bottom effect grade. -/
example (someRow : EffectGrade) :
    GradeJoinSemilattice.le
      (GradeJoinSemilattice.bottom : EffectGrade) someRow :=
  GradeJoinSemilattice.bottom_le someRow

/-- Joining IO and Alloc contains Alloc. -/
example :
    LeanFX2.Effects.EffectRow.Member LeanFX2.Effects.EffectLabel.alloc
      (GradeJoinSemilattice.join
        (LeanFX2.Effects.EffectRow.singleton LeanFX2.Effects.EffectLabel.io)
        (LeanFX2.Effects.EffectRow.singleton LeanFX2.Effects.EffectLabel.alloc)
          : EffectGrade) :=
  LeanFX2.Effects.EffectRow.member_append_right
    [LeanFX2.Effects.EffectLabel.io] _
    (LeanFX2.Effects.EffectRow.Member.head [])

end LeanFX2.Graded.Instances
