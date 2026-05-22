import LeanFX2.Term.StrengtheningImage.RenameImageInterface
import LeanFX2.Term.Inversion

/-! # Term/StrengtheningImage/TargetImageTotality

Target-direction typed image totality.

The shipped renaming-image interface (T1
`strengthenTyped?_rename_eq` and T3
`rename_image_iff_strengthenTyped?_some`) reasons in the
**source direction**: it takes an explicit
`sourceTerm : Term sourceCtx sourceType sourceRaw`,
renames it forward through a typed renaming, and proves
partial strengthening recovers the source.

Block B (`Step.par.preserves_rename_image`, #2022) requires
the *target direction*: given a `Term targetCtx (sourceType.rename rho)
(sourceRaw.rename rho)` that arrived from typed parallel reduction
(`Step.par`) but is not literally a `Term.rename` image, prove
partial strengthening still succeeds.

This file builds the target-direction headline incrementally,
starting with the closed-atomic unit case.  Each per-constructor
theorem here pulls the input term down to its unique
canonical-shape representative via the shipped `Term.<ctor>_unique`
inversion lemma in `Term/Inversion.lean`, then consumes the
dispatcher's definitional reduction at the corresponding arm.
The inversion-then-dispatch pattern avoids the `cases`-on-Term
fragility encountered when the `Term.var` arm is reachable and
`varType` is opaque to the tactic.
-/

namespace LeanFX2

namespace Term

/-- Target-direction totality at `Term.unit`.

Any typed term whose type index is `Ty.unit` and whose raw index
is `RawTerm.unit` strengthens through *every* context strengthening.

The proof routes through `Term.unit_unique` (shipped zero-axiom in
`Term/Inversion.lean`): the inversion lemma yields `HEq targetTerm
Term.unit`, which converts to an `Eq` because both sides share the
same indexed type `Term sourceCtx Ty.unit RawTerm.unit`.  After
substitution, the dispatcher's unit arm reduces by definition to
`some (partialStrengthenTypedUnit strengthening)`. -/
theorem partialStrengthenTyped?_isSome_target_unit
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.unit (level := level) (scope := sourceScope))
        (RawTerm.unit (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm (Term.unit (context := sourceCtx) (level := level)) :=
    Term.unit_unique targetTerm
      (Term.unit (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.unit (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

end Term

end LeanFX2
