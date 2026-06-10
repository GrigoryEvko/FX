import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaBoolFalse — SR arm for iotaBoolFalse

The Subject Reduction arm for preservation across `Step.iotaBoolFalse`.

## What this arm proves

`Step.iotaBoolFalse`: `boolElim motive thenBranch elseBranch boolFalse → elseBranch`.

The SR statement specialized to this arm:

  `HasCertifiedCellDim0 source → HasCertifiedCellDim0 elseBranch`

where source = `mkGen .gen_boolElim () (childCons motive (childCons
thenBranch (childCons elseBranch (childCons boolFalse childNil))))`
in the Phase-Z motive shape (motive first, under one binder;
scrutinee last).

## Symmetry with iotaBoolTrue

This arm is structurally identical to `preservedByIotaBoolTrue` —
the proof pattern transfers verbatim except for the spine
position:

  * iotaBoolTrue: extract the SECOND child (thenBranch) via
    `spine.tail.headAtDim0 rfl`.
  * iotaBoolFalse: extract the THIRD child (elseBranch) via
    `spine.tail.tail.headAtDim0 rfl`.

The bool-eliminator's spine has four children (`binderShifts
[1, 0, 0, 0]`): the motive under one binder at position 0, then the
two branches and the scrutinee at the same scope.  Each `tail` step
peels one off; the branches stay at positions 1 and 2.

## Confirms the pattern template

The pure-projection iota pattern from `preservedByIotaBoolTrue`
transfers without modification.  Sibling pure-projection iotas
(`iotaNatElimZero`, `iotaListElimNil`, `iotaOptionMatchNone`) follow
the same template with possibly different tail-counts and head sorts.

## Zero-axiom verification

Identical proof structure to `preservedByIotaBoolTrue`.  Pure
`cases` on the inductive PolyCell (single-arm match since only
`.gen` produces a `.termBase`-shaped raw cell) followed by spine
projections.  No `simp`, no `omega`, no propext-touching tactics.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaBoolFalse` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source `boolElim motive
thenBranch elseBranch boolFalse` (Phase-Z motive shape), it holds on
the target `elseBranch`.

Symmetric to `preservedByIotaBoolTrue` — the only difference is
which spine position (third instead of second) carries the
target. -/
theorem HasCertifiedCellDim0.preservedByIotaBoolFalse
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {thenBranch elseBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch
                (.childCons (.mkGen .gen_boolFalse () .childNil)
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) elseBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      -- spine has type:
      --   CertifiedTermSpine profile [termUnderBinder, termSameScope,
      --                                  termSameScope, termSameScope]
      --     scope [1, 0, 0, 0]
      --     (childCons motive (childCons thenBranch
      --       (childCons elseBranch (childCons boolFalse childNil))))
      -- `spine.tail` skips the motive (1st position).
      -- `(spine.tail).tail` further skips thenBranch (2nd position).
      -- The resulting 2-element spine has elseBranch as its head.
      exact .intro .term (((spine.tail).tail).headAtDim0 rfl)

end FX1Poly.Core
