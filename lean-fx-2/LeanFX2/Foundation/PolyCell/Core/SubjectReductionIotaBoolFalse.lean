import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaBoolFalse — SR's second arm

V2-L3.1 phase D step 6 (2026-05-27).  Ships the SECOND arm of the
Subject Reduction theorem on the v2 substrate: preservation across
`Step.iotaBoolFalse`.

## What this arm proves

`Step.iotaBoolFalse`: `boolElim boolFalse thenBranch elseBranch → elseBranch`.

The SR statement specialized to this arm:

  `HasCertifiedCellDim0 source → HasCertifiedCellDim0 elseBranch`

where source = `mkGen .gen_boolElim () (childCons boolFalse
(childCons thenBranch (childCons elseBranch childNil)))`.

## Symmetry with iotaBoolTrue

This arm is structurally identical to `preservedByIotaBoolTrue` —
the proof pattern transfers verbatim except for the spine
position:

  * iotaBoolTrue: extract the SECOND child (thenBranch) via
    `spine.tail.headAtDim0 rfl`.
  * iotaBoolFalse: extract the THIRD child (elseBranch) via
    `spine.tail.tail.headAtDim0 rfl`.

The bool-eliminator's spine has three children at the same scope
(`binderShifts [0, 0, 0]`), and each `tail` step peels one off.

## Confirms the pattern template

This symmetric commit validates that the pure-projection iota
pattern from `preservedByIotaBoolTrue` transfers without
modification.  Sibling pure-projection iotas (`iotaNatElimZero`,
`iotaListElimNil`, `iotaOptionMatchNone`) follow the same template
with possibly different tail-counts and head sorts.

## Zero-axiom verification

Identical proof structure to `preservedByIotaBoolTrue`.  Pure
`cases` on the inductive PolyCell (single-arm match since only
`.gen` produces a `.termBase`-shaped raw cell) followed by spine
projections.  No `simp`, no `omega`, no propext-touching tactics.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **SR arm: `Step.iotaBoolFalse` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source `boolElim boolFalse
thenBranch elseBranch`, it holds on the target `elseBranch`.

Symmetric to `preservedByIotaBoolTrue` — the only difference is
which spine position (third instead of second) carries the
target. -/
theorem HasCertifiedCellDim0.preservedByIotaBoolFalse
    {profile : PolyProfile} {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_boolElim ()
          (.childCons (.mkGen .gen_boolFalse () .childNil)
            (.childCons thenBranch
              (.childCons elseBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) elseBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      -- spine has type:
      --   CertifiedTermSpine profile [termSameScope, termSameScope,
      --                                  termSameScope]
      --     scope [0, 0, 0]
      --     (childCons boolFalse (childCons thenBranch
      --       (childCons elseBranch childNil)))
      -- `spine.tail` skips boolFalse (1st position).
      -- `(spine.tail).tail` further skips thenBranch (2nd position).
      -- The resulting 1-element spine has elseBranch as its head.
      exact .intro .term (((spine.tail).tail).headAtDim0 rfl)

end LeanFX2.Foundation.PolyCell.Core
