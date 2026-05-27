import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaBoolTrue — SR's first arm

V2-L3.1 phase D step 5 (2026-05-27).  Ships the FIRST arm of the
Subject Reduction theorem on the v2 substrate: preservation across
`Step.iotaBoolTrue`.

## What this arm proves

`Step.iotaBoolTrue`: `boolElim boolTrue thenBranch elseBranch → thenBranch`.

The SR statement specialized to this arm:

  `HasCertifiedCellDim0 source → HasCertifiedCellDim0 thenBranch`

where source = `mkGen .gen_boolElim () (childCons boolTrue
(childCons thenBranch (childCons elseBranch childNil)))`.

The proof is the textbook minimal iota case:

  1. Destructure `HasCertifiedCellDim0 source` to expose `sort` and
     `sourceCell : PolyCell ... .termBase (mkGen .gen_boolElim ...)`.
  2. `cases sourceCell` — only the `.gen` constructor matches a
     `.termBase`-shaped raw cell.  Get `admission`, `payloadEvidence`,
     `spine`.
  3. The spine has 3 head cells (boolElim's three children: scrutinee,
     then-branch, else-branch).  We need the second.
  4. `spine.tail` skips the scrutinee (boolTrue).  Result: a spine
     over `(childCons thenBranch (childCons elseBranch childNil))`.
  5. `(spine.tail).headAtDim0 rfl` extracts the thenBranch cell at
     dim 0 with trivial boundary.
  6. Wrap as `HasCertifiedCellDim0.intro .term thenCell`.

## Why iotaBoolTrue is the right STARTING arm

Among the 18 Step constructors, `iotaBoolTrue` is uniquely simple:

  * **No substitution**: target is a CHILD of the source, not a
    substituted body.  Avoids needing V2-L2.12's subst preservation.
  * **No rename / lift**: the target lives at the same scope as the
    source (`binderShifts [0, 0, 0]`).
  * **No HEq cast through dim-indexed boundary**: thenBranch is a
    term, and the spine head's cellSort is just `.term`.
  * **Single spine step (tail + head)**: only the second child of
    three, so we tail once then head.

Compare to:

  * `Step.beta` requires subst preservation.
  * `Step.cong` requires inductive hypothesis threading through the
    spine.
  * `Step.iotaNatRecSucc` requires assembling a new applied form.

iotaBoolTrue is the cleanest pure-projection iota — perfect for
establishing the proof-template that the other iotas (iotaBoolFalse,
iotaFstPair, iotaSndPair, iotaNatElimZero, iotaListElimNil,
iotaOptionMatchNone) inherit.

## Pattern-template for sibling iotas

This commit establishes the canonical pattern.  Sibling arms
follow:

  * **Pure projection iotas** (`iotaBoolFalse`, `iotaFstPair`,
    `iotaSndPair`, `iotaNatElimZero`, `iotaListElimNil`,
    `iotaOptionMatchNone`): vary which spine position to extract
    (tail count + head extraction).

  * **Compound iotas** (`iotaNatElimSucc`, `iotaListElimCons`,
    `iotaNatRecSucc`, `iotaOptionMatchSome`): assemble a new
    applied form from extracted spine components — uses the
    PolyCell.gen constructor to rebuild after extraction.

  * **Beta**: requires substitution-preservation (V2-L2.12); the
    extracted body + arg cells are passed through the subst
    preservation lemma.

  * **Cong**: structural induction on the child step + spine
    recursion.

## Zero-axiom verification

The proof uses pure `cases` on the inductive PolyCell (single-arm
match since only `.gen` produces a `.termBase`-shaped raw cell)
followed by the spine projections (V2-L3.1 phase D step 2).  No
`simp`, no `omega`, no propext-touching tactics.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **SR arm: `Step.iotaBoolTrue` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source `boolElim boolTrue
thenBranch elseBranch`, it holds on the target `thenBranch`.

Proof template that sibling pure-projection iotas
(`iotaBoolFalse`, `iotaFstPair`, etc.) inherit. -/
theorem HasCertifiedCellDim0.preservedByIotaBoolTrue
    {profile : PolyProfile} {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_boolElim ()
          (.childCons (.mkGen .gen_boolTrue () .childNil)
            (.childCons thenBranch
              (.childCons elseBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) thenBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    -- sourceCell : PolyCell profile sort 0 scope trivial
    --                (.termBase (.mkGen .gen_boolElim ...))
    -- Only the `.gen` constructor produces a `.termBase`-shaped
    -- raw cell, so `cases` derives a single-arm match.
    cases sourceCell with
    | gen _ _ spine =>
      -- spine has type:
      --   CertifiedTermSpine profile [termSameScope, termSameScope,
      --                                  termSameScope]
      --     scope [0, 0, 0]
      --     (childCons boolTrue (childCons thenBranch
      --       (childCons elseBranch childNil)))
      -- `spine.tail` skips the boolTrue head, leaving a 2-element
      -- spine over `(childCons thenBranch (childCons elseBranch
      -- childNil))`.
      -- `(spine.tail).headAtDim0 rfl` extracts the thenBranch cell.
      exact .intro .term ((spine.tail).headAtDim0 rfl)

end LeanFX2.Foundation.PolyCell.Core
