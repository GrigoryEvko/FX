import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaEither — eitherMatch step iotas

V2-L3.1 phase D step 9 (2026-05-27).  Ships SR arms 9-10: the
FIRST two **compound iotas**.

A compound iota differs from a pure-projection iota in that its
target is NOT a direct child of the source's spine — instead, the
target is a NEWLY-CONSTRUCTED `gen_app` term assembled from a
wrapper's payload + a branch:

  * iotaEitherMatchInl: `eitherMatch (inl value) leftBranch rightBranch ↝ app leftBranch value`
  * iotaEitherMatchInr: `eitherMatch (inr value) leftBranch rightBranch ↝ app rightBranch value`

(The other 4 compound iotas — `iotaOptionMatchSome`,
`iotaNatElimSucc`, `iotaListElimCons`, `iotaNatRecSucc` — follow
the same template with different wrapper / branch positions.)

## What's new vs. the projection iotas

The 8 already-shipped iota arms (pure projection: 6, nested
projection: 2) all extract their target FROM the source's spine
structure.  The target is a child or a descendant child — never a
new construction.

Compound iotas BUILD a new term:

  source: `gen_eitherMatch ()` over `[eitherInl wrapper, leftBranch, rightBranch]`
  target: `gen_app ()` over `[leftBranch, value]`   ← FRESH

The proof must:

  1. Destructure source to access the certified child cells
     (eitherInl wrapper, leftBranch, rightBranch).
  2. Unwrap the eitherInl wrapper to extract the certified `value`
     cell (one level of nested cases — needs the
     `generalize_sort` recipe per #45aedf38 / commit memory
     `feedback_lean_generalize_sort_dep_elim`).
  3. ASSEMBLE a new `CertifiedTermSpine` carrying the leftBranch
     and value cells in the order gen_app expects.
  4. Wrap via `PolyCell.gen` with `SupportedGenerator.gen_app`
     and `GenPayloadEvidence.gen_app scope ()` (= `()`).

## Why the admission witness is `SupportedGenerator.gen_app` directly

`SupportedGenerator` is the GLOBAL admission inductive (one ctor
per Generator).  Profile-level admission layers on top via
`PolyProfile.admitsGenerator`.  `PolyCell.gen` takes the GLOBAL
admission, not the profile-level one — so any `gen_app` cell
construction can use `SupportedGenerator.gen_app` directly with
no profile hypothesis.

The same applies to `GenPayloadEvidence` (= `Unit` by default,
witness = `()`).

## Zero-axiom verification

Both arms close via the generalize-the-sort recipe + explicit
cons-spine construction.  No `simp`, no `omega`, no
propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

After this commit: 10/18 SR arms shipped.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **SR arm: `Step.iotaEitherMatchInl` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source `eitherMatch (inl
value) leftBranch rightBranch`, it holds on the target
`app leftBranch value`.

Compound iota: the target is a NEW `gen_app` term built from the
extracted `leftBranch` (outer spine position 2) and `value`
(inside the `eitherInl` wrapper at outer position 1).  Uses the
`generalize_sort` recipe to unwrap the eitherInl cell. -/
theorem HasCertifiedCellDim0.preservedByIotaEitherMatchInl
    {profile : PolyProfile} {scope : Nat}
    {value leftBranch rightBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_eitherMatch ()
          (.childCons
            (.mkGen .gen_eitherInl () (.childCons value .childNil))
            (.childCons leftBranch
              (.childCons rightBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons leftBranch (.childCons value .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      -- Destructure outer spine into [eitherInlCell, leftBranchCell, rightBranchCell].
      cases outerSpine with
      | cons eitherInlCell restAfterEitherInl =>
        cases restAfterEitherInl with
        | cons leftBranchCell _restAfterLeft =>
          -- Unwrap the eitherInl cell to get its inner spine carrying `value`.
          -- The generalize-sort recipe avoids the dep-elim wall:
          -- replacing the concrete `termSameScope.cellSort = .term` with
          -- a free variable lets the matcher derive the inner generator
          -- from the (concrete) raw cell index alone.
          generalize hSort :
              (ChildSpec.termSameScope.cellSort) = innerSort
            at eitherInlCell
          cases eitherInlCell with
          | gen _ _ eitherInlInnerSpine =>
            cases eitherInlInnerSpine with
            | cons valueCell _ =>
              -- Assemble the target gen_app spine: [leftBranch, value].
              -- Then build the target cell via PolyCell.gen with the
              -- global SupportedGenerator.gen_app admission witness and
              -- trivial GenPayloadEvidence (= () for default profile).
              exact .intro .term
                (PolyCell.gen
                  SupportedGenerator.gen_app
                  (genPayloadEvidence (generator := .gen_app)
                                       (scope := scope) ())
                  (CertifiedTermSpine.cons leftBranchCell
                    (CertifiedTermSpine.cons valueCell
                      CertifiedTermSpine.nil)))

/-- **SR arm: `Step.iotaEitherMatchInr` preserves `HasCertifiedCellDim0`.**

Symmetric to `preservedByIotaEitherMatchInl`: the only differences
are (a) the wrapper is `gen_eitherInr` instead of `gen_eitherInl`,
and (b) the branch built into the app is `rightBranch` instead of
`leftBranch`.  Same structural proof. -/
theorem HasCertifiedCellDim0.preservedByIotaEitherMatchInr
    {profile : PolyProfile} {scope : Nat}
    {value leftBranch rightBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_eitherMatch ()
          (.childCons
            (.mkGen .gen_eitherInr () (.childCons value .childNil))
            (.childCons leftBranch
              (.childCons rightBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons rightBranch (.childCons value .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons eitherInrCell restAfterEitherInr =>
        cases restAfterEitherInr with
        | cons _leftBranchCell restAfterLeft =>
          cases restAfterLeft with
          | cons rightBranchCell _ =>
            generalize hSort :
                (ChildSpec.termSameScope.cellSort) = innerSort
              at eitherInrCell
            cases eitherInrCell with
            | gen _ _ eitherInrInnerSpine =>
              cases eitherInrInnerSpine with
              | cons valueCell _ =>
                exact .intro .term
                  (PolyCell.gen
                    SupportedGenerator.gen_app
                    (genPayloadEvidence (generator := .gen_app)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons rightBranchCell
                      (CertifiedTermSpine.cons valueCell
                        CertifiedTermSpine.nil)))

end LeanFX2.Foundation.PolyCell.Core
