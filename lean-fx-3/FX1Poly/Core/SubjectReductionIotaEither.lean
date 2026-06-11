import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaEither — eitherMatch step iotas

The SR arms for the two `eitherMatch` **compound iotas**.

A compound iota differs from a pure-projection iota in that its
target is NOT a direct child of the source's spine — instead, the
target is a NEWLY-CONSTRUCTED `gen_app` term assembled from a
wrapper's payload + a branch:

  * iotaEitherMatchInl: `eitherMatch motive leftBranch rightBranch (inl value) ↝ app leftBranch value`
  * iotaEitherMatchInr: `eitherMatch motive leftBranch rightBranch (inr value) ↝ app rightBranch value`

The other compound iotas — `iotaOptionMatchSome`, `iotaNatElimSucc`,
`iotaListElimCons`, `iotaNatRecSucc` — follow the same template with
different wrapper / branch positions.

## What distinguishes compound from projection iotas

The projection iotas (pure and nested) all extract their target FROM the
source's spine structure: the target is a child or a descendant child,
never a new construction.

Compound iotas BUILD a new term:

  source: `gen_eitherMatch ()` over `[motive, leftBranch, rightBranch, eitherInl wrapper]`
  target: `gen_app ()` over `[leftBranch, value]`   ← FRESH

The proof must:

  1. Destructure source to access the certified child cells
     (motive, leftBranch, rightBranch, eitherInl wrapper) — the
     Phase-Z motive heads the spine (under one binder) and is
     discarded; the eitherInl wrapper sits LAST.
  2. Unwrap the eitherInl wrapper to extract the certified `value`
     cell (one level of nested cases — needs the
     `generalize_sort` recipe, per commit memory
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
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaEitherMatchInl` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source `eitherMatch motive
leftBranch rightBranch (inl value)`, it holds on the target
`app leftBranch value`.

Compound iota: the target is a NEW `gen_app` term built from the
extracted `leftBranch` (outer spine position 1, after the discarded
motive) and `value` (inside the `eitherInl` wrapper at the LAST outer
position).  Uses the `generalize_sort` recipe to unwrap the eitherInl
cell. -/
theorem HasCertifiedCellDim0.preservedByIotaEitherMatchInl
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {value leftBranch rightBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch
                (.childCons
                  (.mkGen .gen_eitherInl () (.childCons value .childNil))
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons leftBranch (.childCons value .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      -- Destructure outer spine into
      -- [motiveCell, leftBranchCell, rightBranchCell, eitherInlCell].
      cases outerSpine with
      | cons _motiveCell restAfterMotive =>
        cases restAfterMotive with
        | cons leftBranchCell restAfterLeft =>
          cases restAfterLeft with
          | cons _rightBranchCell restAfterRight =>
            cases restAfterRight with
            | cons eitherInlCell _ =>
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
    {motive : RawTerm (scope + 1)}
    {value leftBranch rightBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch
                (.childCons
                  (.mkGen .gen_eitherInr () (.childCons value .childNil))
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons rightBranch (.childCons value .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons _motiveCell restAfterMotive =>
        cases restAfterMotive with
        | cons _leftBranchCell restAfterLeft =>
          cases restAfterLeft with
          | cons rightBranchCell restAfterRight =>
            cases restAfterRight with
            | cons eitherInrCell _ =>
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

end FX1Poly.Core
