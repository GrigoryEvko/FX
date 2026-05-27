import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaOption — optionMatch step iota

V2-L3.1 phase D step 10 (2026-05-27).  Ships SR arm 11:
`iotaOptionMatchSome`.

`optionMatch (optionSome value) noneBranch someBranch ↝ app someBranch value`.

Structurally IDENTICAL to `iotaEitherMatchInl` /
`iotaEitherMatchInr` (sibling commit a8f3c45a) — a single-payload
wrapper plus two branches, target `gen_app` of the relevant branch
+ wrapped value.  Only difference: the wrapper generator is
`gen_optionSome` (instead of `gen_eitherInl` / `gen_eitherInr`),
and the chosen branch is `someBranch` (the second of two
branches).

The template proven in the eitherMatch commit applies verbatim
modulo these names.

After this commit: 11/18 SR arms shipped.  Remaining: 3 compound
iotas (natElimSucc / natRecSucc / listElimCons — all build NESTED
`gen_app` terms with recursive calls or 2-arg payload extraction),
2 identity iotas, beta, cong.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **SR arm: `Step.iotaOptionMatchSome` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source
`optionMatch (optionSome value) noneBranch someBranch`, it holds
on the target `app someBranch value`.

Compound iota with single-payload wrapper, same template as the
eitherMatch arms. -/
theorem HasCertifiedCellDim0.preservedByIotaOptionMatchSome
    {profile : PolyProfile} {scope : Nat}
    {value noneBranch someBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_optionMatch ()
          (.childCons
            (.mkGen .gen_optionSome () (.childCons value .childNil))
            (.childCons noneBranch
              (.childCons someBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons someBranch (.childCons value .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons optionSomeCell restAfterOptionSome =>
        cases restAfterOptionSome with
        | cons _noneBranchCell restAfterNone =>
          cases restAfterNone with
          | cons someBranchCell _ =>
            generalize hSort :
                (ChildSpec.termSameScope.cellSort) = innerSort
              at optionSomeCell
            cases optionSomeCell with
            | gen _ _ optionSomeInnerSpine =>
              cases optionSomeInnerSpine with
              | cons valueCell _ =>
                exact .intro .term
                  (PolyCell.gen
                    SupportedGenerator.gen_app
                    (genPayloadEvidence (generator := .gen_app)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons someBranchCell
                      (CertifiedTermSpine.cons valueCell
                        CertifiedTermSpine.nil)))

end LeanFX2.Foundation.PolyCell.Core
