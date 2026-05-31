import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaOption — optionMatch step iota

The SR arm for `iotaOptionMatchSome`:

`optionMatch (optionSome value) noneBranch someBranch ↝ app someBranch value`.

Structurally identical to `iotaEitherMatchInl` / `iotaEitherMatchInr` — a
single-payload wrapper plus two branches, target `gen_app` of the relevant
branch + wrapped value.  The wrapper generator is `gen_optionSome` and the
chosen branch is `someBranch` (the second of two branches).
-/

namespace FX1Poly.Core

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

end FX1Poly.Core
