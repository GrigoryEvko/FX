import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaOption — optionMatch step iota

The SR arm for `iotaOptionMatchSome`:

`optionMatch motive noneBranch someBranch (optionSome value) ↝ app someBranch value`.

Structurally identical to `iotaEitherMatchInl` / `iotaEitherMatchInr` — a
single-payload wrapper plus two branches, target `gen_app` of the relevant
branch + wrapped value.  The wrapper generator is `gen_optionSome` and the
chosen branch is `someBranch` (the second of two branches).  Phase-Z motive
shape: motive heads the spine (under one binder), the scrutinee
`optionSome value` sits LAST; the iota DISCARDS the motive.
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaOptionMatchSome` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source
`optionMatch motive noneBranch someBranch (optionSome value)`, it holds
on the target `app someBranch value`.

Compound iota with single-payload wrapper, same template as the
eitherMatch arms.  Phase-Z motive shape: motive is skipped (`tail`),
someBranch is the spine head after two tails, the scrutinee
`optionSome value` is the last spine cell. -/
theorem HasCertifiedCellDim0.preservedByIotaOptionMatchSome
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {value noneBranch someBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch
                (.childCons
                  (.mkGen .gen_optionSome () (.childCons value .childNil))
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons someBranch (.childCons value .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons _motiveCell restAfterMotive =>
        cases restAfterMotive with
        | cons _noneBranchCell restAfterNone =>
          cases restAfterNone with
          | cons someBranchCell restAfterSome =>
            cases restAfterSome with
            | cons optionSomeCell _ =>
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
