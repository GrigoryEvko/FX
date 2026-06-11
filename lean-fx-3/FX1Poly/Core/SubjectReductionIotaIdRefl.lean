import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaIdRefl — identity-type iotas on refl

The two identity-eliminator iotas on `refl`:

  * iotaIdJRefl         : `idJ baseCase (refl rawWitness) ↝ baseCase`
  * iotaIdStrictRecRefl : same shape with `gen_idStrictRec`

## Why these are PURE PROJECTION (not compound)

Despite the name "identity iotas" suggesting motive substitution
(textbook MLTT idJ), the substrate factors the motive/endpoint
work into the PROFILE layer.  At the substrate level, the iota
rule simply DISCARDS the refl witness and returns the base case:

  source spine = [baseCase, refl-wrapper]
  target       = baseCase  (HEAD of the source spine)

That's pure projection — the simplest iota shape, simpler than
`iotaBoolTrue` (which does `spine.tail.headAtDim0` to skip the
position-0 motive head in the Phase-Z 4-child boolElim spine; here
we extract the HEAD directly).

Same template as `iotaBoolTrue`/`iotaBoolFalse`/etc.: single
`cases` on the certified cell, single `headAtDim0` on its spine.

## Zero-axiom verification

Both arms close with the identical 4-line tactic block.  No
`simp`, no `omega`, no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaIdJRefl` preserves `HasCertifiedCellDim0`.**

`idJ motive baseCase (refl rawWitness) ↝ baseCase`.

Pure-projection iota: target is spine position 1 (the base case).
Phase-Z motive shape places the motive (under two binders) at
position 0 and the base case at position 1 — like `iotaBoolTrue`,
extract via `tail.headAtDim0`, skipping the motive head. -/
theorem HasCertifiedCellDim0.preservedByIotaIdJRefl
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 2)}
    {baseCase rawWitness : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_idJ ()
          (.childCons motive
            (.childCons
              baseCase
              (.childCons
                (.mkGen .gen_refl () (.childCons rawWitness .childNil))
                .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCase := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      exact .intro .term (outerSpine.tail.headAtDim0 rfl)

/-- **SR arm: `Step.iotaIdStrictRecRefl` preserves `HasCertifiedCellDim0`.**

Symmetric to `preservedByIotaIdJRefl` — same proof template,
different outer generator (`gen_idStrictRec` instead of `gen_idJ`).
The substrate treats both eliminators identically at the
metadata level. -/
theorem HasCertifiedCellDim0.preservedByIotaIdStrictRecRefl
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 2)}
    {baseCase rawWitness : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_idStrictRec ()
          (.childCons motive
            (.childCons
              baseCase
              (.childCons
                (.mkGen .gen_refl () (.childCons rawWitness .childNil))
                .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCase := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      exact .intro .term (outerSpine.tail.headAtDim0 rfl)

end FX1Poly.Core
