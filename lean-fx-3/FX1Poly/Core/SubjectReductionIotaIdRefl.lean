import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaIdRefl — identity-type iotas on refl

V2-L3.1 phase D step 11 (2026-05-27).  Ships SR arms 12-13:
the two identity-eliminator iotas on `refl`.

  * iotaIdJRefl       : `idJ baseCase (refl rawWitness) ↝ baseCase`
  * iotaIdStrictRecRefl : same shape with `gen_idStrictRec`

## Why these are PURE PROJECTION (not compound)

Despite the name "identity iotas" suggesting motive substitution
(textbook MLTT idJ), the v2 substrate factors the motive/endpoint
work into the PROFILE layer.  At the substrate level, the iota
rule simply DISCARDS the refl witness and returns the base case:

  source spine = [baseCase, refl-wrapper]
  target       = baseCase  (HEAD of the source spine)

That's pure projection — the SIMPLEST iota shape, simpler than
`iotaBoolTrue` (which does `spine.tail.headAtDim0` to skip the
boolTrue head; here we extract the HEAD directly).

Same template as `iotaBoolTrue`/`iotaBoolFalse`/etc.: single
`cases` on the certified cell, single `headAtDim0` on its spine.

## Zero-axiom verification

Both arms close with the identical 4-line tactic block.  No
`simp`, no `omega`, no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

After this commit: 13/18 SR arms shipped.  Remaining: 3 compound
iotas with nested-app + recursive-call construction
(`iotaNatElimSucc`, `iotaNatRecSucc`, `iotaListElimCons`), `beta`
(uses V2-L2.12 subst preservation), and `cong` (structural
induction on the child step + spine recursion).
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaIdJRefl` preserves `HasCertifiedCellDim0`.**

`idJ baseCase (refl rawWitness) ↝ baseCase`.

Pure-projection iota: target is the head of the source's spine.
Identical to `iotaBoolTrue` modulo extracting position 1 (head)
instead of position 2 (tail.head). -/
theorem HasCertifiedCellDim0.preservedByIotaIdJRefl
    {profile : PolyProfile} {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_idJ ()
          (.childCons
            baseCase
            (.childCons
              (.mkGen .gen_refl () (.childCons rawWitness .childNil))
              .childNil))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCase := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      exact .intro .term (outerSpine.headAtDim0 rfl)

/-- **SR arm: `Step.iotaIdStrictRecRefl` preserves `HasCertifiedCellDim0`.**

Symmetric to `preservedByIotaIdJRefl` — same proof template,
different outer generator (`gen_idStrictRec` instead of `gen_idJ`).
The substrate treats both eliminators identically at the
metadata level. -/
theorem HasCertifiedCellDim0.preservedByIotaIdStrictRecRefl
    {profile : PolyProfile} {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_idStrictRec ()
          (.childCons
            baseCase
            (.childCons
              (.mkGen .gen_refl () (.childCons rawWitness .childNil))
              .childNil))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCase := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      exact .intro .term (outerSpine.headAtDim0 rfl)

end FX1Poly.Core
