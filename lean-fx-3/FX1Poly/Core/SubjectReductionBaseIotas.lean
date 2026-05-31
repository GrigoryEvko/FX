import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionBaseIotas — base-case iotas

The SR arms for the base-case branch-selection iotas.

Each base-case eliminator (natElim/natRec on natZero, listElim on
listNil, optionMatch on optionNone) selects the "base" branch from a
3-child same-scope spine.  The proof pattern is identical to
`iotaBoolTrue` (which extracts the then-branch from boolElim's
3-child spine).

## One family, one file

The four arms are STRUCTURALLY INDISTINGUISHABLE at the proof level —
they differ only by which generator's spine they case-analyze:

  * iotaNatElimZero    : natElim natZero    zeroBranch succBranch ↝ zeroBranch
  * iotaNatRecZero     : natRec  natZero    zeroBranch succBranch ↝ zeroBranch
  * iotaListElimNil    : listElim listNil   nilBranch  consBranch ↝ nilBranch
  * iotaOptionMatchNone: optionMatch optionNone noneBranch someBranch ↝ noneBranch

Each: 3-child same-scope spine, target = second child.  Proof =
`spine.tail.headAtDim0 rfl`.  Grouping these semantically-similar
lemmas in one file keeps the audit gate organized.

## Zero-axiom verification

All four arms close by identical proof structure.  No `simp`, no
`omega`, no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaNatElimZero` preserves `HasCertifiedCellDim0`.**

`natElim natZero zeroBranch succBranch` reduces to `zeroBranch`.
Same 3-child same-scope spine as `iotaBoolTrue`; second child is
the target. -/
theorem HasCertifiedCellDim0.preservedByIotaNatElimZero
    {profile : PolyProfile} {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natElim ()
          (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch
              (.childCons succBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

/-- **SR arm: `Step.iotaNatRecZero` preserves `HasCertifiedCellDim0`.**

`natRec natZero zeroBranch succBranch` reduces to `zeroBranch`.
Identical structure to `iotaNatElimZero` — different generator,
same arity / binderShifts / target position. -/
theorem HasCertifiedCellDim0.preservedByIotaNatRecZero
    {profile : PolyProfile} {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natRec ()
          (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch
              (.childCons succBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

/-- **SR arm: `Step.iotaListElimNil` preserves `HasCertifiedCellDim0`.**

`listElim listNil nilBranch consBranch` reduces to `nilBranch`.
Identical structure to `iotaNatElimZero`. -/
theorem HasCertifiedCellDim0.preservedByIotaListElimNil
    {profile : PolyProfile} {scope : Nat}
    {nilBranch consBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_listElim ()
          (.childCons (.mkGen .gen_listNil () .childNil)
            (.childCons nilBranch
              (.childCons consBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) nilBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

/-- **SR arm: `Step.iotaOptionMatchNone` preserves `HasCertifiedCellDim0`.**

`optionMatch optionNone noneBranch someBranch` reduces to
`noneBranch`.  Identical structure to `iotaNatElimZero`. -/
theorem HasCertifiedCellDim0.preservedByIotaOptionMatchNone
    {profile : PolyProfile} {scope : Nat}
    {noneBranch someBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_optionMatch ()
          (.childCons (.mkGen .gen_optionNone () .childNil)
            (.childCons noneBranch
              (.childCons someBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) noneBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

end FX1Poly.Core
