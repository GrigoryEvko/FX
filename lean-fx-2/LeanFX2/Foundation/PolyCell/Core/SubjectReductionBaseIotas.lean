import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionBaseIotas — base-case iotas

V2-L3.1 phase D step 7 (2026-05-27).  Ships SR arms 3-6: the
remaining base-case branch-selection iotas.

Each base-case eliminator (natElim/natRec on natZero, listElim on
listNil, optionMatch on optionNone) selects the "base" branch from a
3-child same-scope spine.  The proof pattern is identical to
`iotaBoolTrue` (which extracts the then-branch from boolElim's
3-child spine).

## Family ships in one commit

The four arms shipped here are STRUCTURALLY INDISTINGUISHABLE at
the proof level — they differ only by which generator's spine they
case-analyze:

  * iotaNatElimZero    : natElim natZero    zeroBranch succBranch ↝ zeroBranch
  * iotaNatRecZero     : natRec  natZero    zeroBranch succBranch ↝ zeroBranch
  * iotaListElimNil    : listElim listNil   nilBranch  consBranch ↝ nilBranch
  * iotaOptionMatchNone: optionMatch optionNone noneBranch someBranch ↝ noneBranch

Each: 3-child same-scope spine, target = second child.  Proof =
`spine.tail.headAtDim0 rfl`.  Shipping them together demonstrates
the template's broad applicability and groups semantically-similar
lemmas in one file (cleaner audit-gate organization).

## Total SR arm progress

After this commit: 6/18 SR arms shipped.

  * Pure projection iotas (base-case, 3-child spine, 2nd-child
    target):           **5/5 done** (iotaBoolTrue + this commit's
                       4 arms).
  * Pure projection iotas (base-case, 3-child spine, 3rd-child
    target):           1/1 done (iotaBoolFalse).
  * Nested projection iotas (fst/snd/either-match-inl/inr):
                       0/4 — pending (need nested cases on the
                       wrapped raw cell's spine).
  * Compound iotas (natElim/natRec/listElim/optionMatch on
    successor/cons/some):
                       0/4 — pending (need to build a `gen_app`
                       term after extraction via PolyCell.gen
                       constructor).
  * Identity iotas (idJ/idStrictRec on refl):
                       0/2 — pending (similar to compound iotas,
                       but with motive substitution that may
                       require subst preservation).
  * Beta:              0/1 — pending (the heaviest arm; uses
                       V2-L2.12 substitution preservation).
  * Cong:              0/1 — pending (the only arm requiring
                       structural induction on a sub-Step + spine
                       recursion).

## Zero-axiom verification

All four arms close by identical proof structure.  No `simp`, no
`omega`, no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

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

end LeanFX2.Foundation.PolyCell.Core
