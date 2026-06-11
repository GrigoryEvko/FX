import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionBaseIotas — base-case iotas

The SR arms for the base-case branch-selection iotas.

The base-case eliminators split into two spine shapes.  natElim/natRec
on natZero and listElim on listNil now carry the Phase-Z 4-child motive
shape (`binderShifts [1, 0, 2, 0]` for nat, `[1, 0, 0, 0]` for list):
children are `(motive, zeroBranch, succBranch, scrutinee)` with the
motive a term under one binder and the scrutinee LAST; the base-case
iota DISCARDS the motive and projects the zero/nil-branch which sits at
spine position 1 — extracted via `spine.tail.headAtDim0 rfl` (the tail
drops the motive head, leaving the branch at the head of the tail).
optionMatch on optionNone now carries the same Phase-Z 4-child motive
shape (`binderShifts [1, 0, 0, 0]`), children `(motive, noneBranch,
someBranch, scrutinee)` with the scrutinee LAST; noneBranch sits at
spine position 1 and is projected identically.  The proof pattern is
the pure-projection iota template shared with `iotaBoolTrue`.

## One family, one file

The four arms are STRUCTURALLY INDISTINGUISHABLE at the proof level —
they differ only by which generator's spine they case-analyze:

  * iotaNatElimZero    : natElim motive zeroBranch succBranch natZero ↝ zeroBranch
  * iotaNatRecZero     : natRec  motive zeroBranch succBranch natZero ↝ zeroBranch
  * iotaListElimNil    : listElim motive nilBranch consBranch listNil ↝ nilBranch
  * iotaOptionMatchNone: optionMatch motive noneBranch someBranch optionNone ↝ noneBranch

Each: target = the branch at spine position 1.  Proof =
`spine.tail.headAtDim0 rfl`.  Grouping these semantically-similar
lemmas in one file keeps the audit gate organized.

## Zero-axiom verification

All four arms close by identical proof structure.  No `simp`, no
`omega`, no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaNatElimZero` preserves `HasCertifiedCellDim0`.**

`natElim motive zeroBranch succBranch natZero` reduces to `zeroBranch`.
Phase-Z motive shape: motive heads the spine (shift 1), succBranch sits
under TWO binders (`scope + 2`), scrutinee LAST; zeroBranch stays at
spine position 1, projected via `spine.tail.headAtDim0 rfl`.  Identical
structure to `iotaListElimNil` modulo the leading motive head. -/
theorem HasCertifiedCellDim0.preservedByIotaNatElimZero
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

/-- **SR arm: `Step.iotaNatRecZero` preserves `HasCertifiedCellDim0`.**

`natRec motive zeroBranch succBranch natZero` reduces to `zeroBranch`.
Identical structure to `iotaNatElimZero` — different generator,
same arity / binderShifts / target position. -/
theorem HasCertifiedCellDim0.preservedByIotaNatRecZero
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

/-- **SR arm: `Step.iotaListElimNil` preserves `HasCertifiedCellDim0`.**

`listElim motive nilBranch consBranch listNil` reduces to `nilBranch`.
Phase-Z motive shape: motive heads the spine (shift 1), scrutinee LAST;
nilBranch stays at spine position 1, projected via `spine.tail.headAtDim0`.
Identical structure to `iotaNatElimZero` modulo the leading motive head. -/
theorem HasCertifiedCellDim0.preservedByIotaListElimNil
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {nilBranch consBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch
                (.childCons (.mkGen .gen_listNil () .childNil) .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) nilBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

/-- **SR arm: `Step.iotaOptionMatchNone` preserves `HasCertifiedCellDim0`.**

`optionMatch motive noneBranch someBranch optionNone` reduces to
`noneBranch`.  Phase-Z motive shape: motive heads the spine (shift 1),
scrutinee LAST; noneBranch stays at spine position 1, projected via
`spine.tail.headAtDim0 rfl`.  Identical structure to `iotaNatElimZero`. -/
theorem HasCertifiedCellDim0.preservedByIotaOptionMatchNone
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {noneBranch someBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch
                (.childCons (.mkGen .gen_optionNone () .childNil) .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) noneBranch := by
  cases sourceCert with
  | intro sort sourceCell =>
    cases sourceCell with
    | gen _ _ spine =>
      exact .intro .term ((spine.tail).headAtDim0 rfl)

end FX1Poly.Core
