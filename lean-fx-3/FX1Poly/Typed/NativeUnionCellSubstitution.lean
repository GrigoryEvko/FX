import FX1Poly.Typed.CellConstructors
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Typed.NativeUnionRuleTables
import FX1Poly.Typed.NatElimComputingCanonicity
import FX1Poly.Typed.ListElimComputingCanonicity
import FX1Poly.Typed.RecursorHostFold

/-! # FX1Poly/Typed/NativeUnionCellSubstitution — how `RawTerm.subst` acts on the native-union cells

The native-union substitution lemma (NATIVE-37 part b) reassembles each arm's substituted subject and
classifier from the substituted children.  The arms' member cells and rule outputs are all `mkGen`
spines built from the typing cells; `RawTerm.subst` distributes over them DEFINITIONALLY (the cell is a
`mkGen`, `subst` is a `fold` that rebuilds the same cell at the substituted children, threading
`iterateLiftRaw substitution depth` at each binder-shifted child).  Every commutation below is `rfl`,
mirroring the shipped `subst_lamCell` / `subst_piTyCodeCell`.

The closed nullary type/value codes (`natTypeCell`, `boolTypeCell`, `listTypeCell elementType`, …) are
substitution-INVARIANT only when CLOSED (no free vars); the parameterized container codes thread the
substitution over their type parameters (`subst_listTypeCell` / `subst_optionTypeCell` / …).  The fully
closed nullary leaves (`natTypeCell` / `natZeroCell` / `listNilCell` / `optionNoneCell`) are `rfl`
identities.

## Zero-axiom

Every theorem closes by `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditNativeUnionSubstitution.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Closed nullary type/value leaves — substitution-invariant (`rfl`) -/

/-- `Nat` code is substitution-invariant (closed nullary leaf). -/
theorem subst_natTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (natTypeCell : RawTerm sourceScope) = natTypeCell := rfl

/-- `natZero` is substitution-invariant. -/
theorem subst_natZeroCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (natZeroCell : RawTerm sourceScope) = natZeroCell := rfl

/-- `Bool` code is substitution-invariant. -/
theorem subst_boolTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (boolTypeCell : RawTerm sourceScope) = boolTypeCell := rfl

/-- `listNil` is substitution-invariant. -/
theorem subst_listNilCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (listNilCell : RawTerm sourceScope) = listNilCell := rfl

/-- `optionNone` is substitution-invariant. -/
theorem subst_optionNoneCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (optionNoneCell : RawTerm sourceScope) = optionNoneCell := rfl

/-! ## Parameterized container codes — substitution threads over the type parameters (`rfl`) -/

/-- `list(A)` code distributes the substitution over the element type. -/
theorem subst_listTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (elementType : RawTerm sourceScope) :
    RawTerm.subst substitution (listTypeCell elementType)
      = listTypeCell (RawTerm.subst substitution elementType) := rfl

/-- `option(A)` code distributes over the element type. -/
theorem subst_optionTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (elementType : RawTerm sourceScope) :
    RawTerm.subst substitution (optionTypeCell elementType)
      = optionTypeCell (RawTerm.subst substitution elementType) := rfl

/-- `either(A, B)` code distributes over both type params. -/
theorem subst_eitherTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (leftType rightType : RawTerm sourceScope) :
    RawTerm.subst substitution (eitherTypeCell leftType rightType)
      = eitherTypeCell (RawTerm.subst substitution leftType)
          (RawTerm.subst substitution rightType) := rfl

/-- `A × B` product code distributes over both type params. -/
theorem subst_productTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (firstType secondType : RawTerm sourceScope) :
    RawTerm.subst substitution (productTypeCell firstType secondType)
      = productTypeCell (RawTerm.subst substitution firstType)
          (RawTerm.subst substitution secondType) := rfl

/-- `Id(A, x, y)` code distributes over the type code and both endpoints. -/
theorem subst_idTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (typeCode left right : RawTerm sourceScope) :
    RawTerm.subst substitution (idTypeCell typeCode left right)
      = idTypeCell (RawTerm.subst substitution typeCode) (RawTerm.subst substitution left)
          (RawTerm.subst substitution right) := rfl

/-- The bridge type code distributes over the carrier and both endpoints. -/
theorem subst_bridgeTypeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (typeCode left right : RawTerm sourceScope) :
    RawTerm.subst substitution (bridgeTypeCell typeCode left right)
      = bridgeTypeCell (RawTerm.subst substitution typeCode) (RawTerm.subst substitution left)
          (RawTerm.subst substitution right) := rfl

/-! ## Value / introduction cells -/

/-- `natSucc(p)` distributes over the predecessor. -/
theorem subst_natSuccCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (predecessor : RawTerm sourceScope) :
    RawTerm.subst substitution (natSuccCell predecessor)
      = natSuccCell (RawTerm.subst substitution predecessor) := rfl

/-- `listCons(head, tail)` distributes over both children. -/
theorem subst_listConsCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (headValue tailList : RawTerm sourceScope) :
    RawTerm.subst substitution (listConsCell headValue tailList)
      = listConsCell (RawTerm.subst substitution headValue)
          (RawTerm.subst substitution tailList) := rfl

/-- `optionSome(v)` distributes over the value. -/
theorem subst_optionSomeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (value : RawTerm sourceScope) :
    RawTerm.subst substitution (optionSomeCell value)
      = optionSomeCell (RawTerm.subst substitution value) := rfl

/-- `eitherInl(v)` distributes over the value. -/
theorem subst_eitherInlCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (value : RawTerm sourceScope) :
    RawTerm.subst substitution (eitherInlCell value)
      = eitherInlCell (RawTerm.subst substitution value) := rfl

/-- `eitherInr(v)` distributes over the value. -/
theorem subst_eitherInrCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (value : RawTerm sourceScope) :
    RawTerm.subst substitution (eitherInrCell value)
      = eitherInrCell (RawTerm.subst substitution value) := rfl

/-- `pair(x, y)` distributes over both children. -/
theorem subst_pairCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (firstValue secondValue : RawTerm sourceScope) :
    RawTerm.subst substitution (pairCell firstValue secondValue)
      = pairCell (RawTerm.subst substitution firstValue)
          (RawTerm.subst substitution secondValue) := rfl

/-- `refl(w)` distributes over the witness. -/
theorem subst_reflCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (witness : RawTerm sourceScope) :
    RawTerm.subst substitution (reflCell witness)
      = reflCell (RawTerm.subst substitution witness) := rfl

/-! ## Eliminator cells — motives thread one or two lifts, branches at shift 0 -/

/-- `natElim` distributes: motive under one lift, succ-branch under two, the rest directly. -/
theorem subst_natElimCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (zeroBranch : RawTerm sourceScope)
    (succBranch : RawTerm (sourceScope + 2)) (scrutinee : RawTerm sourceScope) :
    RawTerm.subst substitution (natElimCell motive zeroBranch succBranch scrutinee)
      = natElimCell (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution zeroBranch)
          (RawTerm.subst (iterateLiftRaw substitution 2) succBranch)
          (RawTerm.subst substitution scrutinee) := rfl

/-- `natRec` distributes: motive under one lift, succ-branch under two, the rest directly. -/
theorem subst_natRecCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (zeroBranch : RawTerm sourceScope)
    (succBranch : RawTerm (sourceScope + 2)) (scrutinee : RawTerm sourceScope) :
    RawTerm.subst substitution (natRecCell motive zeroBranch succBranch scrutinee)
      = natRecCell (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution zeroBranch)
          (RawTerm.subst (iterateLiftRaw substitution 2) succBranch)
          (RawTerm.subst substitution scrutinee) := rfl

/-- `boolElim` distributes: motive under one lift, scrutinee/branches directly. -/
theorem subst_boolElimCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (scrutinee thenBranch elseBranch : RawTerm sourceScope) :
    RawTerm.subst substitution (boolElimCell motive scrutinee thenBranch elseBranch)
      = boolElimCell (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution thenBranch)
          (RawTerm.subst substitution elseBranch) := rfl

/-- `optionMatch` distributes: motive under one lift, the rest directly. -/
theorem subst_optionMatchCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (noneBranch someBranch scrutinee : RawTerm sourceScope) :
    RawTerm.subst substitution (optionMatchCell motive noneBranch someBranch scrutinee)
      = optionMatchCell (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution noneBranch) (RawTerm.subst substitution someBranch)
          (RawTerm.subst substitution scrutinee) := rfl

/-- `eitherMatch` distributes: motive under one lift, the rest directly. -/
theorem subst_eitherMatchCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (leftBranch rightBranch scrutinee : RawTerm sourceScope) :
    RawTerm.subst substitution (eitherMatchCell motive leftBranch rightBranch scrutinee)
      = eitherMatchCell (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution leftBranch) (RawTerm.subst substitution rightBranch)
          (RawTerm.subst substitution scrutinee) := rfl

/-- `idJ` distributes: motive under two lifts, base/witness directly. -/
theorem subst_idJCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 2)) (baseCase witness : RawTerm sourceScope) :
    RawTerm.subst substitution (idJCell motive baseCase witness)
      = idJCell (RawTerm.subst (iterateLiftRaw substitution 2) motive)
          (RawTerm.subst substitution baseCase) (RawTerm.subst substitution witness) := rfl

/-- `fst` distributes over the pair term. -/
theorem subst_fstCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (pairTerm : RawTerm sourceScope) :
    RawTerm.subst substitution (fstCell pairTerm)
      = fstCell (RawTerm.subst substitution pairTerm) := rfl

/-- `snd` distributes over the pair term. -/
theorem subst_sndCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (pairTerm : RawTerm sourceScope) :
    RawTerm.subst substitution (sndCell pairTerm)
      = sndCell (RawTerm.subst substitution pairTerm) := rfl

/-- `listElim` distributes: motive under one lift, the rest directly. -/
theorem subst_listElimCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (scrutinee nilBranch consBranch : RawTerm sourceScope) :
    RawTerm.subst substitution (listElimCell motive scrutinee nilBranch consBranch)
      = listElimCell (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution scrutinee) (RawTerm.subst substitution nilBranch)
          (RawTerm.subst substitution consBranch) := rfl

/-! ## Bridge cells -/

/-- `pathLam(body)` distributes: body under one lift. -/
theorem subst_pathLamCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (body : RawTerm (sourceScope + 1)) :
    RawTerm.subst substitution (pathLamCell body)
      = pathLamCell (RawTerm.subst (iterateLiftRaw substitution 1) body) := rfl

/-- `pathApp(path, argument)` distributes over both children. -/
theorem subst_pathAppCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (path argument : RawTerm sourceScope) :
    RawTerm.subst substitution (pathAppCell path argument)
      = pathAppCell (RawTerm.subst substitution path)
          (RawTerm.subst substitution argument) := rfl

/-! ## The composite step-function type (listElim cons branch classifier) -/

/-- The lift/weaken naturality square in the `iterateLiftRaw _ 1` presentation (≡ `RawTermSubst.lift`)
and the `RawTerm.weaken` presentation (≡ `rename RawRenaming.weaken`) — both sides defeq to
`subst_lift_weaken_commute`, restated so the listStepFunctionType chain rewrites without `simp` (propext
-clean). -/
theorem subst_iterateLift_one_weaken_commute {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst (iterateLiftRaw substitution 1) (RawTerm.weaken sourceTerm)
      = RawTerm.weaken (RawTerm.subst substitution sourceTerm) :=
  subst_lift_weaken_commute substitution sourceTerm

/-- The one-level lift/weaken naturality square in the EXPLICIT `rename RawRenaming.weaken` presentation
(rather than the `RawTerm.weaken` abbreviation), so `rw` matches the recursiveElim step-branch context
binding `subst (iterateLiftRaw σ 1) (rename weaken resultType)` without unfolding `RawTerm.weaken`. -/
theorem subst_iterateLift_one_renameWeaken_commute {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst (iterateLiftRaw substitution 1)
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken sourceTerm)
      = RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
          (RawTerm.subst substitution sourceTerm) :=
  subst_lift_weaken_commute substitution sourceTerm

/-- The TWICE-iterated lift/weaken naturality square (the recursive-eliminator step-branch classifier
shape).  `subst (iterateLiftRaw σ 2) (weaken (weaken X)) = weaken (weaken (subst σ X))` — two composed
applications of the one-level square, with `iterateLiftRaw σ 2` defeq to `lift (lift σ)` so the outer
square runs at `iterateLiftRaw σ 1` and the inner at `σ`.  Used to retype the recursiveElim arm's
twice-weakened result-type step-branch classifier after substitution. -/
theorem subst_iterateLift_two_weaken_weaken_commute {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst (iterateLiftRaw substitution 2)
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
          (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken sourceTerm))
      = RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
          (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
            (RawTerm.subst substitution sourceTerm)) := by
  show RawTerm.subst (iterateLiftRaw (iterateLiftRaw substitution 1) 1)
      (RawTerm.weaken (RawTerm.weaken sourceTerm))
    = RawTerm.weaken (RawTerm.weaken (RawTerm.subst substitution sourceTerm))
  rw [subst_iterateLift_one_weaken_commute (iterateLiftRaw substitution 1)
        (RawTerm.weaken sourceTerm),
    subst_iterateLift_one_weaken_commute substitution sourceTerm]

/-- `listStepFunctionType` distributes over both type params: built from `piTyCodeCell` /
`listTypeCell` / `weaken` spines, the substitution threads through.  Proved by `rw` of the per-cell
commutations + the lift/weaken naturality square (no `simp`, propext-clean). -/
theorem subst_listStepFunctionType {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (elementType resultType : RawTerm sourceScope) :
    RawTerm.subst substitution (listStepFunctionType elementType resultType)
      = listStepFunctionType (RawTerm.subst substitution elementType)
          (RawTerm.subst substitution resultType) := by
  show RawTerm.subst substitution
      (piTyCodeCell elementType
        (RawTerm.weaken (piTyCodeCell (listTypeCell elementType)
          (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType))))))
    = piTyCodeCell (RawTerm.subst substitution elementType)
        (RawTerm.weaken (piTyCodeCell (listTypeCell (RawTerm.subst substitution elementType))
          (RawTerm.weaken (piTyCodeCell (RawTerm.subst substitution resultType)
            (RawTerm.weaken (RawTerm.subst substitution resultType))))))
  rw [subst_piTyCodeCell, subst_iterateLift_one_weaken_commute, subst_piTyCodeCell,
    subst_listTypeCell, subst_iterateLift_one_weaken_commute, subst_piTyCodeCell,
    subst_iterateLift_one_weaken_commute]

/-- The non-dependent function code `piTyCodeCell domain (weaken codomain)` distributes: domain directly,
codomain weakened then substituted (the lift/weaken naturality square).  The classifier shape of every
option/either match branch. -/
theorem subst_nonDependentArrow {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (domain codomain : RawTerm sourceScope) :
    RawTerm.subst substitution (piTyCodeCell domain (RawTerm.weaken codomain))
      = piTyCodeCell (RawTerm.subst substitution domain)
          (RawTerm.weaken (RawTerm.subst substitution codomain)) := by
  rw [subst_piTyCodeCell, subst_iterateLift_one_weaken_commute]

end FX1Poly.Typed
