import FX1Poly.Typed.Ledger.Cell.CellConstructors
import FX1Poly.Typed.Ledger.Cell.CellSubstitution
import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Metatheory.Canonicity.Core.NatElimComputingCanonicity
import FX1Poly.Typed.Metatheory.Canonicity.Core.ListElimComputingCanonicity
import FX1Poly.Typed.Corpus.Faithfulness.RecursorHostFold
import FX1Poly.Typed.Ledger.Cell.ListElimDependentConsType
import FX1Poly.Tier0.Term.Subst.RawTermSubst0Commute

/-! # FX1Poly/Typed/UnionCellSubstitution — how `RawTerm.subst` acts on the native-union cells

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
`native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditUnionSubstitution.lean`. -/

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
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken sourceTerm)
      = RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
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
        (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
          (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken sourceTerm))
      = RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
          (RawTerm.rename FX1Poly.Tier0.Syntax.RawRenaming.weaken
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

/-- **Substitution naturality of the DEPENDENT `listElim` cons-branch TYPE** (DEP-LIST sub-D2a) — the wrapped
(`piTyCodeCell`-level) form the dependent `listElim` rule's `HasTypeUnion.substRespectingContext` arm consumes,
the dependent twin of `subst_listStepFunctionType`.  Unlike the non-dependent step type (whose inner Πs are
`weaken`-wrapped, constant in the binders), the dependent cons branch's inner pieces are motive re-basings, so
the three `piTyCodeCell` peels feed the cons-branch codomain (`lift³`) and the recursive-result binder type
(`lift²`) their own naturality lemmas; the `List A` domain re-bases via `subst_listTypeCell` +
`subst_iterateLift_one_weaken_commute`.  The `iterateLiftRaw`-nesting the three peels produce
(`iterateLiftRaw (iterateLiftRaw σ 1) 1 ≡ iterateLiftRaw σ 2`, depth 3 likewise) collapses by `rfl` (structural
`Nat` recursion of `iterateLiftRaw`) so the depth-2 / depth-3 `_iterateLift` lemmas match. -/
theorem subst_listElimDependentConsBranchType_iterateLift {sourceScope targetScope : Nat}
    (motive : RawTerm (sourceScope + 1)) (elementType : RawTerm sourceScope)
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (listElimDependentConsBranchType motive elementType)
      = listElimDependentConsBranchType (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution elementType) := by
  unfold listElimDependentConsBranchType
  rw [subst_piTyCodeCell, subst_piTyCodeCell, subst_listTypeCell,
    subst_iterateLift_one_weaken_commute, subst_piTyCodeCell,
    show iterateLiftRaw (iterateLiftRaw (iterateLiftRaw substitution 1) 1) 1
        = iterateLiftRaw substitution 3 from rfl,
    show iterateLiftRaw (iterateLiftRaw substitution 1) 1 = iterateLiftRaw substitution 2 from rfl,
    subst_listElimDependentRecBinderType_iterateLift,
    subst_listElimDependentConsBranchCodomain_iterateLift]

/-- The non-dependent function code `piTyCodeCell domain (weaken codomain)` distributes: domain directly,
codomain weakened then substituted (the lift/weaken naturality square).  The classifier shape of every
option/either match branch. -/
theorem subst_nonDependentArrow {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (domain codomain : RawTerm sourceScope) :
    RawTerm.subst substitution (piTyCodeCell domain (RawTerm.weaken codomain))
      = piTyCodeCell (RawTerm.subst substitution domain)
          (RawTerm.weaken (RawTerm.subst substitution codomain)) := by
  rw [subst_piTyCodeCell, subst_iterateLift_one_weaken_commute]

/-! ## DEP-LIST sub-D2b: the cons-branch APP-SPINE output-type reshapings

The dependent `listElim` cons-ι reduct `app (app (app consBranch head) tail) (listElim … tail)` is a
THREE-application spine over `consBranch : (head : A) → (tail : List A) → (rec : motive tail) →
motive (cons head tail)`.  Each application's natural output type is the consumed Π's codomain at the
argument (`unionAppCellTyped` lands `subst0 codomain argument`).  The two intermediate types and three
collapse lemmas below compute those codomains so the spine types at `subst0 motive (cons head tail)` —
the dependent eliminator's output.  `subst_piTyCodeCell` / `subst_listTypeCell` compute the Π / `List`
spine DEFINITIONALLY; the only propositional steps are the `weaken`-domain collapse
(`weaken_subst_singleton`), the recursive-result-binder collapse to `motive tail`, and the codomain
collapse to `motive (cons head tail)` (the shipped `…_consIota`). -/

/-- The dependent cons branch's type after the `head` argument is consumed:
    `(tail : List A) → (rec : motive tail) → motive (cons head tail)` — `subst0`-at-`head` of the cons
    branch's outer-Π codomain (the `List (weaken A)` domain strips to `List A`). -/
def listElimDependentConsTypeAfterHead {scope : Nat} (motive : RawTerm (scope + 1))
    (elementType headValue : RawTerm scope) : RawTerm scope :=
  piTyCodeCell (listTypeCell elementType)
    (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton headValue))
      (piTyCodeCell (listElimDependentRecBinderType motive)
        (listElimDependentConsBranchCodomain motive)))

/-- The dependent cons branch's type after the `head` and `tail` arguments are consumed:
    `(rec : motive tail) → motive (cons head tail)` — the recursive-result binder's domain is
    `motive tail` (`subst0 motive tail`), its codomain the cons codomain re-based under both fillings. -/
def listElimDependentConsTypeAfterHeadTail {scope : Nat} (motive : RawTerm (scope + 1))
    (headValue tailList : RawTerm scope) : RawTerm scope :=
  piTyCodeCell (RawTerm.subst0 motive tailList)
    (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton tailList))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton headValue)))
        (listElimDependentConsBranchCodomain motive)))

/-- **App-1 reshaping.**  Substituting `head` into the cons branch's outer-Π codomain reaches the
    `listElimDependentConsTypeAfterHead` form: `subst_piTyCodeCell` / `subst_listTypeCell` compute the
    spine, the `List (weaken A)` domain collapses to `List A` via `weaken_subst_singleton`. -/
theorem subst0_listElimConsBranchOuterCodomain_afterHead {scope : Nat}
    (motive : RawTerm (scope + 1)) (elementType headValue : RawTerm scope) :
    RawTerm.subst0
        (piTyCodeCell (listTypeCell (RawTerm.weaken elementType))
          (piTyCodeCell (listElimDependentRecBinderType motive)
            (listElimDependentConsBranchCodomain motive)))
        headValue
      = listElimDependentConsTypeAfterHead motive elementType headValue := by
  unfold listElimDependentConsTypeAfterHead RawTerm.subst0
  rw [subst_piTyCodeCell, subst_listTypeCell, RawTerm.weaken_subst_singleton]
  rfl

/-- **The recursive-result binder collapse.**  Filling the cons branch's `head` then `tail` binders carries
    the recursive-result binder's type `listElimDependentRecBinderType motive` (the re-based `motive tail`)
    to `subst0 motive tail` — the type at which the recursive `listElim` call is union-typed.  The composite
    of the rec-binder re-basing, the head lift, and the tail singleton is the `subst0`-at-`tail`
    substitution (two-arm `Fin` match: `subst_compose` twice, the per-position arms `rfl`). -/
theorem subst0_subst_lift_singleton_listElimDependentRecBinderType {scope : Nat}
    (motive : RawTerm (scope + 1)) (headValue tailList : RawTerm scope) :
    RawTerm.subst0
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton headValue))
          (listElimDependentRecBinderType motive))
        tailList
      = RawTerm.subst0 motive tailList := by
  unfold listElimDependentRecBinderType RawTerm.subst0
  rw [RawTerm.subst_compose, RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ priorValue => rfl

/-- **App-2 reshaping.**  Substituting `tail` into the after-`head` type's codomain reaches the
    `listElimDependentConsTypeAfterHeadTail` form: the recursive-result binder domain collapses to
    `motive tail` (`subst0_subst_lift_singleton_listElimDependentRecBinderType`), the codomain rides the
    nested `lift`s definitionally. -/
theorem subst0_listElimConsTypeAfterHead_afterHeadTail {scope : Nat}
    (motive : RawTerm (scope + 1)) (headValue tailList : RawTerm scope) :
    RawTerm.subst0
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton headValue))
          (piTyCodeCell (listElimDependentRecBinderType motive)
            (listElimDependentConsBranchCodomain motive)))
        tailList
      = listElimDependentConsTypeAfterHeadTail motive headValue tailList := by
  unfold listElimDependentConsTypeAfterHeadTail
  rw [subst_piTyCodeCell, RawTerm.subst0,
    show RawTerm.subst (RawTermSubst.singleton tailList)
        (piTyCodeCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton headValue))
          (listElimDependentRecBinderType motive))
          (RawTerm.subst (iterateLiftRaw (RawTermSubst.lift (RawTermSubst.singleton headValue)) 1)
            (listElimDependentConsBranchCodomain motive)))
        = piTyCodeCell
            (RawTerm.subst (RawTermSubst.singleton tailList)
              (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton headValue))
                (listElimDependentRecBinderType motive)))
            (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton tailList))
              (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton headValue)))
                (listElimDependentConsBranchCodomain motive))) from rfl]
  rw [← RawTerm.subst0, subst0_subst_lift_singleton_listElimDependentRecBinderType]

/-- **App-3 reshaping (the cons-ι output collapse).**  Substituting the recursive call into the
    after-`head`-`tail` type's codomain reaches the eliminator's output type `subst0 motive (cons head tail)`
    — the recursive call is irrelevant to the type, and the three filled binders carry the cons codomain to
    `motive (cons head tail)` (the shipped `subst_listElimDependentConsBranchCodomain_consIota`).  Routed by
    pinning the composite three-fold substitution to `cons recCall (cons tail (singleton head))`. -/
theorem subst0_listElimConsTypeAfterHeadTailCodomain_consIota {scope : Nat}
    (motive : RawTerm (scope + 1)) (headValue tailList recursiveValue : RawTerm scope) :
    RawTerm.subst0
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton tailList))
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton headValue)))
            (listElimDependentConsBranchCodomain motive)))
        recursiveValue
      = RawTerm.subst0 motive (listConsCell headValue tailList) := by
  rw [← subst_listElimDependentConsBranchCodomain_consIota motive recursiveValue tailList headValue]
  unfold RawTerm.subst0
  -- Merge the three substitutions left-to-right (head lift first, then tail lift, then the rec singleton)
  -- so each binder is filled by a `subst (lift _) (weaken _)` / `subst (singleton _) (weaken _)` cancellation.
  rw [RawTerm.subst_compose (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton headValue)))
        (RawTermSubst.lift (RawTermSubst.singleton tailList))
        (listElimDependentConsBranchCodomain motive),
    RawTerm.subst_compose
        (RawTermSubst.compose (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton headValue)))
          (RawTermSubst.lift (RawTermSubst.singleton tailList)))
        (RawTermSubst.singleton recursiveValue) (listElimDependentConsBranchCodomain motive)]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ firstPrior => cases firstPrior with
      | zero =>
          -- position 1 ↦ tail: head-lift sends `var 0` to `weaken (var 0)`, the tail-lift cancels one
          -- weakening leaving `weaken tail`, the rec-singleton cancels it to `tail`.
          dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons, RawTermSubst.singleton]
          rw [RawTerm.subst_lift_weaken, RawTerm.weaken_subst_singleton]
          rfl
      | succ secondPrior => cases secondPrior with
        | zero =>
            -- position 2 ↦ head: head-lift sends `var 0` to `weaken (weaken head)`, the tail-lift cancels
            -- one weakening (`subst_lift_singleton_weaken_weaken`), the rec-singleton cancels the other.
            dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons, RawTermSubst.singleton]
            rw [RawTerm.subst_lift_singleton_weaken_weaken, RawTerm.weaken_subst_singleton]
        | succ deepPrior =>
            -- position k+3 ↦ var k: every binder weakens the ambient variable, each lift/singleton cancels.
            dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons, RawTermSubst.singleton]
            rw [RawTerm.subst_lift_singleton_weaken_weaken, RawTerm.weaken_subst_singleton]

end FX1Poly.Typed
