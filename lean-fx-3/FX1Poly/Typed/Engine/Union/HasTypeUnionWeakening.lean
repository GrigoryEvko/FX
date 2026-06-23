import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Cell.UnionCellSubstitution
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiWeakening
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubst

/-! # FX1Poly/Typed/HasTypeUnionWeakening — the RENAMING / WEAKENING lemma for the 5-arm native
    union (the de-Bruijn-insertion twin of `HasTypeUnion.substRespectingContext`)

The grown engine ships `HasTypeDescPi.renameRespectingContext` (its cartesian-lift fibration leg); the
unified judgment `HasTypeUnion` must too.  This file supplies that missing union-metatheory
primitive — `HasTypeUnion` is preserved along ANY renaming respecting the context — the structural
mirror of the union substitution lemma with a RENAMING in place of the substitution.

## The renaming-respects-context discipline (the formation engine's EQUALITY carrier)

`renameRespectingContext` is preserved along any renaming whose looked-up image equals the target's
looked-up binding (`RawTerm.rename rawRenaming (sourceContext.lookup index) = targetContext.lookup
(rawRenaming index)`).  This is the IDENTICAL carrier the grown twin
`HasTypeDescPi.renameRespectingContext` uses, so every engine-embedding arm composes verbatim.

## How the 5 arms discharge (the post-TYTAB-1-collapse arm set)

  * The SOLE ENGINE EMBEDDING (`ofGrown`) routes its host premise through the grown engine's own
    `renameRespectingContext` and re-embeds.
  * The TABLE-DRIVEN `formationRule` arm renames its premise telescope via the flat / term-indexed
    telescope `renameRespectingContext` helpers and reconstructs the abstract cell via
    `RawTerm.rename_mkGen_of_ne_var`.  (The six zoo intro embeddings, plus the base-type / data-intro /
    flat / term-indexed-former STANDALONE ENGINES, were RETIRED — NATIVE-42 the intro zoo, NATIVE-36/44
    the base-type/data-intro/flat engines into table arms, TABLE-CANON-6 the term-indexed-former engine —
    every data value and code now enters through its native table row.)
  * ★ The UNIFIED `intro` arm (the TYTAB-1 intro collapse — all FOUR introducer families in ONE:
    nullary constructors `boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` / `natZero`, graded
    binders `lam` / `pathLam`, recursive constructors `natSucc` / `listCons`, grown constructors
    `optionSome` / `optionNone` / `listNil` / `eitherInl` / `eitherInr` / `pair` / `refl`) carries its
    premises as a single `∀ obligation ∈ rule.obligations …` list with one induction hypothesis
    `ihPremises`, plus a `sideHolds : rule.sideCondition …`.  The case `rcases introRuleOf_cases` to the
    concrete row (17-way) + matches the `args` / `params` children, after which `rule.memberCell` /
    `rule.outputType` / `rule.obligations` / `rule.sideCondition` reduce to concrete cells.  Per row the
    member cell and output rename through their per-cell `rfl` commutations (`pathLam`'s bridge output
    threads `RawTerm.rename_subst0_commute`); the `sideCondition` is `trivial` for the data constructors
    and `gradedBinderChecks_rename_lift` for the graded binders (a lifted renaming preserves the
    freshest-binder occurrence count, so the usage bound survives verbatim); and each obligation typing is
    `ihPremises _ <List.Mem position> <renamed target>`, reshaped per row (`rename_universeCodeCell` for
    the formedness premises, `rename_listTypeCell` for the `listCons` tail, the per-container cell
    commutations for the others).  The `lam` codomain / body and the `pathLam` body premises live at
    `scope + 1`, so their obligation renaming lifts once (`iterateLiftRaw rawRenaming 1`) via
    `renameContextCondition_cons`, and the `pathLam` body classifier carries a `RawTerm.weaken` layer
    reshaped by `rename_iterateLift_one_weaken_commute`.
  * ★ The UNIFIED `elim` arm (the TYTAB-1 elim collapse — `app` / `pathApp` / `natElim` / `natRec` /
    `boolElim` / `optionMatch` / `eitherMatch` / `idJ` / `fst` / `snd` / `listElim` in ONE) carries its
    premises as a single `∀ obligation ∈ rule.obligations …` list with one induction hypothesis
    `ihPremises` ranging over that list.  The case `rcases elimRuleOf_cases` to the concrete row + matches
    the `args` / `params` children, after which `rule.memberCell` / `rule.outputType` / `rule.obligations`
    all reduce to concrete cells: the member cell and output rename through their per-cell `rfl`
    commutations (`app`'s output threads `RawTerm.rename_subst0_commute`), and each obligation typing is
    `ihPremises _ <List.Mem position> <renamed target>`, reshaped per row (`rename_piTyCodeCell` for the
    function premise, `rename_nonDependentArrow` for the option/either handlers, `rename_idTypeCell` for the
    `idJ` witness, the per-container cell commutations for the scrutinees).  The `natElim` / `natRec` step
    branch lives at TWO binders, so its obligation renaming lifts twice (`iterateLiftRaw rawRenaming 2`)
    via `RenameRespectsContext.consTwice` and the classifier carries two `RawTerm.weaken` layers reshaped
    by `rename_iterateLift_two_weakenAbbrev_commute`.
  * The CONV arm recurses both premises, transports the conversion through `Conv.rename`, and
    re-applies the conv arm — the `universeCodeCell` reclassifier renames to itself
    (`rename_universeCodeCell`).

## Zero-axiom

`renameRespectingContext` is `induction` over the 5 arms + the cell-rename `rfl` commutations + the
per-rule `rename_subst0_commute` reshapes + the lifted-occurrence preservation + the engine rename
lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditUnionWeakening.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-! ## Cell-rename commutations — the rename twins of the `subst_*Cell` lemmas (all `rfl`) -/

/-- `Nat` code is renaming-invariant (closed nullary leaf). -/
theorem rename_natTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (natTypeCell : RawTerm sourceScope) = natTypeCell := rfl

/-- `natSucc(p)` distributes over the predecessor. -/
theorem rename_natSuccCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (predecessor : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (natSuccCell predecessor)
      = natSuccCell (RawTerm.rename rawRenaming predecessor) := rfl

/-- `listCons(head, tail)` distributes over both children. -/
theorem rename_listConsCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (headValue tailList : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (listConsCell headValue tailList)
      = listConsCell (RawTerm.rename rawRenaming headValue)
          (RawTerm.rename rawRenaming tailList) := rfl

/-- `optionSome(v)` distributes over the value. -/
theorem rename_optionSomeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (value : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (optionSomeCell value)
      = optionSomeCell (RawTerm.rename rawRenaming value) := rfl

/-- `optionNone` is renaming-invariant. -/
theorem rename_optionNoneCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (optionNoneCell : RawTerm sourceScope) = optionNoneCell := rfl

/-- `listNil` is closed — renaming fixes it. -/
theorem rename_listNilCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (listNilCell : RawTerm sourceScope) = listNilCell := rfl

/-- `eitherInl(v)` distributes over the value. -/
theorem rename_eitherInlCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (value : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (eitherInlCell value)
      = eitherInlCell (RawTerm.rename rawRenaming value) := rfl

/-- `eitherInr(v)` distributes over the value. -/
theorem rename_eitherInrCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (value : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (eitherInrCell value)
      = eitherInrCell (RawTerm.rename rawRenaming value) := rfl

/-- `pair(x, y)` distributes over both children. -/
theorem rename_pairCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (firstValue secondValue : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (pairCell firstValue secondValue)
      = pairCell (RawTerm.rename rawRenaming firstValue)
          (RawTerm.rename rawRenaming secondValue) := rfl

/-- `refl(w)` distributes over the witness. -/
theorem rename_reflCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (witness : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (reflCell witness)
      = reflCell (RawTerm.rename rawRenaming witness) := rfl

/-- `list(A)` code distributes over the element type. -/
theorem rename_listTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (elementType : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (listTypeCell elementType)
      = listTypeCell (RawTerm.rename rawRenaming elementType) := rfl

/-- `option(A)` code distributes over the element type. -/
theorem rename_optionTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (elementType : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (optionTypeCell elementType)
      = optionTypeCell (RawTerm.rename rawRenaming elementType) := rfl

/-- `either(A, B)` code distributes over both type params. -/
theorem rename_eitherTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (leftType rightType : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (eitherTypeCell leftType rightType)
      = eitherTypeCell (RawTerm.rename rawRenaming leftType)
          (RawTerm.rename rawRenaming rightType) := rfl

/-- `A × B` product code distributes over both type params. -/
theorem rename_productTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (firstType secondType : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (productTypeCell firstType secondType)
      = productTypeCell (RawTerm.rename rawRenaming firstType)
          (RawTerm.rename rawRenaming secondType) := rfl

/-- `Id(A, x, y)` code distributes over the type code and both endpoints. -/
theorem rename_idTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (typeCode left right : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (idTypeCell typeCode left right)
      = idTypeCell (RawTerm.rename rawRenaming typeCode) (RawTerm.rename rawRenaming left)
          (RawTerm.rename rawRenaming right) := rfl

/-- The bridge type code distributes over the carrier and both endpoints. -/
theorem rename_bridgeTypeCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (typeCode left right : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (bridgeTypeCell typeCode left right)
      = bridgeTypeCell (RawTerm.rename rawRenaming typeCode) (RawTerm.rename rawRenaming left)
          (RawTerm.rename rawRenaming right) := rfl

/-- `natElim` distributes: motive under one lift, succ-branch under two, the rest directly. -/
theorem rename_natElimCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (zeroBranch : RawTerm sourceScope)
    (succBranch : RawTerm (sourceScope + 2)) (scrutinee : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (natElimCell motive zeroBranch succBranch scrutinee)
      = natElimCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming zeroBranch)
          (RawTerm.rename (iterateLiftRaw rawRenaming 2) succBranch)
          (RawTerm.rename rawRenaming scrutinee) := rfl

/-- `natRec` distributes: motive under one lift, succ-branch under two, the rest directly. -/
theorem rename_natRecCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (zeroBranch : RawTerm sourceScope)
    (succBranch : RawTerm (sourceScope + 2)) (scrutinee : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (natRecCell motive zeroBranch succBranch scrutinee)
      = natRecCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming zeroBranch)
          (RawTerm.rename (iterateLiftRaw rawRenaming 2) succBranch)
          (RawTerm.rename rawRenaming scrutinee) := rfl

/-- `boolElim` distributes: motive under one lift, scrutinee/branches directly. -/
theorem rename_boolElimCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (scrutinee thenBranch elseBranch : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (boolElimCell motive scrutinee thenBranch elseBranch)
      = boolElimCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming thenBranch)
          (RawTerm.rename rawRenaming elseBranch) := rfl

/-- `optionMatch` distributes: motive under one lift, the rest directly. -/
theorem rename_optionMatchCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (noneBranch someBranch scrutinee : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (optionMatchCell motive noneBranch someBranch scrutinee)
      = optionMatchCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming noneBranch) (RawTerm.rename rawRenaming someBranch)
          (RawTerm.rename rawRenaming scrutinee) := rfl

/-- `eitherMatch` distributes: motive under one lift, the rest directly. -/
theorem rename_eitherMatchCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (leftBranch rightBranch scrutinee : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (eitherMatchCell motive leftBranch rightBranch scrutinee)
      = eitherMatchCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming leftBranch) (RawTerm.rename rawRenaming rightBranch)
          (RawTerm.rename rawRenaming scrutinee) := rfl

/-- `idJ` distributes: motive under two lifts, base/witness directly. -/
theorem rename_idJCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 2)) (baseCase witness : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (idJCell motive baseCase witness)
      = idJCell (RawTerm.rename (iterateLiftRaw rawRenaming 2) motive)
          (RawTerm.rename rawRenaming baseCase) (RawTerm.rename rawRenaming witness) := rfl

/-- `fst` distributes over the pair term. -/
theorem rename_fstCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (pairTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (fstCell pairTerm)
      = fstCell (RawTerm.rename rawRenaming pairTerm) := rfl

/-- `snd` distributes over the pair term. -/
theorem rename_sndCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (pairTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (sndCell pairTerm)
      = sndCell (RawTerm.rename rawRenaming pairTerm) := rfl

/-- `listElim` distributes: motive under one lift, the rest directly. -/
theorem rename_listElimCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motive : RawTerm (sourceScope + 1)) (scrutinee nilBranch consBranch : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (listElimCell motive scrutinee nilBranch consBranch)
      = listElimCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming nilBranch)
          (RawTerm.rename rawRenaming consBranch) := rfl

/-- `pathLam(body)` distributes: body under one lift. -/
theorem rename_pathLamCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (body : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming (pathLamCell body)
      = pathLamCell (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) := rfl

/-- `pathApp(path, argument)` distributes over both children. -/
theorem rename_pathAppCell {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (path argument : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (pathAppCell path argument)
      = pathAppCell (RawTerm.rename rawRenaming path)
          (RawTerm.rename rawRenaming argument) := rfl

/-! ## The lift/weaken naturality squares in `iterateLiftRaw` form (the rename twins of the
    `subst_iterateLift_*_commute` bricks) -/

/-- The one-level lift/weaken naturality square in the EXPLICIT `rename RawRenaming.weaken` presentation:
`rename (iterateLiftRaw ρ 1) (rename weaken X) = rename weaken (rename ρ X)`.  Defeq to
`rename_lift_weaken_commute` (`iterateLiftRaw ρ 1 ≡ RawRenaming.lift ρ`); restated with `iterateLiftRaw`
so the recursiveElim step-branch chain rewrites without `simp` (propext-clean). -/
theorem rename_iterateLift_one_renameWeaken_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename (iterateLiftRaw rawRenaming 1)
        (RawTerm.rename RawRenaming.weaken sourceTerm)
      = RawTerm.rename RawRenaming.weaken (RawTerm.rename rawRenaming sourceTerm) :=
  rename_lift_weaken_commute rawRenaming sourceTerm

/-- The one-level naturality square in the `RawTerm.weaken` abbreviation presentation (the
listStepFunctionType / nonDependentArrow chain shape). -/
theorem rename_iterateLift_one_weaken_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename (iterateLiftRaw rawRenaming 1) (RawTerm.weaken sourceTerm)
      = RawTerm.weaken (RawTerm.rename rawRenaming sourceTerm) :=
  rename_lift_weaken_commute rawRenaming sourceTerm

/-- The TWICE-iterated lift/weaken naturality square (the recursive-eliminator step-branch classifier
shape): `rename (iterateLiftRaw ρ 2) (weaken (weaken X)) = weaken (weaken (rename ρ X))` — two composed
applications of the one-level square, with `iterateLiftRaw ρ 2` defeq to `lift (lift ρ)`. -/
theorem rename_iterateLift_two_weaken_weaken_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename (iterateLiftRaw rawRenaming 2)
        (RawTerm.rename RawRenaming.weaken
          (RawTerm.rename RawRenaming.weaken sourceTerm))
      = RawTerm.rename RawRenaming.weaken
          (RawTerm.rename RawRenaming.weaken
            (RawTerm.rename rawRenaming sourceTerm)) := by
  show RawTerm.rename (iterateLiftRaw (iterateLiftRaw rawRenaming 1) 1)
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken sourceTerm))
    = RawTerm.rename RawRenaming.weaken
        (RawTerm.rename RawRenaming.weaken (RawTerm.rename rawRenaming sourceTerm))
  rw [rename_iterateLift_one_renameWeaken_commute (iterateLiftRaw rawRenaming 1)
        (RawTerm.rename RawRenaming.weaken sourceTerm),
    rename_iterateLift_one_renameWeaken_commute rawRenaming sourceTerm]


/-- The TWICE-iterated lift/weaken naturality square in the `RawTerm.weaken` ABBREVIATION presentation
(the `ElimRule` step-branch obligation classifier shape — natElim / natRec store their step branch at the
doubly-weakened result type written with `RawTerm.weaken`): `rename (iterateLiftRaw ρ 2) (weaken (weaken
X)) = weaken (weaken (rename ρ X))`.  Defeq to `rename_iterateLift_two_weaken_weaken_commute`
(`RawTerm.weaken X ≡ RawTerm.rename RawRenaming.weaken X`); restated in the abbreviation form so the
natElim / natRec step-branch obligation chain rewrites without unfolding `RawTerm.weaken`
(propext-clean). -/
theorem rename_iterateLift_two_weakenAbbrev_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename (iterateLiftRaw rawRenaming 2)
        (RawTerm.weaken (RawTerm.weaken sourceTerm))
      = RawTerm.weaken (RawTerm.weaken (RawTerm.rename rawRenaming sourceTerm)) :=
  rename_iterateLift_two_weaken_weaken_commute rawRenaming sourceTerm

/-- The non-dependent function code `piTyCodeCell domain (weaken codomain)` distributes under a renaming:
domain directly, codomain weakened then renamed (the lift/weaken naturality square).  The classifier
shape of every option/either match branch. -/
theorem rename_nonDependentArrow {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (domain codomain : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (piTyCodeCell domain (RawTerm.weaken codomain))
      = piTyCodeCell (RawTerm.rename rawRenaming domain)
          (RawTerm.weaken (RawTerm.rename rawRenaming codomain)) := by
  rw [rename_piTyCodeCell, rename_iterateLift_one_weaken_commute]

/-- `listStepFunctionType` distributes under a renaming over both type params: built from `piTyCodeCell` /
`listTypeCell` / `weaken` spines, the renaming threads through.  Proved by `rw` of the per-cell
commutations + the lift/weaken naturality square (no `simp`, propext-clean). -/
theorem rename_listStepFunctionType {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) (elementType resultType : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (listStepFunctionType elementType resultType)
      = listStepFunctionType (RawTerm.rename rawRenaming elementType)
          (RawTerm.rename rawRenaming resultType) := by
  show RawTerm.rename rawRenaming
      (piTyCodeCell elementType
        (RawTerm.weaken (piTyCodeCell (listTypeCell elementType)
          (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType))))))
    = piTyCodeCell (RawTerm.rename rawRenaming elementType)
        (RawTerm.weaken (piTyCodeCell (listTypeCell (RawTerm.rename rawRenaming elementType))
          (RawTerm.weaken (piTyCodeCell (RawTerm.rename rawRenaming resultType)
            (RawTerm.weaken (RawTerm.rename rawRenaming resultType))))))
  rw [rename_piTyCodeCell, rename_iterateLift_one_weaken_commute, rename_piTyCodeCell,
    rename_listTypeCell, rename_iterateLift_one_weaken_commute, rename_piTyCodeCell,
    rename_iterateLift_one_weaken_commute]

/-- **Renaming naturality of the DEPENDENT `listElim` cons-branch TYPE** (DEP-LIST sub-D2a) — the RENAME twin of
`subst_listElimDependentConsBranchType_iterateLift`, the form the dependent `listElim` rule's
`HasTypeUnion.renameRespectsContext` arm consumes (the dependent twin of `rename_listStepFunctionType`).  Three
`rename_piTyCodeCell` peels feed the cons-branch codomain (`lift³`) and the recursive-result binder type (`lift²`)
their rename naturality lemmas; the `List A` domain re-bases via `rename_listTypeCell` +
`rename_iterateLift_one_weaken_commute`; the `iterateLiftRaw`-nesting collapses by `rfl`. -/
theorem rename_listElimDependentConsBranchType_iterateLift {sourceScope targetScope : Nat}
    (motive : RawTerm (sourceScope + 1)) (elementType : RawTerm sourceScope)
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (listElimDependentConsBranchType motive elementType)
      = listElimDependentConsBranchType (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming elementType) := by
  unfold listElimDependentConsBranchType
  rw [rename_piTyCodeCell, rename_piTyCodeCell, rename_listTypeCell,
    rename_iterateLift_one_weaken_commute, rename_piTyCodeCell,
    show iterateLiftRaw (iterateLiftRaw (iterateLiftRaw rawRenaming 1) 1) 1
        = iterateLiftRaw rawRenaming 3 from rfl,
    show iterateLiftRaw (iterateLiftRaw rawRenaming 1) 1 = iterateLiftRaw rawRenaming 2 from rfl,
    rename_listElimDependentRecBinderType_iterateLift,
    rename_listElimDependentConsBranchCodomain_iterateLift]

/-! ## The renaming-respects-context carrier + the binder-crossing helpers -/

/-- The renaming-respects-context condition for the native union: each source binding's looked-up type
renames to the target's looked-up binding.  IDENTICAL to the grown engine's carrier so the embedding arms
compose verbatim. -/
abbrev HasTypeUnion.RenameRespectsContext {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    RawTerm.rename rawRenaming (sourceContext.lookup index)
      = targetContext.lookup (rawRenaming index)

/-- The two-binder lift of the renaming context-condition (the recursiveElim / idJ step-branch shape):
the double lift of a renaming context-condition is a context-condition at the context extended by the two
domains.  An iterate of `renameContextCondition_cons`. -/
theorem HasTypeUnion.RenameRespectsContext.consTwice {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    {rawRenaming : RawRenaming sourceScope targetScope}
    (condition : HasTypeUnion.RenameRespectsContext sourceContext targetContext rawRenaming) :
    HasTypeUnion.RenameRespectsContext ((sourceContext.cons outerType).cons innerType)
      ((targetContext.cons (RawTerm.rename rawRenaming outerType)).cons
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) innerType))
      (iterateLiftRaw rawRenaming 2) :=
  renameContextCondition_cons innerType (iterateLiftRaw rawRenaming 1)
    (renameContextCondition_cons outerType rawRenaming condition)

/-- **The affine binder check transports through a lifted renaming.**  `gradedBinderChecks usage body`
(a bound on `occurrenceCountAt body (var 0)`) survives renaming by `iterateLiftRaw ρ 1`: the lift hits
`var 0` exactly at `var 0` (`occurrenceCountAt_rename_image`), so the freshest-binder occurrence count is
unchanged and the bound holds verbatim.  The graded arm's binder-grade premise transport. -/
theorem gradedBinderChecks_rename_lift {sourceScope targetScope : Nat}
    (usage : UsageGrade) (rawRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1))
    (checked : gradedBinderChecks usage body) :
    gradedBinderChecks usage (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) := by
  show usage.boundsCount (RawTerm.occurrenceCountAt
    (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) ⟨0, Nat.succ_pos targetScope⟩)
  rw [RawTerm.occurrenceCountAt_rename_image (iterateLiftRaw rawRenaming 1) body
        ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos targetScope⟩
        (by
          intro candidatePosition
          obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
          cases candidateValue with
          | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
          | succ priorValue =>
              exact ⟨fun hit => Nat.noConfusion (congrArg Fin.val hit),
                fun isZero => Nat.noConfusion (congrArg Fin.val isZero)⟩)]
  exact checked

/-- **★ The pointwise renaming / weakening lemma over the native union.**  A union derivation at
`sourceContext`, renamed by any context-respecting renaming, gives a union derivation of the renamed
subject at the renamed classifier.  By `induction` over the 5 arms: the `ofGrown` embedding and the
`formationRule` arm route through the engines' own `renameRespectingContext` and re-embed; the recursive
`intro` / `elim` arms recurse via the IHs over their rule obligations with `RawRenaming.lift` crossing
binders; the `intro` arm transports the affine binder check by the lifted-occurrence preservation; the
`conv` arm transports the conversion through `Conv.rename`.  The de-Bruijn-insertion twin of
`HasTypeDescPi.renameRespectingContext`. -/
theorem HasTypeUnion.renameRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      HasTypeUnion.RenameRespectsContext sourceContext targetContext rawRenaming →
      HasTypeUnion profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) := by
  induction derivation with
  | var context index =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeUnion.ofGrown
        ((HasTypeDescPi.ofFormation (HasTypeDesc.var context index)).renameRespectingContext
          targetContext rawRenaming condition)
  | universeFormation context levelExpr flag =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeUnion.ofGrown
        ((HasTypeDescPi.ofFormation
            (HasTypeDesc.universeFormation context levelExpr flag)).renameRespectingContext
          targetContext rawRenaming condition)
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext rawRenaming condition
      have typedRenamed := typedIH targetContext rawRenaming condition
      have reclassifierRenamed := reclassifierIH targetContext rawRenaming condition
      rw [rename_universeCodeCell] at reclassifierRenamed
      exact HasTypeUnion.conv levelExpr flag typedRenamed
        (Conv.rename rawRenaming converts) reclassifierRenamed
  | ofGrown hostTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeUnion.ofGrown
        (hostTyped.renameRespectingContext targetContext rawRenaming condition)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold ihPremises =>
      intro targetScope targetContext rawRenaming condition
      cases rule with
      | baseType baseRule =>
          have isBaseType : baseTypeRuleDescOf generator = some baseRule :=
            formationRuleOf_baseType_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var := baseTypeRuleImpliesNotVariable isBaseType
          dsimp only [FormationRule.outputType]
          rw [RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar,
            baseTypeRuleDescOf_outputRenameStable isBaseType rawRenaming]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children) (.baseType baseRule)
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule trivial
      | flat flatRule =>
          -- TYTAB-2 formationRule promotion (rename twin): push the UNION obligation premise through the
          -- renaming via `FormationRule.obligations_pushRename`, sourcing each obligation from `ihPremises`.
          have isFlatFormation : flatTypingRuleDescOf generator = some flatRule :=
            formationRuleOf_flat_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            flatFormationRuleImpliesNotVariable isFlatFormation
          obtain rfl : flatRule = { outputType := universeFormerOutput } :=
            flatFormationRuleIsUniverseFormer isFlatFormation
          dsimp only [FormationRule.outputType, universeFormerOutput]
          rw [rename_universeCodeCell, RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children)
            (.flat { outputType := universeFormerOutput })
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule
            (FormationRule.obligations_pushRename (.flat { outputType := universeFormerOutput })
              targetContext rawRenaming children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext rawRenaming condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.rename rawRenaming domain))
                  (iterateLiftRaw rawRenaming 1)
                  (renameContextCondition_cons domain rawRenaming condition)))
      | cumulative cumulativeRule =>
          -- TYTAB-2 wave U2 (rename twin): the four cumulative codes (Π / Σ / list / option) plus the
          -- nullary unit code are now `formationRuleOf` rows.  ROW-SHAPE-AGNOSTIC: `formationRuleImpliesNotVariable`
          -- for the non-`gen_var` side condition, `typingRuleDescOf_output_renameStable` for the row-shape-agnostic
          -- output rewrite (uniform over the universe-former and the flag-pinned nullary rows), and
          -- `FormationRule.obligations_pushRename` for the UNION obligation premise (its `crossingTypings` clause
          -- supplies the Π/Σ binder-crossing codomain from `ihPremises` at the lifted renaming).
          have isCumulative : typingRuleDescOf generator = some cumulativeRule :=
            formationRuleOf_cumulative_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            cumulativeFormationRuleImpliesNotVariable isCumulative
          dsimp only [FormationRule.outputType]
          rw [typingRuleDescOf_output_renameStable isCumulative rawRenaming levels flag,
            RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children)
            (.cumulative cumulativeRule)
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule
            (FormationRule.obligations_pushRename (.cumulative cumulativeRule)
              targetContext rawRenaming children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext rawRenaming condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.rename rawRenaming domain))
                  (iterateLiftRaw rawRenaming 1)
                  (renameContextCondition_cons domain rawRenaming condition)))
      | termIndexed termRule =>
          have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
            formationRuleOf_termIndexed_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            termIndexedFormerRuleImpliesNotVariable isTermIndexed
          obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
            termIndexedFormerRuleIsCarrierOutput isTermIndexed
          dsimp only [FormationRule.outputType, termIndexedCarrierOutput]
          rw [rename_universeCodeCell, RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children)
            (.termIndexed { outputType := termIndexedCarrierOutput })
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule
            (FormationRule.obligations_pushRename (.termIndexed { outputType := termIndexedCarrierOutput })
              targetContext rawRenaming children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext rawRenaming condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.rename rawRenaming domain))
                  (iterateLiftRaw rawRenaming 1)
                  (renameContextCondition_cons domain rawRenaming condition)))
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      intro targetScope targetContext rawRenaming condition
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue: closed nullary value at the closed `Bool` type code (no premises).
      · match args, params with
        | .childNil, .childNil =>
          refine HasTypeUnion.intro targetContext .gen_boolTrue boolTrueIntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- boolFalse: the boolTrue twin at the other discriminator.
      · match args, params with
        | .childNil, .childNil =>
          refine HasTypeUnion.intro targetContext .gen_boolFalse boolFalseIntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- unit: the sole `Unit` member.
      · match args, params with
        | .childNil, .childNil =>
          refine HasTypeUnion.intro targetContext .gen_unit unitIntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- interval0: the `0 : Interval` endpoint.
      · match args, params with
        | .childNil, .childNil =>
          refine HasTypeUnion.intro targetContext .gen_interval0 interval0IntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- interval1: the `1 : Interval` endpoint.
      · match args, params with
        | .childNil, .childNil =>
          refine HasTypeUnion.intro targetContext .gen_interval1 interval1IntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- natZero: the `0 : Nat` base value.
      · match args, params with
        | .childNil, .childNil =>
          refine HasTypeUnion.intro targetContext .gen_natZero natZeroIntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- lam: the graded binder; domain/codomain formations + a body at `scope + 1`, usage side condition.
      · match args, params with
        | .childCons domainCode (.childCons body .childNil),
          .childCons codomainCode .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (lamCell domainCode body))
            (RawTerm.rename rawRenaming (piTyCodeCell domainCode codomainCode))
          rw [show RawTerm.rename rawRenaming (lamCell domainCode body)
                = lamCell (RawTerm.rename rawRenaming domainCode)
                    (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) from rfl,
            rename_piTyCodeCell]
          refine HasTypeUnion.intro targetContext .gen_lam lamIntroRule
            (RawTermChildren.rename rawRenaming (.childCons domainCode (.childCons body .childNil)))
            (RawTermChildren.rename rawRenaming (.childCons codomainCode .childNil))
            level0 level1 flag rfl
            (gradedBinderChecks_rename_lift UsageGrade.omega rawRenaming body sideHolds) ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have domainRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_universeCodeCell] at domainRenamed
              exact domainRenamed
          | tail _ hmem => cases hmem with
            | head =>
                have codomainCondition := renameContextCondition_cons domainCode rawRenaming condition
                have codomainRenamed := ihPremises _ (List.Mem.tail _ (List.Mem.head _))
                  (targetContext.cons (RawTerm.rename rawRenaming domainCode))
                  (iterateLiftRaw rawRenaming 1) codomainCondition
                rw [rename_universeCodeCell] at codomainRenamed
                exact codomainRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have bodyCondition := renameContextCondition_cons domainCode rawRenaming condition
                  exact ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                    (targetContext.cons (RawTerm.rename rawRenaming domainCode))
                    (iterateLiftRaw rawRenaming 1) bodyCondition
              | tail _ hmem => cases hmem
      -- pathLam: the affine path abstraction; body at `scope + 1` against the weakened carrier,
      -- the bridge output reads the body at the two endpoints (`subst0`).
      · match args, params with
        | .childCons body .childNil,
          .childCons carrierCode .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (pathLamCell body))
            (RawTerm.rename rawRenaming
              (bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
                (RawTerm.subst0 body intervalOneCell)))
          rw [rename_pathLamCell, rename_bridgeTypeCell, RawTerm.rename_subst0_commute,
            RawTerm.rename_subst0_commute]
          refine HasTypeUnion.intro targetContext .gen_pathLam pathLamIntroRule
            (RawTermChildren.rename rawRenaming (.childCons body .childNil))
            (RawTermChildren.rename rawRenaming (.childCons carrierCode .childNil))
            level0 level1 flag rfl
            (gradedBinderChecks_rename_lift UsageGrade.one rawRenaming body sideHolds) ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have bodyCondition :=
                renameContextCondition_cons intervalTypeCell rawRenaming condition
              have bodyRenamed := ihPremises _ (List.Mem.head _)
                (targetContext.cons (RawTerm.rename rawRenaming intervalTypeCell))
                (iterateLiftRaw rawRenaming 1) bodyCondition
              rw [rename_iterateLift_one_weaken_commute] at bodyRenamed
              exact bodyRenamed
          | tail _ hmem => cases hmem
      -- natSucc: the recursive unary constructor; one union-recursive premise at `Nat`.
      · match args, params with
        | .childCons child .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (natSuccCell child))
            (RawTerm.rename rawRenaming natTypeCell)
          rw [rename_natSuccCell, rename_natTypeCell]
          refine HasTypeUnion.intro targetContext .gen_natSucc natSuccIntroRule
            (RawTermChildren.rename rawRenaming (.childCons child .childNil))
            (RawTermChildren.rename rawRenaming .childNil) level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have childRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_natTypeCell] at childRenamed
              exact childRenamed
          | tail _ hmem => cases hmem
      -- listCons: a head at the element type, a union-recursive tail at `List(A)`.
      · match args, params with
        | .childCons head (.childCons tail .childNil), .childCons elementType .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (listConsCell head tail))
            (RawTerm.rename rawRenaming (listTypeCell elementType))
          rw [rename_listConsCell, rename_listTypeCell]
          refine HasTypeUnion.intro targetContext .gen_listCons listConsIntroRule
            (RawTermChildren.rename rawRenaming (.childCons head (.childCons tail .childNil)))
            (RawTermChildren.rename rawRenaming (.childCons elementType .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                have tailRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [rename_listTypeCell] at tailRenamed
                exact tailRenamed
            | tail _ hmem => cases hmem
      -- optionSome: a grown value at the element type, output `option(A)`.
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (optionSomeCell value))
            (RawTerm.rename rawRenaming (optionTypeCell typeParam0))
          rw [rename_optionSomeCell, rename_optionTypeCell]
          refine HasTypeUnion.intro targetContext .gen_optionSome optionSomeIntroRule
            (RawTermChildren.rename rawRenaming (.childCons value .childNil))
            (RawTermChildren.rename rawRenaming (.childCons typeParam0 .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem
      -- optionNone: childless, a formedness premise on the free element type.
      · match args, params with
        | .childNil, .childCons typeParam0 .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming optionNoneCell)
            (RawTerm.rename rawRenaming (optionTypeCell typeParam0))
          rw [rename_optionNoneCell, rename_optionTypeCell]
          refine HasTypeUnion.intro targetContext .gen_optionNone optionNoneIntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming (.childCons typeParam0 .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have elementFormRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_universeCodeCell] at elementFormRenamed
              exact elementFormRenamed
          | tail _ hmem => cases hmem
      -- listNil: the optionNone twin with the list container.
      · match args, params with
        | .childNil, .childCons typeParam0 .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming listNilCell)
            (RawTerm.rename rawRenaming (listTypeCell typeParam0))
          rw [rename_listNilCell, rename_listTypeCell]
          refine HasTypeUnion.intro targetContext .gen_listNil listNilIntroRule
            (RawTermChildren.rename rawRenaming .childNil)
            (RawTermChildren.rename rawRenaming (.childCons typeParam0 .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have elementFormRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_universeCodeCell] at elementFormRenamed
              exact elementFormRenamed
          | tail _ hmem => cases hmem
      -- eitherInl: a grown value at the LEFT, a formedness premise on the free RIGHT.
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (eitherInlCell value))
            (RawTerm.rename rawRenaming (eitherTypeCell typeParam0 typeParam1))
          rw [rename_eitherInlCell, rename_eitherTypeCell]
          refine HasTypeUnion.intro targetContext .gen_eitherInl eitherInlIntroRule
            (RawTermChildren.rename rawRenaming (.childCons value .childNil))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParam0 (.childCons typeParam1 .childNil)))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                have freeFormRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [rename_universeCodeCell] at freeFormRenamed
                exact freeFormRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  -- The flag-coherence formedness premise on the LEFT type param.
                  have leftFormRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_universeCodeCell] at leftFormRenamed
                  exact leftFormRenamed
              | tail _ hmem => cases hmem
      -- eitherInr: a grown value at the pinned RIGHT, a formedness premise on the free LEFT;
      -- output puts the free side first.
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (eitherInrCell value))
            (RawTerm.rename rawRenaming (eitherTypeCell typeParam1 typeParam0))
          rw [rename_eitherInrCell, rename_eitherTypeCell]
          refine HasTypeUnion.intro targetContext .gen_eitherInr eitherInrIntroRule
            (RawTermChildren.rename rawRenaming (.childCons value .childNil))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParam0 (.childCons typeParam1 .childNil)))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                have freeFormRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [rename_universeCodeCell] at freeFormRenamed
                exact freeFormRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  -- The flag-coherence formedness premise on the RIGHT type param.
                  have rightFormRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_universeCodeCell] at rightFormRenamed
                  exact rightFormRenamed
              | tail _ hmem => cases hmem
      -- pair: two grown children at two independent type params.
      · match args, params with
        | .childCons child0 (.childCons child1 .childNil),
          .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (pairCell child0 child1))
            (RawTerm.rename rawRenaming (productTypeCell typeParam0 typeParam1))
          rw [rename_pairCell, rename_productTypeCell]
          refine HasTypeUnion.intro targetContext .gen_pair pairIntroRule
            (RawTermChildren.rename rawRenaming (.childCons child0 (.childCons child1 .childNil)))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParam0 (.childCons typeParam1 .childNil)))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  -- The flag-coherence formedness premise on the FIRST type param.
                  have firstFormRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_universeCodeCell] at firstFormRenamed
                  exact firstFormRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    -- The flag-coherence formedness premise on the SECOND type param.
                    have secondFormRenamed :=
                      ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                        targetContext rawRenaming condition
                    rw [rename_universeCodeCell] at secondFormRenamed
                    exact secondFormRenamed
                | tail _ hmem => cases hmem
      -- refl: a grown witness; the output reads the witness VALUE into `Id(A, a, a)`.
      · match args, params with
        | .childCons witness .childNil, .childCons typeParam0 .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (reflCell witness))
            (RawTerm.rename rawRenaming (idTypeCell typeParam0 witness witness))
          rw [rename_reflCell, rename_idTypeCell]
          refine HasTypeUnion.intro targetContext .gen_refl reflIntroRule
            (RawTermChildren.rename rawRenaming (.childCons witness .childNil))
            (RawTermChildren.rename rawRenaming (.childCons typeParam0 .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem
  | elim context generator rule args params level0 level1 flag isElim premisesHold ihPremises =>
      intro targetScope targetContext rawRenaming condition
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app: dependent application output via `subst0`; the function premise is at the Π code.
      · match args, params with
        | .childCons function (.childCons argument .childNil),
          .childCons domainCode (.childCons codomainCode .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (appCell function argument))
            (RawTerm.rename rawRenaming (RawTerm.subst0 codomainCode argument))
          rw [rename_appCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_app appElimRule
            (RawTermChildren.rename rawRenaming (.childCons function (.childCons argument .childNil)))
            (RawTermChildren.rename rawRenaming
              (.childCons domainCode (.childCons codomainCode .childNil))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have functionRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_piTyCodeCell] at functionRenamed
              exact functionRenamed
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem
      -- pathApp: the (constant) carrier output reads off a param directly; no `subst0`.
      · match args, params with
        | .childCons path (.childCons argument .childNil),
          .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
          refine HasTypeUnion.elim targetContext .gen_pathApp pathAppElimRule
            (RawTermChildren.rename rawRenaming (.childCons path (.childCons argument .childNil)))
            (RawTermChildren.rename rawRenaming
              (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil))))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have pathRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_bridgeTypeCell] at pathRenamed
              exact pathRenamed
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  have resultRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_universeCodeCell] at resultRenamed
                  exact resultRenamed
              | tail _ hmem => cases hmem
      -- natElim: DEPENDENT recursive eliminator; output `subst0 motive scrutinee`, base branch at zero
      -- (`rename_subst0_commute`, closed `natZeroCell`), step branch under TWO binders at
      -- `natElimDependentSuccBranchType motive` (reshaped by the rename-naturality lemma
      -- `rename_natElimDependentSuccBranchType_iterateLift`), motive under one `natTypeCell` binder.
      · match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (natElimCell motive baseBranch stepBranch scrutinee))
            (RawTerm.rename rawRenaming (RawTerm.subst0 motive scrutinee))
          rw [rename_natElimCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_natElim natElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                have baseRenamed := ihPremises _ (List.Mem.tail _ (List.Mem.head _))
                  targetContext rawRenaming condition
                rw [RawTerm.rename_subst0_commute] at baseRenamed
                exact baseRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have stepCondition := HasTypeUnion.RenameRespectsContext.consTwice
                    natTypeCell motive condition
                  have stepRenamed := ihPremises _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                    _ (iterateLiftRaw rawRenaming 2) stepCondition
                  rw [rename_natElimDependentSuccBranchType_iterateLift] at stepRenamed
                  exact stepRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 1)
                      (renameContextCondition_cons natTypeCell rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem
      -- natRec: DEPENDENT recursor twin of natElim (same substrate, `natRecCell` / `gen_natRec`).
      · match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (natRecCell motive baseBranch stepBranch scrutinee))
            (RawTerm.rename rawRenaming (RawTerm.subst0 motive scrutinee))
          rw [rename_natRecCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_natRec natRecElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                have baseRenamed := ihPremises _ (List.Mem.tail _ (List.Mem.head _))
                  targetContext rawRenaming condition
                rw [RawTerm.rename_subst0_commute] at baseRenamed
                exact baseRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have stepCondition := HasTypeUnion.RenameRespectsContext.consTwice
                    natTypeCell motive condition
                  have stepRenamed := ihPremises _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                    _ (iterateLiftRaw rawRenaming 2) stepCondition
                  rw [rename_natElimDependentSuccBranchType_iterateLift] at stepRenamed
                  exact stepRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 1)
                      (renameContextCondition_cons natTypeCell rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem
      -- boolElim: DEPENDENT two-branch match; output `subst0 motive scrutinee`, branches at the motive at
      -- the boolean values, motive obligation under one `boolTypeCell` binder.  The output and each branch
      -- classifier reshape through `rename_subst0_commute` (the `app` template); the motive obligation's
      -- context extends by one binder via `renameContextCondition_cons`.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))),
          .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (boolElimCell motive scrutinee thenBranch elseBranch))
            (RawTerm.rename rawRenaming (RawTerm.subst0 motive scrutinee))
          rw [rename_boolElimCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_boolElim boolElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                have thenRenamed := ihPremises _ (List.Mem.tail _ (List.Mem.head _))
                  targetContext rawRenaming condition
                rw [RawTerm.rename_subst0_commute] at thenRenamed
                exact thenRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have elseRenamed := ihPremises _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) targetContext rawRenaming condition
                  rw [RawTerm.rename_subst0_commute] at elseRenamed
                  exact elseRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 1)
                      (renameContextCondition_cons boolTypeCell rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem
      -- optionMatch: DEPENDENT — output `subst0 motive scrutinee`; the none branch is nullary at
      -- `subst0 motive optionNoneCell` (reshaped via `rename_subst0_commute`, the closed `optionNoneCell`
      -- defeq-erases), the some branch at the dependent some branch type (reshaped by
      -- `rename_optionMatchDependentSomeBranchType_iterateLift`), motive under one `optionTypeCell` binder
      -- (`renameContextCondition_cons`).
      · match args, params with
        | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (optionMatchCell motive noneBranch someBranch scrutinee))
            (RawTerm.rename rawRenaming (RawTerm.subst0 motive scrutinee))
          rw [rename_optionMatchCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_optionMatch optionMatchElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParamA (.childCons typeParamB .childNil))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have scrutineeRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_optionTypeCell] at scrutineeRenamed
              exact scrutineeRenamed
          | tail _ hmem => cases hmem with
            | head =>
                have noneRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [RawTerm.rename_subst0_commute] at noneRenamed
                exact noneRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have someRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_optionMatchDependentSomeBranchType_iterateLift] at someRenamed
                  exact someRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 1)
                      (renameContextCondition_cons (optionTypeCell typeParamA) rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem
      -- eitherMatch: DEPENDENT — output `subst0 motive scrutinee`; branches at the dependent inl/inr branch
      -- types (reshaped by `rename_eitherMatchDependentInl/InrBranchType_iterateLift`), motive under one
      -- `eitherTypeCell` binder (`renameContextCondition_cons`).
      · match args, params with
        | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (eitherMatchCell motive leftBranch rightBranch scrutinee))
            (RawTerm.rename rawRenaming (RawTerm.subst0 motive scrutinee))
          rw [rename_eitherMatchCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_eitherMatch eitherMatchElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParamA (.childCons typeParamB .childNil))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have scrutineeRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_eitherTypeCell] at scrutineeRenamed
              exact scrutineeRenamed
          | tail _ hmem => cases hmem with
            | head =>
                have leftRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [rename_eitherMatchDependentInlBranchType_iterateLift] at leftRenamed
                exact leftRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have rightRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_eitherMatchDependentInrBranchType_iterateLift] at rightRenamed
                  exact rightRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 1)
                      (renameContextCondition_cons (eitherTypeCell typeParamA typeParamB) rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem
      -- idJ: path induction; the witness premise sits at the reflexive identity code.
      · match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons endpoint (.childCons resultType .childNil)) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (idJCell motive baseCase witness))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_idJCell]
          refine HasTypeUnion.elim targetContext .gen_idJ idJElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons baseCase (.childCons witness .childNil))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeCode (.childCons endpoint (.childCons resultType .childNil)))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have witnessRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_idTypeCell] at witnessRenamed
              exact witnessRenamed
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  have resultRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_universeCodeCell] at resultRenamed
                  exact resultRenamed
              | tail _ hmem => cases hmem
      -- fst: the Σ first projection; one premise at the product code.
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (fstCell pairTerm))
            (RawTerm.rename rawRenaming firstType)
          rw [rename_fstCell]
          refine HasTypeUnion.elim targetContext .gen_fst fstElimRule
            (RawTermChildren.rename rawRenaming (.childCons pairTerm .childNil))
            (RawTermChildren.rename rawRenaming
              (.childCons firstType (.childCons secondType .childNil))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have pairRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_productTypeCell] at pairRenamed
              exact pairRenamed
          | tail _ hmem => cases hmem with
            | head =>
                have resultRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [rename_universeCodeCell] at resultRenamed
                exact resultRenamed
            | tail _ hmem => cases hmem
      -- snd: the Σ second projection.
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (sndCell pairTerm))
            (RawTerm.rename rawRenaming secondType)
          rw [rename_sndCell]
          refine HasTypeUnion.elim targetContext .gen_snd sndElimRule
            (RawTermChildren.rename rawRenaming (.childCons pairTerm .childNil))
            (RawTermChildren.rename rawRenaming
              (.childCons firstType (.childCons secondType .childNil))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have pairRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_productTypeCell] at pairRenamed
              exact pairRenamed
          | tail _ hmem => cases hmem with
            | head =>
                have resultRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [rename_universeCodeCell] at resultRenamed
                exact resultRenamed
            | tail _ hmem => cases hmem
      -- listElim: DEPENDENT — output `subst0 motive scrutinee`; the nil branch is nullary at
      -- `subst0 motive listNilCell` (reshaped via `rename_subst0_commute`, the closed `listNilCell`
      -- defeq-erases), the cons branch at the dependent cons-branch type (reshaped by
      -- `rename_listElimDependentConsBranchType_iterateLift`), motive under one `listTypeCell` binder
      -- (`renameContextCondition_cons`).  The list (recursive) twin of the optionMatch row; 2nd param vestigial.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
          .childCons elementType (.childCons _resultType .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (listElimCell motive scrutinee nilBranch consBranch))
            (RawTerm.rename rawRenaming (RawTerm.subst0 motive scrutinee))
          rw [rename_listElimCell, RawTerm.rename_subst0_commute]
          refine HasTypeUnion.elim targetContext .gen_listElim listElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons elementType (.childCons elementType .childNil))) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have scrutineeRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_listTypeCell] at scrutineeRenamed
              exact scrutineeRenamed
          | tail _ hmem => cases hmem with
            | head =>
                have nilRenamed :=
                  ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
                rw [RawTerm.rename_subst0_commute] at nilRenamed
                exact nilRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have consRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_listElimDependentConsBranchType_iterateLift] at consRenamed
                  exact consRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 1)
                      (renameContextCondition_cons (listTypeCell elementType) rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem

/-! ## ★ The weakening corollary (the `fun _ => rfl` context-condition specialization) -/

/-- **★ INTRINSIC weakening for the native union.**  A `HasTypeUnion` derivation survives extending
the context by one fresh binding, subject and classifier shifted by `RawRenaming.weaken` — the union twin
of `HasTypeDescPi.weakenUnderBinding`.  The corollary of `renameRespectingContext` whose
context-condition holds DEFINITIONALLY (`fun _ => rfl`): `weaken index` is `Fin.succ index`, the `cons`
`lookup` fires its successor arm. -/
theorem HasTypeUnion.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} (newBinding : RawTerm scope)
    (derivation : HasTypeUnion profile context subject classifier) :
    HasTypeUnion profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.cons newBinding) RawRenaming.weaken
    (fun _ => rfl)

end FX1Poly.Typed
