import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Ledger.Cell.UnionCellSubstitution
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiWeakening
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubst

/-! # FX1Poly/Typed/HasTypeUnionWeakening — the RENAMING / WEAKENING lemma for the 25-arm native
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

## How the 8 arms discharge (the post-TYTAB-1-collapse arm set)

  * The SOLE ENGINE EMBEDDING (`ofGrown`) routes its host premise through the grown engine's own
    `renameRespectingContext` and re-embeds.  The TABLE-DRIVEN FORMATION arms (`formationRule` /
    `dataIntroNullary`) rename their premise telescope via the
    flat / term-indexed telescope `renameRespectingContext` helpers and reconstruct the abstract cell via
    `RawTerm.rename_mkGen_of_ne_var`.  (The six zoo intro embeddings, plus the base-type / data-intro /
    flat / term-indexed-former STANDALONE ENGINES, were RETIRED — NATIVE-42 the intro zoo, NATIVE-36/44
    the base-type/data-intro/flat engines into table arms, TABLE-CANON-6 the term-indexed-former engine —
    every data value and code now enters through its native table row.)
  * The TABLE-DRIVEN RECURSIVE arms `gradedBinderIntro` / `recursiveDataIntro` / `grownDataIntro` recurse
    via the induction hypotheses, with `RawRenaming.lift` crossing the one/two binders (the lifted
    condition keeps the renaming context-respecting: `0` → `rename_lift_weaken_commute` on the domain,
    `k+1` → the condition under weakening), and the cell-rename `rfl` commutations push `RawTerm.rename`
    through each rule's member cell / classifier builders.
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
  * The graded arm additionally transports the affine binder check
    (`RawTerm.occurrenceCountAt_rename_image` on the lifted renaming: a lifted renaming preserves the
    freshest-binder occurrence count, so `gradedBinderChecks usage body` survives verbatim).

## Zero-axiom

`renameRespectingContext` is `induction` over the 8 arms + the cell-rename `rfl` commutations + the
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
subject at the renamed classifier.  By `induction` over the 8 arms: the engine embeddings and
host-premise arms route through the engines' own `renameRespectingContext` and re-embed; the recursive
native arms recurse via the IHs with `RawRenaming.lift` crossing binders; the graded arm transports the
affine binder check by the lifted-occurrence preservation; the conv arm transports the conversion through
`Conv.rename`.  The de-Bruijn-insertion twin of `HasTypeDescPi.renameRespectingContext`. -/
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
      premise =>
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
          have isFlatFormation : flatTypingRuleDescOf generator = some flatRule :=
            formationRuleOf_flat_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            flatFormationRuleImpliesNotVariable isFlatFormation
          obtain rfl : flatRule = { outputType := universeFormerOutput } :=
            flatFormationRuleIsUniverseFormer isFlatFormation
          have flatPremise : FlatDescTelescopePi profile context flag levels children := premise
          have renamedPremise :=
            FlatDescTelescopePi.renameRespectingTelescope flatPremise targetContext rawRenaming
              condition
          dsimp only [FormationRule.outputType, universeFormerOutput]
          rw [rename_universeCodeCell, RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children)
            (.flat { outputType := universeFormerOutput })
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule renamedPremise
      | termIndexed termRule =>
          have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
            formationRuleOf_termIndexed_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            termIndexedFormerRuleImpliesNotVariable isTermIndexed
          obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
            termIndexedFormerRuleIsCarrierOutput isTermIndexed
          have termPremise : TermIndexedFormerTelescope profile context children carrier level flag :=
            premise
          have renamedPremises :=
            TermIndexedFormerTelescope.renameRespectingContext termPremise targetContext rawRenaming
              condition
          dsimp only [FormationRule.outputType, termIndexedCarrierOutput]
          rw [rename_universeCodeCell, RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children)
            (.termIndexed { outputType := termIndexedCarrierOutput })
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule renamedPremises
  | dataIntroNullary context generator payload children rule isDataIntro =>
      intro targetScope targetContext rawRenaming _condition
      have hNotVar : generator ≠ Generator.gen_var := dataIntroNullaryRuleImpliesNotVariable isDataIntro
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar,
        dataIntroNullaryRuleDescOf_outputRenameStable isDataIntro rawRenaming]
      exact HasTypeUnion.dataIntroNullary targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) rule isDataIntro
  | recursiveDataIntro context generator spec head recursiveChild elementType isRecursiveDataIntro
      headTyped _recursiveChildTyped recursiveChildIH =>
      intro targetScope targetContext rawRenaming condition
      rcases recursiveDataIntroSpecOf_cases
          (show recursiveDataIntroSpecOf generator = some spec from isRecursiveDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩
      · subst specEq
        have childRenamed := recursiveChildIH targetContext rawRenaming condition
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (natSuccCell recursiveChild))
          (RawTerm.rename rawRenaming natTypeCell)
        rw [rename_natSuccCell, rename_natTypeCell]
        exact HasTypeUnion.recursiveUnaryIntro targetContext .gen_natSucc
          natSuccNativeRecursiveUnaryRule (RawTerm.rename rawRenaming recursiveChild) rfl childRenamed
      · subst specEq
        have tailRenamed := recursiveChildIH targetContext rawRenaming condition
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (listConsCell head recursiveChild))
          (RawTerm.rename rawRenaming (listTypeCell elementType))
        rw [rename_listConsCell, rename_listTypeCell]
        exact HasTypeUnion.recursiveBinaryIntro targetContext .gen_listCons
          listConsNativeRecursiveBinaryRule (RawTerm.rename rawRenaming head)
          (RawTerm.rename rawRenaming recursiveChild) (RawTerm.rename rawRenaming elementType) rfl
          ((headTyped rfl).renameRespectingContext targetContext rawRenaming condition) tailRenamed
  | grownDataIntro context generator spec child0 child1 typeParam0 typeParam1 formednessLevel
      formednessFlag isGrownDataIntro child0Typed child1Typed formednessTyped =>
      intro targetScope targetContext rawRenaming condition
      rcases grownDataIntroSpecOf_cases
          (show grownDataIntroSpecOf generator = some spec from isGrownDataIntro)
        with ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩ | ⟨_, specEq⟩
          | ⟨_, specEq⟩
      · subst specEq
        -- optionSome row: one grown child at the element type, output optionTypeCell.
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (optionSomeCell child0))
          (RawTerm.rename rawRenaming (optionTypeCell typeParam0))
        rw [rename_optionSomeCell, rename_optionTypeCell]
        exact HasTypeUnion.pinnedUnaryIntro targetContext .gen_optionSome
          optionSomeNativePinnedUnaryRule (RawTerm.rename rawRenaming child0)
          (RawTerm.rename rawRenaming typeParam0) rfl
          ((child0Typed rfl).renameRespectingContext targetContext rawRenaming condition)
      · subst specEq
        -- optionNone row: childless, grown-formedness on the free element type.
        have elementFormRenamed :=
          (formednessTyped rfl).renameRespectingContext targetContext rawRenaming condition
        rw [rename_universeCodeCell] at elementFormRenamed
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming optionNoneCell)
          (RawTerm.rename rawRenaming (optionTypeCell typeParam0))
        rw [rename_optionNoneCell, rename_optionTypeCell]
        exact HasTypeUnion.nullaryFreeTypeIntro targetContext .gen_optionNone
          optionNoneNativeNullaryFreeTypeRule (RawTerm.rename rawRenaming typeParam0)
          formednessLevel formednessFlag rfl elementFormRenamed
      · subst specEq
        -- listNil row: the optionNone twin with the list container.
        have elementFormRenamed :=
          (formednessTyped rfl).renameRespectingContext targetContext rawRenaming condition
        rw [rename_universeCodeCell] at elementFormRenamed
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming listNilCell)
          (RawTerm.rename rawRenaming (listTypeCell typeParam0))
        rw [rename_listNilCell, rename_listTypeCell]
        exact HasTypeUnion.nullaryFreeTypeIntro targetContext .gen_listNil
          listNilNativeNullaryFreeTypeRule (RawTerm.rename rawRenaming typeParam0)
          formednessLevel formednessFlag rfl elementFormRenamed
      · subst specEq
        -- eitherInl row: grown value at the pinned left, formedness on the free right.
        have valueRenamed :=
          (child0Typed rfl).renameRespectingContext targetContext rawRenaming condition
        have freeFormRenamed :=
          (formednessTyped rfl).renameRespectingContext targetContext rawRenaming condition
        rw [rename_universeCodeCell] at freeFormRenamed
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (eitherInlCell child0))
          (RawTerm.rename rawRenaming (eitherTypeCell typeParam0 typeParam1))
        rw [rename_eitherInlCell, rename_eitherTypeCell]
        exact HasTypeUnion.coproductIntro targetContext .gen_eitherInl
          eitherInlNativeCoproductRule (RawTerm.rename rawRenaming child0)
          (RawTerm.rename rawRenaming typeParam0) (RawTerm.rename rawRenaming typeParam1)
          formednessLevel formednessFlag rfl valueRenamed freeFormRenamed
      · subst specEq
        -- eitherInr row: grown value pinning the right, free left first in the output.
        have valueRenamed :=
          (child0Typed rfl).renameRespectingContext targetContext rawRenaming condition
        have freeFormRenamed :=
          (formednessTyped rfl).renameRespectingContext targetContext rawRenaming condition
        rw [rename_universeCodeCell] at freeFormRenamed
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (eitherInrCell child0))
          (RawTerm.rename rawRenaming (eitherTypeCell typeParam1 typeParam0))
        rw [rename_eitherInrCell, rename_eitherTypeCell]
        exact HasTypeUnion.coproductIntro targetContext .gen_eitherInr
          eitherInrNativeCoproductRule (RawTerm.rename rawRenaming child0)
          (RawTerm.rename rawRenaming typeParam0) (RawTerm.rename rawRenaming typeParam1)
          formednessLevel formednessFlag rfl valueRenamed freeFormRenamed
      · subst specEq
        -- pair row: two grown children at two independent type params.
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (pairCell child0 child1))
          (RawTerm.rename rawRenaming (productTypeCell typeParam0 typeParam1))
        rw [rename_pairCell, rename_productTypeCell]
        exact HasTypeUnion.nonDependentBinaryIntro targetContext .gen_pair
          pairNativeNonDependentBinaryRule (RawTerm.rename rawRenaming child0)
          (RawTerm.rename rawRenaming child1) (RawTerm.rename rawRenaming typeParam0)
          (RawTerm.rename rawRenaming typeParam1) rfl
          ((child0Typed rfl).renameRespectingContext targetContext rawRenaming condition)
          ((child1Typed rfl).renameRespectingContext targetContext rawRenaming condition)
      · subst specEq
        -- refl row: grown witness, term-indexed Id(typeParam0, child0, child0) output.
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (reflCell child0))
          (RawTerm.rename rawRenaming (idTypeCell typeParam0 child0 child0))
        rw [rename_reflCell, rename_idTypeCell]
        exact HasTypeUnion.reflexiveIntro targetContext .gen_refl
          reflNativeReflexiveRule (RawTerm.rename rawRenaming child0)
          (RawTerm.rename rawRenaming typeParam0) rfl
          ((child0Typed rfl).renameRespectingContext targetContext rawRenaming condition)
  | elim context generator rule args params isElim premisesHold ihPremises =>
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
              (.childCons domainCode (.childCons codomainCode .childNil))) rfl ?_
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
            rfl ?_
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
            | tail _ hmem => cases hmem
      -- natElim: the recursive eliminator; the step branch lives at `scope + 2` (two-cell extended).
      · match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
          .childCons resultType .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (natElimCell motive baseBranch stepBranch scrutinee))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_natElimCell]
          refine HasTypeUnion.elim targetContext .gen_natElim natElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))))
            (RawTermChildren.rename rawRenaming (.childCons resultType .childNil)) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  have stepCondition := HasTypeUnion.RenameRespectsContext.consTwice
                    natTypeCell (RawTerm.weaken resultType) condition
                  have stepRenamed := ihPremises _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                    _ (iterateLiftRaw rawRenaming 2) stepCondition
                  rw [rename_iterateLift_one_weaken_commute, rename_natTypeCell,
                    rename_iterateLift_two_weakenAbbrev_commute] at stepRenamed
                  exact stepRenamed
              | tail _ hmem => cases hmem
      -- natRec: the dependent recursor twin of natElim (same substrate, `natRecCell`).
      · match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
          .childCons resultType .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (natRecCell motive baseBranch stepBranch scrutinee))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_natRecCell]
          refine HasTypeUnion.elim targetContext .gen_natRec natRecElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))))
            (RawTermChildren.rename rawRenaming (.childCons resultType .childNil)) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  have stepCondition := HasTypeUnion.RenameRespectsContext.consTwice
                    natTypeCell (RawTerm.weaken resultType) condition
                  have stepRenamed := ihPremises _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                    _ (iterateLiftRaw rawRenaming 2) stepCondition
                  rw [rename_iterateLift_one_weaken_commute, rename_natTypeCell,
                    rename_iterateLift_two_weakenAbbrev_commute] at stepRenamed
                  exact stepRenamed
              | tail _ hmem => cases hmem
      -- boolElim: two-branch match; motive under one lift, both branches at the result type.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (boolElimCell motive scrutinee thenBranch elseBranch))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_boolElimCell]
          refine HasTypeUnion.elim targetContext .gen_boolElim boolElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)))) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              exact ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  exact ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                    targetContext rawRenaming condition
              | tail _ hmem => cases hmem
      -- optionMatch: the Some handler classifier is the non-dependent arrow `A → C`.
      · match args, params with
        | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (optionMatchCell motive noneBranch someBranch scrutinee))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_optionMatchCell]
          refine HasTypeUnion.elim targetContext .gen_optionMatch optionMatchElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)))) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have scrutineeRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_optionTypeCell] at scrutineeRenamed
              exact scrutineeRenamed
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  have someRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_nonDependentArrow] at someRenamed
                  exact someRenamed
              | tail _ hmem => cases hmem
      -- eitherMatch: both handler classifiers are non-dependent arrows.
      · match args, params with
        | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (eitherMatchCell motive leftBranch rightBranch scrutinee))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_eitherMatchCell]
          refine HasTypeUnion.elim targetContext .gen_eitherMatch eitherMatchElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)))) rfl ?_
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
                rw [rename_nonDependentArrow] at leftRenamed
                exact leftRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have rightRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_nonDependentArrow] at rightRenamed
                  exact rightRenamed
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
              (.childCons typeCode (.childCons endpoint (.childCons resultType .childNil)))) rfl ?_
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
              (.childCons firstType (.childCons secondType .childNil))) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have pairRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_productTypeCell] at pairRenamed
              exact pairRenamed
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
              (.childCons firstType (.childCons secondType .childNil))) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have pairRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_productTypeCell] at pairRenamed
              exact pairRenamed
          | tail _ hmem => cases hmem
      -- listElim: the scrutinee is at `List(A)`; the cons branch is the step function `A → List A → C → C`.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
          .childCons elementType (.childCons resultType .childNil) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (listElimCell motive scrutinee nilBranch consBranch))
            (RawTerm.rename rawRenaming resultType)
          rw [rename_listElimCell]
          refine HasTypeUnion.elim targetContext .gen_listElim listElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))))
            (RawTermChildren.rename rawRenaming
              (.childCons elementType (.childCons resultType .childNil))) rfl ?_
          intro obligation hmem
          cases hmem with
          | head =>
              have scrutineeRenamed :=
                ihPremises _ (List.Mem.head _) targetContext rawRenaming condition
              rw [rename_listTypeCell] at scrutineeRenamed
              exact scrutineeRenamed
          | tail _ hmem => cases hmem with
            | head =>
                exact ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext rawRenaming condition
            | tail _ hmem => cases hmem with
              | head =>
                  have consRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_listStepFunctionType] at consRenamed
                  exact consRenamed
              | tail _ hmem => cases hmem
  | gradedBinderIntro context generator rule typeParamA typeParamB body domainLevel codomainLevel flag
      isIntro binderGraded _domainFormed _classifierFormed _bodyTyped domainIH classifierIH bodyIH =>
      intro targetScope targetContext rawRenaming condition
      have liftedCondition :
          HasTypeUnion.RenameRespectsContext
            (context.cons (rule.domainCell _ typeParamA))
            (targetContext.cons (RawTerm.rename rawRenaming (rule.domainCell _ typeParamA)))
            (iterateLiftRaw rawRenaming 1) :=
        renameContextCondition_cons (rule.domainCell _ typeParamA) rawRenaming condition
      have bodyRenamed := bodyIH (targetContext.cons
        (RawTerm.rename rawRenaming (rule.domainCell _ typeParamA)))
        (iterateLiftRaw rawRenaming 1) liftedCondition
      have binderGradedRenamed :
          gradedBinderChecks rule.binderUsage (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) :=
        gradedBinderChecks_rename_lift rule.binderUsage rawRenaming body binderGraded
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        obtain rfl : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        have domainRenamed := domainIH rfl targetContext rawRenaming condition
        rw [rename_universeCodeCell] at domainRenamed
        have classifierRenamed := classifierIH rfl (targetContext.cons
          (RawTerm.rename rawRenaming typeParamA)) (iterateLiftRaw rawRenaming 1) liftedCondition
        rw [rename_universeCodeCell] at classifierRenamed
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (lamCell typeParamA body))
          (RawTerm.rename rawRenaming (piTyCodeCell typeParamA typeParamB))
        rw [show RawTerm.rename rawRenaming (lamCell typeParamA body)
              = lamCell (RawTerm.rename rawRenaming typeParamA)
                  (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) from rfl,
          rename_piTyCodeCell]
        exact HasTypeUnion.gradedBinderIntro targetContext .gen_lam lamGradedIntroRule
          (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) typeParamB)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) body)
          domainLevel codomainLevel flag rfl binderGradedRenamed
          (fun _ => domainRenamed) (fun _ => classifierRenamed) bodyRenamed
      · subst hPath
        obtain rfl : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        rw [show pathLamGradedIntroRule.bodyClassifier _ typeParamA typeParamB
              = RawTerm.weaken typeParamA from rfl, rename_iterateLift_one_weaken_commute] at bodyRenamed
        show HasTypeUnion profile targetContext
          (RawTerm.rename rawRenaming (pathLamCell body))
          (RawTerm.rename rawRenaming
            (bridgeTypeCell typeParamA (RawTerm.subst0 body intervalZeroCell)
              (RawTerm.subst0 body intervalOneCell)))
        rw [rename_pathLamCell, rename_bridgeTypeCell, RawTerm.rename_subst0_commute,
          RawTerm.rename_subst0_commute]
        exact HasTypeUnion.gradedBinderIntro targetContext .gen_pathLam pathLamGradedIntroRule
          (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) typeParamB)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) body)
          domainLevel codomainLevel flag rfl binderGradedRenamed
          (fun gateHolds => Bool.noConfusion gateHolds)
          (fun gateHolds => Bool.noConfusion gateHolds) bodyRenamed

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
