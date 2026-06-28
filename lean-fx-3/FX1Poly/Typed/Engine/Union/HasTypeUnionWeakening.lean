import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility
import FX1Poly.Typed.Cell.UnionCellSubstitution
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Tier0.Term.Subst.RawTermOccurrenceSubst

/-! # FX1Poly/Typed/HasTypeUnionWeakening — the RENAMING / WEAKENING lemma for the 6-arm native
    union (the de-Bruijn-insertion twin of `HasTypeUnion.substRespectingContext`)

`HasTypeUnion` is preserved along ANY renaming respecting the context — the structural mirror of the
union substitution lemma with a RENAMING in place of the substitution.  Proved directly over the
NATIVE judgment: the master reflects its `HasTypeUnion` input through `toNativeOnly` and inducts on the
`ofGrown`-free `HasTypeUnionNativeOnly`, so no host-engine `renameRespectingContext` is invoked.

## The renaming-respects-context discipline (the EQUALITY carrier)

`renameRespectingContext` is preserved along any renaming whose looked-up image equals the target's
looked-up binding (`RawTerm.rename rawRenaming (sourceContext.lookup index) = targetContext.lookup
(rawRenaming index)`).

## How the 6 native arms discharge (the post-TYTAB-1-collapse native arm set)

  * The STRUCTURAL LEAVES `var` and `universeFormation` reconstruct directly: `var` renames its subject
    by `rename_variableCell` and its classifier by the context condition, then re-applies
    `HasTypeUnion.var`; `universeFormation` renames both universe codes to themselves
    (`rename_universeCodeCell`) and re-applies `HasTypeUnion.universeFormation`.
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

`renameRespectingContext` is `induction` over the 6 native arms + the cell-rename `rfl` commutations +
the per-rule `rename_subst0_commute` reshapes + the lifted-occurrence preservation + the table rename
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
renames to the target's looked-up binding.  The lookup component IS the grown engine's carrier; the
ACCESSIBILITY component (A1-CONJUNCT-WIRE substrate) additionally demands the renaming preserve every
binding's modality-accessibility (a `lockCons`-bound dimension stays non-fibrantly-accessible at its image).
Accessibility is NOT recoverable from the lookup component (that constrains looked-up TYPES; accessibility is
a structural property of the lock spine, `isFibrantlyAccessibleAt`), so it is bundled as a second conjunct —
this is exactly what the intro arm's use-site usability conjunct needs to transport under the renaming. -/
abbrev HasTypeUnion.RenameRespectsContext {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope) : Prop :=
  (∀ index : Fin sourceScope,
    RawTerm.rename rawRenaming (sourceContext.lookup index)
      = targetContext.lookup (rawRenaming index)) ∧
  (∀ (modality : ObligationModality) (index : Fin sourceScope),
    sourceContext.isAccessibleAtModality index modality = true →
    targetContext.isAccessibleAtModality (rawRenaming index) modality = true)

-- `HasTypeUnion.RenameRespectsContext.cons` / `.lockCons` / `.consTwice` — the single- and double-binder
-- lifts of the (now bundled) renaming context-condition — are defined just below the
-- accessibility-preservation lemmas (`accessibilityAtModalityPreservedUnder*`), since the bundled lift must
-- transport BOTH the lookup component AND the accessibility component, and the latter lemmas are stated there.

/-! ## Accessibility-preservation under renaming — the Fitch var-arm-flip prerequisites

Once the variable typing arm is gated by `isFibrantlyAccessibleAt` (the FitchTT affine-lock discipline,
A1-SR-STRUCTURAL), the renaming/weakening master must re-derive the accessibility side condition in the TARGET
context.  Accessibility is NOT recoverable from the lookup context-condition (that constrains looked-up TYPES,
not the lock STRUCTURE), so it must be transported separately.  These three lemmas supply exactly that transport:
weakening into a fresh `cons`/`lockCons` preserves accessibility verbatim (the affine lock is CX/EXTEND, so it is
transparent to an ambient variable's suffix-lock), and a context-respecting accessibility map lifts across a
binder.  Pure facts about `isFibrantlyAccessibleAt` and `RawRenaming.lift`/`weaken`; consumed when the var arm
carries its `isAccessible` field. -/

/-- Weakening into a fresh ordinary binder preserves fibrant accessibility: `RawRenaming.weaken index` is
`Fin.succ index`, and `(context.cons _).isFibrantlyAccessibleAt (Fin.succ index)` recurses (`cons_succ`) to
`context.isFibrantlyAccessibleAt index`.  The accessibility leg `weakenUnderBinding` consumes after the flip. -/
theorem accessibilityPreservedUnderWeakenCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (newBinding : RawTerm scope)
    (index : Fin scope) (accessible : context.isFibrantlyAccessibleAt index = true) :
    (context.cons newBinding).isFibrantlyAccessibleAt (RawRenaming.weaken index) = true := by
  obtain ⟨indexValue, indexBound⟩ := index
  exact accessible

/-- Weakening into a fresh affine dimension lock preserves fibrant accessibility — an ambient variable stays
accessible behind the lock (CX/EXTEND transparency, `locks(Gamma, i :^mu A) = locks(Gamma)`).  The `lockCons`
twin of `accessibilityPreservedUnderWeakenCons`; the leg `weakenUnderLockBinding` consumes after the flip. -/
theorem accessibilityPreservedUnderWeakenLockCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (dimensionType : RawTerm scope)
    (index : Fin scope) (accessible : context.isFibrantlyAccessibleAt index = true) :
    (context.lockCons dimensionType).isFibrantlyAccessibleAt (RawRenaming.weaken index) = true := by
  obtain ⟨indexValue, indexBound⟩ := index
  exact accessible

/-- **★ Accessibility-preservation lifts across a binder.**  If `rawRenaming` carries every fibrantly-accessible
source variable to a fibrantly-accessible target variable, then its single lift (`iterateLiftRaw rawRenaming 1`)
does the same for the contexts extended by a fresh `cons`: the fresh `var 0` maps to `var 0` (accessible by
`cons_zero` on both sides), and a deeper variable threads through the base map (`cons_succ` on both sides, the
lift sending `k + 1` to `succ (rawRenaming k)`).  The binder-crossing companion to `renameContextCondition_cons`
on the accessibility component — the lemma the `renameRespectingContext` var arm consumes once it is
accessibility-gated. -/
theorem accessibilityPreservedUnderLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (renamedDomain : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope}
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isFibrantlyAccessibleAt index = true →
        targetContext.isFibrantlyAccessibleAt (rawRenaming index) = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.cons domainCode).isFibrantlyAccessibleAt index = true →
      (targetContext.cons renamedDomain).isFibrantlyAccessibleAt
        (iterateLiftRaw rawRenaming 1 index) = true := by
  intro index accessibleInExtended
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero => rfl
  | succ priorValue =>
      exact accessPreserved ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ accessibleInExtended

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

/-! ### Dimensional + subject-level transport — the genuine `.dimensional` discipline's renaming kit (A1-WEAKEN-RENAME)

The three lemmas above transport FIBRANT accessibility (`isFibrantlyAccessibleAt`).  The genuine `.dimensional`
check (`isDimensionallyAccessibleAt`, the lockCons-gated dual that replaced the degenerate `.dimensional -> true`)
needs the SAME transport, and the use-site conjunct the three table arms carry is phrased at the SUBJECT level
(`isSubjectUsableAtModality`), so threading it through a renamed derivation needs a subject-level transport that
dispatches the var / non-var split.  These four lemmas complete the kit: the dimensional duals of the three
fibrant transports, then the headline `subjectUsabilityPreservedUnderRename` that lifts ANY modality-accessibility
transport to the subject level. -/

/-- Dimensional dual of `accessibilityPreservedUnderWeakenCons`: weakening into a fresh ordinary `cons` preserves
DIMENSIONAL accessibility verbatim — `RawRenaming.weaken index` is `Fin.succ index`, and the `cons`-succ arm of
`isDimensionallyAccessibleAt` recurses to the ambient check (the lock suffix is untouched). -/
theorem dimensionalAccessibilityPreservedUnderWeakenCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (newBinding : RawTerm scope)
    (index : Fin scope) (accessible : context.isDimensionallyAccessibleAt index = true) :
    (context.cons newBinding).isDimensionallyAccessibleAt (RawRenaming.weaken index) = true := by
  obtain ⟨indexValue, indexBound⟩ := index
  exact accessible

/-- Dimensional dual of `accessibilityPreservedUnderWeakenLockCons`: weakening into a fresh affine dimension lock
preserves DIMENSIONAL accessibility — an ambient dimension variable stays dimensionally accessible behind a
further lock (CX/EXTEND transparency, `locks(Gamma, i :^mu A) = locks(Gamma)`). -/
theorem dimensionalAccessibilityPreservedUnderWeakenLockCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (dimensionType : RawTerm scope)
    (index : Fin scope) (accessible : context.isDimensionallyAccessibleAt index = true) :
    (context.lockCons dimensionType).isDimensionallyAccessibleAt (RawRenaming.weaken index) = true := by
  obtain ⟨indexValue, indexBound⟩ := index
  exact accessible

/-- **★ Dimensional accessibility lifts across a binder.**  The dimensional dual of
`accessibilityPreservedUnderLift`: under a `cons`-lift, the fresh `var 0` is NOT dimensionally accessible
(`cons`-zero is `false`), so the zero case is vacuous (its hypothesis is `false = true`); a deeper variable
threads through the base dimensional map.  The binder-crossing transport a renamed derivation's dimensional
obligations (e.g. `pathApp`'s interval argument) consume. -/
theorem dimensionalAccessibilityPreservedUnderLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (renamedDomain : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope}
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isDimensionallyAccessibleAt index = true →
        targetContext.isDimensionallyAccessibleAt (rawRenaming index) = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.cons domainCode).isDimensionallyAccessibleAt index = true →
      (targetContext.cons renamedDomain).isDimensionallyAccessibleAt
        (iterateLiftRaw rawRenaming 1 index) = true := by
  intro index accessibleInExtended
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      have reduced : (false : Bool) = true := accessibleInExtended
      exact Bool.noConfusion reduced
  | succ priorValue =>
      exact accessPreserved ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ accessibleInExtended

/-- **Fibrant accessibility lifts across a LOCK binder.**  The `lockCons` twin of
`accessibilityPreservedUnderLift`: under a `lockCons`-lift the fresh `var 0` is NOT fibrantly accessible
(`isFibrantlyAccessibleAt` on `lockCons`-zero is `false`, `dimensionIsNotFibrantlyAccessible`), so the zero case
is vacuous; a deeper variable threads the base map.  The transport the renamed `pathLam` body — typed under the
dimension lock once `pathLam` binds `lockCons` (#1789) — consumes for its FIBRANT leaf obligations. -/
theorem accessibilityPreservedUnderLockConsLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (renamedDimensionType : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope}
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isFibrantlyAccessibleAt index = true →
        targetContext.isFibrantlyAccessibleAt (rawRenaming index) = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.lockCons dimensionType).isFibrantlyAccessibleAt index = true →
      (targetContext.lockCons renamedDimensionType).isFibrantlyAccessibleAt
        (iterateLiftRaw rawRenaming 1 index) = true := by
  intro index accessibleInExtended
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      have reduced : (false : Bool) = true := accessibleInExtended
      exact Bool.noConfusion reduced
  | succ priorValue =>
      exact accessPreserved ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ accessibleInExtended

/-- **★ Dimensional accessibility lifts across a LOCK binder.**  The `lockCons` twin of
`dimensionalAccessibilityPreservedUnderLift`: under a `lockCons`-lift the fresh `var 0` IS dimensionally
accessible (`isDimensionallyAccessibleAt` on `lockCons`-zero is `true` — it is the locked dimension itself), so the
zero case is `rfl` on both sides; a deeper variable threads the base map.  The transport a renamed dimension
variable bound by an outer `pathLam` lock consumes for a DIMENSIONAL obligation (`pathApp`'s interval argument). -/
theorem dimensionalAccessibilityPreservedUnderLockConsLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (renamedDimensionType : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope}
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isDimensionallyAccessibleAt index = true →
        targetContext.isDimensionallyAccessibleAt (rawRenaming index) = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.lockCons dimensionType).isDimensionallyAccessibleAt index = true →
      (targetContext.lockCons renamedDimensionType).isDimensionallyAccessibleAt
        (iterateLiftRaw rawRenaming 1 index) = true := by
  intro index accessibleInExtended
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero => rfl
  | succ priorValue =>
      exact accessPreserved ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ accessibleInExtended

/-- **★ Subject-usability transports along a modal-accessibility-preserving renaming (the headline #1796).**  The
use-site conjunct's predicate `isSubjectUsableAtModality` (the SUBJECT-level lift of `isAccessibleAtModality`)
survives any renaming that preserves accessibility AT THAT MODALITY.  A bare variable subject threads through
`accessPreserved` (its index renamed, its accessibility transported); a non-variable subject's head generator is
preserved by `rename` (`rename_mkGen_of_ne_var`), so it stays unconditionally usable (the modality-independent
`else true` branch via `isSubjectUsableAtModality_ofNonVarHead`).  The lemma the renamed-derivation master invokes
to carry each obligation's usability witness into the target context. -/
theorem subjectUsabilityPreservedUnderRename {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (rawRenaming : RawRenaming sourceScope targetScope) (modality : ObligationModality)
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true)
    (subject : RawTerm sourceScope)
    (usable : sourceContext.isSubjectUsableAtModality subject modality = true) :
    targetContext.isSubjectUsableAtModality (RawTerm.rename rawRenaming subject) modality = true := by
  cases subject with
  | mkGen generator payload children =>
      by_cases generatorIsVar : generator = Generator.gen_var
      · subst generatorIsVar
        cases children
        rw [isSubjectUsableAtModality_var] at usable
        change targetContext.isSubjectUsableAtModality
          (RawTerm.rename rawRenaming (variableCell payload)) modality = true
        rw [rename_variableCell]
        change targetContext.isSubjectUsableAtModality
          (RawTerm.mkGen .gen_var (rawRenaming payload) .childNil) modality = true
        rw [isSubjectUsableAtModality_var]
        exact accessPreserved payload usable
      · rw [RawTerm.rename_mkGen_of_ne_var rawRenaming generatorIsVar]
        exact isSubjectUsableAtModality_ofNonVarHead targetContext generator _ _ modality generatorIsVar

/-! ### Modality-dispatched binder-crossing transport — the conjunct-wire's `cons` / `lockCons` glue (A1-WEAKEN-RENAME)

The four binder-lift lemmas above transport accessibility one modality at a time (`isFibrantlyAccessibleAt` /
`isDimensionallyAccessibleAt`).  The use-site conjunct the three table arms carry is phrased at the unified
`isAccessibleAtModality`, so a binder-crossing obligation (a graded binder's body / codomain at `cons`, the
`pathLam` body at `lockCons`) needs the lift AT WHATEVER modality the obligation declares.  `isAccessibleAtModality`
is a `match` on the modality, so a single `cases modality` dispatches each unified lift to its fibrant / dimensional
half.  The two subject-level corollaries then compose the dispatched lift with `subjectUsabilityPreservedUnderRename`,
giving the exact `cons` / `lockCons` subject-usability transport the conjunct-wire's obligation drift consumes. -/

/-- **★ Modality-dispatched accessibility lift across a `cons` binder.**  The `isAccessibleAtModality`-level glue
over `accessibilityPreservedUnderLift` (fibrant) and `dimensionalAccessibilityPreservedUnderLift` (dimensional):
a renaming preserving accessibility AT A GIVEN `modality` lifts across an ordinary `cons` binder at the SAME
modality.  `cases modality` reduces both the hypothesis and the goal to the matching half (the `match` on the
modality computes), so each branch is the corresponding single-modality transport. -/
theorem accessibilityAtModalityPreservedUnderLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (renamedDomain : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope} (modality : ObligationModality)
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.cons domainCode).isAccessibleAtModality index modality = true →
      (targetContext.cons renamedDomain).isAccessibleAtModality
        (iterateLiftRaw rawRenaming 1 index) modality = true := by
  cases modality with
  | fibrant => exact accessibilityPreservedUnderLift domainCode renamedDomain accessPreserved
  | dimensional => exact dimensionalAccessibilityPreservedUnderLift domainCode renamedDomain accessPreserved

/-- **★ Modality-dispatched accessibility lift across a `lockCons` (affine dimension lock) binder.**  The
`isAccessibleAtModality`-level glue over `accessibilityPreservedUnderLockConsLift` (fibrant) and
`dimensionalAccessibilityPreservedUnderLockConsLift` (dimensional): a renaming preserving accessibility at a
`modality` lifts across the dimension lock at that SAME modality.  Same `cases modality` dispatch; the fresh
`var 0` is dimensionally accessible (the locked dimension) but NOT fibrantly accessible.  The transport the renamed
`pathLam` body's obligation consumes. -/
theorem accessibilityAtModalityPreservedUnderLockConsLift {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (renamedDimensionType : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope} (modality : ObligationModality)
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.lockCons dimensionType).isAccessibleAtModality index modality = true →
      (targetContext.lockCons renamedDimensionType).isAccessibleAtModality
        (iterateLiftRaw rawRenaming 1 index) modality = true := by
  cases modality with
  | fibrant =>
      exact accessibilityPreservedUnderLockConsLift dimensionType renamedDimensionType accessPreserved
  | dimensional =>
      exact dimensionalAccessibilityPreservedUnderLockConsLift dimensionType renamedDimensionType
        accessPreserved

/-- **★ Modality-dispatched accessibility preservation under WEAKENING into a fresh `cons` binder.**  The
`isAccessibleAtModality`-level glue over `accessibilityPreservedUnderWeakenCons` (fibrant) and
`dimensionalAccessibilityPreservedUnderWeakenCons` (dimensional): weakening into a fresh ordinary binder preserves
accessibility at a given modality (an ambient variable stays accessible behind the new binding, `RawRenaming.weaken
index = Fin.succ index` threading through `cons`-succ on both modality legs).  The subst-side `cons`-lift's
deeper-variable image (`RawTermSubst.lift σ` sends `k+1` to `RawTerm.weaken (σ k)`) consumes this to weaken the
substituent image past the fresh bound variable. -/
theorem accessibilityAtModalityPreservedUnderWeakenCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (newBinding : RawTerm scope)
    (modality : ObligationModality) (index : Fin scope)
    (accessible : context.isAccessibleAtModality index modality = true) :
    (context.cons newBinding).isAccessibleAtModality (RawRenaming.weaken index) modality = true := by
  cases modality with
  | fibrant => exact accessibilityPreservedUnderWeakenCons context newBinding index accessible
  | dimensional => exact dimensionalAccessibilityPreservedUnderWeakenCons context newBinding index accessible

/-- **★ Modality-dispatched accessibility preservation under WEAKENING into a fresh `lockCons` (affine dimension
lock) binder.**  The `lockCons` twin of `accessibilityAtModalityPreservedUnderWeakenCons`, dispatching over
`accessibilityPreservedUnderWeakenLockCons` (fibrant) and `dimensionalAccessibilityPreservedUnderWeakenLockCons`
(dimensional): an ambient variable stays accessible at its modality behind a further dimension lock (CX/EXTEND
transparency, `locks(Gamma, i :^mu A) = locks(Gamma)`).  The subst-side `lockCons`-lift's deeper-variable image
consumes this. -/
theorem accessibilityAtModalityPreservedUnderWeakenLockCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (dimensionType : RawTerm scope)
    (modality : ObligationModality) (index : Fin scope)
    (accessible : context.isAccessibleAtModality index modality = true) :
    (context.lockCons dimensionType).isAccessibleAtModality (RawRenaming.weaken index) modality = true := by
  cases modality with
  | fibrant => exact accessibilityPreservedUnderWeakenLockCons context dimensionType index accessible
  | dimensional =>
      exact dimensionalAccessibilityPreservedUnderWeakenLockCons context dimensionType index accessible

/-! ### The bundled context-condition lifts (A1-CONJUNCT-WIRE) — lookup AND accessibility together

`RenameRespectsContext` is now the conjunction of lookup-preservation and accessibility-preservation, so a
binder-crossing obligation needs BOTH conjuncts lifted.  These three wrappers replace the bare lookup-only
`renameContextCondition_cons` / `renameContextCondition_lockCons` at the union arms' cons/lockCons-crossing
sites: lookup via the shared bare lemma on `.1`, accessibility via the modality-dispatched lift on `.2`. -/

/-- **★ The bundled single-binder (`cons`) lift of the renaming context-condition.** -/
theorem HasTypeUnion.RenameRespectsContext.cons {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (bindingType : RawTerm sourceScope)
    (rawRenaming : RawRenaming sourceScope targetScope)
    (condition : HasTypeUnion.RenameRespectsContext sourceContext targetContext rawRenaming) :
    HasTypeUnion.RenameRespectsContext (sourceContext.cons bindingType)
      (targetContext.cons (RawTerm.rename rawRenaming bindingType))
      (iterateLiftRaw rawRenaming 1) :=
  ⟨renameContextCondition_cons bindingType rawRenaming condition.1,
   fun modality => accessibilityAtModalityPreservedUnderLift bindingType
     (RawTerm.rename rawRenaming bindingType) modality (condition.2 modality)⟩

/-- **★ The bundled `lockCons` (affine dimension lock) single-binder lift.** -/
theorem HasTypeUnion.RenameRespectsContext.lockCons {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope)
    (rawRenaming : RawRenaming sourceScope targetScope)
    (condition : HasTypeUnion.RenameRespectsContext sourceContext targetContext rawRenaming) :
    HasTypeUnion.RenameRespectsContext (sourceContext.lockCons dimensionType)
      (targetContext.lockCons (RawTerm.rename rawRenaming dimensionType))
      (iterateLiftRaw rawRenaming 1) :=
  ⟨renameContextCondition_lockCons dimensionType rawRenaming condition.1,
   fun modality => accessibilityAtModalityPreservedUnderLockConsLift dimensionType
     (RawTerm.rename rawRenaming dimensionType) modality (condition.2 modality)⟩

/-- The two-binder lift (the recursiveElim / idJ step-branch shape): the double `.cons` of a bundled
renaming context-condition.  An iterate of `RenameRespectsContext.cons`. -/
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
  HasTypeUnion.RenameRespectsContext.cons innerType (iterateLiftRaw rawRenaming 1)
    (HasTypeUnion.RenameRespectsContext.cons outerType rawRenaming condition)

/-- **★ Subject usability transports across a `cons` binder.**  Composes the modality-dispatched `cons`-lift with
`subjectUsabilityPreservedUnderRename` at the lifted renaming: a subject usable at `modality` under
`sourceContext.cons domainCode` stays usable under `targetContext.cons renamedDomain` after renaming by the lift.
The exact transport a graded binder's body / codomain obligation (lam) needs once the conjunct is wired. -/
theorem subjectUsabilityPreservedUnderConsLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (renamedDomain : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope} (modality : ObligationModality)
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true)
    (subject : RawTerm (sourceScope + 1))
    (usable : (sourceContext.cons domainCode).isSubjectUsableAtModality subject modality = true) :
    (targetContext.cons renamedDomain).isSubjectUsableAtModality
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) subject) modality = true :=
  subjectUsabilityPreservedUnderRename (iterateLiftRaw rawRenaming 1) modality
    (accessibilityAtModalityPreservedUnderLift domainCode renamedDomain modality accessPreserved)
    subject usable

/-- **★ Subject usability transports across a `lockCons` (affine dimension lock) binder.**  The `pathLam`-body twin
of `subjectUsabilityPreservedUnderConsLift`: composes the dispatched `lockCons`-lift with
`subjectUsabilityPreservedUnderRename`.  The transport the renamed `pathLam` body's single obligation consumes once
the conjunct is wired (the body typed under `lockCons intervalTypeCell`). -/
theorem subjectUsabilityPreservedUnderLockConsLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (renamedDimensionType : RawTerm targetScope)
    {rawRenaming : RawRenaming sourceScope targetScope} (modality : ObligationModality)
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true)
    (subject : RawTerm (sourceScope + 1))
    (usable : (sourceContext.lockCons dimensionType).isSubjectUsableAtModality subject modality = true) :
    (targetContext.lockCons renamedDimensionType).isSubjectUsableAtModality
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) subject) modality = true :=
  subjectUsabilityPreservedUnderRename (iterateLiftRaw rawRenaming 1) modality
    (accessibilityAtModalityPreservedUnderLockConsLift dimensionType renamedDimensionType modality
      accessPreserved)
    subject usable

/-- **★ Subject usability transports across TWO `cons` binders.**  The double-`cons` companion to
`subjectUsabilityPreservedUnderConsLift` (the natElim / natRec step-branch and idJ-motive shape, at
`sourceScope + 2`): iterate the single-`cons` lift, exactly as `RenameRespectsContext.consTwice` iterates
`RenameRespectsContext.cons`.  The transport a two-binder eliminator obligation consumes once the elim arm's
use-site conjunct is wired into the weakening master. -/
theorem subjectUsabilityPreservedUnderConsTwiceLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    (renamedOuter : RawTerm targetScope) (renamedInner : RawTerm (targetScope + 1))
    {rawRenaming : RawRenaming sourceScope targetScope} (modality : ObligationModality)
    (accessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true)
    (subject : RawTerm (sourceScope + 2))
    (usable : ((sourceContext.cons outerType).cons innerType).isSubjectUsableAtModality
        subject modality = true) :
    ((targetContext.cons renamedOuter).cons renamedInner).isSubjectUsableAtModality
        (RawTerm.rename (iterateLiftRaw rawRenaming 2) subject) modality = true :=
  subjectUsabilityPreservedUnderConsLift innerType renamedInner modality
    (accessibilityAtModalityPreservedUnderLift outerType renamedOuter modality accessPreserved)
    subject usable

/-- **★ The intro-rule obligation-USABILITY renaming push (A1-CONJUNCT-WIRE substrate).**  The use-site
conjunct's drift companion to `HasTypeUnion.renameRespectingContext`'s intro arm: if the SOURCE obligations of
an intro rule all satisfy the use-site usability conjunct (`isSubjectUsableAtModality`), and the renaming
preserves accessibility at every modality (`baseAccessPreserved`), then the RENAMED obligations (the rule fired
at the renamed children + renamed context) ALSO satisfy the conjunct.  Every intro obligation is FIBRANT (no
intro row declares a `.dimensional` position), so base obligations transport by
`subjectUsabilityPreservedUnderRename`, `lam`'s codomain/body (under `cons`) by
`subjectUsabilityPreservedUnderConsLift`, and `pathLam`'s body (under the affine `lockCons`) by
`subjectUsabilityPreservedUnderLockConsLift`.  The 17-row `introRuleOf_cases` enumeration mirrors the master's
per-former premise discharge; once the `intro` arm carries the conjunct as a field, the master discharges the
renamed conjunct by ONE call here, NOT per-former.  Zero-axiom: the per-row `cases` on the concrete obligation
list bottoms out in the shipped transports. -/
theorem IntroRule.obligationsUsable_pushRename {profile : PolyProfile} {generator : Generator}
    {rule : IntroRule} (isIntro : introRuleOf generator = some rule)
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope)
    (args : RawTermChildren rule.argShifts sourceScope)
    (params : RawTermChildren rule.paramShifts sourceScope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (baseAccessPreserved : ∀ (modality : ObligationModality) (index : Fin sourceScope),
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true)
    (sourceUsable : ∀ obligation ∈ rule.obligations sourceScope sourceContext args params level0 level1 flag,
        obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) :
    ∀ obligation ∈ rule.obligations targetScope targetContext
        (RawTermChildren.rename rawRenaming args) (RawTermChildren.rename rawRenaming params)
        level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- boolTrue / boolFalse / unit / interval0 / interval1 / natZero: no obligations.
  · match args, params with
    | .childNil, .childNil => intro obligation hmem; cases hmem
  · match args, params with
    | .childNil, .childNil => intro obligation hmem; cases hmem
  · match args, params with
    | .childNil, .childNil => intro obligation hmem; cases hmem
  · match args, params with
    | .childNil, .childNil => intro obligation hmem; cases hmem
  · match args, params with
    | .childNil, .childNil => intro obligation hmem; cases hmem
  · match args, params with
    | .childNil, .childNil => intro obligation hmem; cases hmem
  -- lam: domain (base) + codomain (cons) + body (cons).
  · match args, params with
    | .childCons domainCode (.childCons body .childNil), .childCons codomainCode .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            domainCode (sourceUsable _ (List.Mem.head _))
      | tail _ hmem =>
          cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderConsLift domainCode
                (RawTerm.rename rawRenaming domainCode) .fibrant (baseAccessPreserved .fibrant)
                codomainCode (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ hmem =>
              cases hmem with
              | head =>
                  exact subjectUsabilityPreservedUnderConsLift domainCode
                    (RawTerm.rename rawRenaming domainCode) .fibrant (baseAccessPreserved .fibrant)
                    body (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem
  -- pathLam: body (lockCons over the closed intervalTypeCell).
  · match args, params with
    | .childCons body .childNil, .childCons carrierCode .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderLockConsLift intervalTypeCell intervalTypeCell .fibrant
            (baseAccessPreserved .fibrant) body (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem
  -- natSucc: child (base).
  · match args, params with
    | .childCons child .childNil, .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            child (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem
  -- listCons: head (base) + tail (base).
  · match args, params with
    | .childCons consHead (.childCons consTail .childNil), .childCons elementType .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            consHead (sourceUsable _ (List.Mem.head _))
      | tail _ hmem =>
          cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                consTail (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ hmem => cases hmem
  -- optionSome: value (base).
  · match args, params with
    | .childCons value .childNil, .childCons typeParam0 .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            value (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem
  -- optionNone: free element-type formedness (base).
  · match args, params with
    | .childNil, .childCons typeParam0 .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            typeParam0 (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem
  -- listNil: the optionNone twin (free element-type formedness, base).
  · match args, params with
    | .childNil, .childCons typeParam0 .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            typeParam0 (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem
  -- eitherInl: value (base) + free-RIGHT formedness (base) + LEFT flag-coherence formedness (base).
  · match args, params with
    | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            value (sourceUsable _ (List.Mem.head _))
      | tail _ hmem =>
          cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                typeParam1 (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ hmem =>
              cases hmem with
              | head =>
                  exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant
                    (baseAccessPreserved .fibrant) typeParam0
                    (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem
  -- eitherInr: value (base) + free-LEFT formedness (base) + RIGHT flag-coherence formedness (base).
  · match args, params with
    | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            value (sourceUsable _ (List.Mem.head _))
      | tail _ hmem =>
          cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                typeParam1 (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ hmem =>
              cases hmem with
              | head =>
                  exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant
                    (baseAccessPreserved .fibrant) typeParam0
                    (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem
  -- pair: child0 + child1 + two flag-coherence formedness premises (all base).
  · match args, params with
    | .childCons child0 (.childCons child1 .childNil),
      .childCons typeParam0 (.childCons typeParam1 .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            child0 (sourceUsable _ (List.Mem.head _))
      | tail _ hmem =>
          cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                child1 (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ hmem =>
              cases hmem with
              | head =>
                  exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant
                    (baseAccessPreserved .fibrant) typeParam0
                    (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem =>
                  cases hmem with
                  | head =>
                      exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant
                        (baseAccessPreserved .fibrant) typeParam1
                        (sourceUsable _
                          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                  | tail _ hmem => cases hmem
  -- refl: witness (base).
  · match args, params with
    | .childCons witness .childNil, .childCons typeParam0 .childNil =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            witness (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem

/-- **★ The ELIM-rule obligation-USABILITY renaming push (A1-CONJUNCT-WIRE substrate, elim arm).**  The elim-arm
twin of `IntroRule.obligationsUsable_pushRename`: if the SOURCE obligations of an elim rule all satisfy the
use-site usability conjunct, and the renaming preserves accessibility at every modality, then the RENAMED
obligations (the rule fired at the renamed children + renamed context) ALSO satisfy it.  Every elim obligation is
FIBRANT EXCEPT `pathApp`'s interval argument (`.dimensional`, the bridge's core operation); the
`subjectUsabilityPreservedUnderRename` transport is modality-parametric, so the dimensional pathApp obligation
goes through `baseAccessPreserved .dimensional` while every other obligation goes through `... .fibrant`.  The
ambient obligations transport by `subjectUsabilityPreservedUnderRename`, the recursive eliminators' motive (under
one `cons`) by `subjectUsabilityPreservedUnderConsLift`, and natElim / natRec step + idJ motive (under two
binders) by `subjectUsabilityPreservedUnderConsTwiceLift`.  Once the `elim` arm carries the conjunct as a field,
the weakening master discharges it by ONE call here. -/
theorem ElimRule.obligationsUsable_pushRename {profile : PolyProfile} {generator : Generator}
    {rule : ElimRule} (isElim : elimRuleOf generator = some rule)
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope)
    (args : RawTermChildren rule.argShifts sourceScope)
    (params : RawTermChildren rule.paramShifts sourceScope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (baseAccessPreserved : ∀ (modality : ObligationModality) (index : Fin sourceScope),
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isAccessibleAtModality (rawRenaming index) modality = true)
    (sourceUsable : ∀ obligation ∈ rule.obligations sourceScope sourceContext args params level0 level1 flag,
        obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) :
    ∀ obligation ∈ rule.obligations targetScope targetContext
        (RawTermChildren.rename rawRenaming args) (RawTermChildren.rename rawRenaming params)
        level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  rcases elimRuleOf_cases isElim with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- app: function (base) + argument (base).
  · match args, params with
    | .childCons function (.childCons argument .childNil),
      .childCons domainCode (.childCons codomainCode .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            function (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              argument (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem
  -- pathApp: path (base/fibrant) + argument (base/DIMENSIONAL) + carrierCode (base/fibrant).
  · match args, params with
    | .childCons path (.childCons argument .childNil),
      .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            path (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .dimensional
              (baseAccessPreserved .dimensional) argument (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                carrierCode (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem
  -- natElim: scrutinee (base) + baseBranch (base) + stepBranch (consTwice) + motive (cons).
  · match args with
    | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            scrutinee (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              baseBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderConsTwiceLift natTypeCell motive
                (RawTerm.rename rawRenaming natTypeCell)
                (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive) .fibrant
                (baseAccessPreserved .fibrant) stepBranch
                (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsLift natTypeCell
                  (RawTerm.rename rawRenaming natTypeCell) .fibrant (baseAccessPreserved .fibrant)
                  motive (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem
  -- natRec: byte-identical to natElim (same obligation shape).
  · match args with
    | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            scrutinee (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              baseBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderConsTwiceLift natTypeCell motive
                (RawTerm.rename rawRenaming natTypeCell)
                (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive) .fibrant
                (baseAccessPreserved .fibrant) stepBranch
                (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsLift natTypeCell
                  (RawTerm.rename rawRenaming natTypeCell) .fibrant (baseAccessPreserved .fibrant)
                  motive (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem
  -- boolElim: scrutinee + thenBranch + elseBranch (base) + motive (cons).
  · match args with
    | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            scrutinee (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              thenBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                elseBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsLift boolTypeCell
                  (RawTerm.rename rawRenaming boolTypeCell) .fibrant (baseAccessPreserved .fibrant)
                  motive (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem
  -- optionMatch: scrutinee + noneBranch + someBranch (base) + motive (cons over optionTypeCell A).
  · match args, params with
    | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
      .childCons typeParamA (.childCons typeParamB .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            scrutinee (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              noneBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                someBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsLift (optionTypeCell typeParamA)
                  (RawTerm.rename rawRenaming (optionTypeCell typeParamA)) .fibrant
                  (baseAccessPreserved .fibrant) motive
                  (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem
  -- eitherMatch: scrutinee + leftBranch + rightBranch (base) + motive (cons over eitherTypeCell A B).
  · match args, params with
    | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
      .childCons typeParamA (.childCons typeParamB .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            scrutinee (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              leftBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                rightBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsLift (eitherTypeCell typeParamA typeParamB)
                  (RawTerm.rename rawRenaming (eitherTypeCell typeParamA typeParamB)) .fibrant
                  (baseAccessPreserved .fibrant) motive
                  (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem
  -- idJ: witness + rightEndpoint + baseCase (base) + motive (consTwice).
  · match args, params with
    | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
      .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            witness (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              rightEndpoint (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                baseCase (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsTwiceLift typeCode
                  (idJMotiveSecondBinderType typeCode leftEndpoint)
                  (RawTerm.rename rawRenaming typeCode)
                  (idJMotiveSecondBinderType (RawTerm.rename rawRenaming typeCode)
                    (RawTerm.rename rawRenaming leftEndpoint)) .fibrant
                  (baseAccessPreserved .fibrant) motive
                  (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem
  -- fst: pairTerm (base) + firstType (base).
  · match args, params with
    | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            pairTerm (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              firstType (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem
  -- snd: pairTerm (base) + secondType (base).
  · match args, params with
    | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            pairTerm (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              secondType (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem
  -- listElim: scrutinee + nilBranch + consBranch (base) + motive (cons over listTypeCell A).
  · match args, params with
    | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
      .childCons elementType (.childCons resultType .childNil) =>
      intro obligation hmem
      cases hmem with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
            scrutinee (sourceUsable _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head =>
            exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
              nilBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant (baseAccessPreserved .fibrant)
                consBranch (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem with
            | head =>
                exact subjectUsabilityPreservedUnderConsLift (listTypeCell elementType)
                  (RawTerm.rename rawRenaming (listTypeCell elementType)) .fibrant
                  (baseAccessPreserved .fibrant) motive
                  (sourceUsable _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
            | tail _ hmem => cases hmem

/-- A flat-family obligation list's use-site usability transports along a renaming.  Mirrors
`flatFormationObligations_pushRename` with the typing hypothesis replaced by a usability hypothesis (every flat
obligation is an ambient-context child, fibrant — transported by `subjectUsabilityPreservedUnderRename`). -/
theorem flatFormationObligations_usable_pushRename {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope} (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope) (flag : UniverseFlag)
    (baseAccessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isAccessibleAtModality (rawRenaming index) .fibrant = true) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope) (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ flatFormationObligations profile sourceContext flag children levels →
        sourceContext.isSubjectUsableAtModality subject .fibrant = true) →
      ∀ targetObligation ∈ flatFormationObligations profile targetContext flag
          (RawTermChildren.rename rawRenaming children) levels,
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children levels _sourceUsable targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children levels sourceUsable targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  cases targetMember with
                  | head =>
                      exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
                        childHead (sourceUsable childHead (universeCodeCell LevelExpr.lzero flag)
                          (List.Mem.head _))
                  | tail _ tailMember =>
                      exact ih childTail []
                        (fun subject classifier member =>
                          sourceUsable subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
              | cons headLevel restLevels =>
                  cases targetMember with
                  | head =>
                      exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
                        childHead (sourceUsable childHead (universeCodeCell headLevel flag) (List.Mem.head _))
                  | tail _ tailMember =>
                      exact ih childTail restLevels
                        (fun subject classifier member =>
                          sourceUsable subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
          | succ _ => cases targetMember

/-- A term-indexed endpoint obligation list's use-site usability transports along a renaming (every endpoint is
an ambient-context term, fibrant). -/
theorem termIndexedEndpointObligations_usable_pushRename {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope} (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope) (carrier : RawTerm sourceScope)
    (baseAccessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isAccessibleAtModality (rawRenaming index) .fibrant = true) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts sourceScope),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ termIndexedEndpointObligations profile sourceContext carrier children →
        sourceContext.isSubjectUsableAtModality subject .fibrant = true) →
      ∀ targetObligation ∈ termIndexedEndpointObligations profile targetContext
          (RawTerm.rename rawRenaming carrier) (RawTermChildren.rename rawRenaming children),
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _sourceUsable targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children sourceUsable targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases targetMember with
              | head =>
                  exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
                    childHead (sourceUsable childHead carrier (List.Mem.head _))
              | tail _ tailMember =>
                  exact ih childTail
                    (fun subject classifier member =>
                      sourceUsable subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ => cases targetMember

/-- A cumulative-family obligation list's use-site usability transports along a renaming.  The element / domain
obligations are ambient-context (transported by `subjectUsabilityPreservedUnderRename`); the Π / Σ binder-crossing
codomain (at `context.cons domain`) by `subjectUsabilityPreservedUnderConsLift`.  Same spine dispatch as
`cumulativeFormationObligations_pushRename`. -/
theorem cumulativeFormationObligations_usable_pushRename {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope} (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope) (flag : UniverseFlag)
    (baseAccessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isAccessibleAtModality (rawRenaming index) .fibrant = true) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope) (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        sourceContext.isSubjectUsableAtModality subject .fibrant = true) →
      (∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
        ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        (sourceContext.cons domain).isSubjectUsableAtModality subject .fibrant = true) →
      ∀ targetObligation ∈ cumulativeFormationObligations profile targetContext flag
          (RawTermChildren.rename rawRenaming children) levels,
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro binderShifts children levels baseUsable crossingUsable targetObligation targetMember
  match binderShifts, children, levels with
  | _, .childNil, _ => cases targetMember
  | _, .childCons (shift := 0) headChild .childNil, [] =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
            headChild (baseUsable headChild (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _))
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) headChild .childNil, elementLevel :: _ =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
            headChild (baseUsable headChild (universeCodeCell elementLevel flag) (List.Mem.head _))
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil),
      domainLevel :: codomainLevel :: _ =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
            domain (baseUsable domain (universeCodeCell domainLevel flag) (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact subjectUsabilityPreservedUnderConsLift domain (RawTerm.rename rawRenaming domain)
                .fibrant baseAccessPreserved codomain
                (crossingUsable domain codomain (universeCodeCell codomainLevel flag)
                  (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [] =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
            domain (baseUsable domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact subjectUsabilityPreservedUnderConsLift domain (RawTerm.rename rawRenaming domain)
                .fibrant baseAccessPreserved codomain
                (crossingUsable domain codomain (universeCodeCell LevelExpr.lzero flag)
                  (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [_] =>
      cases targetMember with
      | head =>
          exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
            domain (baseUsable domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact subjectUsabilityPreservedUnderConsLift domain (RawTerm.rename rawRenaming domain)
                .fibrant baseAccessPreserved codomain
                (crossingUsable domain codomain (universeCodeCell LevelExpr.lzero flag)
                  (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 1) _ (.childCons _ _)), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 0) _ _), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := _ + 2) _ _), _ => cases targetMember
  | _, .childCons (shift := _ + 1) _ _, _ => cases targetMember

/-- **★ The unified FORMATION-rule obligation-USABILITY renaming push (A1-CONJUNCT-WIRE substrate, formation
arm).**  The formation-arm twin of `IntroRule.obligationsUsable_pushRename` / `ElimRule.obligationsUsable_pushRename`:
the source obligations' use-site usability transports along a renaming.  Every formation obligation is FIBRANT, so
base obligations transport by `subjectUsabilityPreservedUnderRename` and the Π / Σ codomain (under `cons`) by
`subjectUsabilityPreservedUnderConsLift`.  Two source-usability clauses keyed exactly as
`FormationRule.obligations_pushRename`'s `baseTypings` / `crossingTypings`. -/
theorem FormationRule.obligationsUsable_pushRename {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rule : FormationRule) {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope)
    {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
    (levels : List LevelExpr) (carrier : RawTerm sourceScope) (level : LevelExpr) (flag : UniverseFlag)
    (baseAccessPreserved : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index .fibrant = true →
        targetContext.isAccessibleAtModality (rawRenaming index) .fibrant = true)
    (baseUsable : ∀ (subject classifier : RawTerm sourceScope),
      ({ scope := sourceScope, context := sourceContext, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      sourceContext.isSubjectUsableAtModality subject .fibrant = true)
    (crossingUsable : ∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
      ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      (sourceContext.cons domain).isSubjectUsableAtModality subject .fibrant = true) :
    ∀ targetObligation ∈ rule.obligations profile targetContext
        (RawTermChildren.rename rawRenaming children) levels
        (RawTerm.rename rawRenaming carrier) level flag,
      targetObligation.context.isSubjectUsableAtModality targetObligation.subject
        targetObligation.modality = true := by
  cases rule with
  | baseType baseRule =>
      intro targetObligation targetMember
      cases targetMember
  | flat flatRule =>
      exact flatFormationObligations_usable_pushRename targetContext rawRenaming flag baseAccessPreserved
        children levels baseUsable
  | cumulative cumulativeRule =>
      exact cumulativeFormationObligations_usable_pushRename targetContext rawRenaming flag
        baseAccessPreserved children levels baseUsable crossingUsable
  | termIndexed termRule =>
      cases children with
      | childNil =>
          intro targetObligation targetMember
          cases targetMember
      | childCons carrierHead rest =>
          rename_i carrierShift _restShifts
          cases carrierShift with
          | zero =>
              intro targetObligation targetMember
              cases targetMember with
              | head =>
                  exact subjectUsabilityPreservedUnderRename rawRenaming .fibrant baseAccessPreserved
                    carrierHead (baseUsable carrierHead (universeCodeCell level flag) (List.Mem.head _))
              | tail _ tailMember =>
                  exact termIndexedEndpointObligations_usable_pushRename targetContext rawRenaming carrier
                    baseAccessPreserved rest
                    (fun subject classifier member =>
                      baseUsable subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ =>
              intro targetObligation targetMember
              cases targetMember

/-- **★ The pointwise renaming / weakening lemma over the native union.**  Proved over the native judgment (input reflected through
`toNativeOnly`).  By `induction` over the 6 native arms: the `var` / `universeFormation` structural
leaves reconstruct directly through their cell-rename commutations; the `formationRule` arm renames its
premise telescope and reconstructs the abstract cell; the recursive `intro` / `elim` arms recurse via the
IHs over their rule obligations with `RawRenaming.lift` crossing binders; the `intro` arm transports the
affine binder check by the lifted-occurrence preservation; the `conv` arm transports the conversion
through `Conv.rename`.  The de-Bruijn-insertion twin of `HasTypeUnion.substRespectingContext`. -/
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
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var context index isAccessible =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_variableCell, condition.1 index]
      refine HasTypeUnion.var targetContext (rawRenaming index) ?_
      have transported := condition.2 .fibrant index
        ((isAccessibleAtModality_fibrant context index).trans isAccessible)
      rwa [isAccessibleAtModality_fibrant] at transported
  | universeFormation context levelExpr flag =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_universeCodeCell, rename_universeCodeCell]
      exact HasTypeUnion.universeFormation targetContext levelExpr flag
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext rawRenaming condition
      have typedRenamed := typedIH targetContext rawRenaming condition
      have reclassifierRenamed := reclassifierIH targetContext rawRenaming condition
      rw [rename_universeCodeCell] at reclassifierRenamed
      exact HasTypeUnion.conv levelExpr flag typedRenamed
        (Conv.rename rawRenaming converts) reclassifierRenamed
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
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.rename rawRenaming children) (.baseType baseRule)
            levels (RawTerm.rename rawRenaming carrier) level flag isFormationRule
            (fun _obligation hmem => by cases hmem)
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
                  (HasTypeUnion.RenameRespectsContext.cons domain rawRenaming condition)))
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
                  (HasTypeUnion.RenameRespectsContext.cons domain rawRenaming condition)))
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
                  (HasTypeUnion.RenameRespectsContext.cons domain rawRenaming condition)))
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
                have codomainCondition := HasTypeUnion.RenameRespectsContext.cons domainCode rawRenaming condition
                have codomainRenamed := ihPremises _ (List.Mem.tail _ (List.Mem.head _))
                  (targetContext.cons (RawTerm.rename rawRenaming domainCode))
                  (iterateLiftRaw rawRenaming 1) codomainCondition
                rw [rename_universeCodeCell] at codomainRenamed
                exact codomainRenamed
            | tail _ hmem => cases hmem with
              | head =>
                  have bodyCondition := HasTypeUnion.RenameRespectsContext.cons domainCode rawRenaming condition
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
                HasTypeUnion.RenameRespectsContext.lockCons intervalTypeCell rawRenaming condition
              have bodyRenamed := ihPremises _ (List.Mem.head _)
                (targetContext.lockCons (RawTerm.rename rawRenaming intervalTypeCell))
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
  | elim context generator rule args params level0 level1 flag isElim premisesHold
      ihPremises =>
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
                      (HasTypeUnion.RenameRespectsContext.cons natTypeCell rawRenaming condition)
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
                      (HasTypeUnion.RenameRespectsContext.cons natTypeCell rawRenaming condition)
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
                      (HasTypeUnion.RenameRespectsContext.cons boolTypeCell rawRenaming condition)
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
                      (HasTypeUnion.RenameRespectsContext.cons (optionTypeCell typeParamA) rawRenaming condition)
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
                      (HasTypeUnion.RenameRespectsContext.cons (eitherTypeCell typeParamA typeParamB) rawRenaming condition)
                    rw [rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
                | tail _ hmem => cases hmem
      -- idJ: GENUINE Paulin-Mohring path induction; output `idJMotiveAt motive right witness`, witness at the
      -- GENERAL `idTypeCell typeCode left right`, right endpoint at `typeCode`, base case at the diagonal
      -- `idJMotiveAt motive left (refl left)`, motive obligation under TWO binders at a universe (host condition
      -- via `RenameRespectsContext.consTwice`, inner binding reshaped via `rename_iterateLift_idJMotiveSecondBinderType`).
      · match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
          show HasTypeUnion profile targetContext
            (RawTerm.rename rawRenaming (idJCell motive baseCase witness))
            (RawTerm.rename rawRenaming (idJMotiveAt motive rightEndpoint witness))
          rw [rename_idJCell, rename_idJMotiveAt_iterateLift]
          refine HasTypeUnion.elim targetContext .gen_idJ idJElimRule
            (RawTermChildren.rename rawRenaming
              (.childCons motive (.childCons baseCase (.childCons witness .childNil))))
            (RawTermChildren.rename rawRenaming
              (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))) level0 level1 flag rfl ?_
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
                  have baseCaseRenamed :=
                    ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
                      targetContext rawRenaming condition
                  rw [rename_idJMotiveAt_iterateLift, rename_reflCell] at baseCaseRenamed
                  exact baseCaseRenamed
              | tail _ hmem => cases hmem with
                | head =>
                    have motiveRenamed := ihPremises _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                      _ (iterateLiftRaw rawRenaming 2)
                      (HasTypeUnion.RenameRespectsContext.consTwice typeCode
                        (idJMotiveSecondBinderType typeCode leftEndpoint) condition)
                    rw [rename_iterateLift_idJMotiveSecondBinderType, rename_universeCodeCell] at motiveRenamed
                    exact motiveRenamed
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
                      (HasTypeUnion.RenameRespectsContext.cons (listTypeCell elementType) rawRenaming condition)
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
    ⟨fun _ => rfl, accessibilityAtModalityPreservedUnderWeakenCons context newBinding⟩

/-- **★ INTRINSIC weakening for the native union under the affine dimension LOCK (`lockCons`)** — the
`lockCons` twin of `HasTypeUnion.weakenUnderBinding`.  `lockCons`'s `lookup` successor arm is byte-identical to
`cons`'s, so the `renameRespectingContext` context-condition still holds DEFINITIONALLY (`fun _ => rfl`): the
lock mark is invisible to the pure renaming action. -/
theorem HasTypeUnion.weakenUnderLockBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} (dimensionType : RawTerm scope)
    (derivation : HasTypeUnion profile context subject classifier) :
    HasTypeUnion profile (context.lockCons dimensionType)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.lockCons dimensionType) RawRenaming.weaken
    ⟨fun _ => rfl, accessibilityAtModalityPreservedUnderWeakenLockCons context dimensionType⟩

end FX1Poly.Typed
