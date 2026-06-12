import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Typed.HasTypeNativeUnionInversion
import FX1Poly.Typed.NativeUnionCellSubstitution
import FX1Poly.Typed.NativeUnionEngineSubstitution
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Core.RawTermOccurrenceSubst

/-! # FX1Poly/Typed/HasTypeNativeUnionWeakening — the RENAMING / WEAKENING lemma for the 25-arm native
    union (the de-Bruijn-insertion twin of `HasTypeNativeUnion.substRespectingContext`)

The grown engine ships `HasTypeDescPi.renameRespectingContext` (its cartesian-lift fibration leg); the
unified judgment `HasTypeNativeUnion` must too.  This file supplies that missing union-metatheory
primitive — `HasTypeNativeUnion` is preserved along ANY renaming respecting the context — the structural
mirror of the union substitution lemma with a RENAMING in place of the substitution.

## The renaming-respects-context discipline (the formation engine's EQUALITY carrier)

`renameRespectingContext` is preserved along any renaming whose looked-up image equals the target's
looked-up binding (`RawTerm.rename rawRenaming (sourceContext.lookup index) = targetContext.lookup
(rawRenaming index)`).  This is the IDENTICAL carrier the grown twin
`HasTypeDescPi.renameRespectingContext` uses, so every engine-embedding arm composes verbatim.

## How the 25 arms discharge

  * The four ENGINE EMBEDDINGS (`ofGrown` / `ofBaseType` / `ofDataIntro` / `ofTermIndexedFormer`) and the
    five scrutinee/intro embeddings (`ofNatIntro` / `ofOptionIntro` / `ofEitherIntro` / `ofIdIntro` /
    `ofPairIntro` / `ofListIntro`) route their engine premises through the respective engine's own
    `renameRespectingContext` (the grown / term-indexed engines ship theirs; the eight data engines'
    rename twins are supplied below — the rename twins of `NativeUnionEngineSubstitution`) and re-embed.
  * The TABLE-DRIVEN RECURSIVE arms (`gradedBinderIntro` / `generalElim` / `recursiveElim` /
    `twoBranchMatchElim` / `pathInductionElim` / `projectionElim` / `recursiveUnaryIntro` /
    `recursiveBinaryIntro` / `pinnedUnaryIntro` / `nullaryFreeTypeIntro` / `coproductIntro` /
    `nonDependentBinaryIntro` / `reflexiveIntro` / `listElim`) recurse via the induction hypotheses, with
    `RawRenaming.lift` crossing the one/two binders (the lifted condition keeps the renaming
    context-respecting: `0` → `rename_lift_weaken_commute` on the domain, `k+1` → the condition under
    weakening), and the cell-rename `rfl` commutations push `RawTerm.rename` through each rule's member
    cell / classifier builders.  The `recursiveElim` step branch lives at TWO binders, so its renaming
    lifts twice (`iterateLiftRaw rawRenaming 2`) and the classifier carries two `RawRenaming.weaken`
    layers.
  * The CONV arm (the 25th) recurses both premises, transports the conversion through `Conv.rename`, and
    re-applies the conv arm — the `universeCodeCell` reclassifier renames to itself
    (`rename_universeCodeCell`).
  * The graded arm additionally transports the affine binder check
    (`RawTerm.occurrenceCountAt_rename_image` on the lifted renaming: a lifted renaming preserves the
    freshest-binder occurrence count, so `gradedBinderChecks usage body` survives verbatim).

## Zero-axiom

`renameRespectingContext` is `induction` over the 25 arms + the cell-rename `rfl` commutations + the
per-rule `rename_subst0_commute` reshapes + the lifted-occurrence preservation + the engine rename
lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditNativeUnionWeakening.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation FX1Poly.Modal

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

/-! ## The eight data-engine rename twins (the rename mirror of `NativeUnionEngineSubstitution`) -/

/-- A nullary data-intro rule's output type code is a closed nullary cell, hence renaming-invariant
across scopes (`rename ρ (output source) = output target`).  Reads off the five-row table. -/
theorem dataIntroNullaryRuleDescOf_outputRenameStable {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat} (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (rule.outputTypeCode sourceScope)
      = rule.outputTypeCode targetScope := by
  rcases dataIntroNullaryRuleDescOf_isNullaryValueConstructor isDataIntro with
    hTrue | hFalse | hUnit | hZero | hOne
  · subst hTrue
    have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hFalse
    have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hUnit
    have hrule : rule = { outputTypeCode := fun _ => unitTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hZero
    have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hOne
    have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl

/-- **Base-type formation renaming.**  `HasTypeDescBaseType` is preserved along any context-respecting
renaming: the subject is a nullary `mkGen` (reconstructed via `rename_mkGen_of_ne_var`), the classifier
is the rule's closed output universe (renaming-invariant). -/
theorem HasTypeDescBaseType.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescBaseType profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescBaseType profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | baseFormation generator payload children rule isBaseType =>
      intro targetScope targetContext rawRenaming _condition
      have hNotVar : generator ≠ Generator.gen_var := baseTypeRuleImpliesNotVariable isBaseType
      have outputClosed : RawTerm.rename rawRenaming (rule.outputUniverse sourceScope)
          = rule.outputUniverse targetScope := by
        rw [baseTypeRuleDescOf_outputIsType0 isBaseType]
        rfl
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar, outputClosed]
      exact HasTypeDescBaseType.baseFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) rule isBaseType

/-- **Nullary data-intro renaming.**  `HasTypeDescDataIntro` is preserved: the subject is a nullary
`mkGen` (reconstructed via `rename_mkGen_of_ne_var`), the classifier is the rule's closed output type
code. -/
theorem HasTypeDescDataIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescDataIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescDataIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      intro targetScope targetContext rawRenaming _condition
      have hNotVar : generator ≠ Generator.gen_var := dataIntroNullaryRuleImpliesNotVariable isDataIntro
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar,
        dataIntroNullaryRuleDescOf_outputRenameStable isDataIntro rawRenaming]
      exact HasTypeDescDataIntro.nullaryIntro targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) rule isDataIntro

/-- **Nat-intro renaming.**  `natZero` / `natSucc(p)` both classify at `natTypeCell`
(renaming-invariant); `natSucc` recurses on the predecessor. -/
theorem HasTypeDescNatIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescNatIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescNatIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  induction derivation with
  | natZeroIntro =>
      intro targetScope targetContext rawRenaming _condition
      rw [show RawTerm.rename rawRenaming (natZeroCell : RawTerm sourceScope) = natZeroCell from rfl,
        rename_natTypeCell]
      exact HasTypeDescNatIntro.natZeroIntro targetContext
  | natSuccIntro predecessor _predecessorTyped predecessorIH =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_natSuccCell, rename_natTypeCell]
      have predecessorRenamed := predecessorIH targetContext rawRenaming condition
      rw [rename_natTypeCell] at predecessorRenamed
      exact HasTypeDescNatIntro.natSuccIntro targetContext
        (RawTerm.rename rawRenaming predecessor) predecessorRenamed

/-- **Option-intro renaming.**  `optionNone` / `optionSome(v)` classify at `option(A)`; the element-type
formation / value premises route through `HasTypeDescPi.renameRespectingContext`. -/
theorem HasTypeDescOptionIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescOptionIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescOptionIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | optionNoneIntro elementType elementLevel flag elementTypeFormed =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_optionNoneCell, rename_optionTypeCell]
      have elementFormRenamed :=
        elementTypeFormed.renameRespectingContext targetContext rawRenaming condition
      rw [rename_universeCodeCell] at elementFormRenamed
      exact HasTypeDescOptionIntro.optionNoneIntro targetContext
        (RawTerm.rename rawRenaming elementType) elementLevel flag elementFormRenamed
  | optionSomeIntro value elementType valueTyped =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_optionSomeCell, rename_optionTypeCell]
      exact HasTypeDescOptionIntro.optionSomeIntro targetContext
        (RawTerm.rename rawRenaming value) (RawTerm.rename rawRenaming elementType)
        (valueTyped.renameRespectingContext targetContext rawRenaming condition)

/-- **Either-intro renaming.**  `eitherInl(v)` / `eitherInr(v)` classify at `either(A, B)`; the value and
free-type premises route through `HasTypeDescPi.renameRespectingContext`. -/
theorem HasTypeDescEitherIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescEitherIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescEitherIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | eitherInlIntro leftValue leftType rightType rightLevel flag leftTyped rightTypeFormed =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_eitherInlCell, rename_eitherTypeCell]
      have rightFormRenamed :=
        rightTypeFormed.renameRespectingContext targetContext rawRenaming condition
      rw [rename_universeCodeCell] at rightFormRenamed
      exact HasTypeDescEitherIntro.eitherInlIntro targetContext
        (RawTerm.rename rawRenaming leftValue) (RawTerm.rename rawRenaming leftType)
        (RawTerm.rename rawRenaming rightType) rightLevel flag
        (leftTyped.renameRespectingContext targetContext rawRenaming condition) rightFormRenamed
  | eitherInrIntro rightValue leftType rightType leftLevel flag rightTyped leftTypeFormed =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_eitherInrCell, rename_eitherTypeCell]
      have leftFormRenamed :=
        leftTypeFormed.renameRespectingContext targetContext rawRenaming condition
      rw [rename_universeCodeCell] at leftFormRenamed
      exact HasTypeDescEitherIntro.eitherInrIntro targetContext
        (RawTerm.rename rawRenaming rightValue) (RawTerm.rename rawRenaming leftType)
        (RawTerm.rename rawRenaming rightType) leftLevel flag
        (rightTyped.renameRespectingContext targetContext rawRenaming condition) leftFormRenamed

/-- **Id-intro renaming.**  `refl(w)` classifies at `Id(A, w, w)`; the witness premise routes through
`HasTypeDescPi.renameRespectingContext`. -/
theorem HasTypeDescIdIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescIdIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescIdIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | reflIntro witness typeCode witnessTyped =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_reflCell, rename_idTypeCell]
      exact HasTypeDescIdIntro.reflIntro targetContext
        (RawTerm.rename rawRenaming witness) (RawTerm.rename rawRenaming typeCode)
        (witnessTyped.renameRespectingContext targetContext rawRenaming condition)

/-- **Pair-intro renaming.**  `pair(x, y)` classifies at `A × B`; both value premises route through
`HasTypeDescPi.renameRespectingContext`. -/
theorem HasTypeDescPairIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescPairIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescPairIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | pairIntro firstValue secondValue firstType secondType firstTyped secondTyped =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_pairCell, rename_productTypeCell]
      exact HasTypeDescPairIntro.pairIntro targetContext
        (RawTerm.rename rawRenaming firstValue) (RawTerm.rename rawRenaming secondValue)
        (RawTerm.rename rawRenaming firstType) (RawTerm.rename rawRenaming secondType)
        (firstTyped.renameRespectingContext targetContext rawRenaming condition)
        (secondTyped.renameRespectingContext targetContext rawRenaming condition)

/-- **List-intro renaming.**  `listNil` / `listCons(h, t)` classify at `list(A)`; the element-type
formation / head premises route through `HasTypeDescPi.renameRespectingContext`, the tail recurses. -/
theorem HasTypeDescListIntro.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescListIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescListIntro profile targetContext
        (RawTerm.rename rawRenaming subject) (RawTerm.rename rawRenaming classifier) := by
  induction derivation with
  | listNilIntro elementType elementLevel flag elementTypeFormed =>
      intro targetScope targetContext rawRenaming condition
      rw [show RawTerm.rename rawRenaming (listNilCell : RawTerm sourceScope) = listNilCell from rfl,
        rename_listTypeCell]
      have elementFormRenamed :=
        elementTypeFormed.renameRespectingContext targetContext rawRenaming condition
      rw [rename_universeCodeCell] at elementFormRenamed
      exact HasTypeDescListIntro.listNilIntro targetContext
        (RawTerm.rename rawRenaming elementType) elementLevel flag elementFormRenamed
  | listConsIntro headValue tailList elementType headTyped _tailTyped tailIH =>
      intro targetScope targetContext rawRenaming condition
      rw [rename_listConsCell, rename_listTypeCell]
      have tailRenamed := tailIH targetContext rawRenaming condition
      rw [rename_listTypeCell] at tailRenamed
      exact HasTypeDescListIntro.listConsIntro targetContext
        (RawTerm.rename rawRenaming headValue) (RawTerm.rename rawRenaming tailList)
        (RawTerm.rename rawRenaming elementType)
        (headTyped.renameRespectingContext targetContext rawRenaming condition) tailRenamed

/-! ## The renaming-respects-context carrier + the binder-crossing helpers -/

/-- The renaming-respects-context condition for the native union: each source binding's looked-up type
renames to the target's looked-up binding.  IDENTICAL to the grown engine's carrier so the embedding arms
compose verbatim. -/
abbrev HasTypeNativeUnion.RenameRespectsContext {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    RawTerm.rename rawRenaming (sourceContext.lookup index)
      = targetContext.lookup (rawRenaming index)

/-- The two-binder lift of the renaming context-condition (the recursiveElim / idJ step-branch shape):
the double lift of a renaming context-condition is a context-condition at the context extended by the two
domains.  An iterate of `renameContextCondition_cons`. -/
theorem HasTypeNativeUnion.RenameRespectsContext.consTwice {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    {rawRenaming : RawRenaming sourceScope targetScope}
    (condition : HasTypeNativeUnion.RenameRespectsContext sourceContext targetContext rawRenaming) :
    HasTypeNativeUnion.RenameRespectsContext ((sourceContext.cons outerType).cons innerType)
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
subject at the renamed classifier.  By `induction` over the 25 arms: the engine embeddings and
host-premise arms route through the engines' own `renameRespectingContext` and re-embed; the recursive
native arms recurse via the IHs with `RawRenaming.lift` crossing binders; the graded arm transports the
affine binder check by the lifted-occurrence preservation; the conv arm transports the conversion through
`Conv.rename`.  The de-Bruijn-insertion twin of `HasTypeDescPi.renameRespectingContext`. -/
theorem HasTypeNativeUnion.renameRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeNativeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      HasTypeNativeUnion.RenameRespectsContext sourceContext targetContext rawRenaming →
      HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext rawRenaming condition
      have typedRenamed := typedIH targetContext rawRenaming condition
      have reclassifierRenamed := reclassifierIH targetContext rawRenaming condition
      rw [rename_universeCodeCell] at reclassifierRenamed
      exact HasTypeNativeUnion.conv levelExpr flag typedRenamed
        (Conv.rename rawRenaming converts) reclassifierRenamed
  | ofGrown hostTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofGrown
        (hostTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofBaseType baseTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofBaseType
        (baseTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofDataIntro dataTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofDataIntro
        (dataTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofTermIndexedFormer formerTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofTermIndexedFormer
        (formerTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofNatIntro natTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofNatIntro
        (natTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofOptionIntro optionTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofOptionIntro
        (optionTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofEitherIntro eitherTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofEitherIntro
        (eitherTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofIdIntro idTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofIdIntro
        (idTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofPairIntro pairTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofPairIntro
        (pairTyped.renameRespectingContext targetContext rawRenaming condition)
  | ofListIntro listTyped =>
      intro targetScope targetContext rawRenaming condition
      exact HasTypeNativeUnion.ofListIntro
        (listTyped.renameRespectingContext targetContext rawRenaming condition)
  | recursiveUnaryIntro context generator rule child isRecursiveUnary _childTyped childIH =>
      intro targetScope targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      have childRenamed := childIH targetContext rawRenaming condition
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (natSuccCell child)) (RawTerm.rename rawRenaming natTypeCell)
      rw [rename_natSuccCell, rename_natTypeCell]
      exact HasTypeNativeUnion.recursiveUnaryIntro targetContext .gen_natSucc
        natSuccNativeRecursiveUnaryRule (RawTerm.rename rawRenaming child) rfl childRenamed
  | recursiveBinaryIntro context generator rule head tail elementType isRecursiveBinary
      headTyped _tailTyped tailIH =>
      intro targetScope targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      have tailRenamed := tailIH targetContext rawRenaming condition
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (listConsCell head tail))
        (RawTerm.rename rawRenaming (listTypeCell elementType))
      rw [rename_listConsCell, rename_listTypeCell]
      exact HasTypeNativeUnion.recursiveBinaryIntro targetContext .gen_listCons
        listConsNativeRecursiveBinaryRule (RawTerm.rename rawRenaming head)
        (RawTerm.rename rawRenaming tail) (RawTerm.rename rawRenaming elementType) rfl
        (headTyped.renameRespectingContext targetContext rawRenaming condition) tailRenamed
  | pinnedUnaryIntro context generator rule child elementType isPinnedUnary childTyped =>
      intro targetScope targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (optionSomeCell child))
        (RawTerm.rename rawRenaming (optionTypeCell elementType))
      rw [rename_optionSomeCell, rename_optionTypeCell]
      exact HasTypeNativeUnion.pinnedUnaryIntro targetContext .gen_optionSome
        optionSomeNativePinnedUnaryRule (RawTerm.rename rawRenaming child)
        (RawTerm.rename rawRenaming elementType) rfl
        (childTyped.renameRespectingContext targetContext rawRenaming condition)
  | nullaryFreeTypeIntro context generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      intro targetScope targetContext rawRenaming condition
      have elementFormRenamed :=
        elementTypeFormed.renameRespectingContext targetContext rawRenaming condition
      rw [rename_universeCodeCell] at elementFormRenamed
      rcases nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType with
          ⟨generatorEq, ruleEq⟩ | ⟨generatorEq, ruleEq⟩
      · subst generatorEq; subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming optionNoneCell)
          (RawTerm.rename rawRenaming (optionTypeCell elementType))
        rw [rename_optionNoneCell, rename_optionTypeCell]
        exact HasTypeNativeUnion.nullaryFreeTypeIntro targetContext .gen_optionNone
          optionNoneNativeNullaryFreeTypeRule (RawTerm.rename rawRenaming elementType)
          elementLevel flag rfl elementFormRenamed
      · subst generatorEq; subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming listNilCell)
          (RawTerm.rename rawRenaming (listTypeCell elementType))
        rw [rename_listNilCell, rename_listTypeCell]
        exact HasTypeNativeUnion.nullaryFreeTypeIntro targetContext .gen_listNil
          listNilNativeNullaryFreeTypeRule (RawTerm.rename rawRenaming elementType)
          elementLevel flag rfl elementFormRenamed
  | coproductIntro context generator rule value pinnedType freeType freeLevel flag isCoproduct
      valueTyped freeTypeFormed =>
      intro targetScope targetContext rawRenaming condition
      have valueRenamed := valueTyped.renameRespectingContext targetContext rawRenaming condition
      have freeFormRenamed := freeTypeFormed.renameRespectingContext targetContext rawRenaming condition
      rw [rename_universeCodeCell] at freeFormRenamed
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (eitherInlCell value))
          (RawTerm.rename rawRenaming (eitherTypeCell pinnedType freeType))
        rw [rename_eitherInlCell, rename_eitherTypeCell]
        exact HasTypeNativeUnion.coproductIntro targetContext .gen_eitherInl
          eitherInlNativeCoproductRule (RawTerm.rename rawRenaming value)
          (RawTerm.rename rawRenaming pinnedType) (RawTerm.rename rawRenaming freeType)
          freeLevel flag rfl valueRenamed freeFormRenamed
      · subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (eitherInrCell value))
          (RawTerm.rename rawRenaming (eitherTypeCell freeType pinnedType))
        rw [rename_eitherInrCell, rename_eitherTypeCell]
        exact HasTypeNativeUnion.coproductIntro targetContext .gen_eitherInr
          eitherInrNativeCoproductRule (RawTerm.rename rawRenaming value)
          (RawTerm.rename rawRenaming pinnedType) (RawTerm.rename rawRenaming freeType)
          freeLevel flag rfl valueRenamed freeFormRenamed
  | nonDependentBinaryIntro context generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      intro targetScope targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (pairCell firstChild secondChild))
        (RawTerm.rename rawRenaming (productTypeCell firstType secondType))
      rw [rename_pairCell, rename_productTypeCell]
      exact HasTypeNativeUnion.nonDependentBinaryIntro targetContext .gen_pair
        pairNativeNonDependentBinaryRule (RawTerm.rename rawRenaming firstChild)
        (RawTerm.rename rawRenaming secondChild) (RawTerm.rename rawRenaming firstType)
        (RawTerm.rename rawRenaming secondType) rfl
        (firstTyped.renameRespectingContext targetContext rawRenaming condition)
        (secondTyped.renameRespectingContext targetContext rawRenaming condition)
  | reflexiveIntro context generator rule witness witnessType isReflexive witnessTyped =>
      intro targetScope targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (reflCell witness))
        (RawTerm.rename rawRenaming (idTypeCell witnessType witness witness))
      rw [rename_reflCell, rename_idTypeCell]
      exact HasTypeNativeUnion.reflexiveIntro targetContext .gen_refl
        reflNativeReflexiveRule (RawTerm.rename rawRenaming witness)
        (RawTerm.rename rawRenaming witnessType) rfl
        (witnessTyped.renameRespectingContext targetContext rawRenaming condition)
  | recursiveElim context generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim _scrutineeTyped _baseBranchTyped _stepBranchTyped
      scrutineeIH baseBranchIH stepBranchIH =>
      intro targetScope targetContext rawRenaming condition
      have scrutineeRenamed := scrutineeIH targetContext rawRenaming condition
      have baseBranchRenamed := baseBranchIH targetContext rawRenaming condition
      have stepLiftedCondition :=
        HasTypeNativeUnion.RenameRespectsContext.consTwice (rule.scrutineeType _)
          (RawTerm.rename RawRenaming.weaken resultType) condition
      have stepBranchRenamed := stepBranchIH _ (iterateLiftRaw rawRenaming 2) stepLiftedCondition
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        dsimp only [natElimNativeRecursiveRule] at stepBranchRenamed
        rw [rename_natTypeCell, rename_iterateLift_one_renameWeaken_commute,
          rename_iterateLift_two_weaken_weaken_commute] at stepBranchRenamed
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming
            (natElimCell motive baseBranch stepBranch scrutinee))
          (RawTerm.rename rawRenaming resultType)
        rw [rename_natElimCell]
        exact HasTypeNativeUnion.recursiveElim targetContext .gen_natElim
          natElimNativeRecursiveRule (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming baseBranch)
          (RawTerm.rename (iterateLiftRaw rawRenaming 2) stepBranch)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming resultType)
          rfl scrutineeRenamed baseBranchRenamed stepBranchRenamed
      · subst ruleEq
        dsimp only [natRecNativeRecursiveRule] at stepBranchRenamed
        rw [rename_natTypeCell, rename_iterateLift_one_renameWeaken_commute,
          rename_iterateLift_two_weaken_weaken_commute] at stepBranchRenamed
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming
            (natRecCell motive baseBranch stepBranch scrutinee))
          (RawTerm.rename rawRenaming resultType)
        rw [rename_natRecCell]
        exact HasTypeNativeUnion.recursiveElim targetContext .gen_natRec
          natRecNativeRecursiveRule (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming baseBranch)
          (RawTerm.rename (iterateLiftRaw rawRenaming 2) stepBranch)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming resultType)
          rfl scrutineeRenamed baseBranchRenamed stepBranchRenamed
  | projectionElim context generator rule pairTerm firstType secondType isProjection
      _pairTyped pairIH =>
      intro targetScope targetContext rawRenaming condition
      have pairRenamed := pairIH targetContext rawRenaming condition
      rw [rename_productTypeCell] at pairRenamed
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (fstCell pairTerm)) (RawTerm.rename rawRenaming firstType)
        rw [rename_fstCell]
        exact HasTypeNativeUnion.projectionElim targetContext .gen_fst fstNativeProjectionRule
          (RawTerm.rename rawRenaming pairTerm) (RawTerm.rename rawRenaming firstType)
          (RawTerm.rename rawRenaming secondType) rfl pairRenamed
      · subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (sndCell pairTerm)) (RawTerm.rename rawRenaming secondType)
        rw [rename_sndCell]
        exact HasTypeNativeUnion.projectionElim targetContext .gen_snd sndNativeProjectionRule
          (RawTerm.rename rawRenaming pairTerm) (RawTerm.rename rawRenaming firstType)
          (RawTerm.rename rawRenaming secondType) rfl pairRenamed
  | twoBranchMatchElim context generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch _scrutineeTyped _firstBranchTyped
      _secondBranchTyped scrutineeIH firstBranchIH secondBranchIH =>
      intro targetScope targetContext rawRenaming condition
      have scrutineeRenamed := scrutineeIH targetContext rawRenaming condition
      have firstBranchRenamed := firstBranchIH targetContext rawRenaming condition
      have secondBranchRenamed := secondBranchIH targetContext rawRenaming condition
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (boolElimCell motive scrutinee firstBranch secondBranch))
          (RawTerm.rename rawRenaming resultType)
        rw [rename_boolElimCell]
        exact HasTypeNativeUnion.twoBranchMatchElim targetContext .gen_boolElim
          boolElimNativeMatchRule (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming firstBranch) (RawTerm.rename rawRenaming secondBranch)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename rawRenaming typeParamB) (RawTerm.rename rawRenaming resultType)
          rfl scrutineeRenamed firstBranchRenamed secondBranchRenamed
      · subst ruleEq
        rw [show optionMatchNativeMatchRule.secondBranchType _ typeParamA typeParamB resultType
              = piTyCodeCell typeParamA (RawTerm.weaken resultType) from rfl,
          rename_nonDependentArrow] at secondBranchRenamed
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (optionMatchCell motive firstBranch secondBranch scrutinee))
          (RawTerm.rename rawRenaming resultType)
        rw [rename_optionMatchCell]
        exact HasTypeNativeUnion.twoBranchMatchElim targetContext .gen_optionMatch
          optionMatchNativeMatchRule (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming firstBranch) (RawTerm.rename rawRenaming secondBranch)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename rawRenaming typeParamB) (RawTerm.rename rawRenaming resultType)
          rfl scrutineeRenamed firstBranchRenamed secondBranchRenamed
      · subst ruleEq
        rw [show eitherMatchNativeMatchRule.firstBranchType _ typeParamA typeParamB resultType
              = piTyCodeCell typeParamA (RawTerm.weaken resultType) from rfl,
          rename_nonDependentArrow] at firstBranchRenamed
        rw [show eitherMatchNativeMatchRule.secondBranchType _ typeParamA typeParamB resultType
              = piTyCodeCell typeParamB (RawTerm.weaken resultType) from rfl,
          rename_nonDependentArrow] at secondBranchRenamed
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (eitherMatchCell motive firstBranch secondBranch scrutinee))
          (RawTerm.rename rawRenaming resultType)
        rw [rename_eitherMatchCell]
        exact HasTypeNativeUnion.twoBranchMatchElim targetContext .gen_eitherMatch
          eitherMatchNativeMatchRule (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
          (RawTerm.rename rawRenaming firstBranch) (RawTerm.rename rawRenaming secondBranch)
          (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename rawRenaming typeParamB) (RawTerm.rename rawRenaming resultType)
          rfl scrutineeRenamed firstBranchRenamed secondBranchRenamed
  | pathInductionElim context generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction _witnessTyped _baseCaseTyped witnessIH baseCaseIH =>
      intro targetScope targetContext rawRenaming condition
      have witnessRenamed := witnessIH targetContext rawRenaming condition
      have baseCaseRenamed := baseCaseIH targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (idJCell motive baseCase witness))
        (RawTerm.rename rawRenaming resultType)
      rw [rename_idJCell]
      exact HasTypeNativeUnion.pathInductionElim targetContext .gen_idJ idJNativePathInductionRule
        (RawTerm.rename (iterateLiftRaw rawRenaming 2) motive)
        (RawTerm.rename rawRenaming baseCase) (RawTerm.rename rawRenaming witness)
        (RawTerm.rename rawRenaming typeCode) (RawTerm.rename rawRenaming endpoint)
        (RawTerm.rename rawRenaming resultType) rfl witnessRenamed baseCaseRenamed
  | listElim context generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      intro targetScope targetContext rawRenaming condition
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      have scrutineeRenamed :=
        scrutineeTyped.renameRespectingContext targetContext rawRenaming condition
      have nilRenamed := nilBranchTyped.renameRespectingContext targetContext rawRenaming condition
      have consRenamed := consBranchTyped.renameRespectingContext targetContext rawRenaming condition
      rw [rename_listTypeCell] at scrutineeRenamed
      rw [rename_listStepFunctionType] at consRenamed
      show HasTypeNativeUnion profile targetContext
        (RawTerm.rename rawRenaming (listElimCell motive scrutinee nilBranch consBranch))
        (RawTerm.rename rawRenaming resultType)
      rw [rename_listElimCell]
      exact HasTypeNativeUnion.listElim targetContext .gen_listElim listElimNativeRule
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) motive)
        (RawTerm.rename rawRenaming scrutinee) (RawTerm.rename rawRenaming nilBranch)
        (RawTerm.rename rawRenaming consBranch) (RawTerm.rename rawRenaming elementType)
        (RawTerm.rename rawRenaming resultType) rfl scrutineeRenamed nilRenamed consRenamed
  | generalElim context generator rule typeParamA typeParamB typeParamC typeParamD eliminated
      argument isElim _eliminatedTyped _argumentTyped eliminatedIH argumentIH =>
      intro targetScope targetContext rawRenaming condition
      have eliminatedRenamed := eliminatedIH targetContext rawRenaming condition
      have argumentRenamed := argumentIH targetContext rawRenaming condition
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        obtain rfl : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        rw [show appGeneralElimRule.eliminatedType _ typeParamA typeParamB typeParamC typeParamD
              = piTyCodeCell typeParamA typeParamB from rfl, rename_piTyCodeCell] at eliminatedRenamed
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (appCell eliminated argument))
          (RawTerm.rename rawRenaming (RawTerm.subst0 typeParamB argument))
        rw [show RawTerm.rename rawRenaming (appCell eliminated argument)
              = appCell (RawTerm.rename rawRenaming eliminated) (RawTerm.rename rawRenaming argument)
                from rfl, RawTerm.rename_subst0_commute]
        exact HasTypeNativeUnion.generalElim targetContext .gen_app appGeneralElimRule
          (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) typeParamB)
          (RawTerm.rename rawRenaming typeParamC) (RawTerm.rename rawRenaming typeParamD)
          (RawTerm.rename rawRenaming eliminated) (RawTerm.rename rawRenaming argument)
          rfl eliminatedRenamed argumentRenamed
      · subst hPath
        obtain rfl : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        rw [show pathAppGeneralElimRule.eliminatedType _ typeParamA typeParamB typeParamC typeParamD
              = bridgeTypeCell typeParamA typeParamC typeParamD from rfl,
          rename_bridgeTypeCell] at eliminatedRenamed
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (pathAppCell eliminated argument))
          (RawTerm.rename rawRenaming typeParamA)
        rw [rename_pathAppCell]
        exact HasTypeNativeUnion.generalElim targetContext .gen_pathApp pathAppGeneralElimRule
          (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) typeParamB)
          (RawTerm.rename rawRenaming typeParamC) (RawTerm.rename rawRenaming typeParamD)
          (RawTerm.rename rawRenaming eliminated) (RawTerm.rename rawRenaming argument)
          rfl eliminatedRenamed argumentRenamed
  | gradedBinderIntro context generator rule typeParamA typeParamB body domainLevel codomainLevel flag
      isIntro binderGraded _domainFormed _classifierFormed _bodyTyped domainIH classifierIH bodyIH =>
      intro targetScope targetContext rawRenaming condition
      have liftedCondition :
          HasTypeNativeUnion.RenameRespectsContext
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
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (lamCell typeParamA body))
          (RawTerm.rename rawRenaming (piTyCodeCell typeParamA typeParamB))
        rw [show RawTerm.rename rawRenaming (lamCell typeParamA body)
              = lamCell (RawTerm.rename rawRenaming typeParamA)
                  (RawTerm.rename (iterateLiftRaw rawRenaming 1) body) from rfl,
          rename_piTyCodeCell]
        exact HasTypeNativeUnion.gradedBinderIntro targetContext .gen_lam lamGradedIntroRule
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
        show HasTypeNativeUnion profile targetContext
          (RawTerm.rename rawRenaming (pathLamCell body))
          (RawTerm.rename rawRenaming
            (bridgeTypeCell typeParamA (RawTerm.subst0 body intervalZeroCell)
              (RawTerm.subst0 body intervalOneCell)))
        rw [rename_pathLamCell, rename_bridgeTypeCell, RawTerm.rename_subst0_commute,
          RawTerm.rename_subst0_commute]
        exact HasTypeNativeUnion.gradedBinderIntro targetContext .gen_pathLam pathLamGradedIntroRule
          (RawTerm.rename rawRenaming typeParamA)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) typeParamB)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) body)
          domainLevel codomainLevel flag rfl binderGradedRenamed
          (fun gateHolds => Bool.noConfusion gateHolds)
          (fun gateHolds => Bool.noConfusion gateHolds) bodyRenamed

/-! ## ★ The weakening corollary (the `fun _ => rfl` context-condition specialization) -/

/-- **★ INTRINSIC weakening for the native union.**  A `HasTypeNativeUnion` derivation survives extending
the context by one fresh binding, subject and classifier shifted by `RawRenaming.weaken` — the union twin
of `HasTypeDescPi.weakenUnderBinding`.  The corollary of `renameRespectingContext` whose
context-condition holds DEFINITIONALLY (`fun _ => rfl`): `weaken index` is `Fin.succ index`, the `cons`
`lookup` fires its successor arm. -/
theorem HasTypeNativeUnion.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} (newBinding : RawTerm scope)
    (derivation : HasTypeNativeUnion profile context subject classifier) :
    HasTypeNativeUnion profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.cons newBinding) RawRenaming.weaken
    (fun _ => rfl)

end FX1Poly.Typed
