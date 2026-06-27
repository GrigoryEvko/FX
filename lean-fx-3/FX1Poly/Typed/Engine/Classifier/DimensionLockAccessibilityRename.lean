import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility
import FX1Poly.Typed.Cell.CellRenaming
import FX1Poly.Tier0.Term.Core.RawTermFoldNonVarCommute

/-! # FX1Poly/Typed/Engine/Classifier/DimensionLockAccessibilityRename
    — the use-modality conjunct transports along a lock-structure-preserving renaming (A1-WEAKEN-RENAME core)

The renaming / weakening metatheory reconstructs every `intro` / `elim` / `formationRule` derivation in a RENAMED
context, so to carry the use-site accessibility conjunct (`isSubjectUsableAtModality`) through it we need ONE fact:
subject usability is preserved by any renaming that preserves the lock-accessibility profile.

`renameRespectingContext` (the weakening condition) equates the looked-up binding TYPES; it says nothing about the
cons / lockCons LOCK-STRUCTURE the accessibility check reads.  `RenamePreservesLockAccess` is the orthogonal
companion: it equates the dimensional-accessibility of each index with its renamed image's.  By the
fibrant / dimensional dichotomy (`isFibrantlyAccessibleAt_eq_not_isDimensionallyAccessibleAt`) a single Boolean
equality per index pins BOTH use-modalities at once.

## The two transports

  * `isAccessibleAtModality_rename_ofPreservesLockAccess` — the index-level fact: accessibility at ANY modality
    transports (dimensional directly from the hypothesis, fibrant via the Boolean dichotomy).
  * `isSubjectUsableAtModality_rename_ofPreservesLockAccess` — the subject-level lift the reconstruction sites
    consume: a VARIABLE subject `var k` defers to the index transport; a NON-VARIABLE subject keeps its head
    generator under `rename` (`RawTerm.rename_mkGen_of_ne_var`), so it stays unconditionally usable
    (`isSubjectUsableAtModality_ofNonVarHead`).

## Zero-axiom

Modality case-split + the Boolean dichotomy + the `decide`-based variable-head split (mirroring
`lockFreeImpliesSubjectFibrantlyUsable`, never `by_cases`) + the `rename_variableCell` /
`rename_mkGen_of_ne_var` `rfl` commutations.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- A renaming **preserves the lock-accessibility profile** iff every source index's dimensional accessibility
equals its renamed image's in the target context.  The lock-structure companion to `renameRespectingContext`
(which equates binding TYPES): both are needed to transport the use-modality conjunct through weakening, since a
variable subject's usability reads only the cons / lockCons lock-structure.  By
`isFibrantlyAccessibleAt_eq_not_isDimensionallyAccessibleAt` the fibrant profile follows from the dimensional one,
so ONE Boolean equality per index suffices. -/
def RenamePreservesLockAccess {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    targetContext.isDimensionallyAccessibleAt (rawRenaming index)
      = sourceContext.isDimensionallyAccessibleAt index

/-- Accessibility at ANY modality transports along a lock-access-preserving renaming.  The dimensional half is the
hypothesis verbatim; the fibrant half is the dimensional one negated on both sides (the dichotomy), so the same
equality discharges it. -/
theorem isAccessibleAtModality_rename_ofPreservesLockAccess {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {rawRenaming : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (preserves : RenamePreservesLockAccess rawRenaming sourceContext targetContext)
    (index : Fin sourceScope) (modality : ObligationModality) :
    targetContext.isAccessibleAtModality (rawRenaming index) modality
      = sourceContext.isAccessibleAtModality index modality := by
  cases modality with
  | dimensional =>
      rw [isAccessibleAtModality_dimensional, isAccessibleAtModality_dimensional]
      exact preserves index
  | fibrant =>
      rw [isAccessibleAtModality_fibrant, isAccessibleAtModality_fibrant,
        targetContext.isFibrantlyAccessibleAt_eq_not_isDimensionallyAccessibleAt,
        sourceContext.isFibrantlyAccessibleAt_eq_not_isDimensionallyAccessibleAt,
        preserves index]

/-- **★ Subject usability transports along a lock-access-preserving renaming** (the A1-WEAKEN-RENAME core).  The
one transport every renaming / weakening reconstruction site feeds the use-modality conjunct through: a VARIABLE
subject `var k` defers to `isAccessibleAtModality k`, carried by
`isAccessibleAtModality_rename_ofPreservesLockAccess`; a NON-VARIABLE subject keeps its head generator under
`rename` (`RawTerm.rename_mkGen_of_ne_var`), so it stays unconditionally usable
(`isSubjectUsableAtModality_ofNonVarHead`), the lock-access hypothesis unused on that branch. -/
theorem isSubjectUsableAtModality_rename_ofPreservesLockAccess {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {rawRenaming : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (preserves : RenamePreservesLockAccess rawRenaming sourceContext targetContext)
    (subject : RawTerm sourceScope) (modality : ObligationModality)
    (usable : sourceContext.isSubjectUsableAtModality subject modality = true) :
    targetContext.isSubjectUsableAtModality (RawTerm.rename rawRenaming subject) modality = true := by
  cases subject with
  | mkGen generator payload children =>
      cases generatorEquality : decide (generator = Generator.gen_var) with
      | true =>
          have generatorIsVar : generator = Generator.gen_var := of_decide_eq_true generatorEquality
          subst generatorIsVar
          cases children with
          | childNil =>
              have renameVar : RawTerm.rename rawRenaming (.mkGen Generator.gen_var payload .childNil)
                  = .mkGen Generator.gen_var (rawRenaming payload) .childNil :=
                rename_variableCell rawRenaming payload
              rw [renameVar, isSubjectUsableAtModality_var]
              rw [isSubjectUsableAtModality_var] at usable
              rw [isAccessibleAtModality_rename_ofPreservesLockAccess preserves payload modality]
              exact usable
      | false =>
          have generatorIsNotVar : generator ≠ Generator.gen_var := of_decide_eq_false generatorEquality
          rw [RawTerm.rename_mkGen_of_ne_var rawRenaming generatorIsNotVar payload children]
          exact isSubjectUsableAtModality_ofNonVarHead targetContext generator _ _ modality generatorIsNotVar

end FX1Poly.Typed
