import FX1Poly.Core.StepSubst
import FX1Poly.Tier0.Syntax.RawTermSubstLiftWeaken

/-! # Foundation/PolyCell/Core/StepRename

Rename compatibility for the canonical beta+iota `Step` relation and its
children-spine and reflexive-transitive closures.

The beta+iota proof deliberately factors through the already-audited
`Step.subst` theorem by viewing a renaming as substitution followed by
identity.

This module is bespoke-eta-FREE: the raw eta sibling relation's rename
closure (`Step.eta.rename` and friends) and the eta-source shape
commutations used to live here, but that forced `StepRename` — and via
`ConvSubstRename` the whole typed engine — to import the bespoke
`Step.eta` inductive (`StepEta.lean`).  They are relocated to
`StepEtaRename.lean` (TABLE-CANON-ETA re-base increment 2) so that
`StepEta` is no longer in the canonical typed stack's transitive
closure.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- One-step beta+iota reduction is stable under raw renaming. -/
theorem Step.rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceStep : Step sourceTerm targetTerm) :
    Step (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  have sourceRenameAsSubst :=
    RawTerm.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := targetScope)) sourceTerm
  have targetRenameAsSubst :=
    RawTerm.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := targetScope)) targetTerm
  rw [RawTerm.subst_identity_apply] at sourceRenameAsSubst
  rw [RawTerm.subst_identity_apply] at targetRenameAsSubst
  rw [sourceRenameAsSubst, targetRenameAsSubst]
  exact Step.subst
    (RawRenaming.thenSubst rawRenaming
      (RawTermSubst.identity (scope := targetScope)))
    sourceStep

/-- Child-spine one-step beta+iota reduction is stable under raw
renaming. -/
theorem StepChildren.rename {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    {sourceChildren targetChildren :
      RawTermChildren binderShifts parentSourceScope}
    (rawRenaming : RawRenaming parentSourceScope parentTargetScope)
    (childrenStep : StepChildren sourceChildren targetChildren) :
    StepChildren (RawTermChildren.rename rawRenaming sourceChildren)
      (RawTermChildren.rename rawRenaming targetChildren) := by
  have sourceRenameAsSubst :=
    RawTermChildren.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := parentTargetScope)) sourceChildren
  have targetRenameAsSubst :=
    RawTermChildren.rename_subst_commute rawRenaming
      (RawTermSubst.identity (scope := parentTargetScope)) targetChildren
  rw [RawTermChildren.subst_identity_apply] at sourceRenameAsSubst
  rw [RawTermChildren.subst_identity_apply] at targetRenameAsSubst
  rw [sourceRenameAsSubst, targetRenameAsSubst]
  exact StepChildren.subst
    (RawRenaming.thenSubst rawRenaming
      (RawTermSubst.identity (scope := parentTargetScope)))
    childrenStep

/-- Rename every term in a `StepStar` chain. -/
theorem StepStar.rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceChain : StepStar sourceTerm targetTerm) :
    StepStar (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  induction sourceChain with
  | refl term =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact StepStar.trans (Step.rename rawRenaming headStep) tailIH

end FX1Poly.Core
