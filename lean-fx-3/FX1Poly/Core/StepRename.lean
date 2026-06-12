import FX1Poly.Core.StepSubst
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.StepEta

/-! # Foundation/PolyCell/Core/StepRename

Rename compatibility for the raw beta+iota `Step` relation, its
children-spine and reflexive-transitive closures, and the raw eta
sibling relation.

The beta+iota proof deliberately factors through the already-audited
`Step.subst` theorem by viewing a renaming as substitution followed by
identity.  Eta needs explicit shape lemmas for the eta-source
constructors because binder eta sources contain `RawTerm.weaken`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

namespace RawTerm

/-- The newest bound variable is fixed by any lifted renaming. -/
theorem rename_lift_newestVar {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming.lift
        (RawTerm.newestVar : RawTerm (sourceScope + 1)) =
      (RawTerm.newestVar : RawTerm (targetScope + 1)) := by
  rfl

/-- Eta-lambda sources commute with raw renaming.

Church-style: the eta-lambda source carries a domain annotation at the
same scope as its first child; renaming maps it directly while the body
(`app (weaken innerFunction) newestVar`) renames under the lifted
renaming. -/
theorem rename_etaLamSource {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (domainAnn innerFunction : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (RawTerm.etaLamSource domainAnn innerFunction) =
      RawTerm.etaLamSource (RawTerm.rename rawRenaming domainAnn)
        (RawTerm.rename rawRenaming innerFunction) := by
  change
    ((.mkGen .gen_lam ()
      (.childCons
        (RawTerm.rename rawRenaming domainAnn)
        (.childCons
          ((.mkGen .gen_app ()
            (.childCons
              (RawTerm.rename rawRenaming.lift
                (RawTerm.weaken innerFunction))
              (.childCons
                (RawTerm.rename rawRenaming.lift
                  (RawTerm.newestVar : RawTerm (sourceScope + 1)))
                .childNil))) : RawTerm (targetScope + 1))
          .childNil))) : RawTerm targetScope) =
      RawTerm.etaLamSource (RawTerm.rename rawRenaming domainAnn)
        (RawTerm.rename rawRenaming innerFunction)
  rw [RawTerm.rename_lift_weaken, RawTerm.rename_lift_newestVar]

/-- Eta-pair sources commute with raw renaming. -/
theorem rename_etaPairSource {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (RawTerm.etaPairSource pairTerm) =
      RawTerm.etaPairSource (RawTerm.rename rawRenaming pairTerm) := by
  rfl

/-- Eta-path sources commute with raw renaming. -/
theorem rename_etaPathLamSource {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (innerPath : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (RawTerm.etaPathLamSource innerPath) =
      RawTerm.etaPathLamSource (RawTerm.rename rawRenaming innerPath) := by
  change
    ((.mkGen .gen_pathLam ()
      (.childCons
        ((.mkGen .gen_pathApp ()
          (.childCons
            (RawTerm.rename rawRenaming.lift (RawTerm.weaken innerPath))
            (.childCons
              (RawTerm.rename rawRenaming.lift
                (RawTerm.newestVar : RawTerm (sourceScope + 1)))
              .childNil))) : RawTerm (targetScope + 1))
        .childNil)) : RawTerm targetScope) =
      RawTerm.etaPathLamSource (RawTerm.rename rawRenaming innerPath)
  rw [RawTerm.rename_lift_weaken, RawTerm.rename_lift_newestVar]

/-- Eta-modal-introduction sources commute with raw renaming. -/
theorem rename_etaModIntroSource {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (modalTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (RawTerm.etaModIntroSource modalTerm) =
      RawTerm.etaModIntroSource (RawTerm.rename rawRenaming modalTerm) := by
  rfl

/-- Eta-Glue-introduction sources commute with raw renaming. -/
theorem rename_etaGlueIntroSource {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (gluedTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (RawTerm.etaGlueIntroSource gluedTerm) =
      RawTerm.etaGlueIntroSource (RawTerm.rename rawRenaming gluedTerm) := by
  rfl

end RawTerm

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

namespace Step

namespace eta

/-- One-step eta reduction is stable under raw renaming. -/
theorem rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (etaStep : Step.eta sourceTerm targetTerm) :
    Step.eta (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  cases etaStep with
  | etaLam domainAnn innerFunction =>
      rw [RawTerm.rename_etaLamSource]
      exact Step.eta.etaLam _ _
  | etaPair pairTerm =>
      rw [RawTerm.rename_etaPairSource]
      exact Step.eta.etaPair _
  | etaPathLam innerPath =>
      rw [RawTerm.rename_etaPathLamSource]
      exact Step.eta.etaPathLam _
  | etaModIntro modalTerm =>
      rw [RawTerm.rename_etaModIntroSource]
      exact Step.eta.etaModIntro _
  | etaGlueIntro gluedTerm =>
      rw [RawTerm.rename_etaGlueIntroSource]
      exact Step.eta.etaGlueIntro _

end eta

namespace etaStar

/-- Rename every term in an eta-star chain. -/
theorem rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceChain : Step.etaStar sourceTerm targetTerm) :
    Step.etaStar (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  induction sourceChain with
  | refl term =>
      exact Step.etaStar.refl _
  | trans headStep _ tailIH =>
      exact Step.etaStar.trans (Step.eta.rename rawRenaming headStep) tailIH

end etaStar

namespace betaEta

/-- One beta+iota-or-eta step is stable under raw renaming. -/
theorem rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (singleStep : Step.betaEta sourceTerm targetTerm) :
    Step.betaEta (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  cases singleStep with
  | inl betaStep =>
      exact Or.inl (Step.rename rawRenaming betaStep)
  | inr etaStep =>
      exact Or.inr (Step.eta.rename rawRenaming etaStep)

end betaEta

namespace betaEtaStar

/-- Rename every term in a beta+iota+eta-star chain. -/
theorem rename {sourceScope targetScope : Nat}
    {sourceTerm targetTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceChain : Step.betaEtaStar sourceTerm targetTerm) :
    Step.betaEtaStar (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming targetTerm) := by
  induction sourceChain with
  | refl term =>
      exact Step.betaEtaStar.refl _
  | trans headStep _ tailIH =>
      exact Step.betaEtaStar.trans
        (Step.betaEta.rename rawRenaming headStep) tailIH

end betaEtaStar

end Step

end FX1Poly.Core
