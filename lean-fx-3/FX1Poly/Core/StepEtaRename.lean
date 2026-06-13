import FX1Poly.Core.StepRename
import FX1Poly.Core.StepEta

/-! # Foundation/PolyCell/Core/StepEtaRename — raw eta-sibling rename
compatibility (relocated out of `StepRename` to sever the bespoke-eta
import edge, TABLE-CANON-ETA re-base increment 2)

`StepRename` proves rename compatibility for the canonical beta+iota
`Step` relation and its closures, and is imported by the entire
`ConvSubstRename` / typed-engine stack.  It used to ALSO carry the raw
eta sibling's rename closure (`Step.eta.rename` and friends), which
forced `StepRename` — and therefore the whole typed engine — to import
the bespoke `Step.eta` inductive (`StepEta.lean`).  That single edge
(`StepRename → StepEta`) was what kept the bespoke-eta cluster
load-bearing for everything and blocked the TABLE-CANON-ETA deletion.

This module holds the relocated bespoke-eta rename content: the
eta-source shape commutations (`rename_etaLamSource` et al., which
mention the `RawTerm.etaLamSource` reducible shapes) and the
`Step.eta` / `etaStar` / `betaEta` / `betaEtaStar` rename closures
(which case on the bespoke inductive).  It imports both the canonical
`StepRename` (for `Step.rename` and `rename_lift_newestVar`) and
`StepEta`; nothing in the canonical typed stack imports it, so
`StepEta` is no longer in the typed engine's transitive closure.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStepEtaRename.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

namespace RawTerm

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
