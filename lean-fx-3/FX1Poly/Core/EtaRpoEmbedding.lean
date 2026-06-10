import FX1Poly.Core.EraseToRoseRenameInvariant
import FX1Poly.Core.StepEta

/-!
# Raw eta-contraction embeds into the `eraseToRose` recursive path order

`Step.eta.rpoEmbeds` is the eta-analogue of the iota embedding
`IotaHeadStep.rpoEmbeds` (RawIotaRpoAssembly): every raw eta source
wraps its target in one or two generator layers, so the target is a
SUBTERM of the source's rose image, and the source is therefore
`Rpo`-above the target.

Crucially the proof goes through `Rpo.subtermEq` / `Rpo.subtermStrict`,
which do NOT mention the precedence — so the embedding holds for an
ARBITRARY `prec : Generator → Generator → Prop`.  Instantiating
`prec := iotaGenPrecedence` (RawIotaRpoAssembly) puts eta on the EXACT
well-founded order the iota fragment already uses (firings 72-74).
That shared order is what lets the combined iota+eta reduction inherit
strong normalization with no fresh measure: a union step is either an
iota step or an eta step, and both strictly decrease `eraseToRose`
under the same `Rpo`.

Two of the five arms (`etaLam`, `etaPathLam`) put the inner function
under one extra binder via `RawTerm.weaken`; `eraseToRose_weaken`
(EraseToRoseRenameInvariant) erases that binder gap so the target's
rose image matches the wrapped subterm exactly.  The other three
(`etaPair`, `etaModIntro`, `etaGlueIntro`) carry the target directly.
`etaGlueIntro` is the cheapest — the target is a DIRECT child of the
source node, so a single `Rpo.subtermEq` suffices; the others reach a
grandchild via `Rpo.subtermStrict` composed with `Rpo.subtermEq`.

Proven via the explicit recursor `Step.eta.rec` (the propext-clean
mutual-recursor pattern), not `cases`, mirroring `IotaStep.rpoEmbeds`.
-/

open FX1Poly.Core.RawIotaRpo
open FX1Poly.Core.RpoInductive

namespace FX1Poly.Core

/-- Every raw eta-contraction RPO-decreases the `eraseToRose` order,
for any precedence.  The eta target is a subterm of the source's rose
image (modulo a weakening rename for the two binder arms, erased by
`eraseToRose_weaken`). -/
theorem Step.eta.rpoEmbeds {scope : Nat} {prec : Generator → Generator → Prop}
    {source target : RawTerm scope} (hEta : Step.eta source target) :
    Rpo prec (eraseToRose source) (eraseToRose target) :=
  Step.eta.rec
    (motive := fun source target _ =>
      Rpo prec (eraseToRose source) (eraseToRose target))
    (fun domainAnn innerFunction => by
      show Rpo prec
        (.node Generator.gen_lam
          [eraseToRose domainAnn,
           .node Generator.gen_app
            [eraseToRose (RawTerm.weaken innerFunction),
             eraseToRose RawTerm.newestVar]])
        (eraseToRose innerFunction)
      rw [eraseToRose_weaken]
      exact Rpo.subtermStrict Generator.gen_lam _ _ _ (List.Mem.tail _ (List.Mem.head _))
        (Rpo.subtermEq Generator.gen_app _ _ (List.Mem.head _)))
    (fun pairTerm => by
      show Rpo prec
        (.node Generator.gen_pair
          [.node Generator.gen_fst [eraseToRose pairTerm],
           .node Generator.gen_snd [eraseToRose pairTerm]])
        (eraseToRose pairTerm)
      exact Rpo.subtermStrict Generator.gen_pair _ _ _ (List.Mem.head _)
        (Rpo.subtermEq Generator.gen_fst _ _ (List.Mem.head _)))
    (fun innerPath => by
      show Rpo prec
        (.node Generator.gen_pathLam
          [.node Generator.gen_pathApp
            [eraseToRose (RawTerm.weaken innerPath),
             eraseToRose RawTerm.newestVar]])
        (eraseToRose innerPath)
      rw [eraseToRose_weaken]
      exact Rpo.subtermStrict Generator.gen_pathLam _ _ _ (List.Mem.head _)
        (Rpo.subtermEq Generator.gen_pathApp _ _ (List.Mem.head _)))
    (fun modalTerm => by
      show Rpo prec
        (.node Generator.gen_modIntro
          [.node Generator.gen_modElim [eraseToRose modalTerm]])
        (eraseToRose modalTerm)
      exact Rpo.subtermStrict Generator.gen_modIntro _ _ _ (List.Mem.head _)
        (Rpo.subtermEq Generator.gen_modElim _ _ (List.Mem.head _)))
    (fun gluedTerm => by
      show Rpo prec
        (.node Generator.gen_glueIntro
          [.node Generator.gen_glueElim [eraseToRose gluedTerm],
           eraseToRose gluedTerm])
        (eraseToRose gluedTerm)
      exact Rpo.subtermEq Generator.gen_glueIntro _ _
        (List.Mem.tail _ (List.Mem.head _)))
    hEta

end FX1Poly.Core
