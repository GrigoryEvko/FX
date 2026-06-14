import FX1Poly.Core.Substrate.Cell.EraseToRoseRenameInvariant
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTable
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaTableBackward
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTableSourceShape

/-!
# Root-table eta-contraction embeds into the `eraseToRose` recursive
path order

`StepEtaRootTable.rpoEmbeds` is the eta-analogue of the iota embedding
`IotaHeadStep.rpoEmbeds` (RawIotaRpoAssembly): every raw eta source
shape wraps its target in one or two generator layers, so the target is
a SUBTERM of the source's rose image, and the source is therefore
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

Two of the three raw-tier shapes (`etaLamSource`, `etaPathLamSource`)
put the inner function under one extra binder via `RawTerm.weaken`;
`eraseToRose_weaken` (EraseToRoseRenameInvariant) erases that binder gap
so the target's rose image matches the wrapped subterm exactly.  The
`etaPairSource` shape carries the target directly via
`Rpo.subtermStrict` composed with `Rpo.subtermEq`.  The root contraction
is inverted and its source shape read off the bespoke-construction-free
`stepEtaRootTableSourceShape` dispatcher, never a `Step.eta`.
-/

open FX1Poly.Core.RawIotaRpo
open FX1Poly.Core.RpoInductive

namespace FX1Poly.Core

/-- **★ Every RAW-TIER
root contraction of the canonical eta-rule table RPO-decreases the
`eraseToRose` order, for any precedence.  Proved NATIVELY: the root
contraction is inverted to its cell shape, the raw source SHAPE is read
off via the bespoke-construction-free `stepEtaRootTableSourceShape`
dispatcher, and `Rpo.subterm*` subterm reasoning over the three raw-tier
source shapes (`etaLamSource`/`etaPairSource`/`etaPathLamSource`)
discharges the order — never constructing a `Step.eta` and never
crossing the bespoke adequacy bridge.

Phrased over the canonical 8-row `etaRuleTable` so the shared
iota∪eta well-founded order (firings 72-74) is available to the table
union with NO fresh measure — `StepEtaRootTable.rpoEmbeds` serves
`RawIotaEtaFullStepSN`. -/
theorem StepEtaRootTable.rpoEmbeds {scope : Nat}
    {prec : Generator → Generator → Prop}
    {source target : RawTerm scope}
    (rootStep : StepEtaRootTable source target) :
    Rpo prec (eraseToRose source) (eraseToRose target) := by
  obtain ⟨rule, isRow, isRawTier, introPayload, introChildren,
    sourceShape, contracts⟩ := rootStep.invert
  subst sourceShape
  rcases stepEtaRootTableSourceShape isRow isRawTier introPayload contracts
    with ⟨domainAnn, lamShape⟩ | pairShape | pathLamShape
  · rw [lamShape]
    show Rpo prec
      (.node Generator.gen_lam
        [eraseToRose domainAnn,
         .node Generator.gen_app
          [eraseToRose (RawTerm.weaken target),
           eraseToRose RawTerm.newestVar]])
      (eraseToRose target)
    rw [eraseToRose_weaken]
    exact Rpo.subtermStrict Generator.gen_lam _ _ _
      (List.Mem.tail _ (List.Mem.head _))
      (Rpo.subtermEq Generator.gen_app _ _ (List.Mem.head _))
  · rw [pairShape]
    show Rpo prec
      (.node Generator.gen_pair
        [.node Generator.gen_fst [eraseToRose target],
         .node Generator.gen_snd [eraseToRose target]])
      (eraseToRose target)
    exact Rpo.subtermStrict Generator.gen_pair _ _ _ (List.Mem.head _)
      (Rpo.subtermEq Generator.gen_fst _ _ (List.Mem.head _))
  · rw [pathLamShape]
    show Rpo prec
      (.node Generator.gen_pathLam
        [.node Generator.gen_pathApp
          [eraseToRose (RawTerm.weaken target),
           eraseToRose RawTerm.newestVar]])
      (eraseToRose target)
    rw [eraseToRose_weaken]
    exact Rpo.subtermStrict Generator.gen_pathLam _ _ _ (List.Mem.head _)
      (Rpo.subtermEq Generator.gen_pathApp _ _ (List.Mem.head _))

end FX1Poly.Core
