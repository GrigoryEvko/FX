import FX1Poly.Tier0.InternalSconing
import FX1Poly.Tier0.FxBaseRenamingVecRMC
import FX1Poly.Tier0.FxBaseRenamingVecGlobalSections

/-! # FX1Poly/Tier0/FxBaseRenamingVecSconingPreservation
    — the concrete `SconingPreservation` instance over the extensional renaming base (SN-090, #593)

`InternalSconing.lean` (BKS, FSCD 2023) defines `SconingPreservation baseCwR globalSections` — the
obligation that (a) every representable map of the base CwR lifts to a `SconingLift`, and (b) every
pullback square lifts to a `SconingPullbackLift`.  The file's own docstring is explicit that possessing
the *type* is not a metatheory-transfer theorem: "a concrete inhabitant for the intended base category
is still required."  SN-089 (#592) supplied the `GlobalSections` over the renaming base; this file
supplies that concrete inhabitant — the first `SconingPreservation` over a genuine FX CwR
(`fxBaseRenamingVecRMC`, the extensional data-morphism renaming category closed by SN-084/085/085a).

## The two lifts (both genuine, both zero-axiom)

  * **`liftsRepresentable`** — the REINDEXING lift.  For a base morphism `f : A ⟶ B`, the canonical BKS
    lift reindexes the tautological-`B` sconing object along `f`: the source sconing object is
    `(A, Γ(B), sectionMap f)` (semantic domain `Γ(B)`, realization the contravariant global-sections
    action `sectionMap f : Γ(B) → Γ(A)`), the target is tautological-`B` `(B, Γ(B), id)`, and the
    semantic map is `id`.  The gluing square `sectionMap f ∘ targetRealization ∘ semanticMap =
    sourceRealization` is `sectionMap f ∘ id ∘ id = sectionMap f`, i.e. `rfl`.  This is the textbook
    reindexing lift; it uses the real `sectionMap`, and it works UNIFORMLY for every base morphism — the
    representability hypothesis is unused (a strengthening, not a weakening).
  * **`liftsPullbacks`** — the tautological lift.  The pullback apex `square.pullbackObject` lifts to its
    own tautological sconing object `SconingObject.tautological` (`S = Γ(pullbackObject)`, realization
    `id`); `projectsToPullback` is `rfl` (the tautological object's `syntacticObject` IS the apex).

## Honest scope boundary

This advances the SN-090 deliverable: a CONCRETE `SconingPreservation` inhabitant for the renaming base.
It is NOT a canonicity / normalization / parametricity TRANSFER theorem — `SconingPreservation` as
defined is the existence-level preservation witness (it carries only the syntactic `projectsToPullback`
law, no coherence tying the lifts together), so it is inhabitable over any `(RMC, GlobalSections)`; the
content here is realizing it concretely and correctly over the FX renaming base.  The real metatheory
strength lives in the EXTRACTION records (`CanonicityExtraction.extractRealizes`,
`NormalizationExtraction.normalizeIdempotent`), whose laws are the downstream ledger work SN-093..096.
Accordingly this file does NOT advance the `fxSconingConstructionLevel` ledger (it stays at
`extractionRecordInterfaces`): the ledger tracks the sconing subsystem for the intended FULL FX
syntactic base, of which this pure-renaming substrate is a precursor, and the ledger advancement to
`concretePreservationInstance` is the deliberate act SN-093..096 perform once the transfer theorems land.

## Zero-axiom verification

Pure structure population over the shipped substrate: the `GlobalSections.sectionMap` (SN-089), the
`SconingObject.tautological` constructor, and two `rfl` laws (the reindexing commute square and the
tautological projection).  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- **The concrete `SconingPreservation` over the extensional renaming base.**  `liftsRepresentable` is
the reindexing lift `(A, Γ(B), sectionMap f) ⟶ taut(B)` (uniform over all base morphisms, commute = rfl);
`liftsPullbacks` is the tautological object over the pullback apex (`projectsToPullback` = rfl).  The
first concrete BKS preservation witness for a genuine FX CwR; existence-level (the transfer theorems are
SN-093..096). -/
def fxBaseRenamingVecSconingPreservation :
    SconingPreservation fxBaseRenamingVecRMC fxBaseRenamingVecGlobalSections where
  liftsRepresentable := fun {_objectA objectB} morphism _isRepresentable =>
    { sourceSemanticDomain := fxBaseRenamingVecGlobalSections.sections objectB
      targetSemanticDomain := fxBaseRenamingVecGlobalSections.sections objectB
      sourceRealizationMap := fxBaseRenamingVecGlobalSections.sectionMap morphism
      targetRealizationMap := id
      semanticMap := id
      commutes := fun _closedSection => rfl }
  liftsPullbacks := fun square =>
    { liftedObject :=
        SconingObject.tautological fxBaseRenamingVecGlobalSections square.pullbackObject
      projectsToPullback := rfl }

end FX1Poly.Tier0
