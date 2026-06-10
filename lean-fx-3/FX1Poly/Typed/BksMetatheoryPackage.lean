import FX1Poly.Typed.ParametricityTransferLedger
import FX1Poly.Tier0.FxBaseRenamingVecSconingPreservation

/-! # FX1Poly/Typed/BksMetatheoryPackage
    — ★ the BKS sconing metatheory package: preservation + the three transfers, bundled (SN-096, #599)

The top of the `SconingConstructionLevel` ladder.  The BKS thesis ("sconing is enough", FSCD 2023):
ONE gluing construction yields canonicity, normalization, and parametricity.  This file bundles the
shipped realization into one record and inhabits it:

  * `BksGluedMetatheoryPackage` — the package: the concrete `SconingPreservation` instance (SN-090)
    plus the three glued-model transfer theorems — canonicity (SN-093), normalization (SN-094), and
    parametricity (SN-095) — each quantified over EVERY glued type (`GluedTypeCell`, hence over the
    SN-091 Π/Σ/universe lifts) with ONE shared hypothesis shape: the fundamental obligation.  That
    sharing IS the thesis: one fundamental theorem feeds all three extractions, the extractions
    themselves being free (CR1, the normalizer, the membership itself).
  * ★ `fxBksGluedMetatheoryPackage` — the inhabitant, by direct application of the four shipped
    pieces.  The `fxSconingConstructionLevel` ledger advances to its TOP level
    `.bksMetatheoryPackage`; every `has*` theorem in `InternalSconing.lean` is now `true`.

## Honest scope boundary

The bundle records what the ladder PROVED, including its verdicts: the three Tier-0 extraction
RECORDS were each found wanting (canonicity's refuted, normalization's content-free, parametricity's
lawless) and the bundled transfers are their honest law-carrying replacements over the glued model.
Per the SN-092/HCAP triangulation discipline, the sconing SN content COMPOSES the Tait candidates
(`sconingSN_eq_taitComposition`) — this package is the Leg-1 categorical organization of the proven
metatheory, not an independent second proof of SN.  Binary parametricity and the full-syntactic-base
sconing (beyond the closed/glued reading) remain the recorded follow-ons.

## Zero-axiom verification

A structure whose fields restate the three shipped transfer theorems plus the shipped preservation
instance, inhabited by direct application.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- **The BKS sconing metatheory package**: the concrete preservation instance plus the three
glued-model transfer theorems, each over every glued type with the ONE shared fundamental
hypothesis — the "one functor, three metatheorems" bundle. -/
structure BksGluedMetatheoryPackage where
  /-- The concrete BKS preservation witness over the renaming RMC (SN-090). -/
  preservation :
    SconingPreservation fxBaseRenamingVecRMC fxBaseRenamingVecGlobalSections
  /-- Canonicity transfer (SN-093): well-typedness → canonicity (strong normalization) through any
  glued type's scone. -/
  canonicityTransfer :
    ∀ {scope : Nat} (glued : GluedTypeCell (scope + 1))
      {isWellTyped : RawTerm (scope + 1) → Prop},
      (∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term) →
      ∀ term : RawTerm (scope + 1), isWellTyped term → IsStronglyNormalizing term
  /-- Normalization transfer (SN-094): well-typedness → reaches a normal form. -/
  normalizationTransfer :
    ∀ {scope : Nat} (glued : GluedTypeCell (scope + 1))
      {isWellTyped : RawTerm (scope + 1) → Prop},
      (∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term) →
      ∀ term : RawTerm (scope + 1), isWellTyped term →
        ∃ normalForm : RawTerm (scope + 1),
          StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm
  /-- Parametricity transfer (SN-095): well-typedness → the term satisfies its type's relational
  interpretation (and is strongly normalizing). -/
  parametricityTransfer :
    ∀ {scope : Nat} (glued : GluedTypeCell (scope + 1))
      {isWellTyped : RawTerm (scope + 1) → Prop},
      (∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term) →
      ∀ term : RawTerm (scope + 1), isWellTyped term →
        glued.computable term ∧ IsStronglyNormalizing term

/-- ★ **The package inhabited** — the four shipped pieces, applied directly.  One fundamental
obligation per glued type feeds all three extractions; the extractions themselves are free. -/
def fxBksGluedMetatheoryPackage : BksGluedMetatheoryPackage where
  preservation := fxBaseRenamingVecSconingPreservation
  canonicityTransfer := fun {scope} glued {isWellTyped} fundamental term typed =>
    GluedTypeCell.canonicityTransfer (scope := scope) glued
      (isWellTyped := isWellTyped) fundamental term typed
  normalizationTransfer := fun {scope} glued {isWellTyped} fundamental term typed =>
    GluedTypeCell.normalizationTransfer (scope := scope) glued
      (isWellTyped := isWellTyped) fundamental term typed
  parametricityTransfer := fun {scope} glued {isWellTyped} fundamental term typed =>
    GluedTypeCell.parametricityTransfer (scope := scope) glued
      (isWellTyped := isWellTyped) fundamental term typed

end FX1Poly.Typed
