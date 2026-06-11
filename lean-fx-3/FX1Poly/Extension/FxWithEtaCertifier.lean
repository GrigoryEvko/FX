import FX1Poly.Extension.ProfileExtension
import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.SubjectReductionEtaStructural
import FX1Poly.Core.SubjectReductionEtaBinder
/-! # FX1Poly/Extension/FxWithEtaCertifier — fxWithEta through the canonical certifier

`fxWithEta := extendProfile fxProfile etaReductionExtension` was, until
this file, pure bookkeeping: a profile-tower node whose interface
declares two eta rules and zero generators.  This file pushes it
through the canonical v2 substrate AS FAR AS IT GOES — the first
end-to-end demonstration that a profile extension is more than an
interface record.

## What carries the demonstration

The certified layer is profile-UNIFORM by construction: `CellBoundary`
takes its profile as a phantom (`_profile`, never inspected), no
constructor of `PolyCell` reads a profile field, and
`certifyRawCellExact?` / `inferRawCellGeneral?` never scrutinize the
profile — the profile index is bookkeeping threaded through types.
Consequently, on every CONCRETE input the certifier's verdict computes
with the profile a FREE VARIABLE, so corpus acceptance theorems hold
for ALL profiles at once and `fxWithEta` instances are instantiations,
not re-proofs.  That is the precise sense in which the eta extension
"threads through" the certifier: extending the profile cannot change
any verdict.

## What is demonstrated end-to-end

1. **Profile-uniform certification** of a corpus (unit leaf, unit
   pair, the eta-pair source) — stated with the profile universally
   quantified, proof `⟨_, rfl⟩` (the verdict computes profile-free).
2. **fxWithEta instances** — the extended profile certifies the
   corpus, including a dim-1 `identityCell` through the exact
   certifier (the CELL layer, not just dim-0 terms).
3. **The OPERATIONAL eta link**: the extension's two declared rules
   (`EtaReductionRule.etaLam` / `.etaPath`) are not dangling names —
   each maps to a kernel `Step.eta` constructor with a PROVEN
   certification-preservation theorem (`preservedByEtaLam` /
   `preservedByEtaPathLam`), instantiated at `fxWithEta` via
   `EtaReductionRule.preservesCertificationAt`.  A concrete eta-pair
   step is run end-to-end: source certified at fxWithEta, the step
   fires, the target's certificate is DERIVED by the SR-eta arm.
4. **Surface pins**: the only profile field `extendProfile` changes is
   the fibration tower; every certifier-relevant axis field of
   `fxWithEta` is definitionally `fxProfile`'s.

## Honest boundary — what does NOT close here

* The ProfileLens generator-roundtrip for fxWithEta is V2-L5.1 (#215):
  eta adds zero generators, so the lens question is degenerate here;
  the non-degenerate test needs a generator-adding extension.
* Capability/metatheory TRANSFER is deliberately absent:
  `etaReductionExtension.capabilities = bot` and the meet collapses
  (`extendedCapabilities_etaReductionExtension_eq_bot`) — flipping the
  `admissibleProfileTheorem` ledger is SN-108 (#611), gated on genuine
  transfer theorems, not on this demonstration.
* The eta rules' SEMANTIC metatheory (typed eta-SR, beta-eta SN,
  beta-eta Church-Rosser) is ALREADY proven for the canonical kernel
  at the term layer (grown-engine eta-SR, OSN-1, BECR-1); this file
  adds the missing CELL-layer link only.  Nothing here claims the
  extension MECHANISM transfers those theorems — the extension points
  at theorems the kernel owns.

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean` (per-decl gates +
the `FX1Poly.Extension` namespace sweep, which loads this file). -/

namespace FX1Poly.Extension

open Core

/-! ## The demonstration corpus -/

/-- Unit leaf: the smallest certifiable term cell. -/
def unitLeafTerm : RawTerm 0 :=
  .mkGen .gen_unit () .childNil

/-- A concrete pair of units — the subject of the eta-pair step. -/
def unitPairTerm : RawTerm 0 :=
  .mkGen .gen_pair ()
    (.childCons unitLeafTerm (.childCons unitLeafTerm .childNil))

/-! ## Profile-uniform certification

The certifier's verdict on each concrete corpus term computes with the
profile a FREE variable — the structural reason no profile extension
can change a certification verdict. -/

/-- The unit leaf certifies under EVERY profile. -/
theorem certified_unitLeaf_uniform (profile : PolyProfile) :
    Certified (profile := profile) unitLeafTerm :=
  ⟨_, rfl⟩

/-- The unit pair certifies under EVERY profile. -/
theorem certified_unitPair_uniform (profile : PolyProfile) :
    Certified (profile := profile) unitPairTerm :=
  ⟨_, rfl⟩

/-- The eta-pair SOURCE `pair (fst p) (snd p)` over the unit pair
certifies under EVERY profile. -/
theorem certified_etaPairSource_uniform (profile : PolyProfile) :
    Certified (profile := profile) (RawTerm.etaPairSource unitPairTerm) :=
  ⟨_, rfl⟩

/-! ## fxWithEta instances — the extension threads through the certifier -/

/-- fxWithEta certifies the unit leaf. -/
theorem fxWithEta_certifies_unitLeaf :
    Certified (profile := fxWithEta) unitLeafTerm :=
  certified_unitLeaf_uniform fxWithEta

/-- fxWithEta certifies the unit pair. -/
theorem fxWithEta_certifies_unitPair :
    Certified (profile := fxWithEta) unitPairTerm :=
  certified_unitPair_uniform fxWithEta

/-- fxWithEta certifies the eta-pair source. -/
theorem fxWithEta_certifies_etaPairSource :
    Certified (profile := fxWithEta) (RawTerm.etaPairSource unitPairTerm) :=
  certified_etaPairSource_uniform fxWithEta

/-- fxWithEta certifies a dim-1 identity CELL through the exact
certifier — the extension reaches the cell layer, not only dim-0
term cells. -/
theorem fxWithEta_certifies_identityCell :
    ∃ cert :
        CertifiedRawCell fxWithEta 0
          (.identityCell (.termBase unitLeafTerm)),
      certifyRawCellExact? (profile := fxWithEta) 0
          (.identityCell (.termBase unitLeafTerm)) = Except.ok cert :=
  ⟨_, rfl⟩

/-! ## The operational eta link

The extension's DECLARED rule namespace (`EtaReductionRule`) maps to
the kernel's `Step.eta` constructors with proven
certification-preservation — the bookkeeping names point at real
operational rules with real SR theorems. -/

/-- The certification-preservation statement each declared eta rule
points at, over an arbitrary profile: contracting the rule's source
shape preserves dim-0 certification.  `etaLam` is the kernel's
`Step.eta.etaLam`; the interface name `etaPath` is the kernel's
`Step.eta.etaPathLam`. -/
def EtaReductionRule.preservesCertificationAt
    (profile : PolyProfile) : EtaReductionRule → Prop
  | .etaLam =>
      ∀ {scope : Nat} (domainAnn innerFunction : RawTerm scope),
        HasCertifiedCellDim0 (profile := profile)
          (RawTerm.etaLamSource domainAnn innerFunction) →
        HasCertifiedCellDim0 (profile := profile) innerFunction
  | .etaPath =>
      ∀ {scope : Nat} (innerPath : RawTerm scope),
        HasCertifiedCellDim0 (profile := profile)
          (RawTerm.etaPathLamSource innerPath) →
        HasCertifiedCellDim0 (profile := profile) innerPath

/-- ★ Both declared eta rules preserve certification at fxWithEta —
the extension's rule namespace discharged against the kernel's SR-eta
arms, instantiated at the extended profile. -/
theorem EtaReductionRule.fxWithEta_preservesCertification :
    ∀ (rule : EtaReductionRule),
      rule.preservesCertificationAt fxWithEta
  | .etaLam => fun domainAnn innerFunction sourceCert =>
      HasCertifiedCellDim0.preservedByEtaLam
        (domainAnn := domainAnn) (innerFunction := innerFunction)
        sourceCert
  | .etaPath => fun innerPath sourceCert =>
      HasCertifiedCellDim0.preservedByEtaPathLam
        (innerPath := innerPath) sourceCert

/-! ## A concrete eta step end-to-end at fxWithEta -/

/-- The eta-pair step fires on the concrete corpus pair. -/
theorem etaPairStep_fires_on_unitPair :
    Step.eta (RawTerm.etaPairSource unitPairTerm) unitPairTerm :=
  .etaPair unitPairTerm

/-- The step's SOURCE has a certified dim-0 cell at fxWithEta
(bridged from the uniform certification). -/
theorem fxWithEta_etaPairSource_hasCertifiedCell :
    HasCertifiedCellDim0 (profile := fxWithEta)
      (RawTerm.etaPairSource unitPairTerm) :=
  (certified_etaPairSource_uniform fxWithEta).toHasCertifiedCellDim0

/-- ★ The step's TARGET certificate, DERIVED by the SR-eta arm at the
extended profile: source certified + eta step ⟹ target certified.
The full end-to-end demonstration in one composition. -/
theorem fxWithEta_etaPairTarget_certified_viaSR :
    HasCertifiedCellDim0 (profile := fxWithEta) unitPairTerm :=
  HasCertifiedCellDim0.preservedByEtaPair
    fxWithEta_etaPairSource_hasCertifiedCell

/-! ## Surface pins — only the fibration tower changed -/

/-- The extension's ONLY profile-field effect: one tower node. -/
theorem fxWithEta_fibrationTower_eq :
    fxWithEta.fibrationTower = .extend fxProfile.fibrationTower := rfl

/-- The algebra universe — the field the certifier's generator table
conceptually lives under — is untouched. -/
theorem fxWithEta_algebraUniverse_eq :
    fxWithEta.algebraUniverse = fxProfile.algebraUniverse := rfl

/-- The universe configuration is untouched. -/
theorem fxWithEta_universeConfig_eq :
    fxWithEta.universeConfig = fxProfile.universeConfig := rfl

end FX1Poly.Extension
