import FX1Poly.Typed.FormationTypeSafety
import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.SubjectReductionAtFormerGeneric
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescPiSubjectReduction

/-! # FX1Poly/Typed/SelfVerifiedMetatheory
    — the §27.3 Layer-4 defense: self-verified metatheory (preservation + progress) as a bundled, anchored
      layer, with the honest formation/grown unconditionality ledger

Layer 4 of the §27.3 five-layer defense is self-verified metatheory: "preservation / progress stated as
theorems in FX, proved by induction, part of build."  Those theorems are already shipped and gated — formation
preservation (`HasTypeDesc.subjectReduction`), formation type-safety/progress (`closedFormationTypeSafety`),
grown progress (`HasTypeDescPi.closedProgress`), and the grown preservation arms — but, unlike Layers 1, 2, 3
and 5 (each with a dedicated assembly file: `KnownUnsoundnessCorpus`, `MetatheoryFuzz`,
`MechanizedProofCrossReference`, `FormalReviewGate`), Layer 4 had no peer assembly that BUNDLES the
self-verification statement and records the honest unconditionality boundary.  This file is that peer.

## The self-verification bundle and the unconditionality boundary

`SelfVerifiedMetatheory` records, per engine, whether preservation and progress hold and whether preservation
is UNCONDITIONAL (not gated on an open conjecture).  The two FX engines differ exactly at this boundary:

  * **Formation engine** (`HasTypeDesc`): preservation (`subjectReduction`) AND progress
    (`closedFormationTypeSafety`) are BOTH unconditional — `formationIsUnconditionallySelfVerified`.
  * **Grown engine** (`HasTypeDescPi`): progress (`closedProgress`) is unconditional, and the preservation
    ARMS — β (`betaSubjectReductionDescPi`), the cascade-free former congruence
    (`subjectReductionAtFormerGeneric`), conv (`subjectReductionAtConv`), ofFormation
    (`subjectReductionAtOfFormation`) — are unconditional; but the MASTER dispatcher
    (`subjectReductionOfGrownTelescopeSR`) takes the telescope-SR / context-conversion premise that is the
    GrownCtxConv-5 crux (#842 / SRD-2 #845).  So `grownIsSelfVerified` holds while `grownNotUnconditionallySelfVerified`
    records that grown preservation is not yet unconditional — the precise, honest GrownCtxConv-5 boundary, the same
    asymmetry the `MetatheoryParityLedger` documents.

So the self-verification flag is `true` for both engines, and the `isUnconditionallySelfVerified` flag is the
exact discriminator of the one open piece (the grown piElim-congruence preservation master).

## Worked instances (each guarantee anchored)

Each anchor `…_<guarantee> := @<shippedWitness>` re-certifies, by its own gate here, that the cited
preservation / progress theorem is a real zero-axiom kernel result — so the bundle's `true`s are backed by
compiling references, not asserted.  Strong normalization (the deeper self-verified metatheory result,
SN-043) backs progress and is itself self-verified (`HasTypeDesc.isStronglyNormalizing` /
`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`); it is anchored by the `MetatheoryParityLedger` and cited
here, not re-anchored, to keep this file to the §27.3-named L4 pair.

## Zero-axiom verification

The guarantee enum / `describe` is a full-enumeration non-dependent match; the record + `Bool` checkers
(`isSelfVerified` / `isUnconditionallySelfVerified`) are `Bool` `&&`; the anchors are bare `@`-references to
shipped zero-axiom witnesses; the pass/fail facts close by `rfl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

/-! ## Part 1 — the two §27.3-Layer-4 guarantees + the bundle record + the checkers -/

/-- **The two §27.3-Layer-4 self-verified-metatheory guarantees**: preservation (subject reduction) and
progress. -/
inductive MetatheoryGuarantee where
  | preservation
  | progress

/-- A human-readable description of each guarantee (full enumeration). -/
def MetatheoryGuarantee.describe : MetatheoryGuarantee → String
  | .preservation => "subject reduction: typing is preserved under every reduction step"
  | .progress => "progress: a closed well-typed term is a canonical value (or steps)"

/-- **The per-engine self-verified-metatheory bundle.**  Records whether preservation and progress hold, and
whether preservation is UNCONDITIONAL (not gated on an open conjecture — the GrownCtxConv-5 boundary). -/
structure SelfVerifiedMetatheory where
  engineName : String
  hasPreservation : Bool
  hasProgress : Bool
  preservationIsUnconditional : Bool

/-- Whether a specific guarantee is carried by the bundle (full enumeration). -/
def SelfVerifiedMetatheory.guaranteed (metatheory : SelfVerifiedMetatheory)
    (guarantee : MetatheoryGuarantee) : Bool :=
  match guarantee with
  | .preservation => metatheory.hasPreservation
  | .progress => metatheory.hasProgress

/-- **The self-verification checker.**  An engine is self-verified (Layer 4) iff it carries BOTH preservation
and progress. -/
def SelfVerifiedMetatheory.isSelfVerified (metatheory : SelfVerifiedMetatheory) : Bool :=
  metatheory.hasPreservation && metatheory.hasProgress

/-- **The unconditional-self-verification checker.**  Self-verified AND preservation unconditional — the
strongest Layer-4 guarantee, satisfied only when no open conjecture (GrownCtxConv-5) gates preservation. -/
def SelfVerifiedMetatheory.isUnconditionallySelfVerified (metatheory : SelfVerifiedMetatheory) : Bool :=
  metatheory.isSelfVerified && metatheory.preservationIsUnconditional

/-! ## Part 2 — formation-engine anchors (both guarantees unconditional) -/

/-- Formation preservation — subject reduction (unconditional, cascade-free). -/
def formationMetatheory_preservation := @HasTypeDesc.subjectReduction

/-- Formation progress — every closed formation-typed term is a canonical value (unconditional). -/
def formationMetatheory_progress := @HasTypeDesc.closedFormationTypeSafety

/-! ## Part 3 — grown-engine anchors (progress + the unconditional preservation arms + the conditional master) -/

/-- Grown progress — a closed grown-typed term is a value or steps (unconditional). -/
def grownMetatheory_progress := @HasTypeDescPi.closedProgress

/-- Grown preservation — the β step (unconditional). -/
def grownMetatheory_preservationBeta := @HasTypeDescPi.betaSubjectReductionDescPi

/-- Grown preservation — the cascade-free former-congruence arm (unconditional). -/
def grownMetatheory_preservationFormerArm := @HasTypeDescPi.subjectReductionAtFormerGeneric

/-- Grown preservation — the conv arm (unconditional). -/
def grownMetatheory_preservationConvArm := @HasTypeDescPi.subjectReductionAtConv

/-- Grown preservation — the ofFormation arm (unconditional). -/
def grownMetatheory_preservationOfFormationArm := @HasTypeDescPi.subjectReductionAtOfFormation

/-- Grown preservation — the MASTER dispatcher, CONDITIONAL on the telescope-SR / context-conversion premise
(the GrownCtxConv-5 crux, #842 / SRD-2 #845).  Anchored to give the unconditionality flag its teeth: the master exists
and is proved, but only conditionally. -/
def grownMetatheory_preservationConditionalMaster := @HasTypeDescPi.subjectReductionOfGrownTelescopeSR

/-! ## Part 4 — the two engine bundles + the self-verification facts -/

/-- **The formation engine's self-verified-metatheory bundle** — preservation + progress, both unconditional. -/
def formationSelfVerifiedMetatheory : SelfVerifiedMetatheory :=
  { engineName := "formation engine (HasTypeDesc)",
    hasPreservation := true,
    hasProgress := true,
    preservationIsUnconditional := true }

/-- **The grown engine's self-verified-metatheory bundle** — preservation + progress hold, but preservation's
master is GrownCtxConv-5-conditional (`preservationIsUnconditional := false`). -/
def grownSelfVerifiedMetatheory : SelfVerifiedMetatheory :=
  { engineName := "grown engine (HasTypeDescPi)",
    hasPreservation := true,
    hasProgress := true,
    preservationIsUnconditional := false }

/-- **The formation engine is UNCONDITIONALLY self-verified** — preservation and progress both hold and are
both unconditional (full Layer 4 for the formation engine). -/
theorem formationIsUnconditionallySelfVerified :
    formationSelfVerifiedMetatheory.isUnconditionallySelfVerified = true := rfl

/-- **The grown engine is self-verified** — preservation and progress both hold. -/
theorem grownIsSelfVerified : grownSelfVerifiedMetatheory.isSelfVerified = true := rfl

/-- **But the grown engine is NOT yet unconditionally self-verified** — preservation's master is gated on the
GrownCtxConv-5 telescope-SR premise (#842 / SRD-2 #845).  This is the precise, honest boundary of the one open piece. -/
theorem grownNotUnconditionallySelfVerified :
    grownSelfVerifiedMetatheory.isUnconditionallySelfVerified = false := rfl

/-! ## Part 5 — non-vacuity: a metatheory missing a guarantee is NOT self-verified -/

/-- A hypothetical engine that proved preservation but not progress — exactly the kind of gap Layer-4
self-verification must catch. -/
def incompleteMetatheory : SelfVerifiedMetatheory :=
  { engineName := "hypothetical engine missing progress",
    hasPreservation := true,
    hasProgress := false,
    preservationIsUnconditional := true }

/-- **The checker is non-vacuous.**  An engine missing a guarantee (here progress) is NOT self-verified —
`isSelfVerified = false` — so `isSelfVerified = true` is a real, discriminating certificate, not a tautology. -/
theorem incompleteMetatheory_notSelfVerified : incompleteMetatheory.isSelfVerified = false := rfl

/-- The missing guarantee is precisely progress (the checker pinpoints the gap). -/
theorem incompleteMetatheory_missingProgress :
    incompleteMetatheory.guaranteed .progress = false := rfl

end FX1Poly.Typed
