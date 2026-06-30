import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextStructureIdentity

/-! # FX1PolyAudit/.../ContextStructureIdentity — zero-axiom gate for context-32

Per-declaration zero-axiom gate for `context-32`'s deliverable
(`FX1Poly/Tier0/Context/ContextStructureIdentity.lean`): the STRUCTURE IDENTITY PRINCIPLE for contexts —
transport of structure along a categorical iso (the funext-free `CategoryIso` of `context-30`) plus
OBSERVATIONAL SUBSTITUTION (the action-on-observations characterization).  The SIP transport via `Eq.rec`
along the univalent universe's `isoToId`, its reflexivity coherence, the SIP statement proven at the discrete
set-level witness (iso-contexts are equal), observational indistinguishability of iso-contexts, and the
by-computation bridge to `context-31`'s `Id_U ↝ Equiv`.  The full HOMOTOPY SIP (which rests on the univalence
axiom / funext) is the honest `×type` deferral (`= false`); the Core table-native row is the honest cross-axis
sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The SIP transport + its reflexivity coherence
#assert_no_axioms FX1Poly.Tier0.transportStructureAlongContextIso
#assert_no_axioms FX1Poly.Tier0.isoToId_identityIso
#assert_no_axioms FX1Poly.Tier0.transportStructureAlongContextIso_identityIso

-- SIP at the discrete (set-level) witness
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_isoImpliesObjectEqual
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_transportStructure

-- Observational substitution (the action on observations) + the by-computation bridge
#assert_no_axioms FX1Poly.Tier0.ContextObservation
#assert_no_axioms FX1Poly.Tier0.contextIso_observationallyIndistinguishable
#assert_no_axioms FX1Poly.Tier0.definitionalUnivalence_observationsAgree

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxContextStructureIdentity_hasStructureIdentityPrinciple
#assert_no_axioms FX1Poly.Tier0.fxContextStructureIdentity_hasObservationalSubstitution
#assert_no_axioms FX1Poly.Tier0.fxContextStructureIdentity_hasFullHomotopySIP
#assert_no_axioms FX1Poly.Tier0.fxContextStructureIdentity_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_transportStructure_identity_smoke
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_observation_smoke

end FX1PolyAudit
