import FX1PolyAudit.AuditGen
-- Leaf module of the FXProfile slice (CertifiedViewsSound imports
-- CertifiedViews, so importing it transitively loads every
-- FX1Poly.FXProfile declaration).
import FX1Poly.FXProfile.CertifiedViewsSound

/-! # FX1PolyAudit/AuditFXProfile — namespace zero-axiom sweep for the FX-profile views

Persistent zero-axiom gate for the FX-profile certifier entry points.
The slice carries the profile-fixed ingress wrappers (`certifyFXCellExact?`
/ `certifyFXCell?`, binding the `PolyProfile` parameter to `fxProfile`)
and their four soundness theorems (compH-rejection, exact-erasure,
cellDimension-equality, and the HEq no-laundering guarantee).

Every wrapper is a definitional delegation to the already-audited
general certifier (`certifyRawCellExact?` / `inferRawCellGeneral?`) and
every soundness theorem is a one-line application of the corresponding
general no-laundering theorem — no new reasoning is introduced.

The `#audit_namespace` walk loads every declaration under
`FX1Poly.FXProfile` and fails the build at the first axiom leak
(including `propext` / `Quot.sound` / `Classical.choice`).
-/

#audit_namespace FX1Poly.FXProfile
#assert_namespace_min_count FX1Poly.FXProfile 6
