import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParRename
import LeanFX2.Bridge
import LeanFX2.Smoke.AuditPhase12AB18CumulConfluence

/-! # Smoke/AuditCumul33 — CUMUL-3.3 raw-layer compat suffices
(Phase CUMUL-2.6 Design D revision).

Phase 12.A.B17 (CUMUL-3.3).  Documents and verifies the architectural
finding: `Step.par.cumulUpInnerCong` requires NO new typed-layer
rename / subst compatibility theorem.

Phase CUMUL-2.6 Design D revision: the bridge no longer collapses to
`RawStep.par.refl _`; instead it now uses `RawStep.par.cumulUpMarkerCong`
on the inner-step's bridge result.  Both source and target raws
become `RawTerm.cumulUpMarker codeSourceRaw` / `cumulUpMarker
codeTargetRaw` — structurally distinct from every other ctor, so
inversion lemmas keep working unchanged.

## Path-Y resolution (raw-layer-suffices, Design D version)

The same architectural conclusion holds under Design D:

1. **Typed `Step.par.{rename,subst}_compatible` does not exist.**
   `LeanFX2/Reduction/Compat.lean` is a 38-line stub planning a future
   port.  No typed-layer parallel-step compatibility framework is in
   flight.

2. **The raw layer already covers cumulUpInnerCong uniformly.**
   `Step.par.toRawBridge`'s `cumulUpInnerCong` arm now lifts the
   inner step's bridge result via `RawStep.par.cumulUpMarkerCong`.
   The cumulUpMarker arm of `RawTerm.{rename,subst}` and
   `RawStep.par.{rename,subst_par}` recurse on the inner code raw,
   matching the typed `Term.{rename,subst}` cumulUp arm structurally.

3. **Typed `Term.rename` / `Term.substHet` on `Term.cumulUp` recurse
   on inner typeCode** (Phase CUMUL-2.6 Design D unification).

Combining (2) and (3): renaming or substituting an outer
`cumulUpInnerCong` parallel step now propagates structurally
through the cumulUpMarker raw shape; no new theorem ships.

## Audit declarations
-/

namespace LeanFX2

#print axioms LeanFX2.Term.cumulUp
#print axioms LeanFX2.Step.cumulUpInner
#print axioms LeanFX2.Step.par.cumulUpInnerCong
#print axioms LeanFX2.RawStep.par.cumulUpMarkerCong
#print axioms LeanFX2.Step.par.toRawBridge

end LeanFX2
