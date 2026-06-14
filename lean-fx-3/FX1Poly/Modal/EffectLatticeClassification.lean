import FX1Poly.Tier0.GradeAlgebra.EffectLatticeClassification

/-!
# Effect-Lattice Classification — re-import shim over Tier0/GradeAlgebra

The DIM-CLASS structure classification (the §6 dimension grade-algebra taxonomy) is now relocated to
`Tier0/GradeAlgebra/EffectLatticeClassification.lean` (the canonical Tier-0 home of the structure
classification).  The declarations remain in the `FX1Poly.Modal`
namespace, so the §6 lattice-dimension files, the `Typed` axis-obligation consumers, and the audit gates
that `import FX1Poly.Modal.EffectLatticeClassification` keep resolving unchanged — this shim just preserves
that historical import path.  The namespace rename to `FX1Poly.Tier0.GradeAlgebra` is deferred to the later
Core↔Tier0 dependency-inversion pass.
-/
