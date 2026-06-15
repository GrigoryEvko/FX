import FX1Poly.Tier0.Mode.GradeAlgebra.ResourceGraded

/-!
# Resource-Graded Doctrine — re-import shim over Tier0/GradeAlgebra

The ordered-grade-semiring substrate + the usage/security grade algebras are now relocated to
`Tier0/GradeAlgebra/ResourceGraded.lean` (the canonical Tier-0 home of the grade algebra).  The
declarations remain in the `FX1Poly.Modal` namespace, so the
§6 dimension files, the `Typed` graded-judgment consumers, and the audit gates that `import
FX1Poly.Modal.ResourceGraded` keep resolving unchanged — this shim just preserves that historical import
path.  The namespace rename to `FX1Poly.Tier0.GradeAlgebra` is deferred to the later Core↔Tier0
dependency-inversion pass.
-/
