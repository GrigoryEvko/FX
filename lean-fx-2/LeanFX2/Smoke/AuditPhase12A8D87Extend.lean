import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness

/-! # AuditPhase12A8D87Extend — D8.7-EXTEND zero-axiom audit.

Reviewer-facing axiom regression log for the second-round extension of the
encoded Lean-kernel typing relation and executable checker.  Closes ticket
#1524 by adding `letE`, `mdata`, and the two `lit` arms (`litNat`,
`litStrAtom`) plus the canonical primitive name helpers
(`Expr.natTypeName`, `Expr.stringTypeName`) and their type-expression
shorthands (`Expr.natType`, `Expr.stringType`).

The remaining three Lean-kernel constructors (`proj`, `fvar`, `mvar`)
are intentionally kept without HasType arms in this slice; their typing
rules depend on infrastructure (inductive-spec lookup for `proj`,
fvar-context for `fvar`, mvar-policy decision for `mvar`) that belongs
to later slices.  See `LeanFX2.FX1.LeanKernel.HasType`'s docstring at
the deferred-constructors comment block for the architectural notes.

Every declaration listed must report "does not depend on any axioms".
The strict harness gate in `LeanFX2.Tools.AuditAll.AuditFX1LeanKernel_Other`
fails the build if any does. -/

-- Primitive-name helpers and canonical literal type expressions.
#print axioms LeanFX2.FX1.LeanKernel.Expr.natTypeName
#print axioms LeanFX2.FX1.LeanKernel.Expr.stringTypeName
#print axioms LeanFX2.FX1.LeanKernel.Expr.natType
#print axioms LeanFX2.FX1.LeanKernel.Expr.stringType

-- New HasType arms.
#print axioms LeanFX2.FX1.LeanKernel.HasType.letE
#print axioms LeanFX2.FX1.LeanKernel.HasType.mdata
#print axioms LeanFX2.FX1.LeanKernel.HasType.litNat
#print axioms LeanFX2.FX1.LeanKernel.HasType.litStrAtom

-- The HasType inductive itself, after the four-arm extension.
#print axioms LeanFX2.FX1.LeanKernel.HasType

-- Executable checker entrypoint, after extension.
#print axioms LeanFX2.FX1.LeanKernel.check
#print axioms LeanFX2.FX1.LeanKernel.check_sound
