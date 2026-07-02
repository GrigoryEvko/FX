import FX1Poly.Typed.Cell.CellConstructors

/-! # FX1Poly/Typed/Cell/CellShorthands — the λ/app term-cell smart constructors (live rule-data)

The two Church-style term-former cell constructors `lamCell` and `appCell`, extracted out of the
(deprecated) Π typing engine `HasTypeDescPi` so the rule-data tables and the native union read the cell
VOCABULARY without importing a dead typing engine.  These are PURE SYNTAX over the one polygraph
substrate (`RawTerm.mkGen` + the generator table), exactly like every sibling constructor in
`CellConstructors` (`piTyCodeCell`, `pathLamCell`, `pathAppCell`, …) — they depend only on `RawTerm`
and carry NO typing-judgment reference.

  * `lamCell` — the λ cell `gen_lam` with a domain-annotation child (shift `0`) and a body child
    (shift `1`), the same `[0, 1]` child shape as `piTyCodeCell`.
  * `appCell` — the application cell `gen_app` with the function and argument children (both shift `0`).

The Π engine that once housed these keeps only its (deprecated) description-driven JUDGMENT and imports
this module; the live substrate reads only the cell constructors below.  The fully-qualified names are
unchanged: `FX1Poly.Typed.lamCell`, `FX1Poly.Typed.appCell`.

## Zero-axiom

Each constructor is a single `RawTerm.mkGen` application — no proofs, no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Cell/CellShorthands.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The λ cell, Church-style: `gen_lam` with the domain-annotation child (parent scope,
shift `0`) followed by the body child (under one fresh value binder, shift `1`).  Same
`[0, 1]` child shape as `piTyCodeCell`. -/
def lamCell {scope : Nat} (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) :
    RawTerm scope :=
  .mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))

/-- The application cell: `gen_app` with the function and argument children (both at the parent
scope, shifts `[0, 0]`). -/
def appCell {scope : Nat} (functionTerm argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))

end FX1Poly.Typed
