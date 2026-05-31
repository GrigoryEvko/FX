import FX1Poly.Core.InferRawCellGeneral

/-! # FXProfile/CertifiedViews — FX-profile entry points over the certifier

The FX-profile-fixed entry points for the certifier infrastructure.
Both wrappers ARE the canonical ingress for callers that work in the
default `fxProfile` (the only profile currently supported).

## Why a separate FX-profile layer

The general certifier infrastructure is parameterized over
`{profile : PolyProfile}` to allow restricted FX profiles ("no-HoTT
FX", "constructive-only FX", "embedded-safe FX").  Most callers —
the typechecker, the FX kernel front-end, the agent protocol — do
NOT need to thread the profile parameter.  They always work in the
default `fxProfile`.

The FX-profile views bind the profile parameter once at the ingress,
giving callers a profile-less API:

```
inferRawCellGeneral? (profile := fxProfile) scope raw   -- general API
       vs.
certifyFXCell?                              scope raw   -- FX-profile API
```

The semantic difference is zero — both reduce to the same computation.
The ergonomic difference is significant: one less implicit to specify,
one less constraint to remember.

The general certifier handles every well-formed fixture by recursive
descent + admission lookup + payload evidence, so the FX-profile view
layer is a pair of one-line wrappers around the general API.

## API design — un-indexed inputs

`RawCell scope` has NO `dim` type parameter — dim is COMPUTED from
the raw cell's structure via `RawCell.dim` (a `def`, not an index):

```
def certifyFXCellExact? (scope : Nat) (raw : RawCell scope) : ...
```

There is no `{dim : CellDim}` implicit, so there is no dim to specify
or solve for at the call site.  Callers pass any well-formed
`RawCell` and the certifier reads its dim internally; the
dim-stratification propext class does not arise when dim is not a
type index.

## Zero-axiom verification

Both definitions are pure wrappers — the certifier infrastructure
they delegate to (`certifyRawCellExact?` and `inferRawCellGeneral?`)
is audited zero-axiom.  The wrappers add no new reasoning, no new
declarations, no new axioms.  Audit gates live in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.FXProfile

open Core

/-- The FX-profile raw-indexed certifier: ONE entry point certifying any
non-`horizontalComposite` raw cell at any dimension, with the certified
result indexed by the EXACT input so erasure back to the input is
definitional.  This is the canonical general ingress for the FX profile.

Wraps `certifyRawCellExact?` with `profile := fxProfile`.  Semantic
equivalence is by definition. -/
def certifyFXCellExact? (scope : Nat) (raw : RawCell scope) :
    Except CellCheckRejection
      (CertifiedRawCell fxProfile scope raw) :=
  certifyRawCellExact? (profile := fxProfile) scope raw

/-- The FX-profile existential ingress: returns the dim-erased
certified-result package carrying inferred sort, dimension, the
certified cell, and a raw-code preservation certificate.

Wraps `inferRawCellGeneral?` with `profile := fxProfile`.  Use this
when the caller doesn't need the raw cell pinned at the type level —
typical for the FX kernel's typechecker, where the inferred dimension
is read off the result rather than asserted at the call site. -/
def certifyFXCell? (scope : Nat) (raw : RawCell scope) :
    Except CellCheckRejection
      (CertifiedRawCellResult fxProfile scope) :=
  inferRawCellGeneral? (profile := fxProfile) scope raw

end FX1Poly.FXProfile
