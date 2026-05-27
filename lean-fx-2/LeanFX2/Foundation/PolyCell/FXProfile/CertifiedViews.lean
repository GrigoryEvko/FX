import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneral

/-! # FXProfile/CertifiedViews — FX-profile entry points over v2 certifier

This file ships the FX-profile-fixed entry points for the v2 certifier
infrastructure.  Both wrappers ARE the canonical ingress for callers
that work in the default `fxProfile` (currently the only profile
supported under v2).

Direct v2 counterpart to v1's `Core/CertifyExact.lean` general
ingress (`Core/CertifyExact.lean:113-126` `certifyFXCellExact?` and
`certifyFXCell?`).

## Why a separate FX-profile layer

The general v2 certifier infrastructure (#162-#171) is parameterized
over `{profile : PolyProfile}` to allow restricted FX profiles in the
future ("no-HoTT FX", "constructive-only FX", "embedded-safe FX").
Most callers — the typechecker, the FX kernel front-end, the agent
protocol — do NOT need to thread the profile parameter.  They always
work in the default `fxProfile`.

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

## How v2's view layer differs from v1's

v1's `CertifiedViews.lean` is 1167 lines because every per-fixture
certified package (`certifiedSeedTerm`, `certifiedApplicationVarZeroVarOne`,
`certifiedLambdaUnitTypeBodyVarZero`, ...) was hand-built — v1's
19-ctor `PolyTerm` made the general certifier too weak to handle
fixtures generically, so each fixture's certification needed bespoke
infrastructure.

In v2, the un-indexed `RawCell` substrate plus the generic `gen`
ctor mean the general certifier handles every well-formed fixture by
recursive descent + admission lookup + payload evidence (see #162's
docstring).  There is NO per-fixture scaffolding.  The FX-profile
view layer collapses to a pair of one-line wrappers around the
general API — UX, not new functionality.

The per-fixture certified packages (`CertifiedFXCell`,
`CertifiedFXArrow`, `CertifiedFXThinCell`, etc.) in v1 remain
migration-deferred to V2-mig.4 (#195).  They are consumer-facing
API, not certifier infrastructure.

## API design — un-indexed inputs

Note the SIGNATURE DIFFERENCE from v1:

```
-- v1 (dim-indexed raw substrate):
def certifyFXCellExact? (scope : Nat) {dim : CellDim}
    (rawCell : PolyTerm fxProfile dim) : ...

-- v2 (un-indexed raw substrate):
def certifyFXCellExact? (scope : Nat)
    (raw : RawCell scope) : ...
```

v2's `RawCell scope` has NO `dim` type parameter — dim is COMPUTED
from the raw cell's structure via `RawCell.dim` (a `def`, not an
index).  This was the v2 substrate's whole architectural payoff: the
dim-stratification propext class that haunted v1 simply does not
exist when dim isn't a type index.

The v2 entry points reflect this directly: no `{dim : CellDim}`
implicit, no `dim` to specify or solve for at the call site.  Callers
pass any well-formed `RawCell` and the certifier reads its dim
internally.

## Zero-axiom verification

Both definitions are pure wrappers — the certifier infrastructure
they delegate to (`certifyRawCellExact?` and `inferRawCellGeneral?`)
is already audited zero-axiom (#162 and #163).  The wrappers add no
new reasoning, no new declarations, no new axioms.  Audit gates live
in `Tools/AuditAll/AuditPolyCell.lean`.

## What's deferred

* **Soundness theorems** (`certifyFXCellExact?_sound`,
  `_compH_rejects`, `certifyFXCell?_accepted_cellDimension_eq`,
  `certifyFXCell?_sound`) → V2-L1cert.18 (#173).  Trivial one-line
  delegations to #165/#166/#167/#169, but kept as a separate task to
  preserve atomic commit semantics.

* **Per-fixture certified packages** (the FX-profile `CertifiedFXCell`
  / `CertifiedFXArrow` infrastructure consumed by FX1.Core) →
  V2-mig.4 (#195).  Re-points existing consumers onto v2.

* **The FX-profile coverage suite** would be a thin layer over
  v2's coverage suite (#170) with the profile fixed.  Not currently
  tracked as a task; can be added if downstream needs surface.
-/

namespace LeanFX2.Foundation.PolyCell.FXProfile

open Core

/-- The FX-profile raw-indexed certifier: ONE entry point certifying any
non-`horizontalComposite` raw cell at any dimension, with the certified
result indexed by the EXACT input so erasure back to the input is
definitional.  This is the canonical general ingress for the FX profile.

Wraps `certifyRawCellExact?` with `profile := fxProfile`.  Semantic
equivalence is by definition.

Direct v2 counterpart to v1's `certifyFXCellExact?` (FXProfile/CertifiedViews.lean:1118). -/
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
is read off the result rather than asserted at the call site.

Direct v2 counterpart to v1's `certifyFXCell?` (FXProfile/CertifiedViews.lean:1126). -/
def certifyFXCell? (scope : Nat) (raw : RawCell scope) :
    Except CellCheckRejection
      (CertifiedRawCellResult fxProfile scope) :=
  inferRawCellGeneral? (profile := fxProfile) scope raw

end LeanFX2.Foundation.PolyCell.FXProfile
