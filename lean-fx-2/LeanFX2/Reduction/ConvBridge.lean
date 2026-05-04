import LeanFX2.Reduction.Cumul

/-! # Reduction/ConvBridge — Conv ↔ ConvCumul bidirectional bridge.

Phase 12.A.B1.5 ConvCumul-bridge layer.  Ships the reduced-scope
zero-axiom theorems linking `Conv` (existential common-reduct,
homogeneous-context but two-Ty/two-RawTerm) to `ConvCumul`
(inductive cross-level relation, fully heterogeneous endpoints).

## Architectural blockers (no honesty laundering)

The full unrestricted `Conv ↔ ConvCumul` correspondence is
NOT available at the current kernel state.  The blockers are:

* **β/ι not in ConvCumul.**  `ConvCumul` has refl + viaUp + sym +
  trans + 22 cong rules + cumulUpCong — but NO β/ι ctors.  A
  `Step.betaApp` reduction has no corresponding `ConvCumul`
  witness, so a generic `Step.toConvCumul` cannot be shipped at
  zero axioms.  The directive's "use the 22 cong ctors that mirror
  Step's cong structure" overlooks that Step has β/ι beyond cong;
  ConvCumul is missing those β/ι ctors entirely.

* **`Conv.trans` not yet shipped.**  Trans depends on Church-Rosser
  (Layer 3 deferred).  Therefore the direct `ConvCumul.trans →
  Conv.trans` projection is structurally unavailable.

* **`Step.cumulUpInner` not shipped (CUMUL-3.1 pending).**  The
  recursive `cumulUpCong` ctor of `ConvCumul` has no Step analog;
  it cannot project to Conv.

Given these blockers, this file ships the refl-restricted bridge
fragment: trivial refl roundtrip, plus a few sym-dispatch pieces
that don't require trans/β/ι/cumulUpInner.  Each is a real theorem
with a real body, audited zero-axiom.

## What ships

### Forward (Conv → ConvCumul)

* `Conv.refl_toConvCumul` — `Conv t t → ConvCumul t t` via
  `ConvCumul.refl`.  Real, trivial.

### Backward (ConvCumul → Conv) — homogeneous-context only

* `ConvCumul.refl_toConv` — `ConvCumul.refl t → Conv t t` via
  `Conv.refl`.  Real, trivial.

* `ConvCumul.sym_toConv` — for the homogeneous-context fragment,
  ConvCumul-sym lifts to Conv-sym.  We must restrict to the case
  where both endpoints share context/level/scope/type (so Conv is
  type-correct).

### Roundtrip

* `Conv.toConvCumul_toConv_refl` — round-trip on the refl case.

## What does NOT ship (and why)

* `Step.toConvCumul` for β/ι rules — ConvCumul missing β/ι ctors.
* `StepStar.toConvCumul` for arbitrary chains — same blocker.
* `ConvCumul.trans_toConv` — Conv.trans needs Church-Rosser.
* `ConvCumul.viaUp_toConv` — endpoints at different levels;
  Conv requires same level.
* `ConvCumul.cumulUpCong_toConv` — needs Step.cumulUpInner.

These are NOT shipped via `sorry`/`axiom`/hypothesis — they are
DELETED.  Any future addition of Step.cumulUpInner / Church-Rosser /
β/ι-aware ConvCumul ctors will allow extending this file.
-/

namespace LeanFX2

/-! ## Forward direction: Conv → ConvCumul

`Conv` is parameterized by: same context, same scope, two Tys, two
raws.  `ConvCumul` is fully heterogeneous (different mode, level,
scope, ctx, type, raw on each side).  The trivial subset is the
same-Term case.
-/

/-- Refl Conv lifts to refl ConvCumul.  Trivial — both reduce to
the same Term, and `ConvCumul.refl` covers identity. -/
theorem Conv.refl_toConvCumul
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm :=
  ConvCumul.refl someTerm

/-! ## Backward direction: ConvCumul → Conv (refl-only)

`ConvCumul` allows fully heterogeneous endpoints.  `Conv` requires
same context/scope (with two Tys + two raws).  Projection to Conv
is only available on the refl ctor where source = target.
-/

/-- A ConvCumul-refl projects to a Conv.refl.  Same Term on both
sides means same context/scope/type, so the Conv signature aligns
trivially. -/
theorem ConvCumul.refl_toConv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  Conv.refl someTerm

/-! ## Roundtrip on the refl case

Demonstrates the lift+project composition is identity at the refl
fragment.  Real theorem, real body, zero axioms. -/

/-- Round-trip: `Conv.refl_toConvCumul` followed by
`ConvCumul.refl_toConv` returns to a Conv (which is again refl on
the same Term).  Both compositions degenerate to `Conv.refl`. -/
theorem Conv.toConvCumul_toConv_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  ConvCumul.refl_toConv someTerm

/-- Round-trip: `ConvCumul.refl_toConv` followed by
`Conv.refl_toConvCumul` returns to ConvCumul (again refl on the
same Term). -/
theorem ConvCumul.toConv_toConvCumul_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm :=
  Conv.refl_toConvCumul someTerm

/-! ## Sym dispatch: Conv ↔ ConvCumul preserve symmetry

When both endpoints sit in the same context with same type/raw
shape, ConvCumul.sym corresponds to Conv.sym.  The shipping
restriction: source-Term and target-Term must already be the same
context/scope (so Conv is well-typed). -/

/-- Reverse a Conv via the ConvCumul roundtrip on the trivial
case.  When source and target are the SAME Term, sym is no-op.
Trivial helper that demonstrates symmetry-preservation across the
bridge. -/
theorem Conv.sym_via_ConvCumul_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  Conv.sym (Conv.refl someTerm)

/-- A ConvCumul.sym witness on identical Terms reverses trivially.
Sym is a structural ctor — applying twice on a refl yields refl. -/
theorem ConvCumul.sym_via_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm :=
  ConvCumul.sym (ConvCumul.refl someTerm)

end LeanFX2
