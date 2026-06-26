import FX1Poly.Tier0.Context.StandaloneModalRMC
import FX1Poly.Tier0.Mode.ModeOmega
import FX1Poly.Tier0.Type.TypeAxis
import FX1Poly.Tier0.Term.TermAxis
import FX1Poly.Tier0.Term.Generator.GeneratorSignatureValue
import FX1Poly.Core.CellRuleFibration

/-! # FX1Poly/Core/Fib/FibrationArchitecture — fib-0 design-lock: the four ω-categories meet at Core/

The FX kernel is built as FOUR standalone ω-category axes, each its own `Tier0/` tower with a capstone:

  * **term**    — `RawTerm` as a SOAS INITIAL ALGEBRA (`Tier0/Term`, `fxTerm_hasInitialAlgebraUniqueness`);
  * **type**    — a standalone Tarski universe + level normalizer (`Tier0/Type`, `TypeAxis` / `fxTypeAxis`);
  * **context** — a modal Representable Map Category / Uemura CwR (`Tier0/Context`, `StandaloneModalRMC` /
    `fxStandaloneModalRMC`), whose `comprehension` field is the display fibration with the representability
    bijection `Sub(Delta, Gamma.A) ~= Sub(Delta, Gamma) x Tm(Delta, A)`;
  * **mode**    — a (weak) higher polygraph carried as data (`Tier0/Mode`, `ModeOmega` / `fxModeOmega`).

Until now those four towers were GLUED NOWHERE: the running judgment `HasTypeUnion`/`TypingContext`
(`Typed/Engine`) imports ONLY the term axis (and the `LevelExpr`/`UniverseFlag` floor of the type axis);
the context and mode towers reach the engine with EXACTLY ZERO imports.  This file is the `Core/fib` home
that `StandaloneModalRMC` already names (`standaloneModalRMC_hasCrossAxisModelAssembly := false`,
"deferred to Core/fib") — the first place all four axes meet.

## The glue object (the design decision)

The fibred kernel is a FIBRATION over a `(mode x context)` BASE with type and term FIBRED:

  * the **base** is the context axis's `StandaloneModalRMC` — already a Uemura CwR whose comprehension
    cleavage IS "types-over-contexts", so type-over-context is the SHIPPED display map, not built fresh;
  * that base is INDEXED by the mode axis's `ModeOmega` — mode is the OUTER index (not a fifth fibre);
    threading the lock `◐_μ ⊣ ⟨μ|−⟩` into the doctrine is exactly what flips
    `fxMode_hasModeOmegaKernelFibration` and `standaloneModalRMC_hasModalLockThreadedNbe`;
  * the **type axis** `TypeAxis` supplies the `Tm ↠ Ty` universe classifier;
  * **term is the fibred syntax itself** — `RawTerm` is the INITIAL ALGEBRA over the presentation, not a
    peer record, so the four-axis glue carries the presentation `presentation : List GeneratorDescriptor`
    (`fxSignature`, the kernel-as-one-value) and reads term off it.

The four axes literally sit at FOUR of the seven `CellSort` strata (`term`/`type`/`context`/`mode`, with
`effect`/`grade`/`protocol` as the spare sorts for later extension) — `FibAxis.cellSort` makes "the four
axes meet at Core" definitional, and the existing rule fibration `CellRuleBundle = RuleFibration CellSort
Generator payload` (`Core/CellRuleFibration`) is the data-table spine whose `term`/`context`/`mode` sorts
(currently `PEmpty`/`[]`, only `type` wired to `typingRowsOf fxTypingBundle`) the gluings populate.  This is
the "fill the empty sorts" reuse mandate: NO parallel structure, NO superseded remnant.

## The three connection points (the fib-1/2/3 gluings, deferred from this design-lock)

  * **fib-1 [type ↠ context]** — lift the shipped display-map prototype `DisplayMapDecidableFibration`
    (currently over the formation engine `HasTypeDesc`) up to `HasTypeUnion`, identify `TypingContext.cons
    context A` with the categorical extension `Gamma.A`, and supply the deferred fibred-Pi right adjoint.
  * **fib-2 [type ↔ term / El]** — SMALLEST gap: term IS type already (one `RawTerm`, `CellSort` tags only),
    the El roundtrip already ships (`tarskiDecode`/`universeMembership_iff`), and the type axis's abstract
    `UniverseCode = LevelExpr x UniverseFlag` is EXACTLY the `gen_universeCode` payload — so fib-2 ~= identify
    the axis code with `universeCodeCell`, tie `successor` to `Type@L : Type@(L+1)`, install the decode field.
  * **fib-3 ★ [everything ⊣ mode]** — the hard keystone: index the judgment by a `ModalityPath`, retire the
    bespoke `ObligationModality` onto a real mode-12 UNPOINTABLE affine multiplier (NOT the mode-2 structure
    class, which is marked `pointed`), DERIVE the lock's fibrant-inaccessibility from unpointedness, and
    consume the accessibility conjunct in the premise relation.  Gated on `fxMode_hasDecidableTwoCellEquality`
    + `fxMode_hasModeRelativeConvDecision` (the "Conv-dec = mode-dec" leg).

Execution staircase by difficulty: **fib-2 < fib-1 < fib-3** (then fib-4 cross-axis right adjoint, fib-5
bi-initiality).

## Bi-initiality (fib-5) — the zero-axiom constraint on the shape

The universal property fib-5 needs is initiality in the `RepresentableMapCategory` + `CwRMorphism`
2-category, with the representable class taken as the DISPLAY maps `Tm ↠ Ty` (not the trivial iso class the
standalone witnesses currently use).  But ON-THE-NOSE CwF/QIIT initiality needs `Quot.sound`/`funext`
(off-limits zero-axiom — `Context/Initiality` and `TwoMonadDoctrine`'s `fxMode_hasStrictBiInitialUniqueness
:= false` both record this).  So the glue exposes bi-initiality as the WEAK, up-to-iso 2-categorical property:
ship the data + EXISTENCE of the interpreting `CwRMorphism`, and leave strict uniqueness to an honest fib-5
marker rather than baking a quotient carrier in.

## Honest scope of fib-0

This design-lock fixes the SHAPE (`FibredKernel` + `fxFibredKernel`) and the connection-point ledger; it does
NOT prove any gluing — those are fib-1..fib-5, tracked by the `fxFib_has*` markers (all `false` here), exactly
as `term-0`/`mode-0` are marker-ledger design-locks for their towers.

## Zero-axiom

A record bundling four already-shipped axis witnesses + a presentation list, a finite-enum `CellSort` map, and
`rfl` sanity facts.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Tier0

/-- The four glue axes — the four of the seven `CellSort` strata the fibred kernel assembles. -/
inductive FibAxis where
  /-- The term axis: `RawTerm` as the SOAS initial algebra. -/
  | term
  /-- The type axis: the standalone Tarski universe. -/
  | type
  /-- The context axis: the modal Uemura CwR base. -/
  | context
  /-- The mode axis: the higher-polygraph outer index. -/
  | mode

/-- Each glue axis sits at its own `CellSort`, making "the four axes meet at Core" definitional over the
existing seven-sort rule-fibration spine. -/
def FibAxis.cellSort : FibAxis → CellSort
  | .term => .term
  | .type => .type
  | .context => .context
  | .mode => .mode

/-- **★ The four-axis fibred kernel (the fib-0 design-lock SHAPE).**  A fibration over a `(mode x context)`
base with the type universe classifying and the term syntax fibred: the context axis's Uemura CwR `base`, the
mode axis's higher-polygraph `modeIndex`, the type axis's Tarski `typeClassifier`, and the `presentation` (the
signature as data, over which `RawTerm` is the initial algebra — the term leg).  This is the carrier the
fib-1/2/3 gluings populate; it bundles the four standalone capstones with NO new parallel structure. -/
structure FibredKernel where
  /-- The context axis: the modal Representable Map Category (the CwR base of the fibration). -/
  base : StandaloneModalRMC
  /-- The mode axis: the higher polygraph indexing the base (the outer modal index). -/
  modeIndex : ModeOmega
  /-- The type axis: the Tarski universe supplying the `Tm ↠ Ty` classifier. -/
  typeClassifier : TypeAxis
  /-- The term axis: the signature as data; `RawTerm` is the initial algebra over it. -/
  presentation : List GeneratorDescriptor

/-- **★ The FX fibred kernel** — the four shipped capstone witnesses assembled at Core for the first time.
The four `Tier0` towers (`fxStandaloneModalRMC` / `fxModeOmega` / `fxTypeAxis` / `fxSignature`) glued into one
value; the gluing PROOFS are fib-1..5 (the `fxFib_has*` ledger below). -/
def fxFibredKernel : FibredKernel where
  base := fxStandaloneModalRMC
  modeIndex := fxModeOmega
  typeClassifier := fxTypeAxis
  presentation := fxSignature

/-! ## The connection-point ledger — the gluings fib-0 fixes the shape for but defers to fib-1..5 -/

/-- **Honesty marker (fib-1).**  The display fibration `type ↠ context` lifted from the formation engine to
`HasTypeUnion` + the fibred-Pi right adjoint.  Deferred.  `= false`. -/
def fxFib_hasTypeContextDisplay : Bool := false

/-- **Honesty marker (fib-2).**  The universe reflection `type ↔ term` — the axis `UniverseCode` identified
with `universeCodeCell` + the El decode installed.  Deferred (smallest gap).  `= false`. -/
def fxFib_hasTypeTermUniverseReflection : Bool := false

/-- **Honesty marker (fib-3 ★).**  The MTT fibration `everything ⊣ mode` — the judgment indexed by
`ModalityPath`, the bespoke `ObligationModality` retired onto a real unpointable affine multiplier.
Deferred (the keystone).  `= false`. -/
def fxFib_hasModeFibration : Bool := false

/-- **Honesty marker (fib-4 ★).**  Cross-axis right-adjoint coherence — transpension recovers the zoo across
all four axes.  Deferred.  `= false`. -/
def fxFib_hasCrossAxisRightAdjointCoherence : Bool := false

/-- **Honesty marker (fib-5 ★).**  Weak (up-to-iso) bi-initiality of the fibred kernel in the
`RepresentableMapCategory` + `CwRMorphism` 2-category, with the display maps `Tm ↠ Ty` as the representable
class.  Deferred (strict uniqueness needs `Quot.sound`/`funext`, off-limits).  `= false`. -/
def fxFib_hasWeakBiInitiality : Bool := false

/-! ## Sanity facts -/

/-- The FX fibred kernel's term leg is exactly the kernel signature value. -/
theorem fxFibredKernel_presentation_eq : fxFibredKernel.presentation = fxSignature := rfl

/-- The mode glue axis sits at the `mode` `CellSort` — the design-lock's structural anchor for the (currently
`PEmpty`) `mode` sort of `fxCellRules` that fib-3 populates. -/
theorem modeAxis_cellSort : FibAxis.mode.cellSort = CellSort.mode := rfl

/-- The term glue axis sits at the `term` `CellSort`. -/
theorem termAxis_cellSort : FibAxis.term.cellSort = CellSort.term := rfl

end FX1Poly.Core.Fib
