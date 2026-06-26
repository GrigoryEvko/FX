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
NOT prove the gluings here — those are fib-1..fib-5, tracked by the `fxFib_has*` markers, exactly as
`term-0`/`mode-0` are marker-ledger design-locks for their towers.  As each gluing lands its marker flips to
`true`: `fxFib_hasTypeTermUniverseReflection` is now `true` (fib-2 shipped, `Core/Fib/UniverseCodeBridge`
+ `UniverseElDecode`); the remaining four (`fib-1`/`fib-3`/`fib-4`/`fib-5`) stay `false`.

## ★ The verified execution map (file:line anchors) — the fib-1/2/3/5 playbook

These anchors are the durable distillate of the fib-0 reconnaissance (a 5-agent fan-out, 2026-06-26); they let a
future agent EXECUTE the gluings without re-exploring.

### The disconnect, by the numbers (imports into `Typed/Engine/`)
  * **term** 24 import-lines / 17 files — LOAD-BEARING (`RawTerm`/`StepOver`/`Generator`/rename-subst). The point
    all others glue TO; needs no new connection.
  * **type** 3 / 2 — THIN (only `LevelExpr`/`UniverseFlag` reach the engine, via `RuleTables/CellTemplate.lean` +
    `Formation/FormerOutputLevelBounds.lean`); the Tarski universe itself is unconsumed.
  * **context** 0 / 0 — ORPHANED from the engine (grazes only `Typed/Dimensions/AxisObligation/*` +
    `Typed/Metatheory/Sconing/*`).
  * **mode** 0 / 0 — ORPHANED (one peripheral importer, `Typed/Dimensions/Parametricity/GelIsTranspensionAtAffine`).
    Headline flag `fxMode_hasModeFibration := false` (`Tier0/Mode/Mode.lean:261`); 16 sibling
    `fxMode_hasKernel*Connection := false` flags are the literal honesty ledger of the gap.

### The reuse skeleton (fill it; do NOT fork — "no remnants")
  * `Tier0/RuleFibration.lean:24-67` — the index-abstract `RuleFibration (Axis)(Head)(payload)` engine.
  * `Core/CellRuleFibration.lean:28` — `CellRuleBundle payload := RuleFibration CellSort Generator payload` over
    the 7 sorts `context·type·term·mode·effect·grade·protocol` (`Tier0/Term/Cell/CellSort.lean:16`).
  * `Typed/CellRuleFibration.lean:60` — `fxCellRules`: ONLY `.type` is wired (↦ `typingRowsOf fxTypingBundle`,
    `:63`); `context`/`term`/`mode` are `PEmpty`/`[]`. **fib-1/2/3 = populate those three empty sorts.**
  * Everything else "glue"-named is NOT four-axis glue: `GluedModel*`/`SconingWitness`/`BksMetatheoryPackage`
    are Artin/reducibility sconing; `Tier0/Context/FibrationCategory.lean` is context-only Brown model structure;
    `ProfileFibration/ProfileMorphism.lean` is a dead axis-8 ledger.

### fib-2 [type ↔ term / El] — SMALLEST gap, do FIRST
  * Term IS type already: ONE `RawTerm` (`Tier0/Term/Core/RawTerm.lean:13`), `.type`/`.term` is only a `CellSort`
    tag — so "a term can be a type code" holds structurally.
  * El already ships as the Tarski roundtrip: `IsReducibleMemberAt.tarskiDecode` / `tarskiEncode` /
    `universeMembership_iff` (`Core/Metatheory/Reducibility/Stratified/StratifiedReducibleUniverseDecode.lean:64-110`).
  * The axis code = the kernel payload, ON THE NOSE: `StandaloneTarskiUniverse.Code = UniverseCode =
    LevelExpr × UniverseFlag` (`Tier0/Type/TypeAxis.lean:74-98`) is EXACTLY `gen_universeCode`'s payload
    (`Tier0/Term/Generator/GeneratorCore.lean:952`); kernel term is `universeCodeCell`
    (`Typed/Cell/CellConstructors.lean:38-40`).
  * Predicativity (Tarski not Russell) proven: `grownUniverseCode_notTypedAtSelf`
    (`Typed/Metatheory/Canonicity/Consistency/GrownUniverseConsistency.lean:58-67`), no-top
    (`Typed/Metatheory/Universe/TypedUniverseNoTop.lean`).
  * DO: identify the axis `Code` with `universeCodeCell`'s payload; tie axis `successor` to
    `HasTypeUnion.universeFormation` (`Type@L : Type@(L+1)`); install the decode/El field the axis omits
    (`StandaloneTarskiUniverse` has `successor`/`predicative` but NO decode); flip
    `fxFib_hasTypeTermUniverseReflection`; close the type-20 Tarski↔Russell coherence.

### fib-1 [type ↠ context] — has a LIVE prototype to lift
  * Kernel side: `TypingContext` telescope (`Typed/Engine/Classifier/TypingContext.lean:74-143`, `empty`/`cons`/
    `lockCons`/`lookup`); the "Γ ⊢ A type" predicate `IsTypeDesc` (`Typed/Engine/IsTypeDesc/IsTypeDesc.lean:32-36`,
    over the FORMATION engine `HasTypeDesc`, NOT `HasTypeUnion`); `WfContextDesc`
    (`Typed/Engine/WfContext/WfContextDesc.lean:33-39`).  Substitution on classifiers: `RawTerm.subst`/`subst0`/
    `rename` (eliminator outputs are literally `subst0`-driven).
  * Context side: `FxComprehensionCategory`/`fxComprehensionCategory`
    (`Tier0/Context/ComprehensionCategory.lean:87-192`, cleavage = de Bruijn lift, Beck-Chevalley,
    `comprehensionIso : Sub(Δ,Γ.A) ≅ Sub(Δ,Γ)×Tm(Δ,A)`); the cellular `Tm↠Ty` `displayClassifier`
    (`Tier0/Context/Instances/Subst/FxBaseSubstDisplayMap.lean:99-213`).
  * The shipped PROTOTYPE: `Typed/Dimensions/AxisObligation/DisplayMapDecidableFibration.lean:54-101`
    (`ClassifiedCell.IsAdmittedByFormation := HasTypeDesc …`, `decideAdmittedByFormation`,
    `genericClassifiedCell_admittedByFormation`).
  * DO: define a union-level "Γ ⊢ A type" predicate (there is NO `IsTypeUnion` yet — only `IsTypeDesc`/
    `IsTypeDescPi`); lift the prototype from `HasTypeDesc` to `HasTypeUnion`; identify
    `TypingContext.cons context A` with the categorical `Γ.A`; supply the deferred fibred-Π right adjoint
    (`fxComprehensionCategory_hasFibredPiRightAdjoint := false`, `:197`); flip `fxFib_hasTypeContextDisplay`.

### fib-3 ★ [everything ⊣ mode] — the HARD keystone, gated
  * Index by `ModalityPath` (`Tier0/Mode/Mode.lean:91-98`: `nil`=identity, `cons`=prepend).
  * **★★ THE WRINKLE (do NOT conflate two distinct facts):** affineness (mode-2
    `MultiplierStructureClass.affine` = NO diagonal, `MultiplierStructureClass.lean:57-58,198`) ≠ unpointedness
    (mode-12 `Multiplier.IsUnpointable := multiplier.dimension → False`, `MultiplierEndofunctor.lean:67-68`,
    witness `voidMultiplier_isUnpointable:127`).  And mode-2's table marks the affine class
    `affine_pointed := … = true` (`MultiplierStructureClass.lean:328`).  So the lock's "no 2-cell μ⇒1" must pin
    to a mode-12 UNPOINTABLE multiplier + the genuine ABSENCE of a `twoCell μ⇒identity` generator
    (`ModeSignature.twoCell`, `Mode.lean:131-136`) — it is NOT readable off the affine structure class.
  * The bespoke mirror to RETIRE: `ObligationModality {fibrant,dimensional}`
    (`Typed/Engine/Classifier/DimensionLockAccessibility.lean:216-220`, NO `Tier0.Mode` import);
    `dimensionIsNotAccessibleFibrantly` (`:257-261`) ASSERTED by a `rfl`-level `false` match arm (`:70`), NOT
    derived; `isSubjectUsableAtModality` called in NO file but its own; the `ElimObligation.modality` field
    (`ElimRuleTable.lean:72`, pathApp arg `.dimensional`) is threaded but the conjunct is unconsumed.
  * GATED on two deferred mode-side flags: `fxMode_hasDecidableTwoCellEquality` (`Mode.lean:253`) +
    `fxMode_hasModeRelativeConvDecision` (`ModeRelativeMetatheory.lean:234`) — the "Conv-dec = mode-dec" leg.
  * DO: pin `lockCons`'s `μ_affine` to a real mode-12 unpointable `Modality`; map `ObligationModality` →
    `ModalityPath` (fibrant↦`identityPath`, dimensional↦the affine generator path); DERIVE the fibrant-
    inaccessibility from unpointedness; index the judgment by `ModalityPath` (or consume the conjunct in the
    premise relation); flip `fxMode_hasModeFibration` + `fxFib_hasModeFibration`.  Realizes A1-FIB3-SEED /
    A1-MODE-AFFINE and retires the bespoke enum (A1-RETIRE).

### fib-5 ★ [weak bi-initiality] — the constraint on the whole shape
  * 2-category: `RepresentableMapCategory` + `CwRMorphism` (`Tier0/Context/RepresentableMapCategory.lean:288,327`);
    representable class = the DISPLAY maps `Tm↠Ty` (NOT the trivial iso class the standalone witnesses use,
    `StandaloneModalRMC.lean:153-159`).
  * ZERO-AXIOM CEILING: on-the-nose CwF/QIIT initiality needs `Quot.sound`/`funext` (off-limits —
    `Tier0/Context/Initiality.lean:7-10`; toy `fxMode_hasStrictBiInitialUniqueness := false`,
    `Tier0/Mode/TwoMonadDoctrine.lean:271-275`).  ⟹ ship bi-initiality WEAK (up-to-iso 2-categorical: data +
    EXISTENCE of the interpreting `CwRMorphism`), leave strict uniqueness to an honest fib-5 marker.
  * Presentation-as-data already exists: `fxSignature` (`Tier0/Term/Generator/GeneratorSignatureValue.lean:107`),
    `fxTypingBundle` (`Typed/Engine/RuleTables/TypingTableBundle.lean:105`), `Conv`; the premises-as-data
    design-lock is `Typed/Engine/RuleTables/UnifiedRuleSignature.lean:17`.  polycell.md:10407 = "kernel presented
    as a bi-initial model over (signature, rule-tables, Conv)" = SIG-3/SIG-5.

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

/-- **ESTABLISHED (fib-1).**  The display fibration `type ↠ context` lifted to `HasTypeUnion` (fib-1b,
`ClassifiedCell.IsAdmittedByUnion` / `genericClassifiedCell_admittedByUnion`), `TypingContext.cons` identified
with the categorical comprehension `Γ.A` (fib-1c, `Core/Fib/ContextComprehension`), and the fibred-Π RIGHT
ADJOINT to comprehension reindexing realized over the SHIPPED kernel (fib-1d, `Core/Fib/ContextDisplayPi`): the
kernel's Π former with `lam` / `app` as the currying transpose pair (`lamRealizesFibredPiTranspose` forward,
`appRealizesFibredPiCotranspose` backward) and the β / η triangle identities as shipped reductions
(`fibredPiBetaTriangle` as raw `Conv`, `fibredPiEtaTriangle` as the unified-relation function-η).  This realizes
the local-exponential core that `context-16` deferred (`×type → fib-1`,
`democracyLCC_hasLocalExponentials = false`).  `= true`.  The adjunction is WEAK (up-to-`Conv`): on-the-nose
strictness of the currying bijection needs `funext`, the fib-5 ceiling. -/
def fxFib_hasTypeContextDisplay : Bool := true

/-- **ESTABLISHED (fib-2).**  The universe reflection `type ↔ term`: the axis `UniverseCode` is identified with
`universeCodeCell` ON THE NOSE (`axisCodeToCell`, `Core/Fib/UniverseCodeBridge`), the axis `successor` is the
kernel's `universeFormation` classifier at the typing level, and the Tarski El decode is installed at the bridge
(`typeTermUniverseReflection`, `Core/Fib/UniverseElDecode`).  `= true`.  (The remaining type-20 strengthening —
decode injectivity + η for El over the whole type system — stays #1532.) -/
def fxFib_hasTypeTermUniverseReflection : Bool := true

/-- **ESTABLISHED (fib-3 ★, the keystone).**  The MTT fibration `everything ⊣ mode`, realized over the
kernel's AFFINE mode theory (`affineDimensionModeGraph`: one mode, one generator, no 2-cell relations — the
mode the kernel's dimension lock is fibred over), assembled in `Core/Fib/ModeFibration`
(`affineModeFibrationRealized`):
  * the lock `lockCons` is pinned to the mode-12 UNPOINTABLE `voidMultiplier` (fib-3a, `Core/Fib/ModeLockMultiplier`);
  * the bespoke `ObligationModality` embeds FAITHFULLY (injectively) into the mode-axis `ModalityPath` (fib-3b,
    `Core/Fib/ModeLockPath`);
  * the lock's fibrant-inaccessibility is DERIVED from (computed as) the multiplier's non-pointedness (fib-3c);
  * the mode 1-cell (modality) equality is DECIDABLE (fib-3d, `affineModalityPathDecidableEq`) — the "mode-dec"
    side of Gratzer's "Conv-dec = mode-dec", specialized to the kernel's mode.
`= true`.  The GENERAL multi-mode `fxMode_hasDecidableTwoCellEquality` (arbitrary theories via a convergent
3-polygraph) stays `false`; the PHYSICAL retirement of the `ObligationModality` enum onto `ModalityPath` is
`A1-RETIRE` (the faithful embedding here makes that a no-op refactor, not a soundness step). -/
def fxFib_hasModeFibration : Bool := true

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
