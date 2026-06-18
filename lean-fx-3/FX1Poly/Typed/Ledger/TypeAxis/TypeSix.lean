import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableHonesty
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableEquivarianceSubstrate
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableStructuralSR
import FX1Poly.Typed.Engine.Classifier.TypedBySomeEngine
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGradedIntro
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGeneralElim

/-! # type-6 — higher inductive types: the cubical computation rules + HIT canonicity

The HIT rung of the type axis.  A HIT adds PATH (and higher) constructors to an inductive type and computes
them via cubical operations.  FX ships a genuine PARTIAL cubical/HIT core: path β reduces, path types are
genuinely typed (as BRIDGE types, with an AFFINE interval binder), the interval and its endpoints are typed,
and the simplest HIT — n-truncation — has a computing recursor (as does the quotient).  But the cubical Kan
operations (hcomp/transp/coe), the De Morgan interval algebra, the HIT path/point constructors beyond the
truncation/quotient introductions, and HIT canonicity are all reserved-tag-only or absent.  Like
`type-1`..`type-5`, a NON-DUPLICATIVE ledger ABOVE Typed: markers + `_isBacked` referencing named shipped
theorems.

## What this rung backs (each `= true`, conjoined with named shipped theorems)

  * **`fxType_hasPathComputation`** — path β COMPUTES: `pathApp(pathLam(body), arg) ↝ subst0 body arg`
    (`pathBetaIotaRow_interpretsTarget`, `rfl`), and `gen_pathApp` carries a reduction rule
    (`hasReductionRule_pathApp`).  The one genuinely operational cubical reduction.
  * **`fxType_hasCubicalPathTyping`** — the cubical TYPING substrate is genuinely shipped: the interval type
    `gen_intervalCode`, both endpoints `gen_interval0` / `gen_interval1`, and the bridge/path type former
    `gen_bridgeCode` all carry a typing rule (`hasSomeTypingRule_*`), the bridge former's term-indexed row
    outputs a universe code at the carrier's level (`termIndexedFormerDescOf_bridgeCode`); and path
    abstraction has a graded introduction row (`gradedIntroRuleOf_pathLam`) whose interval binder is AFFINE —
    usage `one`, the first non-`omega` introduction (`gradedIntroRuleOf_pathLamUsageIsOne`).  Paths typed as
    bridge types.
  * **`fxType_hasPathElimination`** — path APPLICATION is genuinely typed (the elimination half): the generic
    elimination table has a `gen_pathApp` row (`generalElimRuleOf_pathApp`), a neutral path applied to an
    interval argument types at the carrier (`generalElimEngine_typesPathApp`), and the typed endpoint-ι fires
    — `pathApp(pathLam(body), arg)` steps to `body[arg]`, typed at the carrier
    (`gradedIntroEndpointIotaComputesTyped`).
  * **`fxType_hasTruncationRecursor`** — the simplest HIT (n-truncation) has a COMPUTING recursor:
    `truncRec(f, truncIntro(v)) ↝ app(f, v)` (`truncRecIntroIotaRow_interpretsTarget`, `rfl`), and
    `gen_truncRec` carries a reduction rule (`hasReductionRule_truncRec`).  The HIT computation rule for the
    point introduction.
  * **`fxType_hasHitRowStructuralSafety`** — the HIT/path computation rows are well-behaved rewrite rows:
    scope-uniform / renaming-equivariant (`truncRecIntroIotaRow_isScopeUniform`,
    `pathBetaIotaRow_isScopeUniform`) and sort-preserving (`truncRecIntroIotaRow_hasSortPreservingTarget`),
    and the WHOLE presentation preserves sorts (`iotaRuleTable_hasSortPreservingTargets`) — structural
    subject-reduction across the entire rule table.

## What is deferred (the genuine cubical / HIT frontier)

  * `fxType_hasCubicalKanOperations` — the Kan operations hcomp / transp / coe / fill.  `gen_transp` /
    `gen_hcomp` / `gen_transpFill` / `gen_compCubical` / `gen_transpHigherDim` are reserved tags (no iota /
    redex head / typing); there is no `coe` / `comp` / `fill` / face / cofibration generator, and the De
    Morgan interval algebra `gen_intervalOpp` / `gen_intervalMeet` / `gen_intervalJoin` is reserved.  Path β
    (backed above) is path APPLICATION, not Kan filling; the cubical context model self-marks
    `hasKanFibrancy = false`.  Route: `type-23` (cubical Kan operations).  `= false`.
  * `fxType_hasHitPathConstructors` — the HIT path/point constructors beyond truncation/quotient
    introduction.  `gen_circleBase` / `gen_circleLoop` / `gen_circleRec` (circle), `gen_pushInl` /
    `gen_pushInr` / `gen_pushGlue` / `gen_pushRec` (pushout), `gen_truncCoh` (truncation coherence), and
    `gen_glueIntro` / `gen_glueElim` (Glue) are all reserved tags (no iota / redex head / typing).  Route:
    Phase Z₅ (HIT constructors as orthogonal rows).  `= false`.
  * `fxType_hasHitCanonicity` — HIT canonicity / the eliminator-respects-path-constructors coherence.  The
    canonicity model covers only data / identity types (Bool / Nat / List / Σ / Refl / Interval); there is no
    HIT / truncation / circle / pushout canonicity theorem, and "the HIT eliminator's iota rule respects path
    constructors via cubical Kan" is an explicit roadmap commitment (Phase Z₅).  `= false`.

## Zero-axiom verification

Four `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + named shipped theorems:
`pathBetaIotaRow_interpretsTarget` / `hasReductionRule_pathApp`; the interval/bridge `hasSomeTypingRule_*` +
`gradedIntroRuleOf_pathLam` / `gradedIntroRuleOf_pathLamUsageIsOne`; `truncRecIntroIotaRow_interpretsTarget` /
`hasReductionRule_truncRec`; the scope-uniform / sort-preserving certificates +
`iotaRuleTable_hasSortPreservingTargets`) and three `:= false` deferral markers.  All cited substrate is
`FX1Poly.Core` / `FX1Poly.Typed`, funext-free.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TypeSix.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core
open FX1Poly.Typed
open FX1Poly.Modal

/-! ## Path β computation (the one operational cubical reduction) -/

/-- **Honesty marker** — `type-6` (path computation).  Path β reduces and `gen_pathApp` carries a reduction
rule.  Backed in `fxType_pathComputation_isBacked`.  `= true`. -/
def fxType_hasPathComputation : Bool := true

/-- ★ **Backed flip (path computation).**  The marker is `true` AND (i) `gen_pathApp` carries a reduction
rule (`hasReductionRule_pathApp`); (ii) path β fires: `pathApp(pathLam(body), arg) ↝ subst0 body arg`
(`pathBetaIotaRow_interpretsTarget`). -/
theorem fxType_pathComputation_isBacked :
    fxType_hasPathComputation = true
      ∧ Generator.hasReductionRule .gen_pathApp = true
      ∧ (∀ {scope : Nat} (body : RawTerm (scope + 1)) (arg : RawTerm scope),
          pathBetaIotaRow.interpretTarget? ()
            (.childCons (.mkGen .gen_pathLam () (.childCons body .childNil))
              (.childCons arg .childNil))
            = some (RawTerm.subst0 body arg)) := by
  refine ⟨rfl, hasReductionRule_pathApp, ?_⟩
  intro scope body arg
  exact pathBetaIotaRow_interpretsTarget body arg

/-! ## Cubical path typing (interval + bridge types, the affine binder) -/

/-- **Honesty marker** — `type-6` (cubical path typing).  The interval, its endpoints, and the bridge/path
type former are typed, and path abstraction binds its interval variable affinely.  Backed in
`fxType_cubicalPathTyping_isBacked`.  `= true`. -/
def fxType_hasCubicalPathTyping : Bool := true

/-- ★ **Backed flip (cubical path typing).**  The marker is `true` AND the interval type, both endpoints, and
the bridge/path type former carry typing rules (`hasSomeTypingRule_intervalCode` / `_interval0` / `_interval1`
/ `_bridgeCode`); path abstraction has a graded introduction row (`gradedIntroRuleOf_pathLam`) whose interval
binder is AFFINE — usage `one` (`gradedIntroRuleOf_pathLamUsageIsOne`). -/
theorem fxType_cubicalPathTyping_isBacked :
    fxType_hasCubicalPathTyping = true
      ∧ hasSomeTypingRule .gen_intervalCode = true
      ∧ hasSomeTypingRule .gen_interval0 = true
      ∧ hasSomeTypingRule .gen_interval1 = true
      ∧ hasSomeTypingRule .gen_bridgeCode = true
      ∧ termIndexedFormerDescOf .gen_bridgeCode = some { outputType := termIndexedCarrierOutput }
      ∧ gradedIntroRuleOf .gen_pathLam = some pathLamGradedIntroRule
      ∧ (gradedIntroRuleOf .gen_pathLam).map (·.binderUsage) = some UsageGrade.one :=
  ⟨rfl, hasSomeTypingRule_intervalCode, hasSomeTypingRule_interval0, hasSomeTypingRule_interval1,
    hasSomeTypingRule_bridgeCode, termIndexedFormerDescOf_bridgeCode, gradedIntroRuleOf_pathLam,
    gradedIntroRuleOf_pathLamUsageIsOne⟩

/-! ## The truncation recursor (the simplest HIT computes) -/

/-- **Honesty marker** — `type-6` (truncation recursor).  n-truncation, the simplest HIT, has a computing
recursor on its point introduction.  Backed in `fxType_truncationRecursor_isBacked`.  `= true`. -/
def fxType_hasTruncationRecursor : Bool := true

/-- ★ **Backed flip (truncation recursor).**  The marker is `true` AND (i) `gen_truncRec` carries a reduction
rule (`hasReductionRule_truncRec`); (ii) the truncation recursor fires on the intro:
`truncRec(f, truncIntro(v)) ↝ app(f, v)` (`truncRecIntroIotaRow_interpretsTarget`) — the level payloads are
typing coherence data the reduct ignores. -/
theorem fxType_truncationRecursor_isBacked :
    fxType_hasTruncationRecursor = true
      ∧ Generator.hasReductionRule .gen_truncRec = true
      ∧ (∀ {scope : Nat} (kernelFn value : RawTerm scope) (elimLevel introLevel : Nat),
          truncRecIntroIotaRow.interpretTarget? elimLevel
            (.childCons kernelFn
              (.childCons (.mkGen .gen_truncIntro introLevel (.childCons value .childNil)) .childNil))
            = some (.mkGen .gen_app () (.childCons kernelFn (.childCons value .childNil)))) := by
  refine ⟨rfl, hasReductionRule_truncRec, ?_⟩
  intro scope kernelFn value elimLevel introLevel
  exact truncRecIntroIotaRow_interpretsTarget kernelFn value elimLevel introLevel

/-! ## Structural safety of the HIT/path rows -/

/-- **Honesty marker** — `type-6` (HIT-row structural safety).  The HIT/path computation rows are
scope-uniform and sort-preserving, and the whole presentation preserves sorts.  Backed in
`fxType_hitRowStructuralSafety_isBacked`.  `= true`. -/
def fxType_hasHitRowStructuralSafety : Bool := true

/-- ★ **Backed flip (HIT-row structural safety).**  The marker is `true` AND (i) the truncation and path-β
rows are scope-uniform / renaming-equivariant (`truncRecIntroIotaRow_isScopeUniform`,
`pathBetaIotaRow_isScopeUniform`); (ii) the truncation row is sort-preserving
(`truncRecIntroIotaRow_hasSortPreservingTarget`); (iii) EVERY row of the presentation has a sort-preserving
target (`iotaRuleTable_hasSortPreservingTargets`) — structural subject reduction across the table. -/
theorem fxType_hitRowStructuralSafety_isBacked :
    fxType_hasHitRowStructuralSafety = true
      ∧ truncRecIntroIotaRow.IsScopeUniform
      ∧ pathBetaIotaRow.IsScopeUniform
      ∧ truncRecIntroIotaRow.HasSortPreservingTarget
      ∧ pathBetaIotaRow.HasSortPreservingTarget
      ∧ (∀ rule, rule ∈ iotaRuleTable → rule.HasSortPreservingTarget) :=
  ⟨rfl, truncRecIntroIotaRow_isScopeUniform, pathBetaIotaRow_isScopeUniform,
    truncRecIntroIotaRow_hasSortPreservingTarget, pathBetaIotaRow_hasSortPreservingTarget,
    iotaRuleTable_hasSortPreservingTargets⟩

/-! ## Path elimination typing (the missing half — application of a path) -/

/-- **Honesty marker** — `type-6` (path elimination).  Path APPLICATION is genuinely typed: the generic
elimination engine has a `gen_pathApp` row (eliminated at a bridge type, argument PINNED to the interval,
output the carrier), a neutral path applied to an interval argument is typed at the carrier, and the typed
endpoint-ι fires.  The elimination side of the cubical typing that the intro flip only half-covered.  Backed
in `fxType_pathElimination_isBacked`.  `= true`. -/
def fxType_hasPathElimination : Bool := true

/-- ★ **Backed flip (path elimination).**  The marker is `true` AND (i) the generic elimination table has a
`gen_pathApp` row — eliminated at the bridge type, argument PINNED to the interval, output the carrier
(`generalElimRuleOf_pathApp`); (ii) a Pi-typed (neutral) path applied to an interval-typed argument is typed
at the carrier (`generalElimEngine_typesPathApp`); (iii) the typed endpoint-ι: a `pathLam`-typed abstraction
applied to a typed interval argument forces the classifier to the bridge at the body's endpoint
substitutions, the endpoint-β step FIRES, and the reduct `body[arg]` is typed at the extracted carrier
(`gradedIntroEndpointIotaComputesTyped`). -/
theorem fxType_pathElimination_isBacked :
    fxType_hasPathElimination = true
      ∧ generalElimRuleOf .gen_pathApp = some pathAppGeneralElimRule
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          {path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope},
          HasTypeDescPi profile context path
            (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) →
          HasTypeDescPi profile context argument intervalTypeCell →
          HasTypeDescGeneralElim profile context (pathAppCell path argument) carrierCode)
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          {body : RawTerm (scope + 1)} {classifier argument : RawTerm scope},
          HasTypeDescGradedIntro profile context (pathLamCell body) classifier →
          HasTypeDescPi profile context argument intervalTypeCell →
          ∃ carrierCode : RawTerm scope,
            classifier = bridgeTypeCell carrierCode
              (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
            StepTable (pathAppCell (pathLamCell body) argument) (RawTerm.subst0 body argument) ∧
            HasTypeDescPi profile context (RawTerm.subst0 body argument) carrierCode) := by
  refine ⟨rfl, generalElimRuleOf_pathApp, ?_, ?_⟩
  · intro profile scope context path argument carrierCode leftEndpoint rightEndpoint
      pathTyped argumentTyped
    exact generalElimEngine_typesPathApp pathTyped argumentTyped
  · intro profile scope context body classifier argument pathTyped argumentTyped
    exact gradedIntroEndpointIotaComputesTyped pathTyped argumentTyped

/-! ## Honesty markers (the deferred cubical / HIT frontier) -/

/-- **Honesty marker.**  The cubical KAN operations hcomp / transp / coe / fill — `gen_transp` / `gen_hcomp`
/ `gen_transpFill` / `gen_compCubical` / `gen_transpHigherDim` are reserved tags (no iota / redex head /
typing); there is no `coe` / `comp` / `fill` / face / cofibration generator, and the De Morgan interval
algebra `gen_intervalOpp` / `gen_intervalMeet` / `gen_intervalJoin` is reserved (path β is path application,
NOT Kan filling; the cubical model self-marks `hasKanFibrancy = false`).  Route: `type-23`.  Deferred.
`= false`. -/
def fxType_hasCubicalKanOperations : Bool := false

/-- **Honesty marker.**  The HIT path/point constructors beyond truncation/quotient introduction —
`gen_circleBase` / `gen_circleLoop` / `gen_circleRec`, `gen_pushInl` / `gen_pushInr` / `gen_pushGlue` /
`gen_pushRec`, `gen_truncCoh`, `gen_glueIntro` / `gen_glueElim` are all reserved tags (no iota / redex head /
typing).  Route: Phase Z₅ (HIT constructors as orthogonal rows).  Deferred.  `= false`. -/
def fxType_hasHitPathConstructors : Bool := false

/-- **Honesty marker.**  HIT canonicity / the eliminator-respects-path-constructors coherence — the
canonicity model covers only data / identity types (Bool / Nat / List / Σ / Refl / Interval); there is no
HIT / truncation / circle / pushout canonicity theorem, and "the HIT eliminator's iota rule respects path
constructors via cubical Kan" is a roadmap commitment (Phase Z₅).  Deferred.  `= false`. -/
def fxType_hasHitCanonicity : Bool := false

end FX1Poly.Tier0
