import FX1Poly.Typed.KernelParamSubstrateSurvey
import FX1Poly.Core.Step
import FX1Poly.Core.StepOverTable

/-! # FX1Poly/Typed/KernelParamInternalVerdict — the OP1-INT verdict module (closes #1231)

The INTERNAL graded parametricity crux, decided on the `gen_param` substrate
(`KernelParamSubstrateSurvey`).  The PARAM-GEN survey pinned ONE open gap — the endpoint-ι
computation lived only in the table-driven `StepTable` relation, with the promotion into core
`Step` deferred.  TABLE-CANON-1 rebased `Step` onto the canonical 21-row `iotaRuleTable`, of
which `pathBetaIotaRow` is a row, so that gap is now closed: the endpoint-β fires as a genuine
`Step.tableRedex`.

  * `paramSubstrate_endpointBetaIsCoreStep` — the operational fact: `pathApp (pathLam body) arg
    ↝ body[arg]` is a core `Step` (the analogue of `Step.beta` for `betaIotaRow`).
  * `paramSubstrate_op1IntVerdictGo` — ★ the verdict: every `ParamSubstrateLedger` field is now
    satisfied, so internal graded parametricity ADMITS on the substrate.  GO, no refutation.

## Why GO, not a refutation

The historical no-go for internal parametricity (inconsistency with classical axioms) is
irrelevant here — the kernel is axiom-free.  The genuine concern was the BCM bridge dimension's
AFFINITY (a dimension variable used at most once), inexpressible in the structural
`TypingContext`.  FX carries it in the GRADED substrate: the dimension binder is an affine
usage-graded row (the Wood/Atkey-corrected `HasGradeOver` engine).  The static rows pass the
ONORM-M2 per-generator sconing-coverage gate (`paramSubstrate_rowsLive` + the liveSignature
40 → 46 flip), and the operational endpoint-β is a real reduction.  Nothing remains on the
OP1-INT landing list.

Zero-axiom; gated in `FX1PolyAudit/AuditKernelParamInternalVerdict.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- ★ **The endpoint-β IS a core `Step`** — the operational fact behind the ledger flip.
`pathApp (pathLam body) arg ↝ body[arg]` fires as `Step.tableRedex` on the `pathBetaIotaRow`
row of the canonical `iotaRuleTable`, exactly as `Step.beta` fires `betaIotaRow`.  This is the
"core-Step promotion" PARAM-GEN deferred and TABLE-CANON-1 landed. -/
theorem paramSubstrate_endpointBetaIsCoreStep {scope : Nat}
    {body : RawTerm (scope + 1)} {arg : RawTerm scope} :
    Step
      (.mkGen .gen_pathApp ()
        (.childCons (.mkGen .gen_pathLam () (.childCons body .childNil))
          (.childCons arg .childNil)))
      (RawTerm.subst0 body arg) :=
  .tableRedex pathBetaIotaRow_memTable () rfl

/-- ★ **The OP1-INT verdict: GO, no refutation.**  Every `ParamSubstrateLedger` field holds —
dimension binder pair, interval endpoints, interval type code, bridge former, the GRADED typing
rows (carrying the affine dimension usage), the endpoint-ι computation (now a core `Step`,
`paramSubstrate_endpointBetaIsCoreStep`), and the affinity discipline (the usage semiring).
Internal graded parametricity ADMITS on the `gen_param` substrate. -/
theorem paramSubstrate_op1IntVerdictGo :
    paramSubstrateLedger.hasDimensionBinderPair = true ∧
    paramSubstrateLedger.hasIntervalEndpoints = true ∧
    paramSubstrateLedger.hasIntervalTypeCode = true ∧
    paramSubstrateLedger.hasBridgeFormer = true ∧
    paramSubstrateLedger.hasDimensionTypingRows = true ∧
    paramSubstrateLedger.hasEndpointComputation = true ∧
    paramSubstrateLedger.hasAffinityDiscipline = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Typed
