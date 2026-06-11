import FX1Poly.Typed.GeneratorSemanticTier

/-! # FX1Poly/Typed/KernelParamSubstrateSurvey
    — the `gen_param` internal-parametricity substrate SURVEY + typing-row design (PARAM-GEN)

The machine-checked census of what the 203-generator table already provides for INTERNAL
parametricity (Bernardy–Coquand–Moulin presheaf parametricity / Cavallo–Harper cubical
internal parametricity / Narya-style bridge types), what is MISSING, and the typing-row
design the OP1-INT verdict task will land or refute.

## What EXISTS (pinned below)

  * **The dimension-binder pair**: `gen_pathLam` (body under ONE fresh binder — the dimension
    binder, `binderShifts = [1]`) and `gen_pathApp` (`[0, 0]`).  A bridge/param abstraction is
    STRUCTURALLY a path abstraction — the BCM bridge interval is a second interval without
    Kan operations, so the binder pair is reusable as-is.
  * **The interval element algebra**: `gen_interval0` / `gen_interval1` (the endpoints,
    nullary) + `gen_intervalOpp` / `gen_intervalMeet` / `gen_intervalJoin` (the de Morgan
    structure — parametricity needs only the endpoints; the connections are Kan-cubical
    surplus).
  * **The observational-equality family** (`gen_oeqRefl` / `gen_oeqJ` / `gen_oeqFunext`) —
    HOTT-adjacent, NOT consumed by the param substrate but sharing the endpoint-computation
    rule shape.
  * ALL of the above are `semanticTier = reserved` — no typing rules in any engine, no β/ι
    redex head (the η-step `Step.eta.etaPathLam` exists at the RAW layer but is excluded from
    the `hasRedexHead` operational classifier, which is β/ι-rooted).

## What is MISSING (the gap statement, pinned as the ledger)

  1. **No interval TYPE code**: `gen_interval0/1` are TERMS with no classifying code, so a
     dimension binder cannot be context-bound through the standard rules — `TypingContext`
     binds `RawTerm` types only.  Internal-parametricity rows need either an interval
     pseudo-code (a nullary code on the `gen_unitCode` template, with the caveat below) or
     Narya-style judgment-level dimension contexts.
  2. **No bridge FORMER**: the bridge type `Bridge A a b` is a ternary former on the
     `gen_idCode` template (`binderShifts = [0, 0, 0]`, flat) — one new generator at
     CON-A1 cost (table constructor + tag + serializer + count pin 203 → 204).
  3. **The affinity discipline**: the genuine semantic obstruction.  The BCM bridge dimension
     is AFFINE (each dimension variable used at most once — duplication makes internal
     parametricity collapse).  `TypingContext` is structural; the kernel CANNOT express
     affinity natively in the type layer.  BUT the kernel's GRADED substrate already has
     exactly this discipline: the usage semiring's affine grade (`HasGradeOver` with usage
     `≤ 1`, the Wood/Atkey-corrected engine).  The design decision recorded here: the param
     rows are GRADED rows — the dimension binder carries the affine usage grade, making
     OP1-INT the first task where two FX dimensions (type × usage) are LOAD-BEARING for one
     feature's soundness rather than merely composed.

## The typing-row DESIGN (the OP1-INT landing targets, recorded as rule schemas)

      formation   Γ ⊢ A : Type@e   Γ ⊢ a : A   Γ ⊢ b : A
                  ─────────────────────────────────────────   (gen_bridgeCode, flat ternary)
                  Γ ⊢ Bridge A a b : Type@e

      intro       Γ, i :⟨affine⟩ dim ⊢ body : A
                  ─────────────────────────────────────────   (gen_pathLam, graded binder)
                  Γ ⊢ pathLam body : Bridge A body[i:=0] body[i:=1]

      elim        Γ ⊢ p : Bridge A a b   Γ ⊢ ε : dim
                  ─────────────────────────────────────────   (gen_pathApp)
                  Γ ⊢ pathApp p ε : A

      computation pathApp (pathLam body) ε ↝ body[i:=ε]       (the endpoint ι — NEW Step arm)
                  pathApp p 0 ≡ a,  pathApp p 1 ≡ b           (endpoint boundary — definitional)

The OP1-INT verdict question: do these rows pass the sconing admission gate (the ONORM-M2
per-generator coverage discipline) — i.e. does the glued model extend over the bridge former
with the affine dimension, or is there an FX-specific refutation (the known no-go territory:
internal parametricity is inconsistent with classical axioms, irrelevant here — the kernel is
axiom-free — but the AFFINITY soundness interacts with the structural context)?

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## The substrate pins (machine-checked census) -/

/-- The dimension binder: `pathLam`'s single child lives under ONE fresh binder. -/
theorem pathLam_binderShifts_pin : Generator.gen_pathLam.binderShifts = [1] := rfl

/-- The dimension application: two unshifted children (path term, interval argument). -/
theorem pathApp_binderShifts_pin : Generator.gen_pathApp.binderShifts = [0, 0] := rfl

/-- The interval endpoints are nullary. -/
theorem interval0_binderShifts_pin : Generator.gen_interval0.binderShifts = [] := rfl
theorem interval1_binderShifts_pin : Generator.gen_interval1.binderShifts = [] := rfl

/-- The identity-code TEMPLATE for the future bridge former: ternary, flat. -/
theorem idCode_binderShifts_pin : Generator.gen_idCode.binderShifts = [0, 0, 0] := rfl

/-- The ENTIRE param-relevant substrate is semantically RESERVED — no typing rules in any
engine and no β/ι redex head.  The rows designed above are genuinely NEW semantics, not a
re-description of existing meaning. -/
theorem paramSubstrate_allReserved :
    semanticTier .gen_pathLam = .reserved ∧
    semanticTier .gen_pathApp = .reserved ∧
    semanticTier .gen_interval0 = .reserved ∧
    semanticTier .gen_interval1 = .reserved ∧
    semanticTier .gen_intervalOpp = .reserved ∧
    semanticTier .gen_intervalMeet = .reserved ∧
    semanticTier .gen_intervalJoin = .reserved :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The observational-equality family is likewise reserved (shared endpoint-computation rule
shape, surveyed for the HOTT track's benefit). -/
theorem oeqFamily_allReserved :
    semanticTier .gen_oeqRefl = .reserved ∧
    semanticTier .gen_oeqJ = .reserved ∧
    semanticTier .gen_oeqFunext = .reserved :=
  ⟨rfl, rfl, rfl⟩

/-! ## The substrate ledger (the honest gap statement) -/

/-- **The param-substrate ledger** — what internal parametricity needs vs what the table
provides, in the honest-ledger discipline (a `false` field is a recorded GAP, not a claim). -/
structure ParamSubstrateLedger where
  /-- The dimension binder pair (`pathLam`/`pathApp`) exists in the table. -/
  hasDimensionBinderPair : Bool
  /-- The interval endpoint elements (`interval0`/`interval1`) exist in the table. -/
  hasIntervalEndpoints : Bool
  /-- An interval TYPE code (context-bindable dimension classifier) exists. -/
  hasIntervalTypeCode : Bool
  /-- A bridge FORMER (`Bridge A a b`, ternary flat) exists. -/
  hasBridgeFormer : Bool
  /-- The dimension binder family carries typing rows in some engine. -/
  hasDimensionTypingRows : Bool
  /-- An endpoint-computation ι rule for `pathApp ∘ pathLam` exists in `Step`. -/
  hasEndpointComputation : Bool
  /-- The affine-dimension discipline is expressible — TRUE via the GRADED substrate (the
  usage semiring's affine grade), NOT via the structural type context. -/
  hasAffinityDiscipline : Bool

/-- The surveyed ledger: binder pair + endpoints + (graded) affinity exist; the interval
code, the bridge former, the typing rows, and the endpoint ι are the OP1-INT landing list. -/
def paramSubstrateLedger : ParamSubstrateLedger where
  hasDimensionBinderPair := true
  hasIntervalEndpoints := true
  hasIntervalTypeCode := false
  hasBridgeFormer := false
  hasDimensionTypingRows := false
  hasEndpointComputation := false
  hasAffinityDiscipline := true

/-- The gap pins, read off the ledger (stability guard: if a future firing lands one of the
missing pieces, this theorem breaks and forces the ledger refresh). -/
theorem paramSubstrateLedger_gapsPinned :
    paramSubstrateLedger.hasIntervalTypeCode = false ∧
    paramSubstrateLedger.hasBridgeFormer = false ∧
    paramSubstrateLedger.hasDimensionTypingRows = false ∧
    paramSubstrateLedger.hasEndpointComputation = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The asset pins. -/
theorem paramSubstrateLedger_assetsPinned :
    paramSubstrateLedger.hasDimensionBinderPair = true ∧
    paramSubstrateLedger.hasIntervalEndpoints = true ∧
    paramSubstrateLedger.hasAffinityDiscipline = true :=
  ⟨rfl, rfl, rfl⟩

/-- **The reserved-tier coherence of the gap statement**: `hasDimensionTypingRows = false` is
not an unverified ledger entry — it FOLLOWS from the machine-checked tier pins (a reserved
generator is untyped by every engine, HON-5). -/
theorem dimensionTypingRowsGap_coherentWithTier :
    paramSubstrateLedger.hasDimensionTypingRows = false ∧
    semanticTier .gen_pathLam = .reserved ∧ semanticTier .gen_pathApp = .reserved :=
  ⟨rfl, paramSubstrate_allReserved.1, paramSubstrate_allReserved.2.1⟩

end FX1Poly.Typed
