import FX1Poly.Core.IotaRuleTable
import FX1Poly.Core.RawTermStrengthen

/-! # EtaRuleTable — ETA-T0: eta rules as data, the dedicated schema

The eta twin of the iota-rule table (IOTA-T0).  Eta is INTRO-rooted with
STRENGTHENING reducts, so it cannot join `IotaRuleDesc`: the iota
orthogonality discipline (IOTA-T5) requires eliminator roots disjoint
from scrutinee heads, and eta's roots (`lam`, `pair`, `pathLam`, …) ARE
the iota scrutinee heads; the iota `ReductTemplate` DSL deliberately has
no strengthening node.  This file ships the dedicated schema:

* `RawTerm.strengthenBy?` — the un-weakening engine: drop `depth` unused
  newest variables, success iff vars `0..depth-1` are unused; with the
  two roundtrip pins against `RawTerm.weakenBy`.
* `EtaObservationSpec` — ONE observation of the shared core: the intro
  cell's child at `introChildSlot` (under `binderDepth` fresh binders)
  must be an `observerHead` cell whose `coreSlot` child strengthens to
  the core and whose `freshVarSlots` children are exactly the fresh
  variables in order.
* `EtaRuleDesc` — the rule: an intro head plus its observations;
  `requiresTypedFiring` marks the typed-only tier excluded from the raw
  relation (the gated mod/glue semantics; Unit-eta and ghost-eta join at
  ETA-T6).
* `EtaRuleDesc.contractsOn?` — extract the core from the primary
  observation, then require every remaining observation to extract a
  **decidably EQUAL** core.  Eta with two or more observations is
  NON-LEFT-LINEAR (surjective pairing) — this `RawTermDecEq` gate is the
  honest cost, and the reason raw β+η union confluence is Klop-impossible
  (the ETA arc's raw tier targets postponement/quasi-commutation only).
* `etaRuleTable` — the five bespoke arms as rows.  NOTE: the mod/glue
  rows carry `requiresTypedFiring := true` (the GATED, correct
  semantics); the bespoke raw arms fire unconditionally (the StepEta
  over-approximation) — the discrepancy is deliberate and resolves at
  ETA-T7.
* per-row concrete contraction pins (the GO gate), including the
  non-left-linear NEGATIVE pin: `pair (fst unit) (snd OTHER)` does NOT
  contract — the DecEq gate genuinely fires.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaRuleTable.lean`. -/

namespace FX1Poly.Core

/-! ## The un-weakening engine -/

/-- Drop `depth` unused newest variables: invert `RawTerm.weakenBy`,
succeeding exactly when none of the `depth` newest variables occurs.
Structural on `depth`, one `RawTerm.strengthen` per level (newest
first, matching `weakenBy`'s outermost-last orientation). -/
def RawTerm.strengthenBy? {scope : Nat} (depth : Nat)
    (term : RawTerm (scope + depth)) : Option (RawTerm scope) :=
  match depth, term with
  | 0, term => some term
  | innerDepth + 1, term =>
      (RawTerm.strengthen term).bind
        (fun stripped => RawTerm.strengthenBy? innerDepth stripped)

/-- **Roundtrip**: strengthening after weakening recovers the original
(every introduced variable is unused by construction). -/
theorem RawTerm.strengthenBy?_weakenBy {scope : Nat} :
    (depth : Nat) → (sourceTerm : RawTerm scope) →
    RawTerm.strengthenBy? depth (RawTerm.weakenBy depth sourceTerm)
      = some sourceTerm
  | 0, _ => rfl
  | depth + 1, sourceTerm => by
      dsimp only [RawTerm.strengthenBy?, RawTerm.weakenBy]
      rw [RawTerm.strengthen_weaken]
      exact RawTerm.strengthenBy?_weakenBy depth sourceTerm

/-- **Reverse roundtrip**: a successful strengthening is inverted by
weakening — the extracted core reconstructs the input. -/
theorem RawTerm.weakenBy_strengthenBy? {scope : Nat} :
    (depth : Nat) → (term : RawTerm (scope + depth)) →
    (core : RawTerm scope) →
    RawTerm.strengthenBy? depth term = some core →
    RawTerm.weakenBy depth core = term
  | 0, _term, _core, success => (Option.some.inj success).symm
  | depth + 1, term, core, success => by
      dsimp only [RawTerm.strengthenBy?] at success
      match strippedEq : RawTerm.strengthen term with
      | none =>
          rw [strippedEq] at success
          exact nomatch success
      | some stripped =>
          rw [strippedEq] at success
          dsimp only [Option.bind] at success
          dsimp only [RawTerm.weakenBy]
          rw [RawTerm.weakenBy_strengthenBy? depth stripped core success]
          exact RawTerm.strengthen_sound term stripped strippedEq

/-! ## Shift-checked child lookup -/

/-- The child at `slot`, REQUIRED to sit at binder shift
`expectedShift` (decided against the spine's actual shift, with the
generator-coercion `▸` the table substrate already uses). -/
def RawTermChildren.childAtShift? {scope : Nat} {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope)
    (slot expectedShift : Nat) :
    Option (RawTerm (scope + expectedShift)) :=
  match binderShifts, children, slot with
  | _, .childNil, _ => none
  | headShift :: _restShifts, .childCons head _rest, 0 =>
      if shiftMatches : headShift = expectedShift then
        some (shiftMatches ▸ head)
      else none
  | _headShift :: _restShifts, .childCons _head rest, nextSlot + 1 =>
      rest.childAtShift? nextSlot expectedShift

/-! ## The observation schema -/

/-- One observation of the shared eta core: the intro cell's child at
`introChildSlot` (which must sit under `binderDepth` fresh binders) is
an `observerHead` cell whose `coreSlot` child strengthens to the core
and whose `freshVarSlots` children are exactly `var 0`, `var 1`, … in
list order. -/
structure EtaObservationSpec where
  introChildSlot : Nat
  observerHead : Generator
  coreSlot : Nat
  binderDepth : Nat
  freshVarSlots : List Nat

/-- The fresh-variable test: each listed observer slot holds exactly the
expected fresh variable (`var index` for the slot at list position
`index`). -/
def observerFreshVarsHold {observerScope : Nat}
    {observerShifts : List Nat}
    (observedChildren : RawTermChildren observerShifts observerScope) :
    (varSlots : List Nat) → (nextVarIndex : Nat) → Bool
  | [], _ => true
  | slot :: restSlots, varIndex =>
      (match observedChildren.childAtShift? slot 0 with
        | some child =>
            if isInBounds : varIndex < observerScope then
              if child
                  = RawTerm.mkGen .gen_var ⟨varIndex, isInBounds⟩
                      .childNil then
                true
              else false
            else false
        | none => false)
      && observerFreshVarsHold observedChildren restSlots (varIndex + 1)

/-- Extract this observation's core from the intro cell's children:
look up the intro child at the declared slot and binder depth, require
the observer head, require the fresh variables, strengthen the core
slot back to the intro's scope. -/
def EtaObservationSpec.extractCoreFrom? (spec : EtaObservationSpec)
    {scope : Nat} {introShifts : List Nat}
    (introChildren : RawTermChildren introShifts scope) :
    Option (RawTerm scope) :=
  (introChildren.childAtShift? spec.introChildSlot spec.binderDepth).bind
    fun observed =>
      match observed with
      | .mkGen observedHead _observedPayload observedChildren =>
          if observedHead = spec.observerHead then
            if observerFreshVarsHold observedChildren
                spec.freshVarSlots 0 then
              (observedChildren.childAtShift? spec.coreSlot 0).bind
                fun rawCore =>
                  RawTerm.strengthenBy? spec.binderDepth rawCore
            else none
          else none

/-! ## The rule descriptor -/

/-- One eta rule as DATA: the intro head whose cell contracts, plus the
observations that must all exhibit the SAME core.  `requiresTypedFiring`
marks the typed-only tier (the gated mod/glue semantics; Unit-eta and
ghost-eta at ETA-T6) excluded from the raw relation. -/
structure EtaRuleDesc where
  introGenerator : Generator
  observations : List EtaObservationSpec
  requiresTypedFiring : Bool := false

/-- Every remaining observation extracts a core decidably EQUAL to the
primary's — the non-left-linearity gate (surjective pairing). -/
def etaObservationsAgree {scope : Nat} {introShifts : List Nat}
    (introChildren : RawTermChildren introShifts scope)
    (core : RawTerm scope) :
    (specs : List EtaObservationSpec) → Bool
  | [] => true
  | spec :: restSpecs =>
      (match spec.extractCoreFrom? introChildren with
        | some otherCore => if otherCore = core then true else false
        | none => false)
      && etaObservationsAgree introChildren core restSpecs

/-- **The contraction engine**: extract the core from the primary
observation, gate the rest on decidable core equality, return the
shared core.  An observation-free rule never contracts (honest). -/
def EtaRuleDesc.contractsOn? (rule : EtaRuleDesc) {scope : Nat}
    (introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  match rule.observations with
  | [] => none
  | primarySpec :: restSpecs =>
      (primarySpec.extractCoreFrom? introChildren).bind fun core =>
        if etaObservationsAgree introChildren core restSpecs then some core
        else none

/-! ## The five rows

Child-slot ground truth (pinned below): `gen_lam` shifts `[0, 1]`
(domain annotation, body under one binder), `gen_pair`/`gen_glueIntro`
`[0, 0]`, `gen_pathLam` `[1]` (no domain annotation), `gen_modIntro`
`[0]`; every observer head (`gen_app`, `gen_fst`, `gen_snd`,
`gen_pathApp`, `gen_modElim`, `gen_glueElim`) has all-zero shifts. -/

theorem gen_lam_binderShifts :
    Generator.gen_lam.binderShifts = [0, 1] := rfl
theorem gen_pair_binderShifts :
    Generator.gen_pair.binderShifts = [0, 0] := rfl
theorem gen_pathLam_binderShifts :
    Generator.gen_pathLam.binderShifts = [1] := rfl
theorem gen_modIntro_binderShifts :
    Generator.gen_modIntro.binderShifts = [0] := rfl
theorem gen_glueIntro_binderShifts :
    Generator.gen_glueIntro.binderShifts = [0, 0] := rfl

/-- Function eta: `lam domainAnn (app (weaken f) (var 0)) ↝ f` — the
body (intro slot 1, one binder) observed through `gen_app` with the
argument pinned to the fresh variable. -/
def etaLamRow : EtaRuleDesc where
  introGenerator := .gen_lam
  observations :=
    [ { introChildSlot := 1, observerHead := .gen_app, coreSlot := 0
      , binderDepth := 1, freshVarSlots := [1] } ]

/-- Pair eta: `pair (fst p) (snd p) ↝ p` — TWO observations whose cores
must agree (the non-left-linear surjective-pairing row). -/
def etaPairRow : EtaRuleDesc where
  introGenerator := .gen_pair
  observations :=
    [ { introChildSlot := 0, observerHead := .gen_fst, coreSlot := 0
      , binderDepth := 0, freshVarSlots := [] }
    , { introChildSlot := 1, observerHead := .gen_snd, coreSlot := 0
      , binderDepth := 0, freshVarSlots := [] } ]

/-- Path eta: `pathLam (pathApp (weaken p) (var 0)) ↝ p` — the body
(intro slot 0, one binder) observed through `gen_pathApp`. -/
def etaPathLamRow : EtaRuleDesc where
  introGenerator := .gen_pathLam
  observations :=
    [ { introChildSlot := 0, observerHead := .gen_pathApp, coreSlot := 0
      , binderDepth := 1, freshVarSlots := [1] } ]

/-- Modal eta: `modIntro (modElim m) ↝ m` — TYPED-ONLY tier (the gated
semantics; the bespoke raw arm's unconditional firing is the StepEta
over-approximation, resolved at ETA-T7). -/
def etaModIntroRow : EtaRuleDesc where
  introGenerator := .gen_modIntro
  observations :=
    [ { introChildSlot := 0, observerHead := .gen_modElim, coreSlot := 0
      , binderDepth := 0, freshVarSlots := [] } ]
  requiresTypedFiring := true

/-- Glue eta: `glueIntro (glueElim g) _ ↝ g` — TYPED-ONLY tier (CCHM
coherence lives in the typing gate; same ETA-T7 seam). -/
def etaGlueIntroRow : EtaRuleDesc where
  introGenerator := .gen_glueIntro
  observations :=
    [ { introChildSlot := 0, observerHead := .gen_glueElim, coreSlot := 0
      , binderDepth := 0, freshVarSlots := [] } ]
  requiresTypedFiring := true

/-- The eta-rule table: the five bespoke `Step.eta` arms as rows. -/
def etaRuleTable : List EtaRuleDesc :=
  [etaLamRow, etaPairRow, etaPathLamRow, etaModIntroRow, etaGlueIntroRow]

/-- Stale-count guard: 5 eta rows. -/
theorem etaRuleTable_length : etaRuleTable.length = 5 := rfl

/-- The tier ledger: lam/pair/pathLam fire raw; mod/glue are the
typed-only (gated) tier. -/
theorem etaRuleTable_typedTierLedger :
    etaRuleTable.map EtaRuleDesc.requiresTypedFiring
      = [false, false, false, true, true] := rfl

/-! ## Concrete contraction pins — the GO gate -/

/-- `unit` at any scope. -/
@[reducible] def unitFixture (scope : Nat) : RawTerm scope :=
  .mkGen .gen_unit () .childNil

/-- Function eta contracts: `lam unit (app unit (var 0)) ↝ unit` (the
weakened core of a CLOSED function is itself, so the redex computes). -/
theorem etaLamRow_contractsOnConcrete :
    etaLamRow.contractsOn? (scope := 0)
      (.childCons (unitFixture 0)
        (.childCons
          (.mkGen .gen_app ()
            (.childCons (unitFixture 1)
              (.childCons
                (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
                .childNil)))
          .childNil))
    = some (unitFixture 0) := rfl

/-- Function eta REJECTS a non-variable argument position. -/
theorem etaLamRow_rejectsNonVarArgument :
    etaLamRow.contractsOn? (scope := 0)
      (.childCons (unitFixture 0)
        (.childCons
          (.mkGen .gen_app ()
            (.childCons (unitFixture 1)
              (.childCons (unitFixture 1) .childNil)))
          .childNil))
    = none := rfl

/-- Pair eta contracts: `pair (fst unit) (snd unit) ↝ unit`. -/
theorem etaPairRow_contractsOnConcrete :
    etaPairRow.contractsOn? (scope := 0)
      (.childCons
        (.mkGen .gen_fst () (.childCons (unitFixture 0) .childNil))
        (.childCons
          (.mkGen .gen_snd () (.childCons (unitFixture 0) .childNil))
          .childNil))
    = some (unitFixture 0) := rfl

/-- **The non-left-linearity gate FIRES**: `pair (fst unit) (snd p)`
with a DIFFERENT `p` does not contract — the two observations extract
unequal cores and the decidable-equality gate refuses. -/
theorem etaPairRow_rejectsDisagreeingCores :
    etaPairRow.contractsOn? (scope := 0)
      (.childCons
        (.mkGen .gen_fst () (.childCons (unitFixture 0) .childNil))
        (.childCons
          (.mkGen .gen_snd ()
            (.childCons
              (.mkGen .gen_pair ()
                (.childCons (unitFixture 0)
                  (.childCons (unitFixture 0) .childNil)))
              .childNil))
          .childNil))
    = none := rfl

/-- Path eta contracts: `pathLam (pathApp unit (var 0)) ↝ unit`. -/
theorem etaPathLamRow_contractsOnConcrete :
    etaPathLamRow.contractsOn? (scope := 0)
      (.childCons
        (.mkGen .gen_pathApp ()
          (.childCons (unitFixture 1)
            (.childCons
              (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
              .childNil)))
        .childNil)
    = some (unitFixture 0) := rfl

/-- Modal eta contracts (the engine; the typed gate is the RELATION's
job at ETA-T1/T6): `modIntro (modElim unit) ↝ unit`. -/
theorem etaModIntroRow_contractsOnConcrete :
    etaModIntroRow.contractsOn? (scope := 0)
      (.childCons
        (.mkGen .gen_modElim () (.childCons (unitFixture 0) .childNil))
        .childNil)
    = some (unitFixture 0) := rfl

/-- Glue eta contracts: `glueIntro (glueElim unit) unit ↝ unit` (the
second child is unconstrained by the row — the gated semantics
constrains it through typing, ETA-T7). -/
theorem etaGlueIntroRow_contractsOnConcrete :
    etaGlueIntroRow.contractsOn? (scope := 0)
      (.childCons
        (.mkGen .gen_glueElim () (.childCons (unitFixture 0) .childNil))
        (.childCons (unitFixture 0) .childNil))
    = some (unitFixture 0) := rfl

end FX1Poly.Core
