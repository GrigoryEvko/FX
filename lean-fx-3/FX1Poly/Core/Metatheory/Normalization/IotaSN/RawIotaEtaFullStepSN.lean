import FX1Poly.Core.Metatheory.Normalization.IotaSN.RawIotaFullStepSN
import FX1Poly.Core.Metatheory.Normalization.Orders.EtaRpoEmbedding
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTableSourceShape

/-! # FX1Poly/Core/RawIotaEtaFullStepSN
    — the FULL oriented-ι∪η reduction (root + congruence) is strongly normalizing by ONE recursive path
    order, INDEPENDENT of β and of typed SN

This is the union of `RawIotaFullStepSN`'s full oriented-ι `IotaStep` with the canonical root-table η
relation (`StepEtaRootTable`).  The oriented ι reduction was put into a well-founded recursive path order via `eraseToRose`;
`eraseToRose` is rename-invariant; and every raw η-contraction RPO-decreases that SAME `eraseToRose` order
(precedence-agnostically, so it specialises to `iotaGenPrecedence`).  This file assembles the three into the
compatible (congruence) closure of (oriented-ι-root ∨ η-root) and lifts the embedding through congruence,
giving strong normalization of the combined fragment.

Why the union is FREE once both legs embed into one order: an `IotaEtaStep` is either a root step (oriented
ι or η, both RPO-decreasing) or a congruence step (ι or η inside child position `i`, the child
RPO-decreasing by the inductive hypothesis, lifted by `rpo_congruence`).  In every case the whole term's
`eraseToRose` strictly decreases under the single well-founded `Rpo iotaGenPrecedence`, so SN follows by
`Subrelation.wf` + `InvImage.wf` — no fresh measure, no Geser union argument.

## What this ships

  * `IotaEtaStep` / `IotaEtaStepChildren` — the full oriented-ι∪η reduction = compatible closure of
    `IotaOrientedHeadStep ∨ StepEtaRootTable` (mutual, mirrors `IotaStep`/`IotaStepChildren`).
  * `IotaOrientedHeadStep.toIotaEta` / `StepEtaRootTable.toIotaEta` — both fragments inject into the union at the
    head.
  * **`IotaEtaStep.rpoEmbeds` (★)** — every full oriented-ι∪η-step RPO-decreases the erasure.  Root via the
    `Or.elim`: ι → `IotaHeadStep.rpoEmbeds` (fed the oriented step's guard), η → `StepEtaRootTable.rpoEmbeds`;
    congruence via `rpo_congruence` (identical children-spine machinery to `IotaStep.rpoEmbeds`).
  * **`iotaEtaFullStep_wellFounded` (★)** — the FULL oriented-ι∪η reduction is SN by `Subrelation.wf` +
    `InvImage.wf eraseToRose` over `iotaGenRpoWellFounded`.  The terminating ι/η fragment terminates on its
    OWN order, NOT through Tait.
  * `IotaEtaStep.canonicalEtaCongSmoke` — non-vacuity: an η step INSIDE a congruence (the new capability beyond
    root-only η), sourced from the canonical `StepEtaRootTable`.

## Honest scope (Phase-Z re-scope EXECUTED)

β stays Tait-imported (raw β is non-SN — witnessed by the Ω combinator); β's argument-duplication is exactly
what an RPO cannot orient.  Under the Phase-Z motive migration the natElim/natRec SUCCESSOR iotas SUBSTITUTE
and share β's duplication shape, so they too sit at the Tait-imported boundary: the ι leg here is the
ORIENTED fragment (`IotaOrientedHeadStep`, root ι minus those two arms).  This file's claim is precisely
"oriented ι∪η terminates independently"; the β/substituting-ι boundary is the permanent honest seam.

## Zero-axiom verification

Mirrors `RawIotaFullStepSN`: the mutual recursor `IotaEtaStep.rec` with a `Prop` motive is propext-clean (the
`Step.subst` pattern); children eqs use `List.nil_append` / `List.cons_append` (NOT `append_assoc`/`append_nil`);
`eraseChildren` reductions via `dsimp only` / `show`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Core.RpoInductive
open FX1Poly.Core.RawIotaRpo

-- The full oriented-ι∪η reduction: the compatible (congruence) closure of (oriented root ι ∨ root η).
-- Mirrors IotaStep/IotaStepChildren exactly, with the head relation widened to
-- IotaOrientedHeadStep ∨ StepEtaRootTable.  (A /-- -/ doc comment cannot precede `mutual`.)
mutual
  inductive IotaEtaStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
    | head {scope : Nat} {source target : RawTerm scope}
           (rootStep : IotaOrientedHeadStep source target ∨ StepEtaRootTable source target) :
        IotaEtaStep source target
    | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
           {children children' : RawTermChildren gen.binderShifts scope}
           (childStep : IotaEtaStepChildren (binderShifts := gen.binderShifts) children children') :
        IotaEtaStep (.mkGen gen payload children) (.mkGen gen payload children')
  inductive IotaEtaStepChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
      RawTermChildren binderShifts parentScope →
      RawTermChildren binderShifts parentScope → Prop where
    | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
           {head head' : RawTerm (parentScope + headShift)}
           (rest : RawTermChildren restShifts parentScope)
           (childStep : IotaEtaStep head head') :
        IotaEtaStepChildren (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest)
    | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
            (head : RawTerm (parentScope + headShift))
            {rest rest' : RawTermChildren restShifts parentScope}
            (restStep : IotaEtaStepChildren rest rest') :
        IotaEtaStepChildren (RawTermChildren.childCons head rest) (RawTermChildren.childCons head rest')
end

/-- Root injection: every oriented ι-root step is a full oriented-ι∪η step. -/
theorem IotaOrientedHeadStep.toIotaEta {scope : Nat} {source target : RawTerm scope}
    (rootStep : IotaOrientedHeadStep source target) : IotaEtaStep source target :=
  IotaEtaStep.head (Or.inl rootStep)

/-- **Canonical-table root injection**: every canonical root-table η
contraction is a full ι∪η step — the head arm now carries the canonical
`StepEtaRootTable` relation directly, so the injection is a single
constructor with NO bespoke `Step.eta` detour. -/
theorem StepEtaRootTable.toIotaEta {scope : Nat}
    {source target : RawTerm scope}
    (rootStep : StepEtaRootTable source target) : IotaEtaStep source target :=
  IotaEtaStep.head (Or.inr rootStep)

/-- **Head-clash refutation for the canonical root table η**: a cell whose
head generator is none of the three raw-tier η roots (`gen_lam` / `gen_pair`
/ `gen_pathLam`) admits no `StepEtaRootTable` contraction.  Inverting the
contraction pins the head to a row's intro generator; the membership
case-split refutes the three raw-tier rows by the head clash and the five
typed-tier rows by `isRawTier`.  The bespoke-free twin of `Step.eta`'s
head-clash refutations, available to canonical ι∪η-normality consumers. -/
theorem noTableEtaFromGenHead {scope : Nat} {gen : Generator}
    {payload : gen.payload scope} {children : RawTermChildren gen.binderShifts scope}
    {reduct : RawTerm scope}
    (notLam : gen ≠ Generator.gen_lam)
    (notPair : gen ≠ Generator.gen_pair)
    (notPathLam : gen ≠ Generator.gen_pathLam)
    (step : StepEtaRootTable (.mkGen gen payload children) reduct) :
    False := by
  obtain ⟨rule, isRow, isRawTier, _introPayload, _introChildren, sourceShape, _contracts⟩ :=
    step.invert
  have headEq : gen = rule.introGenerator :=
    congrArg
      (fun cell => match cell with | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
      sourceShape
  subst headEq
  cases isRow with
  | head => exact notLam rfl
  | tail _ isRow => cases isRow with
    | head => exact notPair rfl
    | tail _ isRow => cases isRow with
      | head => exact notPathLam rfl
      | tail _ isRow => cases isRow with
        | head => exact Bool.noConfusion isRawTier
        | tail _ isRow => cases isRow with
          | head => exact Bool.noConfusion isRawTier
          | tail _ isRow => cases isRow with
            | head => exact Bool.noConfusion isRawTier
            | tail _ isRow => cases isRow with
              | head => exact Bool.noConfusion isRawTier
              | tail _ isRow => cases isRow with
                | head => exact Bool.noConfusion isRawTier
                | tail _ isRow => cases isRow

/-- **Lam-headed, non-app-body refutation for the canonical root table η**:
a `gen_lam` cell whose body child is not an `app` admits no
`StepEtaRootTable`.  The only `gen_lam`-headed raw-tier row is `etaLamRow`,
whose successful contraction forces the source into `etaLamSource`
(`etaLamRowContraction_sourceShape`) — body `app (weaken core) (var 0)`; a
non-app body clashes with that shape, refuting the firing. -/
theorem noTableEtaFromLamNonAppBody {scope : Nat}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {reduct : RawTerm scope}
    (bodyNotApp :
      (match body with | RawTerm.mkGen bodyGenerator _ _ => bodyGenerator)
        ≠ Generator.gen_app)
    (step : StepEtaRootTable
      (.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons body .childNil))) reduct) :
    False := by
  obtain ⟨rule, isRow, isRawTier, introPayload, introChildren, sourceShape, contracts⟩ :=
    step.invert
  have headEq : Generator.gen_lam = rule.introGenerator :=
    congrArg
      (fun cell => match cell with | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
      sourceShape
  cases isRow with
  | head =>
      -- `rule = etaLamRow`; a successful contraction forces the source into
      -- `etaLamSource`, whose body is an `app` — clashing with `bodyNotApp`.
      obtain ⟨extractedDomain, sourceIsEtaLam⟩ :=
        etaLamRowContraction_sourceShape introPayload contracts
      rw [← sourceShape] at sourceIsEtaLam
      injection sourceIsEtaLam with _scopeRefl _genRefl _payloadEq childrenEq
      injection childrenEq with _domScopeRefl _domHeadShiftRefl _domRestShiftsRefl
        _domainEq bodyTailEq
      injection bodyTailEq with _bodyScopeRefl _bodyHeadShiftRefl _bodyRestShiftsRefl
        bodyEq _nilEq
      subst bodyEq
      exact bodyNotApp rfl
  | tail _ isRow => cases isRow with
    | head => exact nomatch headEq
    | tail _ isRow => cases isRow with
      | head => exact nomatch headEq
      | tail _ isRow => cases isRow with
        | head => exact Bool.noConfusion isRawTier
        | tail _ isRow => cases isRow with
          | head => exact Bool.noConfusion isRawTier
          | tail _ isRow => cases isRow with
            | head => exact Bool.noConfusion isRawTier
            | tail _ isRow => cases isRow with
              | head => exact Bool.noConfusion isRawTier
              | tail _ isRow => cases isRow with
                | head => exact Bool.noConfusion isRawTier
                | tail _ isRow => cases isRow

/-- **★ Every full oriented-ι∪η-step RPO-decreases the erasure.**  Root via `Or.elim` (oriented ι →
`IotaHeadStep.rpoEmbeds` fed the guard component, η → `Step.eta.rpoEmbeds`, both landing at
`iotaGenPrecedence`); ι/η-inside-children via `rpo_congruence` (the children-spine motive extracts the
single-position `prefix ++ child :: suffix` split). -/
theorem IotaEtaStep.rpoEmbeds {scope : Nat} {source target : RawTerm scope}
    (step : IotaEtaStep source target) :
    Rpo iotaGenPrecedence (eraseToRose source) (eraseToRose target) := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) → IotaEtaStep first second → Prop :=
    fun {_} first second _ => Rpo iotaGenPrecedence (eraseToRose first) (eraseToRose second)
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) → IotaEtaStepChildren first second → Prop :=
    fun {_} {_} first second _ =>
      ∃ (prefixChildren suffixChildren : List (RoseTerm Generator))
        (bigChild smallChild : RoseTerm Generator),
        eraseChildren first = prefixChildren ++ bigChild :: suffixChildren ∧
        eraseChildren second = prefixChildren ++ smallChild :: suffixChildren ∧
        Rpo iotaGenPrecedence bigChild smallChild
  exact
    IotaEtaStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_} {_} rootStep =>
        rootStep.elim
          (fun headIota => IotaHeadStep.rpoEmbeds headIota.1 headIota.2)
          (fun headEta => StepEtaRootTable.rpoEmbeds headEta))
      (fun {_} gen _payload {children} {children'} _childStep childStepIH => by
        obtain ⟨prefixChildren, suffixChildren, bigChild, smallChild, hbefore, hafter, hrpo⟩ := childStepIH
        show Rpo iotaGenPrecedence (.node gen (eraseChildren children))
          (.node gen (eraseChildren children'))
        rw [hbefore, hafter]
        exact rpo_congruence gen prefixChildren suffixChildren bigChild smallChild hrpo)
      (fun {_} {_} {_} {head} {head'} rest _childStep childStepIH =>
        ⟨[], eraseChildren rest, eraseToRose head, eraseToRose head',
          (List.nil_append _).symm, (List.nil_append _).symm, childStepIH⟩)
      (fun {_} {_} {_} head {rest} {rest'} _restStep restStepIH => by
        obtain ⟨prefixChildren, suffixChildren, bigChild, smallChild, hbefore, hafter, hrpo⟩ := restStepIH
        refine ⟨eraseToRose head :: prefixChildren, suffixChildren, bigChild, smallChild, ?_, ?_, hrpo⟩
        · dsimp only [eraseChildren]; rw [hbefore]; exact List.cons_append .. |>.symm
        · dsimp only [eraseChildren]; rw [hafter]; exact List.cons_append .. |>.symm)
      step

/-- Accessibility successor: `laterTerm` is below `earlierTerm` when `earlierTerm` full-ι∪η-contracts to it. -/
def IotaEtaStep.successor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  IotaEtaStep earlierTerm laterTerm

/-- **★ The full ι∪η reduction of the real kernel is strongly normalizing — by ONE RPO, Tait-free.**  The
term endpoint of Leg 3: the terminating ι/η fragment terminates on its OWN order (`eraseToRose` into the
well-founded `iotaGenRpoWellFounded`), NOT through Tait.  β stays Tait-imported (raw β is non-SN). -/
theorem iotaEtaFullStep_wellFounded {scope : Nat} :
    WellFounded (IotaEtaStep.successor (scope := scope)) :=
  Subrelation.wf
    (r := InvImage (RpoBelow iotaGenPrecedence) eraseToRose)
    (fun step => IotaEtaStep.rpoEmbeds step)
    (InvImage.wf eraseToRose iotaGenRpoWellFounded)

/-- Every raw term is full-ι∪η strongly normalizing (accessible). -/
theorem IotaEtaStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc IotaEtaStep.successor sourceTerm :=
  iotaEtaFullStep_wellFounded.apply sourceTerm

/-- A canonical raw-tier root-table η contraction at the root: the
function-eta redex `lam unit (app (weaken unit) (var 0))` contracts to
`unit` as a `StepEtaRootTable` step.  Feeds the canonical-relation smoke
below. -/
theorem stepEtaRootTable_etaLamSmoke :
    StepEtaRootTable (scope := 0)
      (RawTerm.etaLamSource (.mkGen .gen_unit () .childNil)
        (.mkGen .gen_unit () .childNil))
      (.mkGen .gen_unit () .childNil) :=
  StepEtaRootOverTable.etaRedex etaLamRow_memTable rfl ()
    (etaLamRow_contractsOnSource (.mkGen .gen_unit () .childNil)
      (.mkGen .gen_unit () .childNil))

/-- **Canonical-table congruence non-vacuity** (TABLE-CANON-ETA twin of
`IotaEtaStep.etaCongSmoke`): an η step INSIDE a congruence, sourced from
the CANONICAL root-table relation through `StepEtaRootTable.toIotaEta`
rather than a bespoke `Step.eta`.  The raw-tier function-eta redex in the
first argument of an `app` ι∪η-reduces to `unit`. -/
theorem IotaEtaStep.canonicalEtaCongSmoke :
    IotaEtaStep (scope := 0)
      (.mkGen .gen_app ()
        (.childCons
          (RawTerm.etaLamSource (.mkGen .gen_unit () .childNil)
            (.mkGen .gen_unit () .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))) :=
  IotaEtaStep.cong .gen_app ()
    (IotaEtaStepChildren.here (.childCons (.mkGen .gen_unit () .childNil) .childNil)
      (StepEtaRootTable.toIotaEta stepEtaRootTable_etaLamSmoke))

end FX1Poly.Core
