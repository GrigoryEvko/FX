import FX1Poly.Core.RawIotaFullStepSN
import FX1Poly.Core.EtaRpoEmbedding

/-! # FX1Poly/Core/RawIotaEtaFullStepSN
    — the FULL ι∪η reduction (root + congruence) is strongly normalizing by ONE recursive path order,
    INDEPENDENT of β and of typed SN

This is the union of `RawIotaFullStepSN`'s full-ι `IotaStep` with the raw η rules (`Step.eta`, StepEta).
The full ι reduction was put into a well-founded recursive path order via `eraseToRose`; `eraseToRose` is
rename-invariant; and every raw η-contraction RPO-decreases that SAME `eraseToRose` order
(precedence-agnostically, so it specialises to `iotaGenPrecedence`).  This file assembles the three into the
compatible (congruence) closure of (ι-root ∨ η-root) and lifts the embedding through congruence, giving
strong normalization of the combined fragment.

Why the union is FREE once both legs embed into one order: an `IotaEtaStep` is either a root step (ι or η,
both RPO-decreasing) or a congruence step (ι or η inside child position `i`, the child RPO-decreasing by the
inductive hypothesis, lifted by `rpo_congruence`).  In every case the whole term's `eraseToRose` strictly
decreases under the single well-founded `Rpo iotaGenPrecedence`, so SN follows by `Subrelation.wf` +
`InvImage.wf` — no fresh measure, no Geser union argument.

## What this ships

  * `IotaEtaStep` / `IotaEtaStepChildren` — the full ι∪η reduction = compatible closure of
    `IotaHeadStep ∨ Step.eta` (mutual, mirrors `IotaStep`/`IotaStepChildren`).
  * `IotaHeadStep.toIotaEta` / `Step.eta.toIotaEta` — both fragments inject into the union at the head.
  * **`IotaEtaStep.rpoEmbeds` (★)** — every full ι∪η-step RPO-decreases the erasure.  Root via the `Or.elim`:
    ι → `IotaHeadStep.rpoEmbeds`, η → `Step.eta.rpoEmbeds`; congruence via `rpo_congruence` (identical
    children-spine machinery to `IotaStep.rpoEmbeds`).
  * **`iotaEtaFullStep_wellFounded` (★)** — the FULL ι∪η reduction is SN by `Subrelation.wf` +
    `InvImage.wf eraseToRose` over `iotaGenRpoWellFounded`.  The terminating ι/η fragment terminates on its
    OWN order, NOT through Tait.
  * `IotaEtaStep.etaCongSmoke` — non-vacuity: an η step INSIDE a congruence (the new capability beyond
    root-only `Step.eta`).

## Honest scope

β stays Tait-imported (raw β is non-SN — witnessed by the Ω combinator); β's argument-duplication is exactly
what an RPO cannot orient.  This file's claim is precisely "ι∪η terminates independently"; the β boundary is
the permanent honest seam.

## Zero-axiom verification

Mirrors `RawIotaFullStepSN`: the mutual recursor `IotaEtaStep.rec` with a `Prop` motive is propext-clean (the
`Step.subst` pattern); children eqs use `List.nil_append` / `List.cons_append` (NOT `append_assoc`/`append_nil`);
`eraseChildren` reductions via `dsimp only` / `show`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Core.RpoInductive
open FX1Poly.Core.RawIotaRpo

-- The full ι∪η reduction: the compatible (congruence) closure of (root ι ∨ root η).  Mirrors
-- IotaStep/IotaStepChildren exactly, with the head relation widened to IotaHeadStep ∨ Step.eta.  (A /-- -/
-- doc comment cannot precede `mutual`.)
mutual
  inductive IotaEtaStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
    | head {scope : Nat} {source target : RawTerm scope}
           (rootStep : IotaHeadStep source target ∨ Step.eta source target) :
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

/-- Root injection: every full ι-root step is a full ι∪η step. -/
theorem IotaHeadStep.toIotaEta {scope : Nat} {source target : RawTerm scope}
    (rootStep : IotaHeadStep source target) : IotaEtaStep source target :=
  IotaEtaStep.head (Or.inl rootStep)

/-- Root injection: every raw η step is a full ι∪η step. -/
theorem Step.eta.toIotaEta {scope : Nat} {source target : RawTerm scope}
    (etaStep : Step.eta source target) : IotaEtaStep source target :=
  IotaEtaStep.head (Or.inr etaStep)

/-- **★ Every full ι∪η-step RPO-decreases the erasure.**  Root via `Or.elim` (ι → `IotaHeadStep.rpoEmbeds`,
η → `Step.eta.rpoEmbeds`, both landing at `iotaGenPrecedence`); ι/η-inside-children via `rpo_congruence` (the
children-spine motive extracts the single-position `prefix ++ child :: suffix` split). -/
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
          (fun headIota => IotaHeadStep.rpoEmbeds headIota)
          (fun headEta => Step.eta.rpoEmbeds headEta))
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

/-- Non-vacuity: an η step INSIDE a congruence (function position of an app) — the new capability beyond
root-only `Step.eta`.  `app (modIntro (modElim unit)) unit` ι∪η-reduces to `app unit unit` by η inside the
function child (`cong` ∘ `here` ∘ `head (Or.inr etaModIntro)`). -/
theorem IotaEtaStep.etaCongSmoke :
    IotaEtaStep (scope := 0)
      (.mkGen .gen_app ()
        (.childCons (RawTerm.etaModIntroSource (.mkGen .gen_unit () .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))) :=
  IotaEtaStep.cong .gen_app ()
    (IotaEtaStepChildren.here (.childCons (.mkGen .gen_unit () .childNil) .childNil)
      (IotaEtaStep.head (Or.inr (Step.eta.etaModIntro (.mkGen .gen_unit () .childNil)))))

end FX1Poly.Core
