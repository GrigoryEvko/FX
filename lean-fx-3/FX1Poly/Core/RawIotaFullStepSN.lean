import FX1Poly.Core.RawIotaRpoAssembly
import FX1Poly.Core.RecursivePathOrderInductive

/-! # FX1Poly/Core/RawIotaFullStepSN
    — the FULL ORIENTED ι-reduction relation of the real kernel (oriented root ι + oriented ι
    inside ANY child context) is strongly normalizing by ONE recursive path order, INDEPENDENT
    of β and typed-SN

`RawIotaRpoAssembly` put the 14 RPO-ORIENTABLE root ι arms of the canonical `IotaHeadStep` — the
oriented sub-relation `IotaOrientedHeadStep`, excluding the two Phase-Z SUBSTITUTING natElim/natRec
succ-iotas — into one well-founded RPO via `eraseToRose`.  But the root relation is root-only (the
redex at the head).  This file lifts that to the FULL oriented ι reduction — the compatible
(congruence) closure: oriented ι at the root OR oriented ι somewhere inside the `RawTermChildren`
spine, mutually defined exactly like the kernel's `Step`/`StepChildren`, restricted to the oriented
ι fragment.

The congruence case is where `rpo_congruence` is finally consumed.  When an ι step fires inside
child position `i`, `eraseToRose` of the whole term changes only in that child's subtree: the children list
`eraseChildren` goes from `prefix ++ eraseToRose child :: suffix` to `prefix ++ eraseToRose child' :: suffix`,
with the child RPO-decreasing by the inductive hypothesis.  `rpo_congruence` (replacing one child of a node by
an RPO-smaller one makes the node RPO-smaller) closes exactly this.  The `here`/`there` walk down the spine
builds the `prefix`: `[]` at the head (`here`), `eraseToRose head :: prefix` one step in (`there`).

## What this ships

  * `IotaStep` / `IotaStepChildren` — the full oriented ι reduction = compatible closure of
    `IotaOrientedHeadStep` (mutual, mirrors `Step`/`StepChildren`); `IotaStep.toStep` (soundness: a
    sub-relation of the live `Step`).
  * **`IotaStep.rpoEmbeds` (★)** — every full oriented ι-step RPO-decreases the erasure.  Root ι via
    `IotaHeadStep.rpoEmbeds` (the guard component discharges the substituting arms); ι-inside-children via
    `rpo_congruence` (the children-spine motive extracts the single-position `prefix ++ child :: suffix`
    split the congruence consumes).  Proven with the explicit mutual recursor `IotaStep.rec` (the codebase's
    clean route for `Step`/`StepChildren`-shaped mutual proofs).
  * **`iotaFullStep_wellFounded` (★)** — the FULL oriented ι-reduction relation is SN by `Subrelation.wf` +
    `InvImage.wf eraseToRose` over the well-founded `iotaGenRpoWellFounded`.  This is the genuine oriented
    ι-fragment strong normalization (not just root), INDEPENDENT of β and of typed-SN.

## Honest scope (Phase-Z re-scope EXECUTED)

This closes the oriented-ι half of "the terminating ι/η fragment terminates on its OWN, NOT through Tait".
η-SN is shipped separately (`Step.etaStar`).  β stays Tait-imported (raw β is non-SN, witnessed by the Ω
combinator) — the honest boundary, since β's argument-duplication is exactly what the RPO cannot orient.
Under the Phase-Z motive migration the natElim/natRec **successor** iotas SUBSTITUTE
(`subst (cons recursiveCall (singleton predecessor)) succBranch`) and share β's duplication shape, so they
JOIN β at the Tait-imported boundary: this relation is the compatible closure of the ORIENTED root fragment
(`IotaOrientedHeadStep` — root ι minus those two arms), and typed-SN covers the substituting iotas through
Tait exactly as it covers β.

## Zero-axiom verification

The mutual recursor `IotaStep.rec` with a `Prop`-valued motive is propext-clean (the `Step.subst` pattern);
the children eqs use the propext-clean `List.nil_append`/`List.cons_append` (NOT `append_assoc`/`append_nil`,
which leak propext per the List.append discipline); `eraseChildren` reductions use `dsimp only` (clean on the
mutual def) / `show` (defeq through the `let`-bound motive).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Core.RpoInductive
open FX1Poly.Core.RawIotaRpo

-- The full ORIENTED ι-reduction relation: the compatible (congruence) closure of IotaOrientedHeadStep.
-- Oriented root ι at the head, OR oriented ι somewhere inside the children spine (mutually with
-- IotaStepChildren).  Mirrors Step/StepChildren exactly, restricted to the oriented ι fragment (no β, no η,
-- no substituting succ-iota).  (A /-- -/ doc comment cannot precede `mutual`.)
mutual
  inductive IotaStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
    | head {scope : Nat} {source target : RawTerm scope}
           (rootStep : IotaOrientedHeadStep source target) : IotaStep source target
    | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
           {children children' : RawTermChildren gen.binderShifts scope}
           (childStep : IotaStepChildren (binderShifts := gen.binderShifts) children children') :
        IotaStep (.mkGen gen payload children) (.mkGen gen payload children')
  inductive IotaStepChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
      RawTermChildren binderShifts parentScope →
      RawTermChildren binderShifts parentScope → Prop where
    | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
           {head head' : RawTerm (parentScope + headShift)}
           (rest : RawTermChildren restShifts parentScope)
           (childStep : IotaStep head head') :
        IotaStepChildren (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest)
    | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
            (head : RawTerm (parentScope + headShift))
            {rest rest' : RawTermChildren restShifts parentScope}
            (restStep : IotaStepChildren rest rest') :
        IotaStepChildren (RawTermChildren.childCons head rest) (RawTermChildren.childCons head rest')
end

/-- **★ Every full oriented ι-step RPO-decreases the erasure** — the genuine oriented-ι lift: root ι via
`IotaHeadStep.rpoEmbeds` (fed the oriented step's guard component), and ι-inside-children via
`rpo_congruence` (the children-spine motive extracts the single-position `prefix ++ child :: suffix` split
that the congruence consumes; `here` gives the empty prefix, `there` prepends the unchanged head). -/
theorem IotaStep.rpoEmbeds {scope : Nat} {source target : RawTerm scope}
    (step : IotaStep source target) :
    Rpo iotaGenPrecedence (eraseToRose source) (eraseToRose target) := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) → IotaStep first second → Prop :=
    fun {_} first second _ => Rpo iotaGenPrecedence (eraseToRose first) (eraseToRose second)
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) → IotaStepChildren first second → Prop :=
    fun {_} {_} first second _ =>
      ∃ (prefixChildren suffixChildren : List (RoseTerm Generator))
        (bigChild smallChild : RoseTerm Generator),
        eraseChildren first = prefixChildren ++ bigChild :: suffixChildren ∧
        eraseChildren second = prefixChildren ++ smallChild :: suffixChildren ∧
        Rpo iotaGenPrecedence bigChild smallChild
  exact
    IotaStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_} {_} rootStep => IotaHeadStep.rpoEmbeds rootStep.1 rootStep.2)
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

/-- **Soundness**: every full oriented ι-step is a genuine `Step` of the real kernel (root ι via
`IotaHeadStep.toStep` on the oriented step's relation component, congruence via `Step.cong`) — a
sub-relation of the live reduction relation, not a toy model. -/
theorem IotaStep.toStep {scope : Nat} {source target : RawTerm scope}
    (step : IotaStep source target) : Step source target := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) → IotaStep first second → Prop :=
    fun {_} first second _ => Step first second
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) → IotaStepChildren first second → Prop :=
    fun {_} {_} first second _ => StepChildren first second
  exact
    IotaStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} {_} {_} rootStep => rootStep.1.toStep)
      (fun {_} gen payload {_} {_} _childStep childStepIH => Step.cong gen payload childStepIH)
      (fun {_} {_} {_} {_} {_} rest _childStep childStepIH => StepChildren.here rest childStepIH)
      (fun {_} {_} {_} head {_} {_} _restStep restStepIH => StepChildren.there head restStepIH)
      step

/-- Accessibility successor: `laterTerm` is below `earlierTerm` when `earlierTerm` full-oriented-ι-contracts
to it (mirrors `Step.etaSuccessor` / `IotaOrientedHeadStep.successor`). -/
def IotaStep.successor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  IotaStep earlierTerm laterTerm

/-- **★ The FULL oriented ι-reduction relation of the real kernel is strongly normalizing — by ONE RPO,
Tait-free.**  Oriented root ι + oriented ι-inside-any-child, ALL via `eraseToRose` into the well-founded
`iotaGenRpoWellFounded` (`Subrelation.wf` + `InvImage.wf`).  This is the genuine oriented-ι SN (not just the
root fragment) — INDEPENDENT of β and of typed-SN.  η-SN is shipped separately; β AND the two Phase-Z
substituting succ-iotas stay Tait-imported. -/
theorem iotaFullStep_wellFounded {scope : Nat} :
    WellFounded (IotaStep.successor (scope := scope)) :=
  Subrelation.wf
    (r := InvImage (RpoBelow iotaGenPrecedence) eraseToRose)
    (fun step => IotaStep.rpoEmbeds step)
    (InvImage.wf eraseToRose iotaGenRpoWellFounded)

/-- Every raw term is full-oriented-ι strongly normalizing (accessible). -/
theorem IotaStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc IotaStep.successor sourceTerm :=
  iotaFullStep_wellFounded.apply sourceTerm

/-- Non-vacuity smoke: the congruence arm genuinely fires — `app (boolElim motive unit unit boolTrue) unit`
full-ι-reduces to `app unit unit` by an ι step INSIDE the function position (`cong` ∘ `here` ∘ `head`), not
at the root.  Demonstrates the closure is inhabited at the congruence arm, not just the head arm.  Phase-Z
motive shape: the motive is `var 0 : RawTerm 1` (under one binder), the scrutinee `boolTrue` is last. -/
theorem IotaStep.congSmoke :
    IotaStep (scope := 0)
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_boolElim ()
            (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
              (.childCons (.mkGen .gen_unit () .childNil)
                (.childCons (.mkGen .gen_unit () .childNil)
                  (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))) :=
  IotaStep.cong .gen_app ()
    (IotaStepChildren.here (.childCons (.mkGen .gen_unit () .childNil) .childNil)
      (IotaStep.head ⟨IotaHeadStep.iotaBoolTrue, rfl⟩))

end FX1Poly.Core
