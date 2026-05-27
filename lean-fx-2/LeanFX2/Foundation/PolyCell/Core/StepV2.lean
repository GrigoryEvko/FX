import LeanFX2.Foundation.PolyCell.Core.RawTermV2Subst0

/-! # Foundation/PolyCell/Core/StepV2 — single-step reduction on V2

V2-L3.1 phase A + B (2026-05-27).  Discharges the first L3 metatheory
task per polycell.md §11.6.1.  Ships the `Step` inductive relation +
the beta-reduction constructor + the **uniform** congruence rule +
two smokes (beta-on-identity and cong-on-lam).

## Phase A vs Phase B

* **Phase A** shipped just `Step.beta` -- the beta-reduction
  constructor + one smoke witnessing the identity-lambda fixture.
* **Phase B** (THIS update) ships the UNIFORM congruence rule
  `Step.cong` via a mutual `Step + StepChildren` block.  ONE rule
  covers all 194 generators because StepChildren expresses "Step at
  some child position" generically using `binderShifts` and the
  generic `RawTermChildrenV2` substrate.

This is the L3 KICKOFF: the FIRST shipped piece of v2's reduction
calculus.  Together with V2-L2.10's `RawTermV2.subst0`, it establishes
the substrate that V2-L3.{1..7} build on (subject reduction,
confluence, strong normalization, decidable Conv).

## What V2-L3.1 wants

Subject Reduction (SR) for the v2 substrate per §11.6.1:

  Step t t' AND <certifier accepts t> => <certifier accepts t' with
                                            same sort>

For the full SR theorem we need:
1. A Step relation on RawTermV2 (this file's `Step`).
2. A certification-acceptance predicate (already provided by
   `inferRawCellGeneralV2?`).
3. A theorem proving the implication for every Step constructor.

Phase A + B ship steps 1 (with `beta` + uniform `cong`) + smokes.
Phase C will add iota / eta rules and prove the full SR theorem.

## The beta-reduction rule

The shipped beta constructor:

  Step (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons arg .childNil)))
       (RawTermV2.subst0 body arg)

Textbook lambda calculus beta rule, formulated over V2's un-indexed
raw substrate.

## The uniform congruence rule

The phase-B `cong` constructor:

  Step.cong (gen) (payload)
            (childStep : StepChildren children children')
    : Step (.mkGen gen payload children)
           (.mkGen gen payload children')

Reading: whenever a `StepChildren` chain witnesses reduction
somewhere inside a `RawTermChildrenV2` spine, the wrapped term
reduces under the SAME generator + payload, with the spine
substituted.  ONE rule, all generators.

The `StepChildren` mutual inductive expresses "Step at some position
in the spine":

  here  : Step head head' --> StepChildren (childCons head rest)
                                            (childCons head' rest)
  there : StepChildren rest rest' --> StepChildren (childCons head rest)
                                                    (childCons head rest')

Together: walk down the spine via `there` until you find the position
you want, then fire `here` with a Step at that position.

## Why mutual?

The cong rule recurses on a `StepChildren` argument whose `here`
constructor in turn recurses on a `Step`.  These two inductives
reference each other's constructors, so they MUST be in a `mutual`
block.

The mutual block requires both inductives to share the SAME
parameter telescope.  Since `StepChildren`'s scope varies across
constructors (child positions at `parentScope + headShift`), scope
cannot be a parameter on either inductive -- it must be an INDEX
on both.  Hence the `: {scope : Nat} → ...` form (implicit index).

The implicit-index syntax preserves the existing API shape: callers
write `Step first second` and Lean infers scope from `first`'s type
(verified in StepStarV2.lean -- which compiles unchanged).

## Why scope-indexed rather than scope-quantified

`Step : {scope : Nat} → RawTermV2 scope → RawTermV2 scope → Prop`
makes scope an implicit index of every Step instance.  Each Step
fixes one scope and the constructor's terms are at that scope.
Reduction across scopes is mediated by `Step` + `RawTermV2.rename`.

## What's NOT shipped yet

* iota rules (eliminator-on-constructor reductions): `natElim z s
  natZero ↝ z`, etc.  Phase C; one constructor per eliminator
  generator.
* eta rules: lambda eta-equality, pair eta-equality, etc.  Phase C;
  opt-in per generator.
* The full SR theorem: `Step t t' → certifier-accepts t →
  certifier-accepts t' (same sort)`.  Phase C.  Substantive
  metatheory cascade requiring structural induction over Step
  (mutually with StepChildren) + the certifier's recursive
  structure.
* `Step` over `RawCellV2` (cell-layer reduction).  Cell-layer is
  V2-L3.x phase later.

## Why phase B's uniform cong is the L3 leverage point

The whole PolyCell v2 thesis is "ONE generic operation covers all
194 generators uniformly".  Phase A's `beta` covers only the
beta-redex shape.  Phase B's `cong + StepChildren` is the FIRST
uniform L3 rule -- congruence under any generator's children spine,
without enumerating generators.

Every subsequent L3 theorem (SR, confluence, SN) gets to handle
"congruence under any ctor" as a single mutual-induction case
rather than 194 enumerated cases.  This is the L3 expression of
the L2 Allais-fold leverage.

## Zero-axiom verification

All 3 declarations (Step, StepChildren, Step.identity_lam_applied_to_unit,
Step.cong_lam_body_beta) pass `#assert_no_axioms`.  The mutual block
+ smokes are axiom-clean per the probe in Tools/_probe_cong.lean.
Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

mutual

/-- Single-step reduction relation on `RawTermV2`.

Phase A shipped `beta` only.  Phase B adds the uniform `cong` rule
that handles reduction under any generator's children spine, mutually
with `StepChildren`.

The relation is parameterized by `scope : Nat` (implicit index): each
Step instance fixes one scope and relates terms at that scope.
Reduction across scopes is mediated by `RawTermV2.rename`. -/
inductive Step : {scope : Nat} → RawTermV2 scope → RawTermV2 scope → Prop where
  /-- **Beta reduction.**  Applying a lambda to an argument contracts
      to `subst0 body arg`.

      Textbook lambda calculus beta rule, formulated over V2's
      un-indexed raw substrate. -/
  | beta {scope : Nat} {body : RawTermV2 (scope + 1)} {arg : RawTermV2 scope} :
      Step
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons arg .childNil)))
        (RawTermV2.subst0 body arg)
  /-- **Uniform congruence under any generator.**  When a
      `StepChildren` chain witnesses reduction somewhere inside the
      `RawTermChildrenV2` spine, the wrapped term reduces under the
      SAME generator + payload, with the spine replaced.

      ONE rule covers all 194 generators -- this is the L3 leverage
      point that v2's uniform substrate buys. -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
         {children children' : RawTermChildrenV2 gen.binderShifts scope}
         (childStep :
            StepChildren (binderShifts := gen.binderShifts) children children') :
      Step (.mkGen gen payload children) (.mkGen gen payload children')

/-- **Step at some position in a children spine.**

The mutual companion to `Step.cong`.  Expresses "the children spine
has a Step somewhere inside it" generically:

* `here`  -- the Step is at the head child position
* `there` -- the Step is somewhere in the tail

Walking down a spine via `there` and firing `here` at the right
position lets `Step.cong` congruence-reduce under ANY child of ANY
generator, uniformly across all 194 generators.

Indices: `parentScope` is the outer scope; `binderShifts` is the
list of per-position scope shifts (from `Generator.binderShifts`).
Both are implicit so call sites infer from the spine arguments. -/
inductive StepChildren :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildrenV2 binderShifts parentScope →
    RawTermChildrenV2 binderShifts parentScope → Prop where
  /-- **Reduction at the head child position.**  When the head
      `RawTermV2 (parentScope + headShift)` Step-reduces, the whole
      spine StepChildren-reduces with the tail unchanged. -/
  | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
         {head head' : RawTermV2 (parentScope + headShift)}
         (rest : RawTermChildrenV2 restShifts parentScope)
         (childStep : Step head head') :
      StepChildren
        (RawTermChildrenV2.childCons head rest)
        (RawTermChildrenV2.childCons head' rest)
  /-- **Reduction somewhere in the tail.**  When the tail spine
      StepChildren-reduces, the whole spine StepChildren-reduces
      with the head unchanged. -/
  | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
          (head : RawTermV2 (parentScope + headShift))
          {rest rest' : RawTermChildrenV2 restShifts parentScope}
          (restStep : StepChildren rest rest') :
      StepChildren
        (RawTermChildrenV2.childCons head rest)
        (RawTermChildrenV2.childCons head rest')

end

/-- **Smoke: identity-lambda applied to unit beta-reduces to unit.**

The simplest concrete beta-reduction instance.  The LHS is
`app (lam (var 0)) unit` -- the identity lambda applied to the
unit value.  The RHS is `unit`.

Closes by `apply Step.beta`: Lean's unifier discharges the
implicit equation `subst0 (var 0) unit = unit` via V2-L2.10's
`subst0_var_zero` (closes by `rfl` thanks to the `@[reducible]`
attribute on `singleton` + `subst0`).

This is the FIRST DOWNSTREAM CONSUMER of the V2-L2.10 subst0
infrastructure -- proof that the L2-L3 cascade was wired
correctly. -/
theorem Step.identity_lam_applied_to_unit :
    let identityLamBody : RawTermV2 1 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
    let unitArg : RawTermV2 0 :=
      .mkGen .gen_unit () .childNil
    let app : RawTermV2 0 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons identityLamBody .childNil))
          (.childCons unitArg .childNil))
    Step app unitArg := by
  apply Step.beta

/-- **Smoke: cong rule fires under `lam`.**

Witnesses Phase B's uniform `cong` rule on a concrete fixture.  The
LHS is `lam (app (lam (var 0)) unit)` -- a lambda whose body contains
a beta-redex.  The RHS is `lam unit` -- the same lambda with the
body reduced.

Closes by:
1. `apply Step.cong .gen_lam ()` -- fire the uniform cong rule
   under the `gen_lam` generator with unit payload.
2. The remaining goal is `StepChildren ... ...` over a one-element
   spine where the head is the beta-redex and the tail is empty.
3. `apply StepChildren.here .childNil` -- the Step happens at the
   head child position (the lambda's body).
4. The remaining goal is `Step (app (lam (var 0)) unit) unit` --
   which is exactly `Step.identity_lam_applied_to_unit`'s claim.
5. `apply Step.beta` discharges it.

This smoke witnesses BOTH the uniform cong rule and the typical
"walk into a binder, beta-reduce inside" reduction pattern -- the
core motion the L3 cascade will compose. -/
theorem Step.cong_lam_body_beta :
    let identityLamBody : RawTermV2 2 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2) .childNil
    let unitArg : RawTermV2 1 :=
      .mkGen .gen_unit () .childNil
    let innerApp : RawTermV2 1 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons identityLamBody .childNil))
          (.childCons unitArg .childNil))
    let outerLamBefore : RawTermV2 0 :=
      .mkGen .gen_lam () (.childCons innerApp .childNil)
    let outerLamAfter : RawTermV2 0 :=
      .mkGen .gen_lam () (.childCons unitArg .childNil)
    Step outerLamBefore outerLamAfter := by
  apply Step.cong .gen_lam ()
  apply StepChildren.here .childNil
  apply Step.beta

end LeanFX2.Foundation.PolyCell.Core
