import LeanFX2.Foundation.PolyCell.Core.RawTermV2Subst0

/-! # Foundation/PolyCell/Core/StepV2 — single-step reduction on V2 (Phase A)

V2-L3.1 phase A (2026-05-27).  Discharges the first L3 metatheory
task per polycell.md §11.6.1.  Ships the `Step` inductive relation
+ the beta-reduction constructor + one smoke witnessing beta on
the identity-lambda fixture.

This file is the L3 KICKOFF: the FIRST shipped piece of v2's
reduction calculus.  Together with V2-L2.10's `RawTermV2.subst0`,
it establishes the substrate that V2-L3.{1..7} build on (subject
reduction, confluence, strong normalization, decidable Conv).

## What V2-L3.1 wants

Subject Reduction (SR) for the v2 substrate per §11.6.1:

  Step t t' AND <certifier accepts t> => <certifier accepts t' with
                                            same sort>

For the full SR theorem we need:
1. A Step relation on RawTermV2 (this file's `Step`).
2. A certification-acceptance predicate (already provided by
   `inferRawCellGeneralV2?`).
3. A theorem proving the implication for every Step constructor.

Phase A ships only step 1 (with one constructor) + a smoke.  Phase
B will extend Step with congruence rules; phase C will prove the
full SR theorem.

## What this file ships

* `Step` inductive over `RawTermV2 scope`: single-step reduction
  relation parameterized by scope.

* `Step.beta` constructor: the canonical beta-reduction rule.
  Applying a lambda to an argument reduces to `subst0 body arg`.

* `Step.identity_lam_applied_to_unit` smoke: the simplest concrete
  beta-reduction instance.  Witnesses that `Step.beta` is
  inhabited on a concrete fixture pair.

## The beta-reduction rule (with full ctor structure)

The shipped constructor:

  Step (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons arg .childNil)))
       (RawTermV2.subst0 body arg)

Reading: the redex is `app (lam body) arg` (in raw form), and
the contractum is `subst0 body arg` — substituting the argument
for the bound variable in the lambda's body.

This is the textbook beta rule of the lambda calculus,
formulated over the V2 raw substrate's un-indexed `RawTermV2`.

## Why the smoke closes by `Step.beta`

The smoke proves `Step (app (λx.x) unit) unit`.  The LHS reduces
to `subst0 (var 0) unit` by `Step.beta`.  By V2-L2.10's
`RawTermV2.subst0_var_zero` (which closes by `rfl` thanks to the
`@[reducible]` attribute on `singleton` + `subst0`):

  subst0 (var 0) unit = unit

So `Step.beta` produces `Step (app (λx.x) unit) (subst0 (var 0) unit)`,
which equals `Step (app (λx.x) unit) unit` definitionally.  Lean's
unifier handles the equation; `apply Step.beta` succeeds.

This is the FIRST DOWNSTREAM CONSUMER of V2-L2.10's subst0
infrastructure -- proof that the L2-L3 cascade was wired
correctly.

## What's NOT shipped in phase A

* Congruence rules (`Step` under each ctor's children): when
  `Step body body'`, then `Step (lam body) (lam body')`, etc.
  Phase B; deferred to a follow-up file.

* iota rules (eliminator-on-constructor reductions): `natElim z s
  (natZero) ↝ z`, etc.  Phase B; one constructor per eliminator
  generator.

* eta rules: lambda eta-equality, pair eta-equality, etc.  Phase
  B; opt-in per generator.

* Reflexive-transitive closure (`Step.star` or `Conv`): the
  closure of Step under repeated reduction.  Phase C / V2-L3.2.

* The full SR theorem: `Step t t' → certifier-accepts t →
  certifier-accepts t' (same sort)`.  Phase C / V2-L3.1.B.
  Substantive metatheory cascade requiring structural induction
  over Step + the certifier's recursive structure.

* `Step` over `RawCellV2` (cell-layer reduction): currently
  `Step` operates at the term layer only.  Cell-layer reduction
  (rewrite rules on certified cells) is V2-L3.x phase later.

## Why scope-parameterized rather than scope-quantified

`Step {scope : Nat}` makes scope an implicit parameter of every
Step constructor.  This means each Step instance fixes one scope
and the constructor's terms are at that scope.  Reduction
between terms at different scopes (e.g., post-renaming) is not a
single Step; it's mediated by `Step` + `RawTermV2.rename`.

Alternative would be `Step : ∀ {scope}, RawTermV2 scope →
RawTermV2 scope → Prop` (explicit scope quantification), but
the parameterised form is cleaner for the inductive's
constructors and matches the discipline of v1's analogous
`Step` definitions.

## Forward-compat: when phase B / C land

Phase B (congruence + iota rules): adds more constructors to
`Step`, each closing by structural pattern-match.  No additional
files needed; this file is extended in place.

Phase C (SR theorem): a separate `StepV2SubjectReduction.lean`
file that depends on this one + `CertifyRawCellExactV2.lean`.
Proof by induction on `Step` + the certifier's dispatch.

V2-L3.2 (confluence) will define `Step.parallel` (parallel reduction
for Tait-Martin-Löf), prove the diamond property, derive
Church-Rosser.  V2-L3.3 (SN) uses Tait reducibility candidates.
All build on this file's `Step` as the substrate.

## Zero-axiom verification

All 2 declarations pass `#assert_no_axioms`.  The inductive is a
simple binary Prop relation; the smoke closes by `apply Step.beta`
+ definitional reduction of `subst0_var_zero`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Single-step reduction relation on `RawTermV2`.

Phase A: ships ONLY the beta-reduction constructor.  Phase B will
extend with congruence rules (Step under each ctor's children) and
iota / eta rules per V2-L3.x.

The relation is parameterized by `scope : Nat`: each Step instance
fixes one scope and relates terms at that scope.  Reduction across
scopes is mediated by `RawTermV2.rename`. -/
inductive Step {scope : Nat} : RawTermV2 scope → RawTermV2 scope → Prop where
  /-- **Beta reduction.**  Applying a lambda to an argument
      contracts to `subst0 body arg`.

      Textbook lambda calculus beta rule, formulated over V2's
      un-indexed raw substrate. -/
  | beta {body : RawTermV2 (scope + 1)} {arg : RawTermV2 scope} :
      Step
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons arg .childNil)))
        (RawTermV2.subst0 body arg)

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

end LeanFX2.Foundation.PolyCell.Core
