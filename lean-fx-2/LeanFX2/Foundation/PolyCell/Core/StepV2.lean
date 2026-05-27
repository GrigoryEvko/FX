import LeanFX2.Foundation.PolyCell.Core.RawTermV2Subst0

/-! # Foundation/PolyCell/Core/StepV2 — single-step reduction on V2

V2-L3.1 phase A + B + C-steps 1/2/3/4a (2026-05-27).  Discharges
the first L3 metatheory task per polycell.md §11.6.1.  Ships the
`Step` inductive relation with: beta-reduction (phase A), uniform
congruence (phase B), branch-selection iota for boolElim
(C-step1), content-projection iota for fst/snd on pair (C-step2),
base-case projection iota for nat/list/option base ctors
(C-step3), and 1-arg app-chain iota for optionSome/eitherInl/
eitherInr step ctors (C-step4a).  Thirteen smokes total.

Three iota SHAPES now fully demonstrated across the standard
inductive types:
  * branch-selection (base ctors -- bool/nat/list/option)
  * content-projection (pair fst/snd)
  * 1-arg app-chain build (optionSome/eitherInl/eitherInr)

C-step4b will add 2-arg app-chain (natSucc); C-step4c will add
3-arg app-chain (listCons).  C-step5 handles idJ + opt-in eta.
C-step6 ships the SR theorem.

## Phase A vs Phase B vs Phase C

* **Phase A** shipped just `Step.beta` -- the beta-reduction
  constructor + one smoke witnessing the identity-lambda fixture.
* **Phase B** shipped the UNIFORM congruence rule `Step.cong` via a
  mutual `Step + StepChildren` block.  ONE rule covers all 194
  generators because StepChildren expresses "Step at some child
  position" generically using `binderShifts` and the generic
  `RawTermChildrenV2` substrate.
* **Phase C step 1** ships branch-selection iota for boolElim:
  `Step.iotaBoolTrue` / `Step.iotaBoolFalse`.  Bool's two-ctor
  scheme + zero binders means iota is pure tag-selection at the
  same scope.
* **Phase C step 2** ships content-projection iota for `fst`/`snd`
  on `pair`: `Step.iotaFstPair` / `Step.iotaSndPair`.  Same scope
  discipline as bool iotas, but a DIFFERENT iota shape -- the
  eliminator unwraps a constructor and returns one of its
  components rather than selecting one of several branches.
* **Phase C step 3** extends branch-selection iota to the
  remaining standard 3-branch eliminators on their BASE (0-arity)
  constructors: `Step.iotaNatElimZero`, `Step.iotaNatRecZero`,
  `Step.iotaListElimNil`, `Step.iotaOptionMatchNone`.  Same shape
  as `iotaBoolTrue` -- base-case ctor's iota is pure projection.
* **Phase C step 4a** (THIS update) introduces the THIRD iota
  SHAPE: 1-arg app-chain build.  `Step.iotaOptionMatchSome`,
  `Step.iotaEitherMatchInl`, `Step.iotaEitherMatchInr`.  Same
  scope discipline, but the reduct is `app branch wrappedValue`
  rather than just `branch`.  No direct substitution at iota --
  beta handles the binding work in a SUBSEQUENT reduction.  This
  decomposition is the Church-encoding payoff: iota recognizes
  the constructor tag, beta does the variable binding.
* **Future phase C** (deferred): 2-arg and 3-arg app-chain iotas
  (natSucc / listCons), iotas with binders (idJ on refl), opt-in
  eta rules, and the SR theorem.

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
  /-- **Iota for boolElim on boolTrue.**  Eliminating on `boolTrue`
      selects the then-branch.  No substitution involved -- pure tag-
      selection at the same scope (`binderShifts [0, 0, 0]`).

      Phase C kickoff: the SIMPLEST iota rule on the v2 substrate.
      Bool's two-constructor scheme + zero binders makes this the
      textbook minimal iota.  More complex iota (natRec on natSucc,
      listElim on listCons) follow the same pattern: pattern-match the
      scrutinee's constructor in the children spine, then return the
      branch term (Church-encoded, no direct subst). -/
  | iotaBoolTrue {scope : Nat}
                 {thenBranch elseBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_boolElim ()
          (.childCons
            (.mkGen .gen_boolTrue () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil))))
        thenBranch
  /-- **Iota for boolElim on boolFalse.**  Eliminating on `boolFalse`
      selects the else-branch.  Symmetric to `iotaBoolTrue`. -/
  | iotaBoolFalse {scope : Nat}
                  {thenBranch elseBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_boolElim ()
          (.childCons
            (.mkGen .gen_boolFalse () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil))))
        elseBranch
  /-- **Iota for fst on pair.**  Projecting the first component of an
      explicitly-constructed pair returns the first value.

      The CONTENT-PROJECTION iota shape (vs. boolElim's BRANCH-
      SELECTION shape).  Same scope discipline: `binderShifts [0]`
      for `gen_fst` and `[0, 0]` for `gen_pair` means everything
      lives at the ambient `scope`.  No substitution involved -- the
      reduction simply unwraps the pair and discards the second
      component. -/
  | iotaFstPair {scope : Nat}
                {firstValue secondValue : RawTermV2 scope} :
      Step
        (.mkGen .gen_fst ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)))
            .childNil))
        firstValue
  /-- **Iota for snd on pair.**  Projecting the second component of
      an explicitly-constructed pair returns the second value.
      Symmetric to `iotaFstPair`. -/
  | iotaSndPair {scope : Nat}
                {firstValue secondValue : RawTermV2 scope} :
      Step
        (.mkGen .gen_snd ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)))
            .childNil))
        secondValue
  /-- **Iota for natElim on natZero (base case).**  Eliminating on
      `natZero` selects the zero-branch.  Same branch-selection
      shape as `iotaBoolTrue` -- the 0-arity constructor's iota is
      always pure projection.  binderShifts `[0, 0, 0]` for
      `gen_natElim`. -/
  | iotaNatElimZero {scope : Nat}
                    {zeroBranch succBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_natElim ()
          (.childCons
            (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil))))
        zeroBranch
  /-- **Iota for natRec on natZero (base case).**  Symmetric to
      `iotaNatElimZero`; the v2 substrate treats `gen_natElim` and
      `gen_natRec` with identical arity and binderShifts, so their
      base-case iotas are structurally identical. -/
  | iotaNatRecZero {scope : Nat}
                   {zeroBranch succBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_natRec ()
          (.childCons
            (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil))))
        zeroBranch
  /-- **Iota for listElim on listNil (base case).**  Eliminating on
      `listNil` selects the nil-branch.  Same branch-selection shape
      as `iotaBoolTrue` / `iotaNatElimZero`; pure projection. -/
  | iotaListElimNil {scope : Nat}
                    {nilBranch consBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_listElim ()
          (.childCons
            (.mkGen .gen_listNil () .childNil)
            (.childCons nilBranch (.childCons consBranch .childNil))))
        nilBranch
  /-- **Iota for optionMatch on optionNone (base case).**  Matching
      on `optionNone` selects the none-branch.  Same branch-selection
      shape; pure projection. -/
  | iotaOptionMatchNone {scope : Nat}
                        {noneBranch someBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_optionMatch ()
          (.childCons
            (.mkGen .gen_optionNone () .childNil)
            (.childCons noneBranch (.childCons someBranch .childNil))))
        noneBranch
  /-- **Iota for optionMatch on optionSome (step case, 1-arg app-chain).**

      Matching on `optionSome value` applies the some-branch to the
      wrapped value: `optionMatch (optionSome v) n s ↝ app s v`.
      The THIRD iota shape: build an `app` term rather than
      projecting.  No direct substitution -- beta handles the
      binding work in a subsequent reduction step, separating
      iota's "tag-recognition" duty from beta's "argument-binding"
      duty. -/
  | iotaOptionMatchSome {scope : Nat}
                        {value : RawTermV2 scope}
                        {noneBranch someBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_optionMatch ()
          (.childCons
            (.mkGen .gen_optionSome () (.childCons value .childNil))
            (.childCons noneBranch (.childCons someBranch .childNil))))
        (.mkGen .gen_app ()
          (.childCons someBranch (.childCons value .childNil)))
  /-- **Iota for eitherMatch on eitherInl (step case, 1-arg
      app-chain).**

      Matching on `eitherInl value` applies the left-branch to the
      wrapped value: `eitherMatch (inl v) l r ↝ app l v`.  Same
      1-arg app-chain shape as `iotaOptionMatchSome`. -/
  | iotaEitherMatchInl {scope : Nat}
                       {value : RawTermV2 scope}
                       {leftBranch rightBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_eitherMatch ()
          (.childCons
            (.mkGen .gen_eitherInl () (.childCons value .childNil))
            (.childCons leftBranch (.childCons rightBranch .childNil))))
        (.mkGen .gen_app ()
          (.childCons leftBranch (.childCons value .childNil)))
  /-- **Iota for eitherMatch on eitherInr (step case, 1-arg
      app-chain).**

      Symmetric to `iotaEitherMatchInl`: matching on `eitherInr
      value` applies the right-branch to the wrapped value. -/
  | iotaEitherMatchInr {scope : Nat}
                       {value : RawTermV2 scope}
                       {leftBranch rightBranch : RawTermV2 scope} :
      Step
        (.mkGen .gen_eitherMatch ()
          (.childCons
            (.mkGen .gen_eitherInr () (.childCons value .childNil))
            (.childCons leftBranch (.childCons rightBranch .childNil))))
        (.mkGen .gen_app ()
          (.childCons rightBranch (.childCons value .childNil)))

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

/-- **Phase C smoke: iotaBoolTrue selects the then-branch.**

Distinct then/else branches verify that the right one is selected:

  `boolElim boolTrue boolTrue boolFalse  ↝  boolTrue`

(The scrutinee `boolTrue` selects the then-branch, which is itself
`boolTrue` -- the result is `boolTrue`, distinct from the
discarded else-branch `boolFalse`.)

Closes by `apply Step.iotaBoolTrue`. -/
theorem Step.iotaBoolTrue_selects_then :
    let trueScrutinee : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let thenBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let elseBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTermV2 0 :=
      .mkGen .gen_boolElim ()
        (.childCons
          trueScrutinee
          (.childCons thenBranch (.childCons elseBranch .childNil)))
    Step elimTerm thenBranch := by
  apply Step.iotaBoolTrue

/-- **Phase C smoke: iotaBoolFalse selects the else-branch.**

Symmetric to `iotaBoolTrue_selects_then`.  Distinct branches verify
the right selection:

  `boolElim boolFalse boolTrue boolFalse  ↝  boolFalse`

(The scrutinee `boolFalse` selects the else-branch, which is itself
`boolFalse` -- the result is `boolFalse`, distinct from the
discarded then-branch `boolTrue`.)

Closes by `apply Step.iotaBoolFalse`. -/
theorem Step.iotaBoolFalse_selects_else :
    let falseScrutinee : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let thenBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let elseBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTermV2 0 :=
      .mkGen .gen_boolElim ()
        (.childCons
          falseScrutinee
          (.childCons thenBranch (.childCons elseBranch .childNil)))
    Step elimTerm elseBranch := by
  apply Step.iotaBoolFalse

/-- **Phase C smoke: iotaFstPair projects the first component.**

Distinct first/second components verify the RIGHT component is
projected:

  `fst (pair boolTrue boolFalse)  ↝  boolTrue`

(The first component is `boolTrue`, the second is `boolFalse`; the
result is `boolTrue`, distinct from the discarded `boolFalse`.)

Closes by `apply Step.iotaFstPair`. -/
theorem Step.iotaFstPair_projects_first :
    let firstValue : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let secondValue : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let pairTerm : RawTermV2 0 :=
      .mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil))
    let fstTerm : RawTermV2 0 :=
      .mkGen .gen_fst () (.childCons pairTerm .childNil)
    Step fstTerm firstValue := by
  apply Step.iotaFstPair

/-- **Phase C smoke: iotaSndPair projects the second component.**

Symmetric to `iotaFstPair_projects_first`.  Distinct components
verify the right projection:

  `snd (pair boolTrue boolFalse)  ↝  boolFalse`

(The first component is `boolTrue`, the second is `boolFalse`; the
result is `boolFalse`, distinct from the discarded `boolTrue`.)

Closes by `apply Step.iotaSndPair`. -/
theorem Step.iotaSndPair_projects_second :
    let firstValue : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let secondValue : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let pairTerm : RawTermV2 0 :=
      .mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil))
    let sndTerm : RawTermV2 0 :=
      .mkGen .gen_snd () (.childCons pairTerm .childNil)
    Step sndTerm secondValue := by
  apply Step.iotaSndPair

/-- **Phase C smoke: iotaNatElimZero selects the zero-branch.**

  `natElim natZero boolTrue boolFalse  ↝  boolTrue`

Distinct zero/succ branches verify the RIGHT one is selected.
(The zero-branch `boolTrue` is selected; the succ-branch
`boolFalse` is discarded.)

Closes by `apply Step.iotaNatElimZero`. -/
theorem Step.iotaNatElimZero_selects_zero :
    let zeroScrutinee : RawTermV2 0 :=
      .mkGen .gen_natZero () .childNil
    let zeroBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let succBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTermV2 0 :=
      .mkGen .gen_natElim ()
        (.childCons
          zeroScrutinee
          (.childCons zeroBranch (.childCons succBranch .childNil)))
    Step elimTerm zeroBranch := by
  apply Step.iotaNatElimZero

/-- **Phase C smoke: iotaNatRecZero selects the zero-branch.**

Symmetric to `iotaNatElimZero_selects_zero` -- same shape on
`gen_natRec` instead of `gen_natElim`. -/
theorem Step.iotaNatRecZero_selects_zero :
    let zeroScrutinee : RawTermV2 0 :=
      .mkGen .gen_natZero () .childNil
    let zeroBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let succBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let recTerm : RawTermV2 0 :=
      .mkGen .gen_natRec ()
        (.childCons
          zeroScrutinee
          (.childCons zeroBranch (.childCons succBranch .childNil)))
    Step recTerm zeroBranch := by
  apply Step.iotaNatRecZero

/-- **Phase C smoke: iotaListElimNil selects the nil-branch.**

  `listElim listNil boolTrue boolFalse  ↝  boolTrue`

Distinct nil/cons branches verify the RIGHT one is selected. -/
theorem Step.iotaListElimNil_selects_nil :
    let nilScrutinee : RawTermV2 0 :=
      .mkGen .gen_listNil () .childNil
    let nilBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let consBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTermV2 0 :=
      .mkGen .gen_listElim ()
        (.childCons
          nilScrutinee
          (.childCons nilBranch (.childCons consBranch .childNil)))
    Step elimTerm nilBranch := by
  apply Step.iotaListElimNil

/-- **Phase C smoke: iotaOptionMatchNone selects the none-branch.**

  `optionMatch optionNone boolTrue boolFalse  ↝  boolTrue`

Distinct none/some branches verify the RIGHT one is selected. -/
theorem Step.iotaOptionMatchNone_selects_none :
    let noneScrutinee : RawTermV2 0 :=
      .mkGen .gen_optionNone () .childNil
    let noneBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let someBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTermV2 0 :=
      .mkGen .gen_optionMatch ()
        (.childCons
          noneScrutinee
          (.childCons noneBranch (.childCons someBranch .childNil)))
    Step matchTerm noneBranch := by
  apply Step.iotaOptionMatchNone

/-- **Phase C smoke: iotaOptionMatchSome builds app chain.**

  `optionMatch (optionSome unit) boolTrue boolFalse
     ↝  app boolFalse unit`

The result is the `app` term (not just `boolFalse`); the wrapped
value is preserved as the application's argument. -/
theorem Step.iotaOptionMatchSome_builds_app :
    let unitVal : RawTermV2 0 :=
      .mkGen .gen_unit () .childNil
    let someScrutinee : RawTermV2 0 :=
      .mkGen .gen_optionSome () (.childCons unitVal .childNil)
    let noneBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let someBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTermV2 0 :=
      .mkGen .gen_optionMatch ()
        (.childCons
          someScrutinee
          (.childCons noneBranch (.childCons someBranch .childNil)))
    let appResult : RawTermV2 0 :=
      .mkGen .gen_app ()
        (.childCons someBranch (.childCons unitVal .childNil))
    Step matchTerm appResult := by
  apply Step.iotaOptionMatchSome

/-- **Phase C smoke: iotaEitherMatchInl builds app chain.**

  `eitherMatch (eitherInl unit) boolTrue boolFalse
     ↝  app boolTrue unit`

Distinct left/right branches verify the RIGHT branch is applied.
The wrapped value is preserved as the application's argument. -/
theorem Step.iotaEitherMatchInl_builds_app :
    let unitVal : RawTermV2 0 :=
      .mkGen .gen_unit () .childNil
    let inlScrutinee : RawTermV2 0 :=
      .mkGen .gen_eitherInl () (.childCons unitVal .childNil)
    let leftBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let rightBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTermV2 0 :=
      .mkGen .gen_eitherMatch ()
        (.childCons
          inlScrutinee
          (.childCons leftBranch (.childCons rightBranch .childNil)))
    let appResult : RawTermV2 0 :=
      .mkGen .gen_app ()
        (.childCons leftBranch (.childCons unitVal .childNil))
    Step matchTerm appResult := by
  apply Step.iotaEitherMatchInl

/-- **Phase C smoke: iotaEitherMatchInr builds app chain.**

  `eitherMatch (eitherInr unit) boolTrue boolFalse
     ↝  app boolFalse unit`

Symmetric to `iotaEitherMatchInl_builds_app`. -/
theorem Step.iotaEitherMatchInr_builds_app :
    let unitVal : RawTermV2 0 :=
      .mkGen .gen_unit () .childNil
    let inrScrutinee : RawTermV2 0 :=
      .mkGen .gen_eitherInr () (.childCons unitVal .childNil)
    let leftBranch : RawTermV2 0 :=
      .mkGen .gen_boolTrue () .childNil
    let rightBranch : RawTermV2 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTermV2 0 :=
      .mkGen .gen_eitherMatch ()
        (.childCons
          inrScrutinee
          (.childCons leftBranch (.childCons rightBranch .childNil)))
    let appResult : RawTermV2 0 :=
      .mkGen .gen_app ()
        (.childCons rightBranch (.childCons unitVal .childNil))
    Step matchTerm appResult := by
  apply Step.iotaEitherMatchInr

end LeanFX2.Foundation.PolyCell.Core
