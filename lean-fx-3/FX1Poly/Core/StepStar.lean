import FX1Poly.Core.Step
import FX1Poly.Core.HeadStep

/-! # Foundation/PolyCell/Core/StepStar — reflexive-transitive closure of Step

The reflexive-transitive closure of the single-step reduction relation
`Step`.  Foundational building block for:

* confluence (Church-Rosser theorem on StepStar)
* decidable Conv (Conv is the symmetric closure of StepStar)
* NbE quote (normalization terminates at a StepStar-reduct that's a
  normal form)

The generic confluence statement per polycell.md §11.6.1:

  StepStar a b AND StepStar a c => exists d, StepStar b d AND StepStar c d

(the "diamond" property at the StepStar level, equivalent to
Church-Rosser).

## What this file provides

* `StepStar` inductive: reflexive-transitive closure of `Step` in
  the LEFT-EXTENSION form (`Step` then `StepStar`).

* The closure properties `single`, `trans_compose`, `transLast`.

* Smoke fixtures `refl_unit_smoke` and `identity_lam_beta_unit`
  witnessing the `.refl` / `.trans` constructors' inhabitedness and
  the standard "single step ↝ StepStar reduct" pattern.

## The left-extension form

The inductive uses LEFT-EXTENSION:

  refl (term : RawTerm scope) : StepStar term term
  trans {first second third : RawTerm scope} :
      Step first second -> StepStar second third
      -> StepStar first third

Reading: a StepStar chain is either reflexive (length 0) or a
Step followed by a shorter StepStar chain.

Alternative would be RIGHT-EXTENSION (StepStar then Step at the
end).  Both forms are equivalent up to the transitivity-composition
theorem.  Left-extension is canonical for proofs by induction on the
chain's length -- the inductive case fires Step first, then recurses
on the StepStar tail.

## Why this is the foundational L3 building block

Every L3 theorem that talks about "eventually reaches" or
"normal-form reduct" routes through StepStar:

* SR: "if Step preserves typing, so does StepStar" by induction on
  StepStar.
* Confluence: "any two StepStar reducts can be joined" is the
  Church-Rosser statement.
* SN: "every term has a StepStar normal form" is the termination
  claim.
* Conv: defined as the symmetric closure of StepStar.

This file is the substrate.  The downstream cascade consumes it
in many places.

## Scope of this file

The diamond / Church-Rosser theorem itself is proved in the confluence
files, not here.  This file is the inductive plus its closure
properties.

## Zero-axiom verification

Every declaration passes `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Reflexive-transitive closure of `Step`.

Left-extension form: a `StepStar` chain is either reflexive
(`.refl`, length 0) or a single `Step` followed by a shorter
`StepStar` chain (`.trans`).

The relation is parameterized by `scope : Nat`: each chain
relates terms at the same scope.  Cross-scope reduction is
mediated by `RawTerm.rename`. -/
inductive StepStar {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  /-- **Reflexivity.**  Every term StepStar-reduces to itself
      in zero steps. -/
  | refl (term : RawTerm scope) : StepStar term term
  /-- **Left-extension.**  Compose a single Step at the head of
      a StepStar chain to extend the chain by one step. -/
  | trans {first second third : RawTerm scope} :
      Step first second → StepStar second third →
      StepStar first third

/-- **Smoke: reflexivity on the unit term.**

Witnesses that the `.refl` constructor is inhabited on a concrete
fixture.  Trivial by `StepStar.refl _`. -/
theorem StepStar.refl_unit_smoke :
    StepStar (.mkGen .gen_unit () .childNil : RawTerm 0)
             (.mkGen .gen_unit () .childNil : RawTerm 0) :=
  StepStar.refl _

/-- **Smoke: identity-lambda beta-reduces to unit via StepStar.**

Composes `Step.beta` with `StepStar.refl` to produce a length-1
StepStar chain from `(lam (var 0)) unit` to `unit`.

Witnesses both:
* That `.trans` is inhabited.
* That `Step.beta` lifts cleanly through StepStar via the
  standard "single-Step-then-refl" pattern. -/
theorem StepStar.identity_lam_beta_unit :
    let identityLamBody : RawTerm 1 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
    let domainAnn : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let unitArg : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let app : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons identityLamBody .childNil)))
          (.childCons unitArg .childNil))
    StepStar app unitArg :=
  StepStar.trans HeadStep.beta.toStep (StepStar.refl _)

/-! ## Closure properties of StepStar

The closure properties that make StepStar a real reflexive-transitive
closure:

* `single`: every Step embeds as a length-1 StepStar.
* `trans_compose`: full transitivity (compose two chains).
* `transLast`: right-extension (append a final Step).

The L3 cascade consumes these:

* Subject reduction uses `single` + `trans_compose` when chaining
  SR-per-step into SR-on-chains.
* Confluence uses `trans_compose` when composing the two diverging
  chains' joining segments.
* Conv inherits transitivity directly via `trans_compose`. -/

/-- **Single-Step embedding.**  Every `Step a b` lifts to
`StepStar a b` as a length-1 chain.

This is the canonical way to "promote" a single reduction to a
reflexive-transitive chain.  Used wherever a theorem about
StepStar must apply to a one-step reduction.

Construction: `Step.beta` followed by `StepStar.refl` -- the
shortest possible non-trivial chain. -/
theorem StepStar.single {scope : Nat} {first second : RawTerm scope}
    (someStep : Step first second) : StepStar first second :=
  StepStar.trans someStep (StepStar.refl _)

/-- **Full transitivity.**  Compose two StepStar chains
end-to-end.

The `StepStar` inductive uses LEFT-EXTENSION (`refl` + `trans` with
Step at the head), which gives reflexivity and one-step extension
for free.  Full transitivity requires induction on the FIRST
chain: peel off the head step, recurse on the tail composed with
the second chain, re-prepend the head step.

This is the load-bearing closure property: every "chain-then-
chain" composition routes through here.  Conv inherits its
transitivity from this theorem.

Proof structure:
* `.refl` case: the first chain is empty (length 0), so `first =
  second`; return the second chain unchanged.
* `.trans` case: peel off the head Step, compose the tail with
  the second chain by induction, re-prepend the head Step. -/
theorem StepStar.trans_compose {scope : Nat}
    {first second third : RawTerm scope}
    (firstChain : StepStar first second)
    (secondChain : StepStar second third) :
    StepStar first third := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans headStep _ restCompose =>
      exact StepStar.trans headStep (restCompose secondChain)

/-- **Right-extension (transLast).**  Append a single Step at the
end of a StepStar chain.

The `StepStar` inductive's `.trans` constructor is left-extension
(Step at the head).  This theorem is the symmetric right-
extension form: given a chain `a -> ... -> b` and a single step
`b -> c`, produce the extended chain `a -> ... -> b -> c`.

Derived from `trans_compose` + `single`: lift the final Step to
a length-1 chain, then compose. -/
theorem StepStar.transLast {scope : Nat}
    {first second third : RawTerm scope}
    (chain : StepStar first second) (lastStep : Step second third) :
    StepStar first third :=
  StepStar.trans_compose chain (StepStar.single lastStep)

/-- Replay a `StepStar` chain in the function child of an application. -/
theorem StepStar.appFunction {scope : Nat}
    {functionTerm updatedFunctionTerm argumentTerm : RawTerm scope}
    (functionChain : StepStar functionTerm updatedFunctionTerm) :
    StepStar
      (.mkGen .gen_app ()
        (.childCons functionTerm (.childCons argumentTerm .childNil)))
      (.mkGen .gen_app ()
        (.childCons updatedFunctionTerm
          (.childCons argumentTerm .childNil))) := by
  induction functionChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact
        StepStar.trans
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons argumentTerm .childNil) :
                RawTermChildren [0] scope)
              headStep))
          tailIH

/-- Replay a `StepStar` chain in the argument child of an application. -/
theorem StepStar.appArgument {scope : Nat}
    (functionTerm : RawTerm scope)
    {argumentTerm updatedArgumentTerm : RawTerm scope}
    (argumentChain : StepStar argumentTerm updatedArgumentTerm) :
    StepStar
      (.mkGen .gen_app ()
        (.childCons functionTerm (.childCons argumentTerm .childNil)))
      (.mkGen .gen_app ()
        (.childCons functionTerm
          (.childCons updatedArgumentTerm .childNil))) := by
  induction argumentChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact
        StepStar.trans
          (Step.cong .gen_app ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              functionTerm
              (StepChildren.here
                (parentScope := scope) (headShift := 0)
                (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                headStep)))
          tailIH

/-- Replay a `StepStar` chain in the body child of a lambda.

Church-style: the lambda carries a domain annotation as its first
(shift-`0`) child; this lemma keeps the annotation fixed and replays
the chain in the body (the second, shift-`1` child).  Each `cong`
step walks past the domain via `there` before firing `here` at the
body. -/
theorem StepStar.lamBody {scope : Nat}
    (domainAnn : RawTerm scope)
    {bodyTerm updatedBodyTerm : RawTerm (scope + 1)}
    (bodyChain : StepStar bodyTerm updatedBodyTerm) :
    StepStar
      (.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons bodyTerm .childNil)) :
        RawTerm scope)
      (.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons updatedBodyTerm .childNil)) :
        RawTerm scope) := by
  induction bodyChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact
        StepStar.trans
          (Step.cong .gen_lam ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [1])
              domainAnn
              (StepChildren.here
                (parentScope := scope) (headShift := 1) (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                headStep)))
          tailIH

end FX1Poly.Core
