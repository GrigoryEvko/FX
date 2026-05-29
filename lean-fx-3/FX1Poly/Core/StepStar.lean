import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/StepStar — reflexive-transitive closure of Step

V2-L3.2 phase A (2026-05-27).  Ships the reflexive-transitive
closure of the single-step reduction relation `Step` (V2-L3.1).
Foundational building block for:

* V2-L3.2 confluence (Church-Rosser theorem on StepStar)
* V2-L3.4 decidable Conv (★ MILESTONE A; Conv is the symmetric
  closure of StepStar)
* V2-L3.7 NbE quote (normalization terminates at a StepStar-
  reduct that's a normal form)

## What V2-L3.2 wants

Generic confluence per polycell.md §11.6.1:

  StepStar a b AND StepStar a c => exists d, StepStar b d AND StepStar c d

(the "diamond" property at the StepStar level, equivalent to
Church-Rosser).

Phase A ships the StepStar inductive itself.  Phase B will prove
basic closure properties (transitivity composition, congruence
under each Step constructor).  Phase C will prove the diamond /
Church-Rosser theorem via Tait-Martin-Löf parallel reduction.

## What this file ships

* `StepStar` inductive: reflexive-transitive closure of `Step` in
  the LEFT-EXTENSION form (`Step` then `StepStar`).

* `StepStar.refl_unit_smoke`: reflexivity instance on the unit
  term -- witnesses the `.refl` constructor's inhabitedness.

* `StepStar.identity_lam_beta_unit`: composition of `Step.beta`
  with `StepStar.refl` to reach `unit` from
  `(lam (var 0)) unit` via the closure -- witnesses the `.trans`
  constructor's inhabitedness and demonstrates the standard
  "single step ↝ StepStar reduct" pattern.

## The left-extension form

The inductive uses LEFT-EXTENSION:

  refl (term : RawTerm scope) : StepStar term term
  trans {first second third : RawTerm scope} :
      Step first second -> StepStar second third
      -> StepStar first third

Reading: a StepStar chain is either reflexive (length 0) or a
Step followed by a shorter StepStar chain.

Alternative would be RIGHT-EXTENSION (StepStar then Step at the
end).  Both forms are equivalent up to the eventual transitivity-
composition theorem (phase B).  Left-extension is canonical for
proofs by induction on the chain's length -- the inductive case
fires Step first, then recurses on the StepStar tail.

## Why this is the foundational L3 building block

Every L3 theorem that talks about "eventually reaches" or
"normal-form reduct" routes through StepStar:

* SR (V2-L3.1.C): "if Step preserves typing, so does StepStar"
  by induction on StepStar.
* Confluence (V2-L3.2): "any two StepStar reducts can be joined"
  is the Church-Rosser statement.
* SN (V2-L3.3): "every term has a StepStar normal form" is the
  termination claim.
* Conv (V2-L3.4): defined as the symmetric closure of StepStar.

This file is the substrate.  The downstream cascade consumes it
in many places.

## What's NOT shipped in phase A

* Basic closure properties:
    - StepStar.trans_compose : StepStar a b -> StepStar b c
                                -> StepStar a c
                              (the full transitivity).
    - StepStar.single : Step a b -> StepStar a b
                        (single-step embedding).
    - StepStar.transLast : StepStar a b -> Step b c
                            -> StepStar a c
                          (right-extension version).
  Phase B.  All provable by induction on the input.

* Congruence under Step's constructors: when StepStar a b under
  a ctor, the wrapped term StepStars accordingly.  Phase B / V2-L3.1
  phase B (Step congruence) provides this.

* The diamond / Church-Rosser theorem.  Phase C; substantial
  metatheory cascade.

## Zero-axiom verification

All 3 declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Reflexive-transitive closure of `Step`.

Left-extension form: a `StepStar` chain is either reflexive
(`.refl`, length 0) or a single `Step` followed by a shorter
`StepStar` chain (`.trans`).

The relation is parameterized by `scope : Nat`: each chain
relates terms at the same scope.  Cross-scope reduction is
mediated by `RawTerm.rename` (see V2-L2.13). -/
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

Composes `Step.beta` (the L3.1 phase A beta-reduction rule) with
`StepStar.refl` to produce a length-1 StepStar chain from
`(lam (var 0)) unit` to `unit`.

Witnesses both:
* That `.trans` is inhabited.
* That `Step.beta` lifts cleanly through StepStar via the
  standard "single-Step-then-refl" pattern.

This is the second downstream consumer of V2-L2.10's subst0
infrastructure (the first being `Step.identity_lam_applied_to_unit`
in V2-L3.1 phase A) -- now also witnessed at the closure level. -/
theorem StepStar.identity_lam_beta_unit :
    let identityLamBody : RawTerm 1 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
    let unitArg : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let app : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons identityLamBody .childNil))
          (.childCons unitArg .childNil))
    StepStar app unitArg :=
  StepStar.trans Step.beta (StepStar.refl _)

/-! ## V2-L3.2 phase B: closure properties of StepStar

Phase A shipped the inductive itself + two smokes.  Phase B
proves the basic closure properties that make StepStar a real
reflexive-transitive closure:

* `single`: every Step embeds as a length-1 StepStar.
* `trans_compose`: full transitivity (compose two chains).
* `transLast`: right-extension (append a final Step).

The L3 cascade consumes these closure properties:

* Subject reduction (V2-L3.1.C) uses `single` + `trans_compose`
  when chaining SR-per-step into SR-on-chains.
* Confluence (V2-L3.2 phase C) uses `trans_compose` when composing
  the two diverging chains' joining segments.
* Conv (V2-L3.4) inherits transitivity directly via
  `trans_compose`. -/

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

The phase-A inductive uses LEFT-EXTENSION (`refl` + `trans` with
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

The phase-A inductive's `.trans` constructor is left-extension
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

/-- Replay a `StepStar` chain in the body child of a lambda. -/
theorem StepStar.lamBody {scope : Nat}
    {bodyTerm updatedBodyTerm : RawTerm (scope + 1)}
    (bodyChain : StepStar bodyTerm updatedBodyTerm) :
    StepStar
      (.mkGen .gen_lam () (.childCons bodyTerm .childNil) :
        RawTerm scope)
      (.mkGen .gen_lam () (.childCons updatedBodyTerm .childNil) :
        RawTerm scope) := by
  induction bodyChain with
  | refl _ =>
      exact StepStar.refl _
  | trans headStep _ tailIH =>
      exact
        StepStar.trans
          (Step.cong .gen_lam ()
            (StepChildren.here
              (parentScope := scope) (headShift := 1) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              headStep))
          tailIH

end FX1Poly.Core
