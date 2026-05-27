import LeanFX2.Foundation.PolyCell.Core.StepV2

/-! # Foundation/PolyCell/Core/StepStarV2 — reflexive-transitive closure of Step

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

  refl (term : RawTermV2 scope) : StepStar term term
  trans {first second third : RawTermV2 scope} :
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

namespace LeanFX2.Foundation.PolyCell.Core

/-- Reflexive-transitive closure of `Step`.

Left-extension form: a `StepStar` chain is either reflexive
(`.refl`, length 0) or a single `Step` followed by a shorter
`StepStar` chain (`.trans`).

The relation is parameterized by `scope : Nat`: each chain
relates terms at the same scope.  Cross-scope reduction is
mediated by `RawTermV2.rename` (see V2-L2.13). -/
inductive StepStar {scope : Nat} : RawTermV2 scope → RawTermV2 scope → Prop where
  /-- **Reflexivity.**  Every term StepStar-reduces to itself
      in zero steps. -/
  | refl (term : RawTermV2 scope) : StepStar term term
  /-- **Left-extension.**  Compose a single Step at the head of
      a StepStar chain to extend the chain by one step. -/
  | trans {first second third : RawTermV2 scope} :
      Step first second → StepStar second third →
      StepStar first third

/-- **Smoke: reflexivity on the unit term.**

Witnesses that the `.refl` constructor is inhabited on a concrete
fixture.  Trivial by `StepStar.refl _`. -/
theorem StepStar.refl_unit_smoke :
    StepStar (.mkGen .gen_unit () .childNil : RawTermV2 0)
             (.mkGen .gen_unit () .childNil : RawTermV2 0) :=
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
    let identityLamBody : RawTermV2 1 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
    let unitArg : RawTermV2 0 :=
      .mkGen .gen_unit () .childNil
    let app : RawTermV2 0 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons identityLamBody .childNil))
          (.childCons unitArg .childNil))
    StepStar app unitArg :=
  StepStar.trans Step.beta (StepStar.refl _)

end LeanFX2.Foundation.PolyCell.Core
