import FX.KernelMTT.Term
import FX.KernelMTT.Substitution
import FX.KernelMTT.Reduction
import FX.KernelMTT.Conversion

/-!
# Subtyping over the well-scoped mode-indexed Term

`subtype : Term n → Term n → Bool` decides T-sub: whether a value
typed `lhs` may be used where a value typed `rhs` is expected.

Subtyping extends convertibility (every `T1 ≡ T2` is `T1 <: T2`)
with three direction-sensitive rules:

  * **U-cumul**: `Type<l1> <: Type<l2>` when `l1 ≤ l2`.
  * **Pi-subtype**: `(x:_g A1) → B1 with eff1
                       <: (x:_g A2) → B2 with eff2`
    when grades are equal and `A2 <: A1` (contravariant input)
    and `B1 <: B2` (covariant output) and `eff1 ⊆ eff2`
    (effect-row subsumption: a function performing fewer
    effects satisfies a context expecting more).
  * **Sigma-subtype**: `Σ (x:_g A1) × B1 <: Σ (x:_g A2) × B2`
    when grades are equal and both `A1 <: A2` and `B1 <: B2`
    (covariant in both — pair construction is positive).
  * **forallLevel**: `forallLevel L. T1 <: forallLevel L. T2`
    when `T1 <: T2` (covariant body; the level binder doesn't
    extend the term context).

Every other constructor pair falls through to convEq (via the
fast-path check at entry).  Modal subsumption — using a value
at a finer modality where a coarser one is expected, via the
2-cell structure of `fx_modecat.md` — is V1.6 (separate task)
and not yet fired here.

## Algorithm

1. **Fast path**: if `convEq lhs rhs`, accept (every convertible
   pair is subtype-related — the reflexive direction).
2. Otherwise reduce both sides to WHNF (V1.15 `whnf`) and
   dispatch on the head pair.
3. The four direction-sensitive cases fire; everything else
   returns false (convEq already failed, no other rule applies).

Same context size on both sides: `Term n × Term n → Bool`.
The Lean type system enforces no cross-scope comparison.

## Asymmetry vs convEq

`subtype lhs rhs` is NOT symmetric.  `convEq` is reflexive,
symmetric, and transitive.  `subtype` is reflexive (via convEq
fast path) and transitive but NOT symmetric — that's the whole
point of the direction-sensitive rules.

## Strict grade equality on Pi/Sigma binders

§6.2's graded rule allows `r ≤ s` for "value at grade r flows
to grade s expected", but on a Pi BINDER the grade is "how
this function consumes its argument", and the direction
interacts with Wood-Atkey context division in ways that need a
worked-out example before landing.  Strict grade equality
matches the legacy `FX/Kernel/Subtyping.lean` discipline; grade
subsumption on binders is reserved for a follow-up.

## Effect-row subsumption direction

Pi with fewer effects is a subtype of Pi with more effects: a
function that performs only `Tot` may be passed where a context
expects `Tot ∪ IO`, because the actual behavior is bounded by
what the function does, not what the context permits.  The
discriminator is `Effect.subsumes le re` — true when `le ⊆ re`.

## What's deferred

  * **Modal subsumption** (V1.6): `[μ_inner](A) <: [μ_outer](A)`
    when `μ_inner ⊑ μ_outer` in the FX mode theory's 2-cell
    structure.  Requires the 2-cell lookup table to wire
    through.  modIntro's structural rule here is convEq-only.
  * **Sigma-η contraction**: convEq doesn't have it yet; needs
    Sigma-intro structure that this kernel encoding doesn't
    have.  Both convEq and subtype defer it.
  * **Refinement weakening**: blocks on first-class refinement
    predicates in `Term`.
  * **Ind / Coind positional variance**: would need per-
    parameter variance metadata; today they're invariant via
    convEq.
  * **Grade subsumption on Pi/Sigma binders**: see above.

## Trust layer

`FX/KernelMTT/**` is UNTRUSTED scaffold during Phase R1.  Zero
`sorry`, zero new axioms.  Mechanized correctness (subtype
soundness vs the conv judgement) is V_meta scope.

## Cross-references

  * `FX/KernelMTT/Conversion.lean` — provides `convEqWith`
  * `FX/KernelMTT/Reduction.lean` — provides `whnf`
  * `FX/Kernel/Subtyping.lean` + `FX/Kernel/Conversion.lean` —
    legacy un-indexed `subOrConv`
  * `fx_design.md` Appendix H.9 / §31 — T-sub composite rule
  * `fx_design.md` §15.5 — per-dimension compatibility table
-/

namespace FX.KernelMTT

open FX.Kernel  -- Grade.beq, Level.leBool, Effect.subsumes

namespace Term

mutual

/-- T-sub: subtype-or-convertible check.  Whnf both sides
    after a convEq fast path; dispatch on the head pair. -/
partial def subtypeWith {n : Nat} (fuel : Nat)
    (lhs rhs : Term n) : Bool :=
  if convEqWith fuel lhs rhs then true
  else
    let lhs' := whnf fuel lhs
    let rhs' := whnf fuel rhs
    subtypeWhnf fuel lhs' rhs'

/-- Compare two WHNF terms for subtyping.  Only the four
    direction-sensitive cases (Type, Pi, Sigma, forallLevel)
    fire; every other constructor pair returns false because
    the convEq fast path in `subtypeWith` already handled
    convertible pairs. -/
partial def subtypeWhnf {n : Nat} (fuel : Nat) :
    Term n → Term n → Bool
  -- U-cumul: Type<l1> <: Type<l2> when l1 ≤ l2 in the
  -- level preorder.  Mode equality is required (no cross-
  -- mode universe subtyping in the v1 mode theory).
  | .type lmode llevel, .type rmode rlevel =>
    decide (lmode = rmode) && Level.leBool llevel rlevel
  -- Pi: contra-domain, co-codomain, co-effect.
  -- Modes equal, grades equal, effects subsumed.
  | .pi lmode lgrade ldom lcod leff,
    .pi rmode rgrade rdom rcod reff =>
    decide (lmode = rmode) && Grade.beq lgrade rgrade
      && subtypeWith fuel rdom ldom        -- contra
      && subtypeWith fuel lcod rcod        -- co
      && Effect.subsumes leff reff         -- co (subset)
  -- Sigma: both positions covariant (pair construction is
  -- positive — building a Σ requires inhabiting both sides).
  | .sigma lmode lgrade ldom lcod,
    .sigma rmode rgrade rdom rcod =>
    decide (lmode = rmode) && Grade.beq lgrade rgrade
      && subtypeWith fuel ldom rdom        -- co
      && subtypeWith fuel lcod rcod        -- co
  -- forallLevel: covariant body.  Level binders don't extend
  -- the term context so the recursion stays at scope `n`.
  | .forallLevel lmode lbody, .forallLevel rmode rbody =>
    decide (lmode = rmode) && subtypeWith fuel lbody rbody
  -- Every other head pair: convEq already tried and failed.
  -- Modal subsumption via 2-cells is deferred to V1.6.
  | _, _ => false

end

/-- Default-fuel wrapper.  Most callers just want to know
    whether one type is acceptable where the other is expected,
    independent of the fuel discipline. -/
abbrev subtype {n : Nat} (lhs rhs : Term n) : Bool :=
  subtypeWith Term.defaultFuel lhs rhs

end Term

end FX.KernelMTT
