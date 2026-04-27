import FX.KernelMTT.Term
import FX.KernelMTT.Substitution
import FX.KernelMTT.Reduction

/-!
# Convertibility / definitional equality (V1.5 first installment)

`convEq : Term n → Term n → Bool` decides whether two terms are
definitionally equal modulo the kernel's reduction rules (β, ι,
ν, modElim-ι, idJ-ι, coerceCell-strip — all from V1.15 whnf)
plus η on Lam binders (`λ x. f x ≡ f` when `f` doesn't
reference `x`).

This is the operational core of the V1.5 MTT checker's "is `T`
the same as `T'`?" question — when an inferred type matches an
expected type modulo β/η, the checker accepts.  Without
convEq, the checker would only accept syntactic equality, which
rejects every program that performs computation in its types.

## Algorithm

1. Reduce both sides to WHNF (`Term.whnf` from V1.15).
2. Compare the resulting heads constructor-by-constructor.
3. For Lam vs non-Lam: try η — convert the non-Lam to its
   η-expanded form `app m (shift0 other) (var m 0) : Term (n+1)`
   and recurse on the body.
4. For variable-arity arg lists: recurse via `convEqArgs`
   (mutual).

Same context size on both sides: `Term n × Term n → Bool`.
Lean's type system enforces that we never compare across
scopes.

## η on Lam — what about Pi, Sigma?

Pi, Sigma are *type formers*; they don't admit η in the
reduction-rule sense.  η-equality for Sigma (`(p.fst, p.snd) ≡
p`) requires a Sigma-intro / projection structure that this
kernel encoding doesn't have.  Pi-η would be a typing-level
rule (functions equal up to η-expanded form), and we already
get Lam-η which covers it.

η for codata (`unfold (head x) (tail x) ≡ x` for stream-like
codata) is a separate convertibility rule that requires
destructor structure — deferred until the IndSpec/CoindSpec
lookup wires through KernelMTT.

## Fuel

`whnf` is fuel-bounded; the same fuel is passed through every
recursive `convEqWith` call.  `Term.defaultFuel = 4096` is the
common-case wrapper.  convEq's own structural recursion is
bounded by term size.

## Termination

`partial def` — the recursion through whnf + η-expansion + arg
lists is non-trivial for Lean's termination checker.  Same
boundary as `Term.structEq` and `Term.whnf`.

## Trust layer

`FX/KernelMTT/**` is UNTRUSTED scaffold during Phase R1.  Zero
`sorry`, zero new axioms.  Mechanized correctness (convEq
soundness/completeness against the conv judgement) is V_meta
scope.

## Cross-references

  * `FX/KernelMTT/Reduction.lean` — provides whnf
  * `FX/Kernel/Conversion.lean` — legacy un-indexed convEq
  * `fx_design.md` §30 H.9 — T-conv definitional equality rule
  * Appendix H.9 / §27.1 — η as a convertibility rule (NOT a
    reduction)
-/

namespace FX.KernelMTT

open FX.Kernel  -- Grade.beq, Level (DecidableEq), Effect (DecidableEq)

namespace Term

/-- Helper: η-expand `other : Term n` to a term of type
    `Term (n+1)`.  Produces `app mode (shift0 other) (var mode 0)` —
    the canonical η-expansion of a function used in reverse to
    decide `λ x. f x ≡ f`. -/
private def etaExpandTo {n : Nat} (mode : Mode) (other : Term n) :
    Term (n+1) :=
  Term.app mode (Term.shift0 other) (Term.var mode ⟨0, by omega⟩)

mutual

/-- Definitional equality: reduce both sides to WHNF (V1.15
    `whnf`) and then compare modulo η on Lam binders.

    Mutual with `convEqWhnf` (the post-whnf comparison) and
    `convEqArgs` (for variable-arity arg lists in `ind` / `ctor`
    / `indRec` / etc). -/
partial def convEqWith {n : Nat} (fuel : Nat)
    (lhs rhs : Term n) : Bool :=
  let lhs' := Term.whnf fuel lhs
  let rhs' := Term.whnf fuel rhs
  convEqWhnf fuel lhs' rhs'

/-- Compare two WHNF terms.  Each constructor's case recurses
    on subterms via `convEqWith` (which re-whnfs them) so we
    don't miss reductions inside subterms.

    The Lam η fallbacks (lam-vs-other and other-vs-lam) handle
    the case where one side reduced to a function and the
    other didn't — this is exactly when we'd lose information
    by structural comparison alone. -/
partial def convEqWhnf {n : Nat} (fuel : Nat) :
    Term n → Term n → Bool
  -- Specific same-constructor cases first.
  | .var lm li, .var rm ri =>
    decide (lm = rm) && li == ri
  | .app lm lf la, .app rm rf ra =>
    decide (lm = rm)
      && convEqWith fuel lf rf && convEqWith fuel la ra
  | .lam lm lg ld lb, .lam rm rg rd rb =>
    decide (lm = rm) && Grade.beq lg rg
      && convEqWith fuel ld rd && convEqWith fuel lb rb
  | .pi lm lg ld lb le, .pi rm rg rd rb re =>
    decide (lm = rm) && Grade.beq lg rg
      && convEqWith fuel ld rd && convEqWith fuel lb rb
      && decide (le = re)
  | .sigma lm lg ld lb, .sigma rm rg rd rb =>
    decide (lm = rm) && Grade.beq lg rg
      && convEqWith fuel ld rd && convEqWith fuel lb rb
  | .type lm ll, .type rm rl =>
    decide (lm = rm) && decide (ll = rl)
  | .forallLevel lm lb, .forallLevel rm rb =>
    decide (lm = rm) && convEqWith fuel lb rb
  | .const lm ln, .const rm rn =>
    decide (lm = rm) && ln == rn
  | .ind lm ln la, .ind rm rn ra =>
    decide (lm = rm) && ln == rn
      && convEqArgs fuel la ra
  | .ctor lm ln li lts lvs, .ctor rm rn ri rts rvs =>
    decide (lm = rm) && ln == rn && li == ri
      && convEqArgs fuel lts rts
      && convEqArgs fuel lvs rvs
  | .indRec lm ln lmot lms ltgt, .indRec rm rn rmot rms rtgt =>
    decide (lm = rm) && ln == rn
      && convEqWith fuel lmot rmot
      && convEqArgs fuel lms rms
      && convEqWith fuel ltgt rtgt
  | .coind lm ln la, .coind rm rn ra =>
    decide (lm = rm) && ln == rn
      && convEqArgs fuel la ra
  | .coindUnfold lm ln lts larms,
    .coindUnfold rm rn rts rarms =>
    decide (lm = rm) && ln == rn
      && convEqArgs fuel lts rts
      && convEqArgs fuel larms rarms
  | .coindDestruct lm ln li ltgt,
    .coindDestruct rm rn ri rtgt =>
    decide (lm = rm) && ln == rn && li == ri
      && convEqWith fuel ltgt rtgt
  | .id lm lty ll lr, .id rm rty rl rr =>
    decide (lm = rm)
      && convEqWith fuel lty rty
      && convEqWith fuel ll rl
      && convEqWith fuel lr rr
  | .refl lm lw, .refl rm rw =>
    decide (lm = rm) && convEqWith fuel lw rw
  | .idJ lm lmot lbase leq, .idJ rm rmot rbase req =>
    decide (lm = rm)
      && convEqWith fuel lmot rmot
      && convEqWith fuel lbase rbase
      && convEqWith fuel leq req
  | .hit lm ln la, .hit rm rn ra =>
    decide (lm = rm) && ln == rn
      && convEqArgs fuel la ra
  | .hitMk lm ln li lts lvs, .hitMk rm rn ri rts rvs =>
    decide (lm = rm) && ln == rn && li == ri
      && convEqArgs fuel lts rts
      && convEqArgs fuel lvs rvs
  | .hitRec lm ln lmot ldms lpps ltgt,
    .hitRec rm rn rmot rdms rpps rtgt =>
    decide (lm = rm) && ln == rn
      && convEqWith fuel lmot rmot
      && convEqArgs fuel ldms rdms
      && convEqArgs fuel lpps rpps
      && convEqWith fuel ltgt rtgt
  | .modIntro lsrc ltgt lmod lt,
    .modIntro rsrc rtgt rmod rt =>
    decide (lsrc = rsrc) && decide (ltgt = rtgt)
      && decide (lmod = rmod)
      && convEqWith fuel lt rt
  | .modElim lsrc ltgt lmod lterm lbody,
    .modElim rsrc rtgt rmod rterm rbody =>
    decide (lsrc = rsrc) && decide (ltgt = rtgt)
      && decide (lmod = rmod)
      && convEqWith fuel lterm rterm
      && convEqWith fuel lbody rbody
  | .transport le ls, .transport re rs =>
    convEqWith fuel le re && convEqWith fuel ls rs
  | .coerceCell lmod lf lt' lt'',
    .coerceCell rmod rf rt' rt'' =>
    -- Defensive: whnf strips coerceCell eagerly, so this case
    -- shouldn't fire in practice.  Compare structurally as a
    -- fallback if fuel exhaustion left coerceCell visible.
    decide (lmod = rmod) && lf == rf && lt' == rt'
      && convEqWith fuel lt'' rt''
  -- η on Lam: when one side is a Lam and the other isn't
  -- a same-mode same-grade Lam, try η-expanding the non-Lam
  -- side and comparing the bodies.
  | .lam lm _ _ lbody, other =>
    convEqWith fuel lbody (etaExpandTo lm other)
  | other, .lam rm _ _ rbody =>
    convEqWith fuel (etaExpandTo rm other) rbody
  -- Different constructors, no η applies: not convertible.
  | _, _ => false

/-- Pointwise convEq over two argument lists at the same context
    size. -/
partial def convEqArgs {n : Nat} (fuel : Nat) :
    TermArgs n → TermArgs n → Bool
  | .nil,       .nil       => true
  | .cons l ls, .cons r rs =>
    convEqWith fuel l r && convEqArgs fuel ls rs
  | _, _ => false

end

/-- Default-fuel wrapper.  Most callers want this — they don't
    care about the fuel bound, just whether the terms agree
    modulo definitional equality. -/
abbrev convEq {n : Nat} (lhs rhs : Term n) : Bool :=
  convEqWith Term.defaultFuel lhs rhs

end Term

end FX.KernelMTT
