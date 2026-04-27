import FX.Kernel.Reduction

/-!
# Definitional equality (conversion)

Per `fx_design.md` §31 (kernel normalization) and Appendix H.9
`T-conv` (the conversion rule — `context ⊢ e : T ∧ context ⊢ T ≡ T' →
context ⊢ e : T'`).

## Strategy

  * **Normalize both sides to whnf**, then compare the outer
    constructor.  If they differ, the terms are not convertible.
  * **For matching constructors, recurse structurally** on their
    sub-terms.  For binders (`lam`, `pi`, `sigma`), compare the
    grade and the domain, then recurse into the body — both
    bodies live under the same new binder (de Bruijn), so no
    renaming is needed.
  * **Grade equality** is structural (pointwise on the 12-field
    `Grade` record).  Two grades are convertible only when they
    are equal; we do not do grade subsumption here — subsumption
    lives in the typing rules themselves.
  * **Level equality** is by definitional `eval?` — if both
    levels evaluate to the same `Nat`, they are equal, even if
    the syntactic `Level` terms differ (e.g., `max zero u` vs
    `u`).  Two levels containing `var _` compare structurally.

## valueType-equivalence

With de Bruijn indices valueType-equivalence is syntactic equality —
variable names are positional, so no renaming pass is needed.
`convEq` is thus already valueType-equivalence-correct by construction.

## eta-equivalence

eta is a convertibility rule, not a reduction rule, per
`fx_design.md` Appendix H.9.  For Pi:

    lambda (x :_g A). f x ≡ f    (when f does not use x)

**Phase 2 implements Pi-eta** (task A6).  When `convEq` sees a
lambda on one side and a non-lambda head on the other, the
helper `etaUnshift?` checks whether the lambda's body has the
form `app f (var 0)` with `f` not mentioning the outer-scope
`var 0`.  If so, it returns `f` with free vars decremented by 1,
and the comparison proceeds against the non-lambda side.  This
matches the Wood-Atkey graded-calculus presentation where eta is
admissible for Pi-types (weaker grade on the eta-converted form).

Sigma-eta is not applicable at Phase 2: our `Term.sigma` is a
type-former only — no pair value constructor exists, so there's
no syntactic shape `(fst p, snd p)` to η-contract against `p`.
Revisited if/when `Sigma-intro` / `Sigma-elim` land.

Multi-step eta (nested lambdas on one side, iterated un-η) is
NOT handled separately — it falls out of the fuel-bounded
recursion: each η step removes one lambda wrapper, then the
outer `convEq` call re-enters with the next level.  Deep eta on
pathological inputs consumes fuel rather than diverging.

## Totality

`convEq` is fuel-bounded through its use of `whnf`.  On
exceeded fuel it returns `false` (the conservative choice —
spurious "not equal" rather than spurious "equal").
-/

namespace FX.Kernel

namespace Level

/-- Definitional equality of levels: equal evaluations, or equal
    syntactic shape for variable-containing levels. -/
def equiv (leftLevel rightLevel : Level) : Bool :=
  match leftLevel.eval?, rightLevel.eval? with
  | some leftValue, some rightValue => leftValue = rightValue
  | none,           none            => decide (leftLevel = rightLevel)
  | _,              _               => false

end Level

namespace Term

/-! ## Pi-η helper

`etaUnshift? body` returns `some f'` when `body` has the form
`app f (var 0)` with `f` free of outer-scope `var 0`, where `f'`
is `f` with every free reference to outer variables decremented
by 1 — i.e., the "collapse the enclosing binder" form that is
η-equivalent to `λx. body`.  Returns `none` when the body
does not fit the η pattern or `f` would capture the binder.

Implementation note on the decrement: `subst 0 placeholder f`
normally substitutes `placeholder` for `var 0` AND decrements
every `var n ≥ 1` by 1.  When we've already established that
`f` does not mention outer `var 0`, the placeholder never
appears in the result — we exploit the decrement side effect
as a zero-cost unshift.  The placeholder is `.type .zero`; any
closed term works. -/

def etaUnshift? (body : Term) : Option Term :=
  match body with
  | .app headFunction (.var 0) =>
    if mentionsVar 0 headFunction then none
    else some (subst 0 (.type .zero) headFunction)
  | _ => none

/-!
## Convertibility

Every branch uses `whnf` on its argument before structural
comparison.  `defaultFuel` is the budget for each whnf call;
deep recursion additionally has `structFuel` to guard against
pathological tree depth (cyclic reference patterns aren't
possible in our tree, but deeply nested terms in malformed
input could otherwise exhaust stack).
-/

/- Definitional equality check.  Returns `true` iff the two
   terms are convertible, using beta/iota/delta-reduction and
   structural equality.

   The `fuel` parameter caps both whnf depth and structural
   recursion depth.  Returns `false` on fuel exhaustion (safe
   default).  `globalEnv` threads to `whnf` so a `.const` head
   marked `@[transparent]` unfolds before comparison; two
   distinct const names whose transparent bodies normalize to
   the same shape are convertible.  Two opaque consts compare
   by name equality only (the `const ... , const ...` arm
   covers this once the match is extended). -/

mutual

partial def convEq (fuel : Nat) (leftTerm rightTerm : Term)
    (globalEnv : GlobalEnv := {}) : Bool :=
  if fuel = 0 then false
  else
    let leftWhnf := whnf fuel leftTerm globalEnv
    let rightWhnf := whnf fuel rightTerm globalEnv
    match leftWhnf, rightWhnf with
    | var leftIndex, var rightIndex => leftIndex = rightIndex
    | const leftName, const rightName => leftName == rightName
    | app leftFun leftArg, app rightFun rightArg =>
      convEq (fuel - 1) leftFun rightFun globalEnv
        && convEq (fuel - 1) leftArg rightArg globalEnv
    | lam leftGrade leftType leftBody, lam rightGrade rightType rightBody =>
      Grade.beq leftGrade rightGrade
        && convEq (fuel - 1) leftType rightType globalEnv
        && convEq (fuel - 1) leftBody rightBody globalEnv
    | pi leftGrade leftType leftBody leftEffect,
      pi rightGrade rightType rightBody rightEffect =>
      Grade.beq leftGrade rightGrade
        && convEq (fuel - 1) leftType rightType globalEnv
        && convEq (fuel - 1) leftBody rightBody globalEnv
        && decide (leftEffect = rightEffect)
    | sigma leftGrade leftType leftBody, sigma rightGrade rightType rightBody =>
      Grade.beq leftGrade rightGrade
        && convEq (fuel - 1) leftType rightType globalEnv
        && convEq (fuel - 1) leftBody rightBody globalEnv
    | type leftLevel, type rightLevel => Level.equiv leftLevel rightLevel
    | forallLevel leftBody, forallLevel rightBody =>
      convEq (fuel - 1) leftBody rightBody globalEnv
    | ind leftName leftArgs, ind rightName rightArgs =>
      leftName == rightName && convEqList (fuel - 1) leftArgs rightArgs globalEnv
    | ctor leftName leftIdx leftTypeArgs leftArgs,
      ctor rightName rightIdx rightTypeArgs rightArgs =>
      leftName == rightName && leftIdx == rightIdx
        && convEqList (fuel - 1) leftTypeArgs rightTypeArgs globalEnv
        && convEqList (fuel - 1) leftArgs rightArgs globalEnv
    | indRec leftName leftMotive leftMethods leftTarget,
      indRec rightName rightMotive rightMethods rightTarget =>
      leftName == rightName
        && convEq (fuel - 1) leftMotive rightMotive globalEnv
        && convEqList (fuel - 1) leftMethods rightMethods globalEnv
        && convEq (fuel - 1) leftTarget rightTarget globalEnv
    | coind leftName leftArgs, coind rightName rightArgs =>
      leftName == rightName
        && convEqList (fuel - 1) leftArgs rightArgs globalEnv
    | coindUnfold leftName leftTypeArgs leftArms,
      coindUnfold rightName rightTypeArgs rightArms =>
      leftName == rightName
        && convEqList (fuel - 1) leftTypeArgs rightTypeArgs globalEnv
        && convEqList (fuel - 1) leftArms rightArms globalEnv
    | coindDestruct leftName leftIdx leftTarget,
      coindDestruct rightName rightIdx rightTarget =>
      leftName == rightName && leftIdx == rightIdx
        && convEq (fuel - 1) leftTarget rightTarget globalEnv
    | id leftType leftLhs leftRhs, id rightType rightLhs rightRhs =>
      convEq (fuel - 1) leftType rightType globalEnv &&
      convEq (fuel - 1) leftLhs rightLhs globalEnv &&
      convEq (fuel - 1) leftRhs rightRhs globalEnv
    | refl leftWitness, refl rightWitness =>
      convEq (fuel - 1) leftWitness rightWitness globalEnv
    | idJ leftMotive leftBase leftEq, idJ rightMotive rightBase rightEq =>
      convEq (fuel - 1) leftMotive rightMotive globalEnv
        && convEq (fuel - 1) leftBase rightBase globalEnv
        && convEq (fuel - 1) leftEq rightEq globalEnv
    | quot leftType leftRel, quot rightType rightRel =>
      convEq (fuel - 1) leftType rightType globalEnv
        && convEq (fuel - 1) leftRel rightRel globalEnv
    | quotMk leftRel leftWitness, quotMk rightRel rightWitness =>
      convEq (fuel - 1) leftRel rightRel globalEnv
        && convEq (fuel - 1) leftWitness rightWitness globalEnv
    | quotLift leftLifted leftRespects leftTarget,
      quotLift rightLifted rightRespects rightTarget =>
      convEq (fuel - 1) leftLifted rightLifted globalEnv
        && convEq (fuel - 1) leftRespects rightRespects globalEnv
        && convEq (fuel - 1) leftTarget rightTarget globalEnv
    -- Pi-η (Appendix H.9): `λ _. f (var 0)` ≡ `f` when `f` is
    -- free of outer `var 0`.  Arms only fire in the mixed case
    -- (one side lambda, the other non-lambda) — both-lambda is
    -- already handled above by the structural `lam, lam` arm,
    -- and both-non-lambda has no η move to try.  Left-lam first,
    -- then symmetric right-lam, then the `_, _` fallthrough.
    | lam _leftGrade _leftType leftBody, _ =>
      match etaUnshift? leftBody with
      | some unshiftedLeft =>
        convEq (fuel - 1) unshiftedLeft rightWhnf globalEnv
      | none => false
    | _, lam _rightGrade _rightType rightBody =>
      match etaUnshift? rightBody with
      | some unshiftedRight =>
        convEq (fuel - 1) leftWhnf unshiftedRight globalEnv
      | none => false
    | _, _ => false

partial def convEqList (fuel : Nat)
    : List Term → List Term → (globalEnv : GlobalEnv := {}) → Bool
  | [], [], _ => true
  | leftHead :: leftRest, rightHead :: rightRest, globalEnv =>
    convEq fuel leftHead rightHead globalEnv
      && convEqList fuel leftRest rightRest globalEnv
  | _, _, _ => false

end  -- mutual

/-- Entry with default fuel and empty globalEnv — preserves the
    pre-transparency API for non-kernel callers that don't have
    a global env on hand. -/
def conv (leftTerm rightTerm : Term) : Bool := convEq defaultFuel leftTerm rightTerm

/--
Subtype-or-convert: asymmetric check for `check context t T` sites.
Returns `true` when a value typed `leftTerm` can be used where
`rightTerm` is expected.

Strategy:

  * **First try convEq** — structural equality is always subtyping,
    and this path handles β/ι/η uniformly.  If that succeeds, done.
  * **Otherwise, normalize both sides to whnf** and dispatch by the
    head constructor pair.

## Per-head rules landed in A7 (this commit)

  * `Type<u> <: Type<v>` when `u ≤ v` (§31.4 U-cumul — landed A11).
  * `Pi g A B <: Pi g A' B'` when:
      - Grades are equal (`Grade.beq g g'` — strict).
      - Domain is contravariant: `A' <: A` (caller's domain may
        be narrower than callee's — but we're asking whether the
        CALLEE's Pi fits in the CALLER's slot, so the callee's
        declared domain `A` must ACCEPT everything the caller
        will pass, i.e., the caller's `A'` must be a subtype of
        the callee's `A`).  Equivalent formulation in the code:
        `subOrConv rightDomain leftDomain`.
      - Codomain is covariant: `B <: B'` (callee's output must
        satisfy what caller expects).
  * `Sigma g A B <: Sigma g A' B'` when:
      - Grades are equal.
      - Both positions covariant: `A <: A'` and `B <: B'`.
        Sigma's components are positive positions — constructing
        a pair requires terms of subtypes.

## Grade subsumption direction — deferred to A7-followup

Pi-binder grade subsumption direction is subtle: §6.2's graded
rule `r ≤ s` allows "value at grade r where grade s expected",
but on a Pi BINDER the grade is "how this function consumes its
argument", and the direction interacts with Wood-Atkey context
division in ways that are not self-evident from the spec.  This
iteration requires strict grade equality on both Pi and Sigma
binders; grade subsumption on binders is reserved as a follow-up
once §6.2's intent is clarified with a worked-out Wood-Atkey
example.

## Still out of scope (reserved for A7-followup / A10 / A12)

  * Refinement weakening (§10).  Needs refinement predicates to
    be first-class in `Term`, which they aren't yet.
  * Effect-row inclusion (§9.3) beyond what `Effect.LessEq` would
    give pointwise once effects flow through typing (blocks on
    A12).
  * Universe polymorphism subtyping (blocks on A10).
  * Ind / Coind positional variance (would require recording
    variance on each parameter).

The A7 core rules below (Pi + Sigma + U-cumul) are sufficient
for the Phase-2.2 test suite's subtyping needs and make the
landed subset mathematically sound without cutting corners on
what is checked.
-/
partial def subOrConv (fuel : Nat) (leftTerm rightTerm : Term)
    (globalEnv : GlobalEnv := {}) : Bool :=
  if fuel = 0 then false
  else if convEq fuel leftTerm rightTerm globalEnv then true
  else
    match whnf fuel leftTerm globalEnv, whnf fuel rightTerm globalEnv with
    | Term.type leftLevel, Term.type rightLevel =>
      Level.leBool leftLevel rightLevel
    | Term.pi leftGrade leftDomain leftCodomain leftEffect,
      Term.pi rightGrade rightDomain rightCodomain rightEffect =>
      -- Pi subtyping: contra-domain + co-codomain + co-effect
      -- per Appendix B (E-Sub).  Effect subsumption honors
      -- §9.3's lattice: `Tot ≤ IO`, `Read ≤ Write`, etc.
      -- A fn declared `→{Tot}` is usable where `→{IO}` is
      -- expected (narrower capability satisfies wider need).
      Grade.beq leftGrade rightGrade
        && subOrConv (fuel - 1) rightDomain leftDomain globalEnv
        && subOrConv (fuel - 1) leftCodomain rightCodomain globalEnv
        && Effect.subsumes leftEffect rightEffect
    | Term.sigma leftGrade leftDomain leftCodomain,
      Term.sigma rightGrade rightDomain rightCodomain =>
      Grade.beq leftGrade rightGrade
        && subOrConv (fuel - 1) leftDomain rightDomain globalEnv
        && subOrConv (fuel - 1) leftCodomain rightCodomain globalEnv
    | _, _ => false

end Term

end FX.Kernel
