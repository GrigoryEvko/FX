import LeanFX2.Foundation.Action

/-! # RawTerm — Layer 0 untyped well-scoped terms.

`RawTerm scope` is the de Bruijn-indexed term family with `Fin scope`
positions for variables.  No types, no Ctx, no Ty references — pure
syntactic skeleton.

## Architectural role

RawTerm is the **type-level index** that makes lean-fx-2's Term
raw-aware.  Every Term ctor's signature pins the corresponding
RawTerm structure, so `Term.toRaw t = raw` is `rfl` (the projection
IS the type index).

## Constructors (28 total)

Mirrors lean-fx-2's typed Term constructor list (sans type
annotations).  Modal ctors (`modIntro`, `modElim`, `subsume`)
included from day 1 even though Layer 6 isn't implemented yet —
this avoids backward-incompatible additions later.

## Decidable equality

Auto-derived via `deriving DecidableEq`.  Per
`feedback_lean_zero_axiom_match.md` Rule 3 (full enumeration on
dependent inductive with universal Nat index), this is propext-free
in Lean 4 v4.29.1.
-/

namespace LeanFX2

/-- Untyped well-scoped terms.  De Bruijn variables via `Fin scope`. -/
inductive RawTerm : Nat → Type
  -- Variable
  | var {scope : Nat} (position : Fin scope) : RawTerm scope
  -- Unit
  | unit {scope : Nat} : RawTerm scope
  -- Function intro/elim (covers both arrow and Π applications)
  | lam {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope
  | app {scope : Nat} (functionTerm argumentTerm : RawTerm scope) : RawTerm scope
  -- Pair intro/elim (covers both non-dep and Σ)
  | pair {scope : Nat} (firstValue secondValue : RawTerm scope) : RawTerm scope
  | fst {scope : Nat} (pairTerm : RawTerm scope) : RawTerm scope
  | snd {scope : Nat} (pairTerm : RawTerm scope) : RawTerm scope
  -- Booleans
  | boolTrue {scope : Nat} : RawTerm scope
  | boolFalse {scope : Nat} : RawTerm scope
  | boolElim {scope : Nat}
      (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope
  -- Naturals
  | natZero {scope : Nat} : RawTerm scope
  | natSucc {scope : Nat} (predecessor : RawTerm scope) : RawTerm scope
  | natElim {scope : Nat}
      (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope
  | natRec {scope : Nat}
      (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope
  -- Lists
  | listNil {scope : Nat} : RawTerm scope
  | listCons {scope : Nat} (headTerm tailTerm : RawTerm scope) : RawTerm scope
  | listElim {scope : Nat}
      (scrutinee nilBranch consBranch : RawTerm scope) : RawTerm scope
  -- Options
  | optionNone {scope : Nat} : RawTerm scope
  | optionSome {scope : Nat} (valueTerm : RawTerm scope) : RawTerm scope
  | optionMatch {scope : Nat}
      (scrutinee noneBranch someBranch : RawTerm scope) : RawTerm scope
  -- Eithers
  | eitherInl {scope : Nat} (valueTerm : RawTerm scope) : RawTerm scope
  | eitherInr {scope : Nat} (valueTerm : RawTerm scope) : RawTerm scope
  | eitherMatch {scope : Nat}
      (scrutinee leftBranch rightBranch : RawTerm scope) : RawTerm scope
  -- Identity types
  | refl {scope : Nat} (rawWitness : RawTerm scope) : RawTerm scope
  | idJ {scope : Nat} (baseCase witness : RawTerm scope) : RawTerm scope
  -- Modal (Layer 6 references; raw-side ctors land from day 1)
  | modIntro {scope : Nat} (raw : RawTerm scope) : RawTerm scope
  | modElim {scope : Nat} (raw : RawTerm scope) : RawTerm scope
  | subsume {scope : Nat} (raw : RawTerm scope) : RawTerm scope
  -- D1.6 extension: 27 new ctors covering cubical / HOTT / refine /
  -- record / codata / session / effect / strict layers.  All are raw-
  -- syntactic skeletons; semantic interpretation lives in Reduction
  -- (D2.5–D2.7) and the typed Term inductive (D1.9).
  -- Cubical interval endpoints + lattice operations
  | interval0 {scope : Nat} : RawTerm scope
  | interval1 {scope : Nat} : RawTerm scope
  | intervalOpp {scope : Nat} (intervalTerm : RawTerm scope) : RawTerm scope
  | intervalMeet {scope : Nat}
      (leftInterval rightInterval : RawTerm scope) : RawTerm scope
  | intervalJoin {scope : Nat}
      (leftInterval rightInterval : RawTerm scope) : RawTerm scope
  -- Cubical path types (intro = lambda over interval, elim = path application)
  | pathLam {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope
  | pathApp {scope : Nat}
      (pathTerm intervalArg : RawTerm scope) : RawTerm scope
  -- Cubical glue + transport / composition
  | glueIntro {scope : Nat}
      (baseValue partialValue : RawTerm scope) : RawTerm scope
  | glueElim {scope : Nat} (gluedValue : RawTerm scope) : RawTerm scope
  | transp {scope : Nat}
      (path source : RawTerm scope) : RawTerm scope
  | hcomp {scope : Nat}
      (sides cap : RawTerm scope) : RawTerm scope
  -- Observational equality (set-level OEq) — refl, J eliminator, funext
  | oeqRefl {scope : Nat} (witness : RawTerm scope) : RawTerm scope
  | oeqJ {scope : Nat}
      (baseCase witness : RawTerm scope) : RawTerm scope
  | oeqFunext {scope : Nat}
      (pointwiseEquality : RawTerm scope) : RawTerm scope
  -- Strict (definitional) identity — refl + eliminator
  | idStrictRefl {scope : Nat} (witness : RawTerm scope) : RawTerm scope
  | idStrictRec {scope : Nat}
      (baseCase witness : RawTerm scope) : RawTerm scope
  -- Type equivalence (Equiv A B) — intro from a function + inverse
  | equivIntro {scope : Nat}
      (forwardFn backwardFn : RawTerm scope) : RawTerm scope
  | equivApp {scope : Nat}
      (equivTerm argument : RawTerm scope) : RawTerm scope
  -- Refinement types — bundle a value with its predicate proof
  | refineIntro {scope : Nat}
      (rawValue predicateProof : RawTerm scope) : RawTerm scope
  | refineElim {scope : Nat} (refinedValue : RawTerm scope) : RawTerm scope
  -- Record types — single-field placeholder (multi-field via nesting)
  | recordIntro {scope : Nat} (firstField : RawTerm scope) : RawTerm scope
  | recordProj {scope : Nat} (recordValue : RawTerm scope) : RawTerm scope
  -- Codata — corecursive constructor + destructor
  | codataUnfold {scope : Nat}
      (initialState transition : RawTerm scope) : RawTerm scope
  | codataDest {scope : Nat} (codataValue : RawTerm scope) : RawTerm scope
  -- Session-typed channels — send / receive / end
  | sessionSend {scope : Nat}
      (channel payload : RawTerm scope) : RawTerm scope
  | sessionRecv {scope : Nat} (channel : RawTerm scope) : RawTerm scope
  -- Algebraic effect operation — perform an effect at runtime
  | effectPerform {scope : Nat}
      (operationTag arguments : RawTerm scope) : RawTerm scope
  /-- Universe-code term: the raw form of "Type ⟨innerLevel⟩".  At
      typing layer this term lives at `Ty.universe outerLevel _` for
      any `outerLevel ≥ innerLevel` (cumulativity is intrinsic to
      `Term.universeCode`).  Used by `Conv.cumul` to prove that the
      same universe code is convertible across compatible outer
      levels.  No scope-dependent payload — just the inner level. -/
  | universeCode {scope : Nat} (innerLevel : Nat) : RawTerm scope
  deriving DecidableEq

/-! ## Tier 3 / MEGA-Z4.A — `ActsOnRawTermVar` typeclass + `RawTerm.act`
recursion engine.

Mirror of Z2.A's `ActsOnTyVar` + `Ty.act` discipline at the raw layer.
The `Action` typeclass (`Foundation/Action.lean`) describes any
`Container : Nat → Nat → Type` that can lift through binders and
compose sequentially.  However, `Action` alone does NOT determine
how a Container acts on the variable case of `RawTerm` — different
Containers map variables to different RawTerm shapes:

* `RawRenaming src tgt` maps `Fin src → Fin tgt` (a renaming);
  on a `RawTerm.var position`, the action wraps the renamed Fin back
  as `RawTerm.var`.
* `RawTermSubst src tgt` maps `Fin src → RawTerm tgt`; on a
  `RawTerm.var position`, the action returns the substituent
  RawTerm directly via the `sigma position` lookup.

`ActsOnRawTermVar Container` adds one method on top of `Action`:

* `varToRawTerm` — lookup at a Fin position in the source scope,
  producing a `RawTerm tgt`.  `RawTerm.var` arm of `RawTerm.act`
  invokes this.

Two binder-bearing RawTerm ctors (`lam`, `pathLam`) recurse with
`Action.liftForRaw someAction` to thread the Container under the
binder; everything else recurses with the unmodified `someAction`.

## Hoisted scope

Per `feedback_lean_match_arity_axioms.md`, having a single Nat index
(scope) per recursion is simpler than Ty.act's two indices (level +
scope).  Pattern arity stays at 2 hoisted Nat indices (sourceScope,
targetScope) plus the RawTerm scrutinee and Container argument.

## Marked `@[reducible]`

So the unifier can chain through definitional equalities (e.g.
`RawTerm.act t Action.identity` should reduce to `t` for
representative ctors).

## Per-Container expectations

When `Container = RawRenaming`, `varToRawTerm` is
`fun rho pos => RawTerm.var (rho pos)`; under that instance,
`RawTerm.act t rho` is propositionally equal to the existing
`RawTerm.rename t rho` (full equivalence theorem deferred to a
later milestone — Z4.B is the redirect target).

When `Container = RawTermSubst`, `varToRawTerm` is
`fun sigma pos => sigma pos`; under that instance, `RawTerm.act t
sigma` is propositionally equal to `RawTerm.subst t sigma`.

## Re-uses existing `ActsOnRawTerm`

The `ActsOnRawTerm` typeclass (defined in `Foundation/Ty.lean:680`)
provides `actOnRawTerm : Container src tgt → RawTerm src → RawTerm
tgt`.  That typeclass is the **dispatch surface** used by
`Ty.act`'s raw-payload arms.  `RawTerm.act` is the engine BEHIND
that dispatch — once `Foundation/RawSubst.lean` instantiates
`ActsOnRawTerm` for `RawRenaming` / `RawTermSubst` via
`RawTerm.act`, the two layers fold into a single recursion.  For
Z4.A we ship the engine + per-Container `varToRawTerm` instances;
the fold-into-actOnRawTerm is left to later phases (it would
require modifying the existing `instance : ActsOnRawTerm
RawRenaming` in `Foundation/Ty.lean`, which is sealed at Z2.A's
boundary).

## Layer

This file (`Foundation/RawTerm.lean`) imports `Foundation/Action.lean`
since Z4.A — `Action.lean` has zero imports (it does NOT depend on
`Ty` or `RawTerm`), so this introduces no cycle.

## Audit

`Smoke/AuditMegaZ4A.lean` runs `#print axioms` on every declaration
introduced in this section.  All zero-axiom under strict policy. -/

/-- A `Container` that acts on `RawTerm.var position` cases.
Different Containers map variables to different RawTerm shapes:
`RawRenaming` wraps the renamed Fin as `RawTerm.var`; `RawTermSubst`
returns the substituent `RawTerm tgt` directly.

This typeclass mirrors `ActsOnTyVar` (`Foundation/Ty.lean:707`) at
the raw layer.  It does NOT extend `Action`; the `RawTerm.act`
engine takes `[Action Container]` and `[ActsOnRawTermVar Container]`
as separate constraints, keeping the typeclass dependency lattice
flat. -/
class ActsOnRawTermVar (Container : Nat → Nat → Type) where
  /-- Variable lookup — convert a Fin position in the source scope
  to a `RawTerm` value in the target scope.  `RawTerm.var` arm of
  `RawTerm.act` calls this. -/
  varToRawTerm : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      Fin sourceScope → RawTerm targetScope

/-- The generic Tier 3 recursion engine over `RawTerm`.  Single
structural recursion that — once instantiated — replaces the
parallel `RawTerm.rename` and `RawTerm.subst` engines.

For each of the 56 RawTerm constructors:
* Non-binder, non-var arms simply recurse with `someAction`.
* The two binder arms (`lam`, `pathLam`) recurse with
  `Action.liftForRaw someAction`.
* `var` invokes `ActsOnRawTermVar.varToRawTerm`.
* `universeCode` passes through (scope-polymorphic, no Fin payload).

Per `feedback_lean_match_arity_axioms.md`: hoisted Nat indices
(sourceScope, targetScope) keep pattern arity manageable.  Per
`feedback_lean_zero_axiom_match.md` Rule 8: full enumeration of all
56 ctors (no wildcards).

Marked `@[reducible]` so the unifier can chain through definitional
equalities. -/
@[reducible] def RawTerm.act
    {Container : Nat → Nat → Type} [Action Container]
    [ActsOnRawTermVar Container] :
    ∀ {sourceScope targetScope : Nat},
      RawTerm sourceScope →
      Container sourceScope targetScope →
      RawTerm targetScope
  | _, _, .var position, someAction =>
      ActsOnRawTermVar.varToRawTerm someAction position
  | _, _, .unit, _ => .unit
  | _, _, .lam body, someAction =>
      .lam (body.act (Action.liftForRaw someAction))
  | _, _, .app functionTerm argumentTerm, someAction =>
      .app (functionTerm.act someAction) (argumentTerm.act someAction)
  | _, _, .pair firstValue secondValue, someAction =>
      .pair (firstValue.act someAction) (secondValue.act someAction)
  | _, _, .fst pairTerm, someAction => .fst (pairTerm.act someAction)
  | _, _, .snd pairTerm, someAction => .snd (pairTerm.act someAction)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, someAction =>
      .boolElim (scrutinee.act someAction)
                (thenBranch.act someAction)
                (elseBranch.act someAction)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, someAction =>
      .natSucc (predecessor.act someAction)
  | _, _, .natElim scrutinee zeroBranch succBranch, someAction =>
      .natElim (scrutinee.act someAction)
               (zeroBranch.act someAction)
               (succBranch.act someAction)
  | _, _, .natRec scrutinee zeroBranch succBranch, someAction =>
      .natRec (scrutinee.act someAction)
              (zeroBranch.act someAction)
              (succBranch.act someAction)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, someAction =>
      .listCons (headTerm.act someAction) (tailTerm.act someAction)
  | _, _, .listElim scrutinee nilBranch consBranch, someAction =>
      .listElim (scrutinee.act someAction)
                (nilBranch.act someAction)
                (consBranch.act someAction)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, someAction =>
      .optionSome (valueTerm.act someAction)
  | _, _, .optionMatch scrutinee noneBranch someBranch, someAction =>
      .optionMatch (scrutinee.act someAction)
                   (noneBranch.act someAction)
                   (someBranch.act someAction)
  | _, _, .eitherInl valueTerm, someAction =>
      .eitherInl (valueTerm.act someAction)
  | _, _, .eitherInr valueTerm, someAction =>
      .eitherInr (valueTerm.act someAction)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, someAction =>
      .eitherMatch (scrutinee.act someAction)
                   (leftBranch.act someAction)
                   (rightBranch.act someAction)
  | _, _, .refl rawWitness, someAction =>
      .refl (rawWitness.act someAction)
  | _, _, .idJ baseCase witness, someAction =>
      .idJ (baseCase.act someAction) (witness.act someAction)
  | _, _, .modIntro inner, someAction =>
      .modIntro (inner.act someAction)
  | _, _, .modElim inner, someAction =>
      .modElim (inner.act someAction)
  | _, _, .subsume inner, someAction =>
      .subsume (inner.act someAction)
  -- D1.6 cubical interval + path
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp intervalTerm, someAction =>
      .intervalOpp (intervalTerm.act someAction)
  | _, _, .intervalMeet leftInterval rightInterval, someAction =>
      .intervalMeet (leftInterval.act someAction)
                    (rightInterval.act someAction)
  | _, _, .intervalJoin leftInterval rightInterval, someAction =>
      .intervalJoin (leftInterval.act someAction)
                    (rightInterval.act someAction)
  | _, _, .pathLam body, someAction =>
      .pathLam (body.act (Action.liftForRaw someAction))
  | _, _, .pathApp pathTerm intervalArg, someAction =>
      .pathApp (pathTerm.act someAction) (intervalArg.act someAction)
  | _, _, .glueIntro baseValue partialValue, someAction =>
      .glueIntro (baseValue.act someAction) (partialValue.act someAction)
  | _, _, .glueElim gluedValue, someAction =>
      .glueElim (gluedValue.act someAction)
  | _, _, .transp path source, someAction =>
      .transp (path.act someAction) (source.act someAction)
  | _, _, .hcomp sides cap, someAction =>
      .hcomp (sides.act someAction) (cap.act someAction)
  -- D1.6 observational + strict equality
  | _, _, .oeqRefl witness, someAction =>
      .oeqRefl (witness.act someAction)
  | _, _, .oeqJ baseCase witness, someAction =>
      .oeqJ (baseCase.act someAction) (witness.act someAction)
  | _, _, .oeqFunext pointwiseEquality, someAction =>
      .oeqFunext (pointwiseEquality.act someAction)
  | _, _, .idStrictRefl witness, someAction =>
      .idStrictRefl (witness.act someAction)
  | _, _, .idStrictRec baseCase witness, someAction =>
      .idStrictRec (baseCase.act someAction) (witness.act someAction)
  -- D1.6 type equivalence
  | _, _, .equivIntro forwardFn backwardFn, someAction =>
      .equivIntro (forwardFn.act someAction) (backwardFn.act someAction)
  | _, _, .equivApp equivTerm argument, someAction =>
      .equivApp (equivTerm.act someAction) (argument.act someAction)
  -- D1.6 refinement / record / codata
  | _, _, .refineIntro rawValue predicateProof, someAction =>
      .refineIntro (rawValue.act someAction) (predicateProof.act someAction)
  | _, _, .refineElim refinedValue, someAction =>
      .refineElim (refinedValue.act someAction)
  | _, _, .recordIntro firstField, someAction =>
      .recordIntro (firstField.act someAction)
  | _, _, .recordProj recordValue, someAction =>
      .recordProj (recordValue.act someAction)
  | _, _, .codataUnfold initialState transition, someAction =>
      .codataUnfold (initialState.act someAction) (transition.act someAction)
  | _, _, .codataDest codataValue, someAction =>
      .codataDest (codataValue.act someAction)
  -- D1.6 sessions, effects
  | _, _, .sessionSend channel payload, someAction =>
      .sessionSend (channel.act someAction) (payload.act someAction)
  | _, _, .sessionRecv channel, someAction =>
      .sessionRecv (channel.act someAction)
  | _, _, .effectPerform operationTag arguments, someAction =>
      .effectPerform (operationTag.act someAction) (arguments.act someAction)
  -- D1.6/A2: universeCode is scope-polymorphic — act is identity on
  -- the inner-level payload (no Fin variables to remap).
  | _, _, .universeCode innerLevel, _ =>
      .universeCode innerLevel

end LeanFX2
