import FX.Kernel.Reduction
import FX.Kernel.Conversion

/-!
# Reduction tests

Compile-time tests for `betaStep?`, `whnf`, `normalize`.  Only
beta-reduction is active in Phase 2; other redex kinds (iota for
inductives, nu for coinductives, Sigma-split, Id-J, Quot-lift) come
with their corresponding value constructors.

Tests use `Term`'s structural `BEq` (from `Context.lean`)
because `Term` has no `DecidableEq` (blocked by `List Provenance`
recursion in the `Grade` record).  Equality is compared via
`==` returning a `Bool`, then evaluated via `native_decide`.
-/

namespace Tests.Kernel.ReductionTests

open FX.Kernel
open FX.Kernel.Term

def universeZero : Level := .zero
def typeZero : Term := .type universeZero

/-- Term equality as Bool, for use in `native_decide` tests. -/
def termsEq (leftTerm rightTerm : Term) : Bool := leftTerm == rightTerm

/-- Option Term equality as Bool. -/
def optionTermEq (optTerm : Option Term) (expected : Term) : Bool :=
  match optTerm with
  | some actual => actual == expected
  | none        => false

def isOptNone (optTerm : Option Term) : Bool :=
  match optTerm with
  | none   => true
  | some _ => false

/-! ## betaStep? — matches exactly one shape -/

-- Canonical beta-redex: (lambda x. x) T  ⟶  T
example :
  optionTermEq (betaStep? (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero)) typeZero
    = true := by native_decide

-- (lambda _. const) arg → const (arg discarded)
example :
  optionTermEq (betaStep? (Term.app (Term.lam Grade.default typeZero typeZero) (Term.var 5))) typeZero
    = true := by native_decide

-- Non-redex: var alone
example : isOptNone (betaStep? (Term.var 0)) = true := by native_decide

-- Non-redex: type alone
example : isOptNone (betaStep? typeZero) = true := by native_decide

-- Non-redex: lam without application
example : isOptNone (betaStep? (Term.lam Grade.default typeZero typeZero)) = true := by
  native_decide

-- Non-redex: app of var
example :
  isOptNone (betaStep? (Term.app (Term.var 0) (Term.var 1))) = true := by
  native_decide

-- Non-redex: nested — app of app-of-lam isn't a head redex
example :
  isOptNone (betaStep?
    (Term.app (Term.app (Term.lam Grade.default typeZero typeZero) typeZero) typeZero)) = true := by
  native_decide

/-! ## whnf — reduces head, leaves inner alone -/

-- Reduces (lambda x. x) T to T
example :
  termsEq (whnf 10 (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero)) typeZero
    = true := by native_decide

-- Fuel 0 is identity
example :
  termsEq (whnf 0 (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero))
     (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero) = true := by
  native_decide

/-! ## normalize — reduces everywhere -/

example : termsEq (normalize 10 typeZero) typeZero = true := by native_decide

example : termsEq (normalize 10 (Term.var 0)) (Term.var 0) = true := by
  native_decide

-- beta-reduce inside a type application — wrapped in Id as a carrier.
example :
  termsEq (normalize 10
       (Term.id typeZero
         (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero)
         typeZero))
     (Term.id typeZero typeZero typeZero) = true := by native_decide

/-! ## iota-reduction — Nat and Bool eliminators (task A5 Phase-2.2) -/

/-- A trivial motive: `lambda _. Nat`.  Used to test iota on Nat. -/
def motive_NatToNat : Term :=
  Term.lam Grade.default (.ind "Nat" []) (.ind "Nat" [])

def zero : Term := .ctor "Nat" 0 [] []
def succ (predecessor : Term) : Term :=
  .ctor "Nat" 1 [] [predecessor]

-- `indRec "Nat" motive [zero_method, succ_method] zero` → `zero_method`.
-- Here we use `zero` itself as the zero-method and `lambda n rec. succ n`
-- as the succ-method (double of n).  Target is Nat.zero.
example :
  termsEq (whnf 100
       (.indRec "Nat" motive_NatToNat
         [zero,                                         -- zero case
          .lam Grade.default (.ind "Nat" [])            -- n : Nat
            (.lam Grade.default (.ind "Nat" [])         -- rec : Nat
              (succ (.var 1)))]                          -- result = succ(n)
         zero))
     zero = true := by native_decide

-- iota on Nat.succ(zero): the recursor runs the succ-method with
-- n = zero and recResult = (recursive call on zero) = zero,
-- producing succ(zero).
example :
  termsEq (whnf 100
       (.indRec "Nat" motive_NatToNat
         [zero,
          .lam Grade.default (.ind "Nat" [])
            (.lam Grade.default (.ind "Nat" [])
              (succ (.var 1)))]
         (succ zero)))
     (succ zero) = true := by native_decide

/-- Bool eliminator test: `if-else` via `Bool.rec`. -/
def true_ : Term := .ctor "Bool" 1 [] []
def false_ : Term := .ctor "Bool" 0 [] []

-- indRec "Bool" motive [thenMethod, elseMethod] false → elseMethod
-- Wait — the ctor order is [False (idx 0), True (idx 1)].  So methods
-- are [falseMethod, trueMethod].  indRec on False picks idx 0.
example :
  termsEq (whnf 100 (.indRec "Bool" motive_NatToNat [zero, succ zero] false_))
     zero = true := by native_decide

example :
  termsEq (whnf 100 (.indRec "Bool" motive_NatToNat [zero, succ zero] true_))
     (succ zero) = true := by native_decide

/-! ## delta-reduction via @[transparent] (Q41 / Q42)

Per `fx_design.md` §10.15: `@[transparent]` on a `GlobalEntry`
lets `whnf` / `normalize` / `convEq` unfold `.const name` to its
body.  Opaque entries (the default) keep the `.const` head
unchanged.  Contrasting transparent-vs-opaque behavior against
the same body term locks in the invariant. -/

/-- `GlobalEnv` with one entry: `myZero : Nat = Nat.Zero` marked
    transparent.  whnf on `Term.const "myZero"` should unfold
    to `Nat.Zero`. -/
private def transparentEnv : GlobalEnv :=
  GlobalEnv.empty.addDecl "myZero" (.ind "Nat" []) zero (transparent := true)

/-- Same entry but opaque. -/
private def opaqueEnv : GlobalEnv :=
  GlobalEnv.empty.addDecl "myZero" (.ind "Nat" []) zero (transparent := false)

-- Transparent const unfolds to its body at whnf.
example :
  termsEq (whnf 100 (.const "myZero") (globalEnv := transparentEnv)) zero
    = true := by native_decide

-- Opaque const stays as a head `const` — whnf leaves it.
example :
  termsEq (whnf 100 (.const "myZero") (globalEnv := opaqueEnv))
          (.const "myZero") = true := by native_decide

-- Default (empty) env behaves like the opaque case — no unfold.
example :
  termsEq (whnf 100 (.const "myZero")) (.const "myZero") = true := by
  native_decide

-- Unregistered name stays as-is even under a transparent env.
example :
  termsEq (whnf 100 (.const "nowhere") (globalEnv := transparentEnv))
          (.const "nowhere") = true := by native_decide

-- convEq picks up transparency at the convertibility layer.
example :
  convEq 100 (.const "myZero") zero transparentEnv = true := by
  native_decide

example :
  convEq 100 (.const "myZero") zero opaqueEnv = false := by
  native_decide

-- Two distinct consts with identical transparent bodies are
-- convertible — §10.15 reveal behavior at the kernel level.
private def twoTransparentEnv : GlobalEnv :=
  GlobalEnv.empty.addDecl "myZeroA" (.ind "Nat" []) zero (transparent := true)
    |>.addDecl "myZeroB" (.ind "Nat" []) zero (transparent := true)

example :
  convEq 100 (.const "myZeroA") (.const "myZeroB") twoTransparentEnv
    = true := by native_decide

-- Two distinct consts with the same body but one is opaque:
-- convEq cannot see through the opaque side, so they are NOT
-- convertible even though their bodies would be.
private def mixedEnv : GlobalEnv :=
  GlobalEnv.empty.addDecl "myZeroClear" (.ind "Nat" []) zero (transparent := true)
    |>.addDecl "myZeroSealed" (.ind "Nat" []) zero (transparent := false)

example :
  convEq 100 (.const "myZeroClear") (.const "myZeroSealed") mixedEnv
    = false := by native_decide

-- Two opaque consts with the same name ARE convertible (name-equality
-- arm matches even when both sides are stuck).
example :
  convEq 100 (.const "myZero") (.const "myZero") opaqueEnv = true := by
  native_decide

/-! ## Substitution-visible beta

The identity-lambda beta `(λx. x) arg → arg` passes under any
implementation that "just returns its argument" — weak test.
These tests use non-identity lambda bodies so a broken `subst`
that dropped the replacement, or a broken `whnf` that returned
the argument unchanged, would produce distinguishable output.
-/

def typeOne : Term := .type (.succ .zero)

-- Body is a type-former mentioning var 0.  After beta with arg =
-- typeOne, the binder slot becomes typeOne, and the codomain
-- `type 0` (no vars) stays put.  A broken subst that "forgot" the
-- replacement would leave `var 0` in the result.
example :
  termsEq (whnf 10
    (.app (.lam Grade.default typeZero
             (.piTot Grade.default (.var 0) (.type .zero)))
           typeOne))
    (.piTot Grade.default typeOne (.type .zero)) = true := by native_decide

-- Body uses var 0 twice — substitution must visit both positions.
-- `(λx. pi _ (var 0) (var 0)) typeOne → pi _ typeOne typeOne_shifted`.
-- The codomain's `var 0` sits UNDER pi's binder so it stays as
-- inner var (unchanged).  Only the domain's var 0 gets replaced.
-- A broken subst that missed the non-top-level occurrence would
-- still produce the wrong result.
example :
  termsEq (whnf 10
    (.app (.lam Grade.default typeZero
             (.piTot Grade.default (.var 0) (.var 0)))
           typeOne))
    (.piTot Grade.default typeOne (.var 0)) = true := by native_decide

-- Argument discarded — binder unused in body.  `(λ_. typeOne) X = typeOne`
-- regardless of X.  Distinguishes correct beta from "returns arg"
-- broken implementation.
example :
  termsEq (whnf 10
    (.app (.lam Grade.default typeZero typeOne) zero))
    typeOne = true := by native_decide

-- Arg is used — `(λx. x) typeOne = typeOne` (not typeZero).
-- Using distinct values here is critical: a broken whnf that
-- returned `typeZero` on every beta would pass a typeZero→typeZero
-- test but fails this one.
example :
  termsEq (whnf 10
    (.app (.lam Grade.default typeZero (.var 0)) typeOne))
    typeOne = true := by native_decide

/-! ## iota-Id — J eliminator on refl (§H.6)

`idJ motive base (refl witness) → app base witness`.  The motive
and Id-type annotations are discarded on the reduct per
§31 H.6.  Tested here via both `betaStep?` (direct one-step
pattern) and `whnf` (which reduces eqProof first).
-/

-- Direct iota-Id via betaStep? — eqProof is already refl.
example :
  optionTermEq
    (betaStep?
      (.idJ (.lam Grade.default typeZero typeZero)  -- motive
            (.lam Grade.default typeZero zero)       -- base
            (.refl typeOne)))                        -- eqProof = refl typeOne
    (.app (.lam Grade.default typeZero zero) typeOne) = true := by native_decide

-- whnf should reach the same reduct — the target-position whnf
-- doesn't change refl (it's already a value).  Then iota-Id fires.
example :
  termsEq
    (whnf 10
      (.idJ (.lam Grade.default typeZero typeZero)
            (.lam Grade.default typeZero (.var 0))
            (.refl typeOne)))
    typeOne = true := by native_decide

-- Negative: eqProof is NOT refl → betaStep? returns none.  A
-- broken iota that fires on non-refl eqProofs would fail here.
example :
  isOptNone
    (betaStep?
      (.idJ (.lam Grade.default typeZero typeZero)
            (.lam Grade.default typeZero zero)
            (.var 7))) = true := by native_decide

/-! ## iota-Quot — Quot.lift on quotMk (§H.7)

`quotLift lifted respects (quotMk _ witness) → app lifted witness`.
The relation and respects-proof are discarded.
-/

-- Direct iota-Quot via betaStep?.
example :
  optionTermEq
    (betaStep?
      (.quotLift
        (.lam Grade.default typeZero zero)       -- lifted
        (.lam Grade.default typeZero typeZero)   -- respects (unused)
        (.quotMk (.lam Grade.default typeZero typeZero) typeOne)))
    (.app (.lam Grade.default typeZero zero) typeOne) = true := by native_decide

-- whnf chain through iota-Quot then inner beta.
example :
  termsEq
    (whnf 10
      (.quotLift
        (.lam Grade.default typeZero (.var 0))
        (.lam Grade.default typeZero typeZero)
        (.quotMk (.lam Grade.default typeZero typeZero) typeOne)))
    typeOne = true := by native_decide

-- Negative: target is NOT quotMk → no reduction.
example :
  isOptNone
    (betaStep?
      (.quotLift
        (.lam Grade.default typeZero zero)
        (.lam Grade.default typeZero typeZero)
        (.var 3))) = true := by native_decide

/-! ## whnf vs normalize distinction

whnf reduces the HEAD only — a redex inside a ctor's argument
stays if the ctor is at the head.  normalize reduces everywhere.
A broken whnf that naively recursed everywhere, or a broken
normalize that only touched the head, would fail to distinguish.
-/

-- redex inside a ctor argument: `succ ((λx. x) zero)`
-- whnf: succ is head, argument untouched → succ ((λx. x) zero)
-- normalize: inner beta fires → succ zero
def redexInsideCtor : Term :=
  succ (.app (.lam Grade.default (.ind "Nat" []) (.var 0)) zero)

-- whnf leaves the inner redex alone.
example :
  termsEq (whnf 10 redexInsideCtor) redexInsideCtor = true := by native_decide

-- normalize reduces the inner redex.
example :
  termsEq (normalize 10 redexInsideCtor) (succ zero) = true := by native_decide

-- redex inside a lam domain: `λ(x : (λy. y) typeZero). typeZero`
-- whnf: lam is head, body and domain untouched (lam is a value).
-- normalize: reduces inside the domain.
def redexInsideLamDomain : Term :=
  .lam Grade.default
    (.app (.lam Grade.default typeOne (.var 0)) typeZero)
    typeZero

example :
  termsEq (whnf 10 redexInsideLamDomain) redexInsideLamDomain = true := by
  native_decide

example :
  termsEq (normalize 10 redexInsideLamDomain)
    (.lam Grade.default typeZero typeZero) = true := by native_decide

/-! ## Fuel exhaustion — partial reduction

whnf's fuel decrements on both the function-normalization step
and the beta step.  A chain that needs multiple fuel units can
partially reduce and return an intermediate form when fuel runs
out.  `whnf 0` as identity is tested elsewhere; these tests
verify fuel > 0 with insufficient fuel for full reduction.
-/

-- Chain: `(λ_. λx. x) Y X` — outer lam (`_` binder unused)
-- applied to Y, then the result (identity) applied to X.
-- Needs at least 2 beta steps to reach X.
def nestedBetaChain : Term :=
  .app
    (.app
      (.lam Grade.default typeZero
        (.lam Grade.default typeZero (.var 0)))
      typeOne)
    zero

-- fuel 0: no reduction.
example :
  termsEq (whnf 0 nestedBetaChain) nestedBetaChain = true := by native_decide

-- fuel sufficient: reduces to the innermost arg (zero).
example :
  termsEq (whnf 10 nestedBetaChain) zero = true := by native_decide

/-! ## Stuck-head apps

`app` where the head isn't a redex-producing form stays as-is.
Verifies that whnf reduces only when a reduction rule fires.
-/

-- `app (var 0) arg` — head is a free var, stuck.
example :
  termsEq (whnf 10 (.app (.var 0) typeZero))
          (.app (.var 0) typeZero) = true := by native_decide

-- `app (type _) arg` — head is a type-former (never reduces).
example :
  termsEq (whnf 10 (.app typeOne typeZero))
          (.app typeOne typeZero) = true := by native_decide

-- `app (ctor ...) arg` — head is a ctor (a value, not a function).
example :
  termsEq (whnf 10 (.app zero typeZero))
          (.app zero typeZero) = true := by native_decide

/-! ## indRec with stuck target — returns neutral form

When target reduces to a non-ctor (e.g., a var or an irreducible
app), iota can't fire and indRec stays in its neutral form.
-/

-- Target is a free var — iota stuck.
example :
  termsEq (whnf 10
    (.indRec "Nat" motive_NatToNat [zero, succ zero] (.var 7)))
    (.indRec "Nat" motive_NatToNat [zero, succ zero] (.var 7)) = true := by
  native_decide

/-! ## ν-reduction — coinductives (A5 / H.5)

Observing a destructor on an unfold fires the matching arm.
Mirrors the iota-Ind pattern: spec name must match, arm index
must be in bounds, else the term stays stuck.  The CoindSpec
registry isn't consulted at reduction time — spec-name
alignment is a defensive check identical to `iotaStep?`'s
`ctorTypeName != specName` guard.
-/

-- Canonical ν-redex: destruct #0 on unfold [typeZero; typeOne]
-- reduces to the head arm (typeZero).
example :
  termsEq
    (whnf 10 (.coindDestruct "Stream" 0
      (.coindUnfold "Stream" [] [typeZero, typeOne])))
    typeZero = true := by native_decide

-- destruct #1 reduces to the second arm.
example :
  termsEq
    (whnf 10 (.coindDestruct "Stream" 1
      (.coindUnfold "Stream" [] [typeZero, typeOne])))
    typeOne = true := by native_decide

-- betaStep? on a direct ν-redex returns the matching arm.
example :
  optionTermEq
    (betaStep? (.coindDestruct "Stream" 0
      (.coindUnfold "Stream" [] [typeZero, typeOne])))
    typeZero = true := by native_decide

-- betaStep? on destruct-of-non-unfold returns none (target stuck).
example :
  isOptNone (betaStep? (.coindDestruct "Stream" 0 (.var 3))) = true := by
  native_decide

/-! ### Spec-name mismatch — ν stays stuck

The iota pattern: an eliminator against a constructor from a
DIFFERENT spec doesn't fire.  Same here: destructor names its
target's spec, and a mismatch leaves the term as a stuck
elimination rather than silently picking the wrong arm.
-/

-- destruct "Stream" applied to an unfold of "OtherCoind" — stays stuck.
example :
  let tm := Term.coindDestruct "Stream" 0
    (.coindUnfold "OtherCoind" [] [typeZero, typeOne])
  termsEq (whnf 10 tm) tm = true := by native_decide

-- nuStep? returns none on spec-name mismatch.
example :
  isOptNone
    (nuStep? "Stream" 0
      (.coindUnfold "OtherCoind" [] [typeZero, typeOne]))
    = true := by native_decide

/-! ### Index out of bounds — ν stays stuck

Defensive against hand-built ill-typed terms.  The real
protection is typing-layer arm-count verification at S6
elimination rule, but the reducer must not crash when the
typechecker hasn't (yet) weighed in.
-/

-- destruct #5 on an unfold with only 2 arms — stays stuck.
example :
  let tm := Term.coindDestruct "Stream" 5
    (.coindUnfold "Stream" [] [typeZero, typeOne])
  termsEq (whnf 10 tm) tm = true := by native_decide

-- nuStep? returns none on index overflow.
example :
  isOptNone
    (nuStep? "Stream" 5 (.coindUnfold "Stream" [] [typeZero, typeOne]))
    = true := by native_decide

-- nuStep? returns none on target not being an unfold (free var).
example :
  isOptNone (nuStep? "Stream" 0 (.var 7)) = true := by native_decide

/-! ### ν composes with β — destructor of beta-applied unfold

`whnf` reduces the target to whnf before attempting ν.  So a
destructor observing the result of `(λ_. unfold ...) T` first
β-reduces the application, then ν-reduces against the exposed
unfold.  Verifies the dispatch order is correct.
-/

-- `coindDestruct 0 ((λ_. unfold [typeZero, typeOne]) T)` reduces
-- first via β (body = unfold), then via ν (#0 = typeZero).
example :
  let body := Term.coindUnfold "Stream" [] [typeZero, typeOne]
  let betaApp := Term.app (Term.lam Grade.default typeZero body) typeZero
  termsEq (whnf 20 (.coindDestruct "Stream" 0 betaApp)) typeZero = true := by
  native_decide

-- Same composition but selecting the tail arm.
example :
  let body := Term.coindUnfold "Stream" [] [typeZero, typeOne]
  let betaApp := Term.app (Term.lam Grade.default typeZero body) typeZero
  termsEq (whnf 20 (.coindDestruct "Stream" 1 betaApp)) typeOne = true := by
  native_decide

/-! ### normalize descends into unfold arms

Unfold in whnf is itself a value form (no destructor wraps it).
`normalize` recurses into every arm to surface nested redexes.
Verifies: an unfold whose first arm contains a β-redex has the
redex reduced AFTER normalize, but the outer unfold structure
stays intact.
-/

-- normalize reduces `(λ_. typeOne) typeZero` inside an unfold arm.
example :
  let innerBeta := Term.app (Term.lam Grade.default typeZero typeOne) typeZero
  let before := Term.coindUnfold "Stream" [] [innerBeta, typeZero]
  let after  := Term.coindUnfold "Stream" [] [typeOne, typeZero]
  termsEq (normalize 20 before) after = true := by native_decide

/-! ### Stuck destructor on a non-unfold — normalize still descends

A `coindDestruct` that can't ν-reduce (target isn't an unfold)
stays in destruct form, but `normalize` recurses into the target
to reduce whatever's inside.  Verifies the fallback `.coindDestruct`
arm in `normalize` preserves the elim shape and descends.
-/

-- normalize on `destruct (var 7)` — target is free var, stays stuck.
example :
  let tm := Term.coindDestruct "Stream" 0 (.var 7)
  termsEq (normalize 10 tm) tm = true := by native_decide

-- normalize on `destruct ((λ_. var 5) T)` — β-reduces the target to
-- (var 5) but the destructor stays stuck (not an unfold).
example :
  let targetBeta := Term.app (Term.lam Grade.default typeZero (.var 5)) typeZero
  let before := Term.coindDestruct "Stream" 0 targetBeta
  let after  := Term.coindDestruct "Stream" 0 (.var 4)  -- subst decrements
  termsEq (normalize 20 before) after = true := by native_decide

end Tests.Kernel.ReductionTests
