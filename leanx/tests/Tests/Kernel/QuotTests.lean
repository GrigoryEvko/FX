import FX.Kernel.Term
import FX.Kernel.Typing
import FX.Kernel.Reduction
import FX.Kernel.Conversion
import FX.Kernel.Substitution
import FX.Kernel.Context

/-!
# Quot introduction + elimination tests (A4, H.7)

Compile-time tests for the two new Quot term forms:

  * `quotMk relation witness` — Quot-intro.  `quotMk R w` has
    type `Quot T R` where `T` is the synthesized type of `w`.
    The relation `R` is stored on the value.
  * `quotLift lifted respects target` — Quot.lift (fully applied).
    Given `target : Quot T R` and `lifted : T → U`, typing
    returns `openWith target (codomain of lifted)`.  Reduction
    discharges `quotLift f _ (quotMk _ w)` to `app f w`.

Sections:

 1. `structEq` distinguishes quotMk / quotLift by their payloads.
 2. `shift` / `subst` traverse both new constructors.
 3. `quotLiftStep?` returns `some (app lifted w)` only for
    `quotMk`-tipped targets.
 4. `whnf` reduces `quotLift f p (quotMk _ w)` and leaves
    non-quotMk targets stuck as `quotLift`.
 5. `normalize` reduces through the iota step.
 6. `convEq` compares both forms pointwise and via iota.
 7. `infer` produces `Quot T R` for `quotMk`, the codomain of
    lifted for `quotLift`, and emits `T010` when the target
    does not have a quotient type.
 8. Rejections — ill-shaped quotLift targets / non-Pi lifted
    functions are typing errors.
-/

namespace Tests.Kernel.QuotTests

open FX.Kernel
open FX.Kernel.Term

/-! ## Fixtures -/

def typeZero : Term := .type .zero
def typeOne  : Term := .type (.succ .zero)

def unitType : Term := .ind "Unit" []
def unitStar : Term := .ctor "Unit" 0 [] []
def natType  : Term := .ind "Nat" []
def natZero  : Term := .ctor "Nat" 0 [] []

/-- A "constant true" relation on `Unit`: `λ _ _. type<0>`.  Its
    type is `Pi _ Unit (Pi _ Unit Type<1>)` — the inferred Pi
    matches the Phase-2 relation shape check (a Pi whose return
    is a type).  We don't actually need the relation to be a
    Prop for Phase 2 — the typing only requires that `infer`
    succeed on it. -/
def trueRel : Term :=
  .lam Grade.default unitType (.lam Grade.default unitType typeZero)

/-- Identity function on Unit: `λ (x : Unit). x` — a non-
    trivial lifted function whose codomain mentions `var 0`.
    Phase 2's `quotLift` typing substitutes the target into the
    codomain slot via `openWith`; for this dependent codomain
    the test expectation is the post-substitution term. -/
def identityLam : Term :=
  .lam Grade.default unitType (.var 0)

/-- Constant lifted function: `λ (_ : Unit). type<0>`.  The
    codomain is free of `var 0`, so `openWith` collapses the
    binder cleanly — the Phase-2 happy-path shape. -/
def constLam : Term :=
  .lam Grade.default unitType typeZero

/-- A "respects" stub — Phase 2 doesn't match the full
    `Π x y. R x y → Id U (f x) (f y)` shape, so we pass any
    type-checkable term.  `typeZero` type-checks (to `Type<1>`)
    and is discarded at reduction time. -/
def trivialRespects : Term := typeZero

/-- `quotMk trueRel unitStar` — an equivalence-class value. -/
def starQuotMk : Term := .quotMk trueRel unitStar

/-! ## 1. structEq -/

example : (Term.quotMk trueRel unitStar == Term.quotMk trueRel unitStar) = true := by
  native_decide
example : (Term.quotMk trueRel unitStar == Term.quotMk trueRel natZero) = false := by
  native_decide
example : (Term.quotMk trueRel unitStar == Term.refl unitStar) = false := by
  native_decide

example :
  (Term.quotLift constLam trivialRespects starQuotMk
    == Term.quotLift constLam trivialRespects starQuotMk) = true := by
  native_decide

example :
  (Term.quotLift constLam trivialRespects starQuotMk
    == Term.quotLift constLam trivialRespects (.quotMk trueRel natZero)) = false := by
  native_decide

/-! ## 2. shift / subst traverse the new constructors -/

example :
  shift 0 1 (Term.quotMk (Term.var 0) (Term.var 1))
    = Term.quotMk (Term.var 1) (Term.var 2) := rfl

example :
  shift 0 1 (Term.quotLift (Term.var 0) (Term.var 1) (Term.var 2))
    = Term.quotLift (Term.var 1) (Term.var 2) (Term.var 3) := rfl

-- shift below the cutoff leaves indices alone.
example :
  shift 5 1 (Term.quotMk (Term.var 3) (Term.var 4))
    = Term.quotMk (Term.var 3) (Term.var 4) := rfl

example :
  subst 0 unitStar (Term.quotMk (Term.var 0) (Term.var 0))
    = Term.quotMk unitStar unitStar := rfl

example :
  subst 0 unitStar (Term.quotLift (Term.var 0) (Term.var 0) (Term.var 0))
    = Term.quotLift unitStar unitStar unitStar := rfl

-- shift_zero corollary — shift by 0 is identity on both forms.
example : shift 0 0 (Term.quotMk trueRel unitStar) = Term.quotMk trueRel unitStar :=
  shift_zero 0 (Term.quotMk trueRel unitStar)

example :
  shift 0 0 (Term.quotLift constLam trivialRespects starQuotMk)
    = Term.quotLift constLam trivialRespects starQuotMk :=
  shift_zero 0 (Term.quotLift constLam trivialRespects starQuotMk)

/-! ## 3. quotLiftStep? — iota helper -/

-- Iota fires when target is a quotMk.
example :
  Term.quotLiftStep? constLam (Term.quotMk trueRel unitStar)
    = some (Term.app constLam unitStar) := rfl

-- Non-quotMk target: no step.
example : Term.quotLiftStep? constLam (Term.var 0) = none := rfl

-- betaStep? routes to the helper.
example :
  betaStep? (Term.quotLift constLam trivialRespects starQuotMk)
    = some (Term.app constLam unitStar) := rfl

-- Non-quotMk target: betaStep? returns none.
example :
  betaStep? (Term.quotLift constLam trivialRespects (Term.var 0)) = none := rfl

/-! ## 4. whnf — reduces Quot.lift-of-quotMk, leaves non-quotMk stuck

`constLam` is `λ (_ : Unit). type<0>`.  Applied to `unitStar`,
it beta-reduces to `type<0>`.  So
`whnf (quotLift constLam _ (quotMk _ unitStar))` should produce
`type<0>` via iota + beta. -/

def termsEq (leftTerm rightTerm : Term) : Bool := leftTerm == rightTerm

example :
  termsEq (whnf 10 (Term.quotLift constLam trivialRespects starQuotMk)) typeZero
    = true := by native_decide

-- Non-quotMk target (a free var): quotLift stays stuck with the
-- target unchanged.
example :
  termsEq (whnf 10 (Term.quotLift constLam trivialRespects (Term.var 0)))
     (Term.quotLift constLam trivialRespects (Term.var 0)) = true := by
  native_decide

-- Fuel 0 returns the term unchanged, even on an iota-redex.
example :
  termsEq (whnf 0 (Term.quotLift constLam trivialRespects starQuotMk))
     (Term.quotLift constLam trivialRespects starQuotMk) = true := by native_decide

-- identityLam: `λ (x : Unit). x` applied to `unitStar` beta-reduces
-- to `unitStar`.  Exercises iota + a non-degenerate beta.
example :
  termsEq (whnf 10 (Term.quotLift identityLam trivialRespects starQuotMk))
    unitStar = true := by native_decide

/-! ## 5. normalize reduces through iota + inside stuck subparts -/

-- Full iota + beta chain on quotLift-of-quotMk.
example :
  termsEq (normalize 10 (Term.quotLift constLam trivialRespects starQuotMk))
    typeZero = true := by native_decide

/-! ## 6. convEq — pointwise and via iota -/

example :
  Term.conv (Term.quotMk trueRel unitStar) (Term.quotMk trueRel unitStar) = true := by
  native_decide

example :
  Term.conv (Term.quotMk trueRel unitStar) (Term.quotMk trueRel natZero) = false := by
  native_decide

-- Quot.lift reducing through iota + beta converts with type<0>.
example :
  Term.conv (Term.quotLift constLam trivialRespects starQuotMk) typeZero = true := by
  native_decide

-- Two quotLift's with identical components convert.
example :
  Term.conv (Term.quotLift constLam trivialRespects starQuotMk)
            (Term.quotLift constLam trivialRespects starQuotMk) = true := by
  native_decide

/-! ## 7. infer — quotMk gives Quot T R; quotLift returns openWith target codomain -/

def inferEq (context : TypingContext) (term expected : Term) : Bool :=
  match Term.infer context term with
  | .ok actual => actual == expected
  | .error _   => false

-- `quotMk trueRel unitStar : Quot Unit trueRel`
example :
  inferEq [] (Term.quotMk trueRel unitStar) (Term.quot unitType trueRel) = true := by
  native_decide

-- `quotMk trueRel natZero : Quot Nat trueRel`
--
-- Note: the relation is not required to be well-typed AT the
-- witness's type for Phase 2 — typing only infers the relation's
-- own type, it doesn't check the relation's domain.  The stored
-- relation is preserved verbatim in the resulting Quot type.
example :
  inferEq [] (Term.quotMk trueRel natZero) (Term.quot natType trueRel) = true := by
  native_decide

-- `quotLift constLam _ (quotMk trueRel unitStar) : type<1>`.
-- `constLam` is `λ (_ : Unit). type<0>`; its inferred Pi type is
-- `Π (_ : Unit). type<1>` (because `type<0> : type<1>`).  Quot.lift
-- returns `openWith target (codomain of the Pi)` = `type<1>`
-- (the codomain is free of var 0, so the substitution collapses
-- cleanly).  This demonstrates that the return type comes from the
-- lifted function's CODOMAIN, not its body.
example :
  inferEq [] (Term.quotLift constLam trivialRespects starQuotMk) typeOne = true := by
  native_decide

/-! ## 8. Rejections -/

def inferErrorCodeIs (expectedCode : String) (term : Term) : Bool :=
  match Term.infer [] term with
  | .error e => e.code == expectedCode
  | .ok _    => false

-- quotLift with a non-Quot target (here: `typeZero`, a universe):
-- T010 ("target must have quotient type").
example :
  inferErrorCodeIs "T010"
    (Term.quotLift constLam trivialRespects typeZero) = true := by native_decide

-- quotLift with a non-Quot target (unit ctor value): T010.
example :
  inferErrorCodeIs "T010"
    (Term.quotLift constLam trivialRespects unitStar) = true := by native_decide

-- quotLift with a non-Pi lifted function: T003
-- ("expected function type").  Use `typeZero` as the lifted
-- arg so its inferred type is `type<1>`, which is NOT a Pi.
example :
  inferErrorCodeIs "T003"
    (Term.quotLift typeZero trivialRespects starQuotMk) = true := by native_decide

end Tests.Kernel.QuotTests
