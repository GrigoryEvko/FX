import FX.Kernel.Term
import FX.Kernel.Typing
import FX.Kernel.Reduction
import FX.Kernel.Conversion
import FX.Kernel.Substitution
import FX.Kernel.Context

/-!
# Id introduction + elimination tests (A3, H.6)

Compile-time tests for the two new Id term forms:

  * `refl witness` — introduction.  Typing gives it
    `Id (typeof witness) witness witness`; the evaluator wraps
    its witness into `Value.reflVal`.
  * `idJ motive base eqProof` — J eliminator.  Typing gives it
    `app (app (app motive lhs) rhs) eqProof` where `eqProof`
    has type `Id _ lhs rhs`.  Reduction discharges
    `idJ motive base (refl witness)` to `app base witness`.

Tests cover, in roughly this order:

 1. `structEq` distinguishes `refl`/`idJ` by their payloads.
 2. `shift` / `subst` traverse both new constructors.
 3. `idJStep?` returns `some (app base witness)` only for
    `refl`-tipped equality proofs.
 4. `whnf` reduces `idJ m b (refl w)` and leaves non-refl eq
    proofs stuck as `idJ`.
 5. `normalize` reduces through the iota step.
 6. `convEq` compares both forms pointwise and via the iota rule.
 7. `infer` produces the expected Id-type for `refl`, propagates
    endpoints into the motive-applied return type for `idJ`, and
    emits `T010` when the eq-proof does not have an Id type.
 8. Rejections — building `idJ` against an ill-typed eq proof
    throws a typing error.
-/

namespace Tests.Kernel.IdTests

open FX.Kernel
open FX.Kernel.Term

/-! ## Canonical fixtures -/

def typeZero : Term := .type .zero
def unitType : Term := .ind "Unit" []
def unitStar : Term := .ctor "Unit" 0 [] []
def natType  : Term := .ind "Nat" []
def natZero  : Term := .ctor "Nat" 0 [] []

/-- Constant motive: ignores all three `(x, y, p)` args, returns
    `type<0>`.  Well-typed without A10's dependent-motive shape
    check because we only `infer` motive, not match its exact
    Pi chain. -/
def constMotive : Term :=
  .lam Grade.default unitType (.lam Grade.default unitType
    (.lam Grade.default (.id unitType (.var 1) (.var 0)) typeZero))

/-- Constant base case: `λ (x : Unit). type<0>`.  Matches the
    shape `Π (x : T). motive x x (refl x)` for this constant
    motive because the motive always returns `type<0>` regardless
    of its arguments. -/
def constBase : Term :=
  .lam Grade.default unitType typeZero

/-- Reflexivity at `Unit.tt`. -/
def starRefl : Term := .refl unitStar

/-! ## 1. structEq -/

example : (Term.refl unitStar == Term.refl unitStar) = true := by native_decide
example : (Term.refl unitStar == Term.refl natZero) = false := by native_decide
example : (Term.refl unitStar == Term.idJ unitStar unitStar unitStar) = false := by
  native_decide

example :
  (Term.idJ constMotive constBase starRefl
    == Term.idJ constMotive constBase starRefl) = true := by native_decide

example :
  (Term.idJ constMotive constBase starRefl
    == Term.idJ constMotive constBase (.refl natZero)) = false := by native_decide

/-! ## 2. shift / subst traverse refl + idJ -/

-- shift rewrites free-var indices inside the witness.
example : shift 0 1 (Term.refl (Term.var 0)) = Term.refl (Term.var 1) := rfl
example : shift 2 3 (Term.refl (Term.var 5)) = Term.refl (Term.var 8) := rfl

-- shift below the cutoff leaves bound vars alone.
example : shift 5 1 (Term.refl (Term.var 3)) = Term.refl (Term.var 3) := rfl

example :
  shift 0 1 (Term.idJ (Term.var 0) (Term.var 1) (Term.var 2))
    = Term.idJ (Term.var 1) (Term.var 2) (Term.var 3) := rfl

-- subst plumbs the replacement through each idJ sub-term.
example :
  subst 0 unitStar (Term.refl (Term.var 0)) = Term.refl unitStar := rfl

example :
  subst 0 unitStar (Term.idJ (Term.var 0) (Term.var 0) (Term.var 0))
    = Term.idJ unitStar unitStar unitStar := rfl

-- shift_zero corollary — applied to refl / idJ, shift by 0 = id.
example : shift 0 0 (Term.refl unitStar) = Term.refl unitStar :=
  shift_zero 0 (Term.refl unitStar)

example :
  shift 0 0 (Term.idJ constMotive constBase starRefl)
    = Term.idJ constMotive constBase starRefl :=
  shift_zero 0 (Term.idJ constMotive constBase starRefl)

/-! ## 3. idJStep? — iota helper

`idJStep? base eqProof` yields `some (app base witness)` when
the proof is `refl witness`, and `none` otherwise. -/

example : Term.idJStep? constBase (Term.refl unitStar)
            = some (Term.app constBase unitStar) := rfl

example : Term.idJStep? constBase (Term.var 0) = none := rfl

-- betaStep? routes the helper.
example :
  betaStep? (Term.idJ constMotive constBase starRefl)
    = some (Term.app constBase unitStar) := rfl

-- Non-reducing eq proof: betaStep? returns none.
example :
  betaStep? (Term.idJ constMotive constBase (Term.var 0)) = none := rfl

/-! ## 4. whnf — reduces idJ-of-refl, leaves non-refl stuck

Applied base is `λ (x : Unit). type<0>`, which whnf then further
beta-reduces to `type<0>`.  This exercises both the Id-iota and
the chained beta. -/

def termsEq (leftTerm rightTerm : Term) : Bool := leftTerm == rightTerm

example :
  termsEq (whnf 10 (Term.idJ constMotive constBase starRefl)) typeZero
    = true := by native_decide

-- Non-refl eq proof: idJ stays stuck with the eq-proof unchanged
-- (it's already a free var, so whnf does nothing to it).
example :
  termsEq (whnf 10 (Term.idJ constMotive constBase (Term.var 0)))
     (Term.idJ constMotive constBase (Term.var 0)) = true := by
  native_decide

-- Fuel 0 returns the term unchanged, even on a J-of-refl.
example :
  termsEq (whnf 0 (Term.idJ constMotive constBase starRefl))
     (Term.idJ constMotive constBase starRefl) = true := by native_decide

/-! ## 5. normalize descends into stuck idJ subparts -/

-- normalize reduces J-of-refl through iota + beta to `type<0>`.
example : termsEq (normalize 10 (Term.idJ constMotive constBase starRefl)) typeZero
    = true := by native_decide

-- refl's witness normalizes along with the wrapper — no beta
-- under the witness in this fixture, but the traversal is
-- covered by the idJ stuck form immediately above.

/-! ## 6. convEq — pointwise and through iota -/

example : Term.conv (Term.refl unitStar) (Term.refl unitStar) = true := by
  native_decide

example : Term.conv (Term.refl unitStar) (Term.refl natZero) = false := by
  native_decide

-- J(motive, base, refl star) converts with type<0> (via iota + beta).
example :
  Term.conv (Term.idJ constMotive constBase starRefl) typeZero = true := by
  native_decide

-- Two idJ's with identical components convert.
example :
  Term.conv (Term.idJ constMotive constBase starRefl)
            (Term.idJ constMotive constBase starRefl) = true := by native_decide

/-! ## 7. infer — refl gives the Id type; idJ gives the applied-motive chain -/

/-- Check `infer context term == expected` as a Bool. -/
def inferEq (context : TypingContext) (term expected : Term) : Bool :=
  match Term.infer context term with
  | .ok actual => actual == expected
  | .error _   => false

-- `refl unitStar : Id Unit Unit.tt Unit.tt`
example :
  inferEq [] (Term.refl unitStar) (Term.id unitType unitStar unitStar) = true := by
  native_decide

-- `refl natZero : Id Nat Nat.Zero Nat.Zero`
example :
  inferEq [] (Term.refl natZero) (Term.id natType natZero natZero) = true := by
  native_decide

-- `idJ motive base (refl unitStar) :
--    app (app (app motive Unit.tt) Unit.tt) (refl unitStar)`
--
-- Typing doesn't reduce the application chain — the syntactic
-- result is exactly the three-fold applied motive.
example :
  inferEq [] (Term.idJ constMotive constBase starRefl)
    (.app (.app (.app constMotive unitStar) unitStar) starRefl) = true := by
  native_decide

/-! ## 8. Rejections -/

/-- Returns true iff `infer` threw a T010 (expected Id in J). -/
def inferFailsT010 (context : TypingContext) (term : Term) : Bool :=
  match Term.infer context term with
  | .error e => e.code == "T010"
  | .ok _    => false

-- idJ with an eq proof of non-Id type (just `type<0>`) → T010.
example :
  inferFailsT010 [] (Term.idJ constMotive constBase typeZero) = true := by
  native_decide

-- idJ with an eq proof of Unit-ctor type (not an Id) → T010.
example :
  inferFailsT010 [] (Term.idJ constMotive constBase unitStar) = true := by
  native_decide

end Tests.Kernel.IdTests
