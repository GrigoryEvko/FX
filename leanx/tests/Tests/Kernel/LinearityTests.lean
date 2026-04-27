import FX.Kernel.Term
import FX.Kernel.Typing
import FX.Kernel.Substitution

/-!
# Linearity enforcement tests — Pi-intro exit check (M001)

The Pi-intro rule's exit check (§6.2, §27.1) verifies that a
binder's runtime usage in the body does not exceed its declared
grade.  Implemented as `countVarAt 0 bodyTerm` compared against
`binderGrade.usage` via the Usage lattice's `LessEq`.

## Test structure

  * `countVarAt` arithmetic — small-term counting in isolation.
  * Positive cases — well-linear programs type-check.
  * Negative cases — linear overuse yields `M001`.
  * Ghost and unrestricted cases — grade 0 and grade omega
    binders behave as expected.
-/

namespace Tests.Kernel.LinearityTests

open FX.Kernel
open FX.Kernel.Term

def typeZero : Term := .type .zero
def natType : Term := .ind "Nat" []

/-! ## 1. `countVarAt` small-term arithmetic -/

-- Direct var reference.
example : countVarAt 0 (.var 0) = Usage.one  := by native_decide
example : countVarAt 0 (.var 1) = Usage.zero := by native_decide
example : countVarAt 3 (.var 3) = Usage.one  := by native_decide

-- Type-former subterms erase to zero.
example : countVarAt 0 (.type .zero) = Usage.zero := by native_decide
example : countVarAt 0 (.piTot Grade.default (.var 0) (.var 0)) = Usage.zero := by
  native_decide
example : countVarAt 0 (.sigma Grade.default (.var 0) (.var 0)) = Usage.zero := by
  native_decide
example : countVarAt 0 (.id (.var 0) (.var 0) (.var 0)) = Usage.zero := by
  native_decide

-- app — sequential sum.
example : countVarAt 0 (.app (.var 0) (.var 0)) = Usage.omega := by native_decide
example : countVarAt 0 (.app (.var 0) (.var 1)) = Usage.one   := by native_decide
example : countVarAt 0 (.app (.var 1) (.var 1)) = Usage.zero  := by native_decide

-- lam — domain erases, body shifts.
example :
  countVarAt 0 (.lam Grade.default typeZero (.var 0)) = Usage.zero := by
  native_decide
example :
  countVarAt 0 (.lam Grade.default typeZero (.var 1)) = Usage.one := by
  native_decide

-- forallLevel — body traverses, no term-var shift (level binder is orthogonal).
example : countVarAt 0 (.forallLevel (.var 0)) = Usage.one := by native_decide

/-! ## 2. Positive — well-linear programs type-check

Basic identity at a concrete type: `λ (x :_1 Type<0>). x`. -/

example :
  (Term.infer [] (.lam Grade.default typeZero (.var 0))).isOk = true := by
  native_decide

-- Identity at a different type.
example :
  (Term.infer [] (.lam Grade.default natType (.var 0))).isOk = true := by
  native_decide

/-! ## 3. Negative — linear overuse yields `M001`

A linear function binder used twice triggers M001.  Using
`λ (f :_1 Nat → Nat). f(f(Zero))` so the body type-checks
(`app` wants a Pi-typed head) and reaches the exit check.
-/

def natToNat : Term := .piTot Grade.default natType natType
def natZero  : Term := .ctor "Nat" 0 [] []

/-- Helper: true iff `infer` rejected with error code `M001`. -/
def inferFailsM001 (term : Term) : Bool :=
  match Term.infer [] term with
  | .error typeError => typeError.code == "M001"
  | .ok _            => false

-- `λ (f :_1 Nat → Nat). f(f(Zero))` — f used twice.
example :
  inferFailsM001
    (.lam Grade.default natToNat
      (.app (.var 0) (.app (.var 0) natZero))) = true := by
  native_decide

-- The Atkey-2018 witness shape: `λ (f :_1 Nat → Nat). λ (x :_1 Nat). f(f(x))`
-- The outer `f` is used twice in the inner lam's body, triggering
-- M001 at the OUTER lam's exit check.
example :
  inferFailsM001
    (.lam Grade.default natToNat
      (.lam Grade.default natType
        (.app (.var 1) (.app (.var 1) (.var 0))))) = true := by
  native_decide

/-! ## 4. Ghost (grade 0) — no runtime usage allowed

A `ghost` binder used at runtime (in a term position) triggers
M001 because `Usage.one ≤ Usage.zero` is false.  Used in a
type position, it erases and is fine. -/

-- Ghost used in a type position (domain of inner lam) — OK.
example :
  (Term.infer [] (.lam Grade.ghost typeZero
                    (.lam Grade.default (.var 0) (.var 0)))).isOk = true := by
  native_decide

-- Ghost used in a term position — M001.
example :
  inferFailsM001 (.lam Grade.ghost typeZero (.var 0)) = true := by
  native_decide

/-! ## 5. Unrestricted (omega) — any count is fine

An `@[copy]` / unrestricted binder can be used any number of
times.  `Usage.leBool x omega` is always true. -/

def unrestrictedGrade : Grade := { Grade.default with usage := Usage.omega }

-- Unrestricted used twice — fine (`Usage.omega ≤ omega`).
example :
  (Term.infer []
    (.lam unrestrictedGrade natToNat
      (.app (.var 0) (.app (.var 0) natZero)))).isOk = true := by
  native_decide

-- Unrestricted used zero times — also fine (no M002 at Phase-2).
example :
  (Term.infer []
    (.lam unrestrictedGrade natType natZero)).isOk = true := by
  native_decide

/-! ## 6. Branch-arm JOIN semantics

Pattern-matching on a Nat-like value where the binder appears
once in each arm should count as ONE use (JOIN), not two (SUM).
This mirrors the elaborator's `match` → `indRec` translation.

A simulated shape: `λ (m :_1 Nat). indRec Nat motive [m, m] (var 0)`
— "return m whether the Nat is Zero or Succ".  Expected: count
is `one` (each arm contributes one; join), not `omega`. -/

-- Fake motive: not dependent, just returns Nat.
def natMotive : Term :=
  .lam Grade.default natType (.ind "Nat" [])

-- The scrutinee target is a Nat, which we represent as var 1
-- (since the outer lam binds m at index 0, and we need something
-- of type Nat at the target position — use a ghost body that
-- matches on itself).  Simplified: bind m and scrutinize m too
-- (so var 0 is both the match result and scrutinee target).
-- Expected count: methods join to one, plus target one = omega.
-- This WILL trigger M001 because the scrutinee position is
-- sequential use.  That's correct: scrutinizing consumes once,
-- using in an arm consumes once, total two.

-- Simpler positive: just the JOIN behavior, via countVarAt alone.
example :
  countVarAt 0
    (.indRec "Nat" natMotive
      [.var 0, .lam Grade.default natType (.lam Grade.default natType (.var 2))]
      (.var 1))
  = Usage.one := by native_decide

-- Where the same structure with plain sum would be omega.
-- Two arms each using var 0 once, joined = one.
example :
  countVarAtJoinList 0 [.var 0, .var 0] = Usage.one := by native_decide

-- While sum-list counts them separately.
example :
  countVarAtList 0 [.var 0, .var 0] = Usage.omega := by native_decide

end Tests.Kernel.LinearityTests
