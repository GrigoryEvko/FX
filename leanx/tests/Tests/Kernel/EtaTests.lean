import FX.Kernel.Term
import FX.Kernel.Substitution
import FX.Kernel.Conversion
import FX.Kernel.Context

/-!
# Pi-η conversion tests (A6, Appendix H.9)

Compile-time tests for the η-equivalence arms added to `convEq`:

    λ x. f x  ≡  f        (when `f` does not mention `x`)

## De Bruijn convention recap

Inside a lambda `λ x. body`, the body is one level deeper:

  * `var 0` in body = the lambda's own binder (x)
  * `var 1` in body = whatever was `var 0` outside
  * `var n` in body = whatever was `var (n-1)` outside

For η to fire on `λ x. body`, the body must be `app headF (var 0)`
where `headF` does NOT mention `var 0` (the new binder).  When
that holds, `etaUnshift?` returns `headF` with every free var
decremented by 1 — mapping back to the outer scope's `f`.

So a test fixture like "`λ x. outerVar0 x`" has body
`app (var 1) (var 0)` — `var 1` is the outer `var 0` seen from
inside the lambda, and `var 0` is the binder.

## Sections

 1. `mentionsVar` — the free-variable probe.
 2. `etaUnshift?` — the helper that recognises the η body shape.
 3. `convEq` η on the left (lam vs non-lam).
 4. `convEq` η on the right (non-lam vs lam).
 5. η failure cases.
 6. Interaction with β — a β-redex reducing to an η-redex.
 7. (lam, lam) stays strict — η does NOT bridge annotation
    mismatches.
-/

namespace Tests.Kernel.EtaTests

open FX.Kernel
open FX.Kernel.Term

/-! ## Fixtures -/

def typeZero : Term := .type .zero
def typeOne  : Term := .type (.succ .zero)
def unitType : Term := .ind "Unit" []
def unitStar : Term := .ctor "Unit" 0 [] []

/-- At outer scope, `var 0` is some free variable — call it `f`.
    When we put this inside a `λ x. _` body, the reference to
    outer `f` is written `var 1` (shifted because we crossed
    one binder). -/
def outerFAtOuter : Term := .var 0          -- outer scope
def outerFAtInner : Term := .var 1          -- inside one lam

/-- `λ x. (outer f) x` — the canonical η-redex: body is
    `app (var 1) (var 0)`, where `var 1` references outer `f`
    and `var 0` is the binder. -/
def etaRedex : Term :=
  .lam Grade.default unitType
    (.app outerFAtInner (.var 0))

/-- Context that makes `var 0` (the "outer f") well-typed as
    a Pi from `Unit` to `Unit`.  Used to type-check fixtures
    whose outer var reaches into context. -/
def piUnitUnit : Term := .piTot Grade.default unitType unitType

/-! ## 1. mentionsVar probes free-variable occurrences -/

-- A bare var mentions only its own index.
example : Term.mentionsVar 0 (.var 0) = true  := by native_decide
example : Term.mentionsVar 0 (.var 1) = false := by native_decide
example : Term.mentionsVar 3 (.var 3) = true  := by native_decide

-- Under a lambda, the target increments.
example :
  Term.mentionsVar 0 (.lam Grade.default typeZero (.var 1)) = true := by
  native_decide
example :
  Term.mentionsVar 0 (.lam Grade.default typeZero (.var 0)) = false := by
  native_decide
example :
  Term.mentionsVar 0 (.lam Grade.default typeZero
    (.lam Grade.default typeZero (.var 2))) = true := by
  native_decide

-- App spreads to both sub-terms.
example :
  Term.mentionsVar 0 (.app (.var 0) (.var 5)) = true := by native_decide
example :
  Term.mentionsVar 0 (.app (.var 5) (.var 0)) = true := by native_decide
example :
  Term.mentionsVar 0 (.app (.var 5) (.var 7)) = false := by native_decide

-- Types / consts / ground ctors never mention anything.
example : Term.mentionsVar 0 typeZero = false := by native_decide
example : Term.mentionsVar 0 (.const "whatever") = false := by native_decide
example : Term.mentionsVar 0 unitStar = false := by native_decide

-- Inductive sub-term lists carry var refs through.
example :
  Term.mentionsVar 0 (.ind "T" [.var 0]) = true := by native_decide
example :
  Term.mentionsVar 0 (.ind "T" [.var 1]) = false := by native_decide

-- Id / refl / idJ / Quot forms all propagate to sub-terms.
example :
  Term.mentionsVar 0 (.id typeZero (.var 0) typeZero) = true := by native_decide
example :
  Term.mentionsVar 0 (.refl (.var 0)) = true := by native_decide
example :
  Term.mentionsVar 0 (.idJ (.var 1) (.var 0) (.var 2)) = true := by native_decide
example :
  Term.mentionsVar 0 (.quotLift (.var 0) typeZero typeZero) = true := by
  native_decide

/-! ## 2. etaUnshift? recognises the η body shape

The body's trailing position must be literally `var 0`; the head
must be free of outer `var 0`.  Success case returns the head
with every free var decremented by 1 (mapping back to outer
scope).

`Term` has `BEq` (via `structEq`) but not `DecidableEq` — the
`Grade` record's `List Provenance` blocks auto-deriving the
latter.  Tests compare results via `==` lifted to `Option`. -/

/-- Compare two `Option Term` values using `structEq` beneath
    the option wrapper. -/
def optTermEq : Option Term → Option Term → Bool
  | some leftTerm, some rightTerm => leftTerm == rightTerm
  | none,          none           => true
  | _,             _              => false

-- Canonical η body: `app (var 1) (var 0)` → unshift to `var 0`.
example :
  optTermEq (Term.etaUnshift? (.app outerFAtInner (.var 0)))
    (some outerFAtOuter) = true := by native_decide

-- Deeper reference: `app (var 3) (var 0)` → unshift to `var 2`.
example :
  optTermEq (Term.etaUnshift? (.app (.var 3) (.var 0)))
    (some (.var 2)) = true := by native_decide

-- Closed head: `app typeZero (var 0)` → some typeZero (no free vars
-- to decrement).
example :
  optTermEq (Term.etaUnshift? (.app typeZero (.var 0)))
    (some typeZero) = true := by native_decide

-- Not the right shape — trailing arg is not var 0.
example :
  optTermEq (Term.etaUnshift? (.app (.var 1) (.var 2))) none = true := by
  native_decide

-- Not the right shape — body is not an app.
example : optTermEq (Term.etaUnshift? (.var 0)) none = true := by native_decide
example : optTermEq (Term.etaUnshift? typeZero) none = true := by native_decide

-- Head captures the binder: `app (var 0) (var 0)` — head mentions
-- var 0, so η fails.
example :
  optTermEq (Term.etaUnshift? (.app (.var 0) (.var 0))) none = true := by
  native_decide

-- Head is a lambda that itself captures the outer binder:
-- `app (λ. var 1) (var 0)`.  Inside the λ, var 1 references the
-- outer binder — the one we're trying to η away.  So the head
-- DOES mention var 0 at our scope (it's var 1 at λ-body scope,
-- which measured at our scope is var 0).
example :
  optTermEq
    (Term.etaUnshift? (.app (.lam Grade.default typeZero (.var 1)) (.var 0)))
    none = true := by native_decide

-- Head is a lambda that doesn't capture: `app (λ. var 0) (var 0)`.
-- The λ's body references its own binder only; no outer capture.
-- η succeeds; head unshifts trivially (no free vars shift).
example :
  optTermEq
    (Term.etaUnshift? (.app (.lam Grade.default typeZero (.var 0)) (.var 0)))
    (some (.lam Grade.default typeZero (.var 0))) = true := by native_decide

/-! ## 3. convEq η on the left — `λ. f x` ≡ `f`

Setup: the context binds one entry (`f : Unit → Unit`), so
`.var 0` is a well-typed free reference at outer scope.  Then
`λ x. f x` (encoded `etaRedex`) η-reduces to `f = .var 0` at
outer scope. -/

-- Canonical Pi-η: lambda on left, free var on right.
example :
  Term.conv etaRedex outerFAtOuter = true := by native_decide

-- η with a const as the head: `λ x. c x` ≡ `c`.
example :
  Term.conv
    (.lam Grade.default unitType (.app (.const "someConst") (.var 0)))
    (.const "someConst") = true := by native_decide

-- η with a deeper var: `λ x. (var 5) x` ≡ `var 4` at outer.
example :
  Term.conv
    (.lam Grade.default unitType (.app (.var 5) (.var 0)))
    (.var 4) = true := by native_decide

/-! ## 4. convEq η on the right — symmetric case -/

-- `f` ≡ `λ x. f x`.
example :
  Term.conv outerFAtOuter etaRedex = true := by native_decide

example :
  Term.conv (.const "c")
    (.lam Grade.default unitType (.app (.const "c") (.var 0))) = true := by
  native_decide

/-! ## 5. η failure cases

These comparisons must return `false` — the lambda doesn't fit
the η shape (or the head captures the binder), and the non-lam
side isn't structurally equal to anything reachable by
alternative means. -/

-- Body is not of `app _ (var 0)` shape (var 0 is not a tail arg).
example :
  Term.conv (.lam Grade.default unitType (.var 0)) outerFAtOuter = false := by
  native_decide

-- Head captures the binder: `λ x. (x) x` ≡ `var 0`?  No.
example :
  Term.conv (.lam Grade.default unitType (.app (.var 0) (.var 0)))
            outerFAtOuter = false := by native_decide

-- Lambda vs a mismatched non-lambda target (not equal post-η).
example :
  Term.conv etaRedex unitStar = false := by native_decide

-- Not a lambda on either side, not structurally equal.
example :
  Term.conv unitStar outerFAtOuter = false := by native_decide

/-! ## 6. β + η interaction

A β-redex on the left that reduces to an η-redex should still
compare equal to the η-reduced head on the right. -/

-- `(λ y. λ x. y x) f` β-reduces to `λ x. f x`, which η-reduces
-- to `f`.  Compare the β-redex form directly with `f`.
example :
  Term.conv
    (.app
      (.lam Grade.default piUnitUnit          -- y : Unit → Unit
        (.lam Grade.default unitType         -- x : Unit
          (.app (.var 1) (.var 0))))          -- y x  ≡  var 1 is y
      outerFAtOuter)
    outerFAtOuter = true := by native_decide

/-! ## 7. (lam, lam) stays strict — η does NOT bridge annotations

Two lambdas with the same η-reduct but different grade
annotations are NOT convertible.  The `(lam, lam)` structural
arm fires before the η arms, and it compares grades pointwise
with no η escape.  (If this started returning `true`, it would
silently admit a soundness hole since grade-differing lambdas
are different values by the §6.2 typing rule.)
-/

-- Two η-redexes with different domain types on the binder.
-- Both η-reduce to the same `var 0` outer free var, but the
-- binder domain differs.  Strict comparison must fail.
example :
  Term.conv
    (.lam Grade.default unitType (.app (.var 1) (.var 0)))   -- λ (_ : Unit). f x
    (.lam Grade.default typeZero (.app (.var 1) (.var 0)))   -- λ (_ : type<0>). f x
    = false := by native_decide

-- Same lambdas with matching annotations DO compare equal
-- (structural, independent of η).
example :
  Term.conv
    (.lam Grade.default unitType (.app (.var 1) (.var 0)))
    (.lam Grade.default unitType (.app (.var 1) (.var 0))) = true := by
  native_decide

end Tests.Kernel.EtaTests
