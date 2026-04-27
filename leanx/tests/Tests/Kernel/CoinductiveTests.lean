import FX.Kernel.Coinductive
import Tests.Framework

/-!
# Coinductive tests — CoindSpec, accessors, guardedness

Covers `FX/Kernel/Coinductive.lean` (task A2):

  * `CoindSpec` accessors (`paramCount`, `destructorCount`,
    `destructorAt?`, `findDestructor?`).
  * `Coinductive.specByName?` returns `none` in Phase-2 (no
    hardcoded codata prelude yet) — pinned so a premature
    wiring breaks this test.
  * `Guarded.absent` — coind-name-absent check with per-Term-
    ctor coverage; a broken walker that short-circuits early is
    caught by both positive (name appears) and negative (name
    absent) witnesses.
  * `Guarded.guardedResultType` / `isSatisfied` — admits the
    canonical `stream.tail : stream<a>` self-reference in
    final-codomain position; rejects self-reference under a
    `pi` domain (contravariant), under nested co-types,
    and via indirect inductive positions.

## Pinning strategy

Each test compares against a CONCRETE value, not `.isSome` /
`≠ none` — so a degenerate implementation that returns any
non-none is caught.  Rejection tests supply at least one
negative witness per Term form the walker recurses into, so
dropping a match arm produces a concrete regression.  The
stream example is built literally in the test (not via
factory functions) to pin the exact data shape the kernel
consumes.
-/

namespace Tests.Kernel.CoinductiveTests

open FX.Kernel
open FX.Kernel.Coinductive
open Tests

/-! ## Phase-2 registry returns none uniformly -/

example : Coinductive.specByName? "stream" = none := by decide
example : Coinductive.specByName? ""        = none := by decide
example : Coinductive.specByName? "Bogus"  = none := by decide

/-! ## Canonical `stream<a>` spec shape

  * params = [Type<0>] — one type parameter `a`
  * destructors: head = var 0 (the `a` param),
                 tail = coind "stream" [var 0]

The `resultType` inside each destructor follows the de Bruijn
convention used everywhere else in the kernel: `var 0` refers
to the sole spec parameter in scope. -/

def streamSpec : CoindSpec :=
  { name        := "stream"
    params      := [Term.type Level.zero]
    destructors := [
      { name := "head", resultType := Term.var 0 },
      { name := "tail", resultType := Term.coind "stream" [Term.var 0] }
    ]
    sized       := true
  }

example : streamSpec.name                = "stream"        := by decide
example : streamSpec.paramCount          = 1               := by decide
example : streamSpec.destructorCount     = 2               := by decide
example : streamSpec.sized               = true            := by decide

example : streamSpec.destructors.map (·.name) = ["head", "tail"] := by decide

example : (streamSpec.destructorAt? 0).map (·.name) = some "head" := by decide
example : (streamSpec.destructorAt? 1).map (·.name) = some "tail" := by decide
example : (streamSpec.destructorAt? 2).map (·.name) = none        := by decide

example : (streamSpec.findDestructor? "head").map Prod.fst = some 0 := by decide
example : (streamSpec.findDestructor? "tail").map Prod.fst = some 1 := by decide
example : streamSpec.findDestructor? "bogus" = none                 := by decide

/-! ## `Guarded.absent` — coverage per Term constructor

Each example witnesses one Term form: the name is either absent
(check returns `true`) or present (check returns `false`).
Dropping any match arm in the walker causes at least one of
these to flip. -/

example : Guarded.absent "stream" (Term.var 0) = true := by decide
example : Guarded.absent "stream" (Term.type Level.zero) = true := by decide
example : Guarded.absent "stream" (Term.const "foo") = true := by decide

-- Direct coind reference present / absent.
example : Guarded.absent "stream" (Term.coind "stream" []) = false := by decide
example : Guarded.absent "stream" (Term.coind "other" []) = true := by decide

-- App — recurses on both sides.
example : Guarded.absent "stream"
    (Term.app (Term.coind "stream" []) (Term.var 0)) = false := by decide
example : Guarded.absent "stream"
    (Term.app (Term.var 0) (Term.coind "stream" [])) = false := by decide
example : Guarded.absent "stream"
    (Term.app (Term.var 0) (Term.var 1)) = true := by decide

-- Pi / lam / sigma — domain and body both visited.
example : Guarded.absent "stream"
    (Term.pi Grade.default (Term.coind "stream" []) (Term.var 0) Effect.tot)
  = false := by decide
example : Guarded.absent "stream"
    (Term.pi Grade.default (Term.var 0) (Term.coind "stream" []) Effect.tot)
  = false := by decide
example : Guarded.absent "stream"
    (Term.lam Grade.default (Term.var 0) (Term.coind "stream" []))
  = false := by decide
example : Guarded.absent "stream"
    (Term.sigma Grade.default (Term.coind "stream" []) (Term.var 0))
  = false := by decide

-- Ind / ctor — self-ref through the type-arg list.
example : Guarded.absent "stream"
    (Term.ind "List" [Term.coind "stream" []]) = false := by decide
example : Guarded.absent "stream"
    (Term.ctor "Pair" 0 [Term.coind "stream" []] [Term.var 0]) = false := by decide
example : Guarded.absent "stream"
    (Term.ctor "Pair" 0 [Term.var 0] [Term.coind "stream" []]) = false := by decide

-- Id / refl / idJ.
example : Guarded.absent "stream"
    (Term.id (Term.coind "stream" []) (Term.var 0) (Term.var 1)) = false := by decide
example : Guarded.absent "stream"
    (Term.refl (Term.coind "stream" [])) = false := by decide
example : Guarded.absent "stream"
    (Term.idJ (Term.coind "stream" []) (Term.var 0) (Term.var 1)) = false := by decide

-- Quot / quotMk / quotLift.
example : Guarded.absent "stream"
    (Term.quot (Term.coind "stream" []) (Term.var 0)) = false := by decide
example : Guarded.absent "stream"
    (Term.quotMk (Term.var 0) (Term.coind "stream" [])) = false := by decide
example : Guarded.absent "stream"
    (Term.quotLift (Term.coind "stream" []) (Term.var 0) (Term.var 1)) = false := by decide

-- forallLevel — body visited.
example : Guarded.absent "stream"
    (Term.forallLevel (Term.coind "stream" [])) = false := by decide
example : Guarded.absent "stream"
    (Term.forallLevel (Term.var 0)) = true := by decide

/-! ## `Guarded.guardedResultType` — accept / reject cases

Canonical acceptance: `stream<a>` in final-codomain position.
Key rejection: `stream<a>` under a left-of-arrow (pi domain).
-/

-- Canonical `head`: resultType is `var 0` — no self-reference, passes.
example : Guarded.guardedResultType "stream" (Term.var 0) = true := by decide

-- Canonical `tail`: resultType is `coind "stream" [var 0]` — legal
-- final-codomain self-reference.
example : Guarded.guardedResultType "stream"
    (Term.coind "stream" [Term.var 0]) = true := by decide

-- Same with more params — still legal at final codomain.
example : Guarded.guardedResultType "stream"
    (Term.coind "stream" [Term.var 0, Term.var 1]) = true := by decide

-- Reject: self-ref under a pi domain (contravariant).
-- A destructor with this resultType would let consumers feed
-- a `stream<a>` INTO this destructor — forbidden.
example : Guarded.guardedResultType "stream"
    (Term.pi Grade.default
      (Term.coind "stream" [Term.var 0])
      (Term.var 0)
      Effect.tot)
  = false := by decide

-- Reject: self-ref nested inside a pi domain's sub-structure.
example : Guarded.guardedResultType "stream"
    (Term.pi Grade.default
      (Term.app (Term.coind "stream" [Term.var 0]) (Term.var 1))
      (Term.var 0)
      Effect.tot)
  = false := by decide

-- Reject: self-ref in codomain's arg where arg itself unguardedly
-- references self inside a pi domain.
example : Guarded.guardedResultType "stream"
    (Term.coind "stream"
      [Term.pi Grade.default (Term.coind "stream" []) (Term.var 0) Effect.tot])
  = false := by decide

-- Accept: a DIFFERENT coind name is unrelated — walker doesn't
-- over-reject on arbitrary coind.
example : Guarded.guardedResultType "stream"
    (Term.coind "other" [Term.var 0]) = true := by decide

/-! ## `Guarded.isSatisfied` — spec-level check

Full `streamSpec` passes.  A tweaked spec where `tail` returns
a pi with stream in the domain must fail.
-/

example : Guarded.isSatisfied streamSpec = true := by decide

def unguardedSpec : CoindSpec :=
  { name        := "bad"
    params      := [Term.type Level.zero]
    destructors := [
      { name := "weird"
        resultType := Term.pi Grade.default
                        (Term.coind "bad" [Term.var 0])
                        (Term.coind "bad" [Term.var 0])
                        Effect.tot
      }
    ]
    sized       := true
  }

example : Guarded.isSatisfied unguardedSpec = false := by decide

/-- A spec with zero destructors vacuously passes guardedness —
    no destructor result type to check.  This is the degenerate
    "unobservable codata" case; whether Phase 6's typing rule
    admits such a spec at the surface is a separate design
    decision (probably requires at least one destructor to be
    useful). -/
def noDestructorSpec : CoindSpec :=
  { name        := "empty_coind"
    params      := []
    destructors := []
  }

example : Guarded.isSatisfied noDestructorSpec = true := by decide

/-! ## Runtime harness

Registered in `tests/Tests/Main.lean` so `lake exe fxi-tests`
exercises these as runtime checks alongside the compile-time
`by decide` proofs above.  All above `example` blocks discharge
at elaboration time; the runtime harness re-asserts the same
facts via `check` so the suite shows up in the test-count
summary and any regression surfaces as a failing check rather
than a silent rebuild. -/

def run : IO Unit := Tests.suite "Tests.Kernel.CoinductiveTests" do
  -- Registry pinning: Phase-2 returns none uniformly.  Uses
  -- `.isNone` so we don't need DecidableEq on CoindSpec (no
  -- Option-level comparison).
  check "stream lookup returns none" true
    (Coinductive.specByName? "stream").isNone
  check "empty lookup returns none"  true
    (Coinductive.specByName? "").isNone
  check "unknown lookup returns none" true
    (Coinductive.specByName? "Bogus").isNone

  -- Stream spec accessor pinning.
  check "streamSpec name" "stream" streamSpec.name
  check "streamSpec paramCount"      1 streamSpec.paramCount
  check "streamSpec destructorCount" 2 streamSpec.destructorCount
  check "streamSpec sized"           true streamSpec.sized
  check "streamSpec destructor names in order"
    ["head", "tail"] (streamSpec.destructors.map (·.name))
  check "streamSpec.destructorAt? 0 name"
    (some "head") ((streamSpec.destructorAt? 0).map (·.name))
  check "streamSpec.destructorAt? 1 name"
    (some "tail") ((streamSpec.destructorAt? 1).map (·.name))
  check "streamSpec.destructorAt? 2 out-of-range"
    (none : Option String) ((streamSpec.destructorAt? 2).map (·.name))
  check "findDestructor? head -> index 0"
    (some 0) ((streamSpec.findDestructor? "head").map Prod.fst)
  check "findDestructor? tail -> index 1"
    (some 1) ((streamSpec.findDestructor? "tail").map Prod.fst)
  check "findDestructor? bogus -> none" true
    (streamSpec.findDestructor? "bogus").isNone

  -- Guardedness check on the canonical spec + unguarded witness.
  check "streamSpec guardedness passes"
    true  (Guarded.isSatisfied streamSpec)
  check "unguardedSpec guardedness fails"
    false (Guarded.isSatisfied unguardedSpec)
  check "noDestructorSpec vacuous pass"
    true  (Guarded.isSatisfied noDestructorSpec)

end Tests.Kernel.CoinductiveTests
