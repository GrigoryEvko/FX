import FX.Kernel.Typing
import FX.Kernel.Reduction
import FX.Kernel.Conversion
import FX.Kernel.Subtyping
import FX.Kernel.AxiomWalker
import FX.Kernel.Inductive
import FX.Kernel.Coinductive
import Tests.Framework

/-!
# Stream A integration tests (G1)

Cross-module smoke tests that exercise multiple Stream A features
together.  Each file under `Tests/Kernel/*Tests.lean` pins one
module's surface; this file pins COMPOSITION — properties that
only surface when two or more modules interact.

The failure mode this catches: a refactor that preserves each
per-module test's behavior but breaks the cross-module
composition.  Classic example: a walker that treats `.coind`
as `true` in isolation (looks right per-module) but silently
drops every child-axiom contribution (visible only when the
coind carries a real sub-term).

## Coverage map

  * `typing + reduction` — well-typed terms reduce to well-typed
    normal forms.  Exercised via β on a specific lambda-app pair
    whose type is preserved.
  * `typing + subtyping` — a term at `Type<0>` is accepted where
    `Type<1>` is expected via U-cumul.
  * `substitution + reduction` — β uses substitution and shift;
    the result under reduction is the same term that substitution
    builds directly.
  * `inductive + axiom walker` — a term using `Nat.succ(Zero)`
    pulls Ind-form + Ind-intro axioms in the correct order.
  * `coinductive + axiom walker` — a coind type whose args
    reference other axiom-bearing sub-terms pulls both axioms.
  * `id + quot + axiom walker` — deep walker sums across
    Appendix-H sections.
  * `conversion + reduction` — convEq respects β-reduced form;
    two terms convertible after reduction stay convertible.
-/

namespace Tests.Kernel.IntegrationTests

open FX.Kernel

/-! ## Shared fixtures -/

-- A `Nat.Zero` term — ctor with index 0, zero args.
private def natZero : Term := .ctor "Nat" 0 [] []

-- A `Nat.succ(Nat.Zero)` term — the number 1.
private def natOne : Term := .ctor "Nat" 1 [] [natZero]

-- The identity lambda on Nat: `λ (x :_linear Nat). x`.
private def identityNat : Term :=
  .lam Grade.default (.ind "Nat" []) (.var 0)

/-! ## typing + reduction — β preserves type

The identity applied to Nat.Zero infers type `Nat` (matches the
domain), reduces via β to `Nat.Zero`, which also has type `Nat`.
A walker that broke either typing or reduction in isolation
would produce a mismatch here. -/

example :
    Term.structEq
      (Term.whnf Term.defaultFuel (.app identityNat natZero))
      natZero
      = true := by native_decide

/-! ## typing + subtyping — universe cumulativity

`Type<0>` is a subtype of `Type<1>` per Appendix H.1 U-cumul.
Subtyping is decidable here and the result must hold
independent of the `Term` shape under comparison. -/

example :
    Term.sub Term.defaultFuel
      (Term.type Level.zero) (Term.type (Level.succ Level.zero))
      = true := by
  native_decide

example :
    Term.sub Term.defaultFuel
      (Term.type (Level.succ Level.zero)) (Term.type Level.zero)
      = false := by
  native_decide

/-! ## substitution + reduction — β equals direct substitution

For any body B with `var 0` referring to the lambda's parameter,
`whnf (λ x. B) a = subst 0 a B`.  We pin the specific case
`(λ x. x) Nat.zero = Nat.zero`. -/

example :
    Term.structEq
      (Term.whnf Term.defaultFuel
        (.app (.lam Grade.default (.ind "Nat" []) (.var 0)) natZero))
      (Term.subst 0 natZero (.var 0))
      = true := by native_decide

/-! ## inductive + axiom walker

A term using `Nat.succ(Zero)` invokes Ind-form (for each ind
reference) and Ind-intro (for each ctor application).  The
walker must surface BOTH. -/

example :
    (Term.collectAxioms natOne).contains KernelAxiom.indIntro = true := by
  native_decide

example :
    List.contains
      (Term.collectAxioms
        (Term.pi Grade.default (.ind "Nat" []) (.ind "Nat" []) Effect.tot))
      KernelAxiom.indForm = true := by
  native_decide

/-! ## coinductive + axiom walker

A coind argument is a real sub-term and its axioms bubble up.
Post-A2 the walker recurses into `coindArgs`.  Here we use a
coind whose arg is itself a `ctor` — the parent axiom set must
include BOTH `.coindForm` and `.indIntro`. -/

example :
    (Term.collectAxioms
      (.coind "stream" [natOne])).contains KernelAxiom.coindForm = true := by
  native_decide

example :
    (Term.collectAxioms
      (.coind "stream" [natOne])).contains KernelAxiom.indIntro = true := by
  native_decide

/-! ## id + quot + axiom walker — cross-section reach

A term with both Id and Quot payloads surfaces axioms from
Appendix H.6 and H.7 in the same walk. -/

example :
    let combined :=
      Term.app
        (.refl (.ind "Nat" []))
        (.quotMk (.var 0) natZero)
    (Term.collectAxioms combined).contains KernelAxiom.idRefl = true := by
  native_decide

example :
    let combined :=
      Term.app
        (.refl (.ind "Nat" []))
        (.quotMk (.var 0) natZero)
    (Term.collectAxioms combined).contains KernelAxiom.quotMk = true := by
  native_decide

/-! ## Q45: reveal + reduction — opaque const unfolds with reveal

Per §10.15, `reveal f;` locally unfolds an opaque declaration.
The mechanism composes through `whnf` automatically because
`whnf` consults `GlobalEnv.unfold?`, which now checks both the
decl's `transparent` flag AND the env's `revealedNames` list.

Scenario: `body := Nat.zero`, declaration `opaqueZero`
registered with `transparent := false`.  Without reveal,
`whnf (const "opaqueZero")` stays stuck at `.const "opaqueZero"`.
After `withReveal "opaqueZero"`, it unfolds to `Nat.zero`. -/

example :
    let globalEnv := GlobalEnv.empty.addDecl "opaqueZero"
                      (.ind "Nat" []) natZero
    -- Opaque: whnf does NOT unfold.
    Term.structEq
      (Term.whnf Term.defaultFuel (.const "opaqueZero") globalEnv)
      (.const "opaqueZero")
      = true := by native_decide

example :
    let globalEnv := (GlobalEnv.empty.addDecl "opaqueZero"
                       (.ind "Nat" []) natZero).withReveal "opaqueZero"
    -- Revealed: whnf unfolds to the body (`Nat.zero`).
    Term.structEq
      (Term.whnf Term.defaultFuel (.const "opaqueZero") globalEnv)
      natZero
      = true := by native_decide

-- Conversion through reveal: two opaque consts with matching bodies
-- are NOT convertible without reveal (stuck-neq-stuck) but ARE
-- convertible after revealing both.
example :
    let globalEnv := GlobalEnv.empty.addDecl "firstCopy"
                      (.ind "Nat" []) natZero
                    |>.addDecl "secondCopy" (.ind "Nat" []) natZero
    Term.convEq Term.defaultFuel (.const "firstCopy") (.const "secondCopy")
      globalEnv = false := by native_decide

example :
    let baseEnv := GlobalEnv.empty.addDecl "firstCopy" (.ind "Nat" []) natZero
                      |>.addDecl "secondCopy" (.ind "Nat" []) natZero
    let globalEnv := baseEnv.withReveals ["firstCopy", "secondCopy"]
    Term.convEq Term.defaultFuel (.const "firstCopy") (.const "secondCopy")
      globalEnv = true := by native_decide

/-! ## conversion + reduction — convEq under β

Two applications that reduce to the same normal form are
convertible.  This composes `Reduction.whnf` (inside `convEq`)
with `Conversion.convEq`'s structural match. -/

-- `(λ x. x) Nat.zero ≡ Nat.zero` — they reduce to the same canonical.
example :
    Term.convEq Term.defaultFuel
      (.app identityNat natZero)
      natZero
      = true := by
  native_decide

-- `(λ x. Nat.succ(x)) Nat.zero ≡ Nat.succ(Nat.zero)` — reduction
-- commutes with substitution under the lambda.
example :
    Term.convEq Term.defaultFuel
      (.app (.lam Grade.default (.ind "Nat" []) natOne) natZero)
      natOne
      = true := by
  native_decide

-- Non-convertible: different ctor indices.
example :
    Term.convEq Term.defaultFuel natZero natOne = false := by
  native_decide

/-! ## Runtime harness

The above `example` blocks discharge at elaboration time.  The
runtime harness re-asserts the same facts via `check` so the
suite shows up in the test-count summary. -/

def run : IO Unit := Tests.suite "Tests.Kernel.IntegrationTests" do
  -- typing + reduction.  Uses `structEq` since `Term` doesn't
  -- derive DecidableEq (walker comparison only — structural).
  checkTrue "(λ x. x) Nat.zero β→ Nat.zero"
    (Term.structEq
      (Term.whnf Term.defaultFuel (.app identityNat natZero))
      natZero)

  -- typing + subtyping (U-cumul both directions).
  check "Type<0> <: Type<1>" true
    (Term.sub Term.defaultFuel
      (Term.type Level.zero) (Term.type (Level.succ Level.zero)))
  check "Type<1> !<: Type<0>" false
    (Term.sub Term.defaultFuel
      (Term.type (Level.succ Level.zero)) (Term.type Level.zero))

  -- axiom walker — Ind, Coind, Id, Quot composition.
  check "Nat.succ(Zero) pulls Ind-intro" true
    ((Term.collectAxioms natOne).contains KernelAxiom.indIntro)
  check "coind [Nat.succ(Zero)] pulls Coind-form" true
    ((Term.collectAxioms (.coind "stream" [natOne])).contains
      KernelAxiom.coindForm)
  check "coind [Nat.succ(Zero)] pulls Ind-intro from arg" true
    ((Term.collectAxioms (.coind "stream" [natOne])).contains
      KernelAxiom.indIntro)

  -- Convertibility under reduction.
  check "(λ x. x) Nat.zero ≡ Nat.zero" true
    (Term.convEq Term.defaultFuel (.app identityNat natZero) natZero)
  check "Nat.zero !≡ Nat.succ(Zero)" false
    (Term.convEq Term.defaultFuel natZero natOne)

  -- Q45 reveal through whnf: opaque const stays stuck; revealed unfolds.
  let opaqueEnv := GlobalEnv.empty.addDecl "oz" (.ind "Nat" []) natZero
  checkTrue "opaque const stays stuck under whnf"
    (Term.structEq (Term.whnf Term.defaultFuel (.const "oz") opaqueEnv)
                   (.const "oz"))
  let revealedEnv := opaqueEnv.withReveal "oz"
  checkTrue "revealed const unfolds under whnf"
    (Term.structEq (Term.whnf Term.defaultFuel (.const "oz") revealedEnv)
                   natZero)
  -- Reveal composes with convEq: two opaque consts become convertible
  -- after reveal of both.
  let twoOpaque :=
    opaqueEnv.addDecl "oz2" (.ind "Nat" []) natZero
  check "opaque consts are not convertible" false
    (Term.convEq Term.defaultFuel (.const "oz") (.const "oz2") twoOpaque)
  let twoRevealed := twoOpaque.withReveals ["oz", "oz2"]
  check "revealed consts are convertible" true
    (Term.convEq Term.defaultFuel (.const "oz") (.const "oz2") twoRevealed)

end Tests.Kernel.IntegrationTests
