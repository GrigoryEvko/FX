import FX.Kernel.Typing

/-!
# Typing tests

Compile-time tests for `infer` / `check` — the bidirectional
type-checker.  Covers all 10 Term forms: var / app / lam / pi /
sigma / type / id / quot are fully checked; ind / coind reject
with `T100`.

Tests use `Term`'s BEq (no DecidableEq — see ReductionTests
docstring) through helpers `inferOk` and `inferFailsT`.
-/

namespace Tests.Kernel.TypingTests

open FX.Kernel
open FX.Kernel.Term

def universeZero : Level := .zero
def universeOne : Level := .succ .zero
def universeTwo : Level := .succ (.succ .zero)
def typeZero : Term := .type universeZero
def typeOne : Term := .type universeOne
def typeTwo : Term := .type universeTwo

/-- True iff `infer context term = .ok inferred` and `inferred == expected`. -/
def inferOk (context : TypingContext) (term expected : Term) : Bool :=
  match infer context term with
  | .ok inferred => inferred == expected
  | .error _     => false

/-- True iff `infer context term` errored. -/
def inferFails (context : TypingContext) (term : Term) : Bool :=
  match infer context term with
  | .error _ => true
  | .ok _    => false

/-- True iff `infer context term = .error e` AND `e.code == expectedCode`.
    Stronger than `inferFails` — distinguishes the specific error
    code the kernel emits from "any failure". -/
def inferFailsCode (context : TypingContext) (term : Term)
    (expectedCode : String) : Bool :=
  match infer context term with
  | .error typeError => typeError.code == expectedCode
  | .ok _            => false

/-- True iff `check context term expectedType` succeeded. -/
def checkOk (context : TypingContext) (term expectedType : Term) : Bool :=
  match check context term expectedType with
  | .ok _    => true
  | .error _ => false

/-- True iff `check context term expectedType` errored. -/
def checkFails (context : TypingContext) (term expectedType : Term) : Bool :=
  match check context term expectedType with
  | .error _ => true
  | .ok _    => false

/-- True iff `check context term expectedType = .error e` AND
    `e.code == expectedCode`.  Stronger rejection assertion. -/
def checkFailsCode (context : TypingContext) (term expectedType : Term)
    (expectedCode : String) : Bool :=
  match check context term expectedType with
  | .error typeError => typeError.code == expectedCode
  | .ok _            => false

/-- True iff `inferType context term = .ok expectedLevel`. -/
def inferTypeIs (context : TypingContext) (term : Term)
    (expectedLevel : Level) : Bool :=
  match inferType context term with
  | .ok actualLevel => decide (actualLevel = expectedLevel)
  | .error _        => false

/-! ## type : type of type -/

example : inferOk [] typeZero typeOne = true := by native_decide
example : inferOk [] typeOne typeTwo = true := by native_decide

/-! ## var — lookup in context -/

example :
  inferOk [{ grade := Grade.default, typeTerm := typeZero }] (Term.var 0) typeZero = true := by
  native_decide

-- var out of range → T004 (not just "any failure").
example : inferFailsCode [] (Term.var 0) "T004" = true := by native_decide

-- Deep out-of-range still T004.
example : inferFailsCode [] (Term.var 7) "T004" = true := by native_decide

/-! ## pi — Pi-form, returns type at max of component levels -/

example :
  inferOk [] (Term.piTot Grade.default typeZero typeZero)
    (.type (Level.max universeOne universeOne)) = true := by native_decide

example :
  inferOk [] (Term.piTot Grade.default typeZero typeOne)
    (.type (Level.max universeOne universeTwo)) = true := by native_decide

/-! ## lam — Pi-intro with Wood-Atkey context division -/

example :
  inferOk []
    (Term.lam Grade.default typeZero (Term.var 0))
    (.piTot Grade.default typeZero typeZero) = true := by native_decide

/-! ## app — Pi-elim with beta-substitution

Well-typed application: `(lambda (x : typeOne). x) typeZero` where `typeZero : typeOne`.
The lambda has type `Pi(x:typeOne)→typeOne`; applying to `typeZero : typeOne` yields
`typeOne` (the body type with `x` substituted for the arg, but the
body was `var 0` of type `typeOne`, so the result type is `typeOne`).

An `(lambda (x : typeZero). x) typeZero` would be ill-typed because the argument
`typeZero` has type `typeOne`, not `typeZero`. -/

example :
  inferOk []
    (Term.app
      (Term.lam Grade.default typeOne (Term.var 0))
      typeZero)
    typeOne = true := by native_decide

-- Apply a non-function: T003 pinned (not just "any failure").
example :
  inferFailsCode [] (Term.app typeZero typeZero) "T003" = true := by native_decide

-- Apply a ctor value as a function — T003 (ctor isn't a Pi).
example :
  inferFailsCode [] (Term.app (Term.ctor "Nat" 0 [] []) typeZero) "T003"
    = true := by native_decide

-- Apply a well-typed lam to an arg of the WRONG type → T002
-- (check detects mismatch between arg type and expected domain).
-- `(λx:typeZero. x) typeZero` — typeZero has type typeOne, not typeZero.
example :
  inferFailsCode []
    (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero)
    "T002" = true := by native_decide

/-! ## sigma — Sigma-form -/

example :
  inferOk [] (Term.sigma Grade.default typeZero typeZero)
    (.type (Level.max universeOne universeOne)) = true := by native_decide

/-! ## id — Id-form

`Id typeOne typeZero typeZero` requires `typeZero : typeOne` (true — typeZero is a type at universe 1).
The Id type itself lives in the same universe as `typeOne` = type universeOne,
so `inferType` of the Id returns `universeOne`.  Then `infer` returns
`type universeTwo` (= typeTwo). -/

example : inferOk [] (Term.id typeOne typeZero typeZero) typeTwo = true := by native_decide

/-! ## quot — Quot-form -/

-- Quot typeOne R where R = lambda _. typeZero is a trivial type-level relation.
example :
  inferOk []
    (Term.quot typeOne (Term.lam Grade.default typeZero typeZero))
    typeTwo = true := by native_decide

/-! ## ind — real inductive family lookup per A1 -/

-- Registered Bool / Nat / Unit / Empty from FX/Kernel/Inductive.lean.
-- Phase-2.2 infers `ind typeName []` as `type zero` — ground
-- inductives live at universe 0 per the comment in
-- `FX/Kernel/Typing.lean` (`.ind` case).  Universe polymorphism
-- (task A10) will thread spec-parameter levels through a `max`.
example :
  inferOk [] (Term.ind "Bool" []) (.type .zero) = true := by
  native_decide

example :
  inferOk [] (Term.ind "Nat" []) (.type .zero) = true := by
  native_decide

-- Unknown type name → T110 (pinned).
example :
  inferFailsCode [] (Term.ind "Unknown" []) "T110" = true := by native_decide

-- ctor — applied constructor returns the applied inductive.
example :
  inferOk [] (Term.ctor "Nat" 0 [] []) (.ind "Nat" []) = true := by
  native_decide

example :
  inferOk []
    (Term.ctor "Nat" 1 [] [Term.ctor "Nat" 0 [] []])
    (.ind "Nat" []) = true := by
  native_decide

-- Ctor on an unknown type name → T110 (same as ind).
example :
  inferFailsCode [] (Term.ctor "Unknown" 0 [] []) "T110" = true := by
  native_decide

-- Ctor index out of range → T112 (pinned).  Bool has 2 ctors (0, 1).
example :
  inferFailsCode [] (Term.ctor "Bool" 99 [] []) "T112" = true := by
  native_decide

-- Ctor arg count mismatch → T113 (pinned).  Nat.Succ takes 1 arg.
example :
  inferFailsCode [] (Term.ctor "Nat" 1 [] []) "T113" = true := by
  native_decide

-- Too many args also fails T113.
example :
  inferFailsCode []
    (Term.ctor "Nat" 0 []
      [Term.ctor "Nat" 0 [] [], Term.ctor "Nat" 0 [] []])
    "T113" = true := by native_decide

-- Ctor arg with wrong type → T002 (via `check` on the arg).
-- Nat.Succ expects a Nat; giving it typeZero fails.
example :
  inferFailsCode []
    (Term.ctor "Nat" 1 [] [typeZero]) "T002" = true := by native_decide

/-! ## coind — unknown spec rejection (S6)

S6 landed Coind-form / Coind-intro / Coind-elim typing rules.
With no spec registered under `"stream"` in `GlobalEnv.userCoindSpecs`,
the typing rule rejects at T110 (unknown coinductive type) —
parallel to the `.ind` case.  Once S11 registers a spec via
`addUserCoindSpec`, the form infers `.type .zero`; tests for
that path live alongside the translation tests.  The
unknown-spec rejection stays pinned here so a registry
regression doesn't silently accept `coind` on an invalid name. -/
example :
  inferFailsCode [] (Term.coind "stream" []) "T110" = true := by native_decide

example :
  inferFailsCode [] (Term.coind "stream" [typeZero]) "T110" = true := by native_decide

/-! ## const — unknown global → T120 -/

example :
  inferFailsCode [] (Term.const "undefinedName") "T120" = true := by native_decide

/-! ## check — drives against expected type -/

example : checkOk [] typeZero typeOne = true := by native_decide

-- checkFails with specific code: checking typeZero against `var 0` —
-- `var 0` isn't a valid expected type in empty context (T004 propagates
-- from trying to infer var 0's type).
example : checkFails [] typeZero (Term.var 0) = true := by native_decide

-- checkFailsCode for a real type mismatch: checking a Pi against
-- typeZero — the Pi's inferred type is `type (max 1 1) = type 1`,
-- not typeZero.  → T002 (type mismatch).
example :
  checkFailsCode []
    (Term.piTot Grade.default typeZero typeZero) typeZero "T002" = true := by
  native_decide

/-! ## beta-conversion during check

`(lambda (x : typeOne). x) typeZero` normalizes to `typeZero`, so checking it against
`typeZero` succeeds — we infer the app's type as `typeOne`, which equals
`typeZero`'s type at position `typeZero : typeOne`.  Wait — let me reconsider.

`(lambda (x : typeOne). x) typeZero` has inferred type `typeOne` (substituting typeZero for
x in the body-type which was typeOne with x at index 0 — but typeOne has
no free vars so substitution is no-op, result is typeOne).

So `check context ((lambda x:typeOne. x) typeZero) typeOne` — inferred typeOne, expected typeOne — succeeds. -/

example :
  checkOk []
    (Term.app (Term.lam Grade.default typeOne (Term.var 0)) typeZero)
    typeOne = true := by native_decide

/-! ## inferType helper -/

example : inferTypeIs [] typeZero universeOne = true := by native_decide

-- inferType of a variable whose declared type is a universe:
-- succeeds, extracting the level.
example :
  inferTypeIs [{ grade := Grade.default, typeTerm := typeZero }] (Term.var 0) universeZero = true := by
  native_decide

/-! ## refl — Id-intro (H.6)

`refl witness : Id T witness witness` where `T = typeof(witness)`.
The kernel infers the witness's type and builds the Id endpoints
from the same witness on both sides.
-/

-- refl of typeZero (which has type typeOne): Id typeOne typeZero typeZero.
example :
  inferOk [] (Term.refl typeZero)
    (Term.id typeOne typeZero typeZero) = true := by native_decide

-- refl with a different witness yields a different Id endpoint —
-- distinguishes correct inference from a broken "always return
-- Id typeOne typeZero typeZero" implementation.
example :
  inferOk [] (Term.refl typeOne)
    (Term.id typeTwo typeOne typeOne) = true := by native_decide

/-! ## idJ — Id-elim / J eliminator (H.6)

Shape: `idJ motive base eqProof` where eqProof has an Id type.
Currently accepts when eqProof whnfs to an Id form, rejects
otherwise with T010.
-/

-- Rejection: eqProof isn't an Id-type → T010.
-- Here eqProof = typeZero which has type typeOne (not Id).
example :
  inferFailsCode []
    (Term.idJ (Term.lam Grade.default typeZero typeZero)
              (Term.lam Grade.default typeZero typeZero)
              typeZero)
    "T010" = true := by native_decide

/-! ## quot — Quot-form edge cases -/

-- Non-type in carrier position — rejects with T001 (from inferType).
-- `Term.quot (Term.var 0)` with empty context: var 0 fails T004 first.
example :
  inferFailsCode [] (Term.quot (Term.var 0) typeZero) "T004" = true := by
  native_decide

/-! ## quotMk / quotLift — introduction + elimination

`quotMk relation witness : Quot T R` where T = witness's type.
`quotLift lifted respects target` — target must be a Quot value.
-/

-- quotMk with concrete witness.  Witness = typeZero (type typeOne),
-- so result is `Quot typeOne rel`.
example :
  inferOk []
    (Term.quotMk (Term.lam Grade.default typeOne typeZero) typeZero)
    (Term.quot typeOne (Term.lam Grade.default typeOne typeZero)) = true := by
  native_decide

-- quotLift on a non-Quot target → T010.
example :
  inferFailsCode []
    (Term.quotLift
      (Term.lam Grade.default typeZero typeZero)
      (Term.lam Grade.default typeZero typeZero)
      typeZero)
    "T010" = true := by native_decide

/-! ## forallLevel — universe polymorphism (A10)

`forallLevel body` accepts body if body infers under an extended
level scope.  Closed body (no `.var` levels) trivially accepts.
`Level.var 0` inside body is in-scope (bound by the forallLevel).
`Level.var 1` inside a single-level scope is out of scope → T060.
-/

-- Closed forallLevel body — accepts.
example :
  inferOk [] (Term.forallLevel typeZero) typeOne = true := by native_decide

-- Body references the level it binds — accepts (T060 does NOT fire).
example :
  (Term.infer [] (Term.forallLevel (.type (Level.var 0)))).isOk = true := by
  native_decide

-- Body references a level that's not bound (var 1 under a single
-- forallLevel) → T060.
example :
  inferFailsCode []
    (Term.forallLevel (.type (Level.var 1))) "T060" = true := by
  native_decide

-- Top-level .type with out-of-scope level var → T060.
example :
  inferFailsCode [] (.type (Level.var 0)) "T060" = true := by native_decide

/-! ## M001 linearity — Atkey-2018 witness rejected (A9)

A linear binder used twice in the body produces usage grade
`omega` which exceeds the declared `one` → M001.  This is the
corpus entry that the Wood-Atkey corrected Lam rule must
reject (§27.1).
-/

def natTy : Term := .ind "Nat" []
def natToNat : Term := Term.piTot Grade.default natTy natTy
def natZero : Term := Term.ctor "Nat" 0 [] []

-- `λ(f : Nat→Nat). f(f(Nat.Zero))` — f used twice, linear → M001.
example :
  inferFailsCode []
    (Term.lam Grade.default natToNat
      (Term.app (.var 0) (Term.app (.var 0) natZero)))
    "M001" = true := by native_decide

-- `λ(f : Nat→Nat). f(Nat.Zero)` — f used once, linear → OK.
example :
  (Term.infer []
    (Term.lam Grade.default natToNat
      (Term.app (.var 0) natZero))).isOk = true := by native_decide

/-! ## check — beta-conversion strengthened

The existing `checkOk` test uses typeOne/typeZero where the app
result HAPPENS to equal the expected.  A broken check that
ignored the expected type would still pass.  Below: use DISTINCT
target/expected so a broken check that "always accepts" or
"ignores the expected" fails.
-/

-- Well-typed app whose result is typeOne, checked against typeOne — OK.
example :
  checkOk []
    (Term.app (Term.lam Grade.default typeOne (Term.var 0)) typeZero)
    typeOne = true := by native_decide

-- Same app, checked against typeZero → T002 (type mismatch).
example :
  checkFailsCode []
    (Term.app (Term.lam Grade.default typeOne (Term.var 0)) typeZero)
    typeZero "T002" = true := by native_decide

-- Check against natType — typeOne is not ≤ natType (not universe-
-- comparable, not convertible) → T002.
example :
  checkFailsCode []
    (Term.app (Term.lam Grade.default typeOne (Term.var 0)) typeZero)
    natTy "T002" = true := by native_decide

-- Universe cumulativity: typeOne is accepted against typeTwo because
-- Type<1> <: Type<2> per A7 / §31.4 U-cumul.  This is the dual of the
-- failing case above — catches a broken `subOrConv` that either
-- dropped cumulativity (→ would fail here) or made it bidirectional
-- (→ would accept the typeZero case above).
example :
  checkOk []
    (Term.app (Term.lam Grade.default typeOne (Term.var 0)) typeZero)
    typeTwo = true := by native_decide

end Tests.Kernel.TypingTests
