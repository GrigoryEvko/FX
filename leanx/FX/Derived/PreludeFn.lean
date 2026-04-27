import FX.Kernel.Term
import FX.Kernel.Grade
import FX.Kernel.Env

/-!
# Prelude built-in functions (Q68)

Kernel-level function definitions seeded into every `GlobalEnv`
before user decls elaborate.  Phase-2 targets binary comparison
operators on `Nat` that reduce via `indRec` — the shape
`fx_design.md` §6.1 requires — without needing a surface-source
round-trip through the elaborator.

The builder functions in this module produce closed kernel
`Term` values: types fit `Π (n : Nat). Π (m : Nat). Bool` and
bodies encode classical Peano-Nat comparison via a double
`indRec "Nat"` fold.  The Succ-case method of the outer
`indRec` uses the kernel iota rule's auto-supplied `rec`
parameter (of type `Nat -> Bool`) to recurse on the inner
scrutinee's predecessor — so no external recursion
infrastructure (e.g. `Term.const` self-reference) is required.

## Functions provided

  * `nat_eq : Π (n : Nat). Π (m : Nat). Bool` — structural
    equality on unary `Nat`.  `True` iff both `n` and `m`
    reduce to `Nat.Zero` or both reduce to `Nat.Succ(pred)`
    with `nat_eq(pred_n, pred_m) == True`.
  * `nat_lt : Π (n : Nat). Π (m : Nat). Bool` — strict
    ordering.  `True` iff `n < m` in the natural order.
    Defined by: `Zero < Zero = False`, `Zero < Succ(_) = True`,
    `Succ(_) < Zero = False`, `Succ(np) < Succ(mp) = np < mp`.

## Transparency

Both prelude fns are registered with `transparent := true` so
the kernel's `whnf` / iota-reduction path can unfold them at
call sites.  Without transparency, `a == b` on concrete
literals would get stuck at a `Term.const` head instead of
reducing to a Bool value.
-/

namespace FX.Derived.PreludeFn

open FX.Kernel

/-! ## Shared closed-Term atoms -/

/-- The kernel `Nat` inductive type as a Term. -/
def natT : Term := Term.ind "Nat" []

/-- The kernel `Bool` inductive type as a Term. -/
def boolT : Term := Term.ind "Bool" []

/-- `Nat -> Bool` as a closed Pi.  Binder type + codomain are
    both closed so shifts through outer binders are no-ops. -/
def natToBool : Term :=
  Term.pi Grade.default natT boolT Effect.tot

/-- `Bool.True` kernel ctor. -/
def boolTrue : Term := Term.ctor "Bool" 1 [] []

/-- `Bool.False` kernel ctor. -/
def boolFalse : Term := Term.ctor "Bool" 0 [] []

/-- Non-dependent motive `λ _ : Nat. Bool` for an inner
    `indRec "Nat"` that yields a Bool. -/
def natToBoolMotive : Term :=
  Term.lam Grade.default natT boolT

/-- Dependent-shape motive `λ _ : Nat. Nat -> Bool` for an
    outer `indRec "Nat"` whose value is a partial-binary
    function (applied to the second operand at the use site). -/
def natToFnMotive : Term :=
  Term.lam Grade.default natT natToBool

/-! ## `nat_eq` builder -/

/-- Method for "a `Succ` is never equal to `Zero`": inside an
    inner `indRec "Nat" (λ _. Bool) [...] m'` for the Succ arm,
    the method has shape `λ (pred : Nat). λ (_rec : Bool).
    Bool.False` — i.e., regardless of the predecessor, Succ(_)
    doesn't match Zero.  Closed term; safe to reuse. -/
private def succIsNotZeroMethod : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default boolT boolFalse)

/-- Outer `Zero`-case method for `nat_eq`: `λ (m' : Nat).
    indRec "Nat" (λ _. Bool) [Bool.True, succIsNotZeroMethod]
    m'`.  Compares the second operand's ctor tag against Zero:
    True when m' is also Zero, False when m' is Succ(_). -/
private def natEqZeroCase : Term :=
  Term.lam Grade.default natT
    (Term.indRec "Nat" natToBoolMotive
      [boolTrue, succIsNotZeroMethod]
      (Term.var 0))

/-- Inner `Succ`-case method inside the outer Succ case of
    `nat_eq`: `λ (mp : Nat). λ (_rec2 : Bool). rec mp`.  The
    `rec` variable refers to the outer indRec's auto-supplied
    recursive result, which has type `Nat -> Bool` because the
    outer motive returns `Nat -> Bool`.  De Bruijn indices are
    computed for the final lambda nest depth:

      * before this method's lambdas: scope is `{n'=2, rec=1,
        m'=0}` — three binders from the outer Succ method's
        `λ n'. λ rec. λ m'.` chain.
      * after `λ mp. λ rec2.`: `{n'=4, rec=3, m'=2, mp=1,
        rec2=0}`.

    So `rec mp = app (var 3) (var 1)`. -/
private def natEqInnerSuccMethod : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default boolT
      (Term.app (Term.var 3) (Term.var 1)))

/-- Outer `Succ`-case method for `nat_eq`: `λ (n' : Nat).
    λ (rec : Nat -> Bool). λ (m' : Nat). indRec "Nat" (λ _.
    Bool) [Bool.False, natEqInnerSuccMethod] m'`.  When the
    inner scrutinee `m'` is Zero, returns False (Succ ≠ Zero);
    when Succ(mp), calls the auto-supplied `rec` on `mp` to
    recurse structurally. -/
private def natEqSuccCase : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natToBool
      (Term.lam Grade.default natT
        (Term.indRec "Nat" natToBoolMotive
          [boolFalse, natEqInnerSuccMethod]
          (Term.var 0))))

/-- Full `nat_eq` body: `λ (n : Nat). λ (m : Nat).
    (indRec "Nat" natToFnMotive [natEqZeroCase, natEqSuccCase]
      n) m`.  The outer indRec returns a `Nat -> Bool` partial
    function (per `natToFnMotive`); we then apply it to `m` to
    get the Bool result. -/
def natEqBody : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.app
        (Term.indRec "Nat" natToFnMotive
          [natEqZeroCase, natEqSuccCase]
          (Term.var 1))
        (Term.var 0)))

/-- `nat_eq` declared type: `Π (n : Nat). Π (m : Nat). Bool`.
    Both Nats are at the default (usage = 1) grade; the
    function is Tot (no effect).  The inner codomain `Bool` is
    closed so no de Bruijn shifting is needed. -/
def natEqType : Term :=
  Term.pi Grade.default natT
    (Term.pi Grade.default natT boolT Effect.tot)
    Effect.tot

/-! ## `nat_lt` builder

Strict `<` on unary Nat.  Semantics:

  * `Zero < Zero = False`
  * `Zero < Succ(_) = True`
  * `Succ(_) < Zero = False`
  * `Succ(np) < Succ(mp) = np < mp` (recursion via outer
    indRec's `rec` parameter, same trick as `nat_eq`).

Shares the outer motive `λ _ : Nat. Nat -> Bool`,
`natToBoolMotive` / `natToFnMotive` atoms, and the outer-Succ
inner-Succ method structure with `nat_eq`.  Only the
"Zero vs Succ" base case differs — `Zero < Succ(_)` is True,
whereas `Zero == Succ(_)` was False. -/

/-- Inner-Succ method for "Zero < Succ(_) is True": `λ (pred :
    Nat). λ (_rec : Bool). Bool.True` — regardless of what `m'`
    decomposes to in the Succ direction, strict-less-than
    succeeds from Zero.  Closed term. -/
private def succIsPosMethod : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default boolT boolTrue)

/-- Outer `Zero`-case method for `nat_lt`: `λ (m' : Nat).
    indRec "Nat" (λ _. Bool) [Bool.False, succIsPosMethod] m'`.
    Returns False when m' is also Zero; True when m' is
    Succ(_).  Analogue of `natEqZeroCase` with flipped base
    Bool values. -/
private def natLtZeroCase : Term :=
  Term.lam Grade.default natT
    (Term.indRec "Nat" natToBoolMotive
      [boolFalse, succIsPosMethod]
      (Term.var 0))

/-- Outer `Succ`-case method for `nat_lt`: identical shape to
    `natEqSuccCase`.  When `m'` is Zero, Succ(_) < Zero = False.
    When `m'` is Succ(mp), recurse via the auto-supplied
    `rec : Nat -> Bool` applied to `mp`.  De Bruijn indices
    match `natEqInnerSuccMethod` exactly. -/
private def natLtSuccCase : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natToBool
      (Term.lam Grade.default natT
        (Term.indRec "Nat" natToBoolMotive
          [boolFalse, natEqInnerSuccMethod]
          (Term.var 0))))

/-- Full `nat_lt` body.  Same outer structure as `nat_eq`;
    only the Zero-case method differs. -/
def natLtBody : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.app
        (Term.indRec "Nat" natToFnMotive
          [natLtZeroCase, natLtSuccCase]
          (Term.var 1))
        (Term.var 0)))

/-- `nat_lt` declared type: `Π (n : Nat). Π (m : Nat). Bool`.
    Structurally identical to `natEqType` — same binder
    grades, same codomain. -/
def natLtType : Term := natEqType

/-! ## `nat_add` / `nat_sub` / `nat_mul` builders (Q70)

Nat arithmetic via double-`indRec`-style structural recursion.
The motive here returns `Nat -> Nat` instead of the `Nat ->
Bool` used by `nat_eq` / `nat_lt`, but the outer scaffold (outer
indRec applied to one operand, result applied to the second) is
identical.

Semantics:

  * `nat_add(n, m) = n + m` — induct on `n`, thread `m` as an
    inner lambda arg.  `add(0, m) = m`, `add(Succ(n'), m) =
    Succ(add(n', m))`.

  * `nat_sub(n, m) = max(0, n - m)` — saturating subtract.
    Induct on `m`.  `sub(n, 0) = n`, `sub(n, Succ(m')) =
    pred(sub(n, m'))` with `pred` inlined as its own indRec.

  * `nat_mul(n, m) = n * m` — induct on `n`.  `mul(0, m) = 0`,
    `mul(Succ(n'), m) = add(m, mul(n', m))`.  The recursive
    chain to `nat_add` flows through `Term.const "nat_add"`, so
    both fns must be registered before `mul` is ever invoked. -/

/-- `Nat -> Nat` as a Pi.  Closed — safe to reuse under any
    outer binder without shifting. -/
def natToNat : Term :=
  Term.pi Grade.default natT natT Effect.tot

/-- Motive `λ _ : Nat. Nat -> Nat` used by `nat_add`, `nat_sub`,
    `nat_mul` — the outer indRec returns a partial (one-arg)
    Nat-to-Nat function that the body then applies to the second
    operand. -/
def natToNatFnMotive : Term :=
  Term.lam Grade.default natT natToNat

/-- `nat_add` outer Zero-case method: `λ m' : Nat. m'` —
    identity (add(0, m) = m).  At scope {n, m} the body `var 0`
    refers to `m'` (the only binder of this lambda). -/
private def natAddZeroCase : Term :=
  Term.lam Grade.default natT (Term.var 0)

/-- `nat_add` outer Succ-case method: `λ n'. λ (rec : Nat ->
    Nat). λ m'. Succ(rec m')`.  De Bruijn after three lambdas:
    {nOuter=4, mOuter=3, n'=2, rec=1, m'=0}; `rec m'` = `app
    (var 1) (var 0)`. -/
private def natAddSuccCase : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natToNat
      (Term.lam Grade.default natT
        (Term.ctor "Nat" 1 [] [Term.app (Term.var 1) (Term.var 0)])))

/-- Full `nat_add` body.  Structurally identical to `nat_eq`'s
    outer scaffold — only the motive and method leaves change. -/
def natAddBody : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.app
        (Term.indRec "Nat" natToNatFnMotive
          [natAddZeroCase, natAddSuccCase]
          (Term.var 1))
        (Term.var 0)))

/-- Type of `nat_add`: `Π (n : Nat). Π (m : Nat). Nat`.  Two
    default-graded binders, codomain `Nat`, Tot effect. -/
def natAddType : Term :=
  Term.pi Grade.default natT
    (Term.pi Grade.default natT natT Effect.tot)
    Effect.tot

/-- `nat_sub` outer Zero-case method: `λ nOuter : Nat. nOuter`
    — the outer induction is on `m`, so when `m = Zero` we
    return the unchanged `nOuter`.  Body `var 0` refers to
    `nOuter` at one-binder depth. -/
private def natSubZeroCase : Term :=
  Term.lam Grade.default natT (Term.var 0)

/-- `nat_sub` outer Succ-case method: `λ m'. λ (rec : Nat ->
    Nat). λ nInner. pred (rec nInner)` — where `pred` is the
    inline indRec `λ x. match x; Zero => Zero; Succ(p) => p; end
    match` = `indRec "Nat" (λ _. Nat) [Zero, λ p _rec. p] x`.

    De Bruijn after the three outer lambdas: {nOuter=4, mOuter=3,
    m'=2, rec=1, nInner=0}.  The inline pred's Succ method
    `λ p. λ _rec. p` pushes two more binders; from the innermost
    body `p` is at depth 1 (mOuter+2 etc. shift up by 2, but we
    only need `p` which is var 1). -/
private def natSubSuccCase : Term :=
  -- Inline pred's indRec applied to `rec nInner`.  Inner pred
  -- methods are at scope {nOuter=4, mOuter=3, m'=2, rec=1,
  -- nInner=0}, so the Succ-case inner body `λ p. λ _rec. p`
  -- resolves `p` at var 1 after the two inner binders are
  -- pushed.  Zero-case method is just `Nat.Zero` (closed ctor).
  let natToNatMotive : Term :=
    -- Motive `λ _ : Nat. Nat` for the inlined pred indRec.
    -- Closed — all shifts through outer binders are no-ops.
    Term.lam Grade.default natT natT
  let predBodyOnRec : Term :=
    Term.indRec "Nat" natToNatMotive
      [Term.ctor "Nat" 0 [] [],
       Term.lam Grade.default natT
         (Term.lam Grade.default natT (Term.var 1))]
      (Term.app (Term.var 1) (Term.var 0))
  Term.lam Grade.default natT
    (Term.lam Grade.default natToNat
      (Term.lam Grade.default natT predBodyOnRec))

/-- Full `nat_sub` body — outer `indRec` on the SECOND operand
    (`m`), unlike `nat_add`/`nat_eq`/`nat_lt` which induct on
    the first.  At empty scope before the lambdas; after `λ n. λ
    m.` scope is {n=1, m=0}, so the indRec's scrutinee `var 0`
    is `m` (not `n` as in the other prelude fns). -/
def natSubBody : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.app
        (Term.indRec "Nat" natToNatFnMotive
          [natSubZeroCase, natSubSuccCase]
          (Term.var 0))  -- induct on m, not n
        (Term.var 1)))   -- apply to n

/-- Type of `nat_sub`: same shape as `nat_add` — Π (n m : Nat).
    Nat. -/
def natSubType : Term := natAddType

/-- `nat_mul` outer Zero-case method: `λ m : Nat. Zero` —
    mul(0, m) = 0.  Ctor is closed, so the single lambda
    binder doesn't need to be referenced in the body. -/
private def natMulZeroCase : Term :=
  Term.lam Grade.default natT (Term.ctor "Nat" 0 [] [])

/-- `nat_mul` outer Succ-case method: `λ n'. λ (rec : Nat ->
    Nat). λ m. nat_add(m, rec m)`.

    De Bruijn after three lambdas: {nOuter=4, mOuter=3, n'=2,
    rec=1, m=0}; `rec m` = `app (var 1) (var 0)`.  The outer
    `nat_add` application is `app (app (const "nat_add") m) (rec
    m)` = `app (app (const "nat_add") (var 0)) (app (var 1)
    (var 0))`.  Relies on `nat_add` being in `globalEnv` at
    reduction time (seedPrelude order guarantees this). -/
private def natMulSuccCase : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natToNat
      (Term.lam Grade.default natT
        (Term.app
          (Term.app (Term.const "nat_add") (Term.var 0))
          (Term.app (Term.var 1) (Term.var 0)))))

/-- Full `nat_mul` body — induct on `n`, apply to `m`. -/
def natMulBody : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.app
        (Term.indRec "Nat" natToNatFnMotive
          [natMulZeroCase, natMulSuccCase]
          (Term.var 1))
        (Term.var 0)))

/-- Type of `nat_mul`: same shape as `nat_add`. -/
def natMulType : Term := natAddType

/-! ## `nat_div` / `nat_mod` builders (Q73)

Integer division and modulus.  Division can't be built from
double-indRec alone — each step consumes `nat_sub a b`, not a
structural predecessor of either argument.  Workaround: the
helper takes `fuel` as a THIRD argument and structurally
inducts on it; `nat_div a b = helper a a b` uses `a` itself as
the fuel bound, which suffices because `nat_sub a b < a`
whenever `b > 0`.  When `b = 0` the recursion emits `a` Succs
and runs out of fuel at `Zero`, so `a / 0 = 0`.

Semantics (total, matches Lean `Nat` convention):

  * `nat_div a 0 = 0`            — undefined case, saturates to 0
  * `nat_div a b = a / b`        — classical integer division
  * `nat_mod a b = a - (a/b)*b`  — derived; `a % 0 = a - 0 = a`

`nat_mod` has no new recursion — it composes `nat_sub`,
`nat_mul`, and `nat_div`. -/

/-- `Nat -> Nat -> Nat` as a closed Pi, used as both the
    return type of the outer indRec's motive and the type of
    the auto-supplied `rec` argument in the Succ method. -/
def natToNatToNat : Term :=
  Term.pi Grade.default natT
    (Term.pi Grade.default natT natT Effect.tot)
    Effect.tot

/-- Motive `λ _ : Nat. Nat -> Nat -> Nat` for `nat_div`'s
    outer indRec on fuel.  At the Succ case, iota supplies
    `rec : Nat -> Nat -> Nat` — exactly the recursion shape we
    need to call `helper predFuel (a - b) b`. -/
def natToNatToNatFnMotive : Term :=
  Term.lam Grade.default natT natToNatToNat

/-- `nat_div` helper Zero-case method: `λ a. λ b. Zero` — out
    of fuel, return 0 regardless of the remaining arguments.
    Closed term; the two binders go unreferenced. -/
private def natDivHelperZeroCase : Term :=
  Term.lam Grade.default natT
    (Term.lam Grade.default natT (Term.ctor "Nat" 0 [] []))

/-- `nat_div` helper Succ-case method: one fuel-step deeper.

    Shape: `λ predFuel. λ rec. λ a. λ b.
      if (nat_lt a b) then Zero
      else Succ (rec (nat_sub a b) b)`.

    De Bruijn scope at the innermost body (after the outer
    `λ nOuter. λ mOuter.` plus this method's four binders):
    `{nOuter=5, mOuter=4, predFuel=3, rec=2, a=1, b=0}`.  The
    Bool `indRec` encodes `if cond then T else E` as methods
    `[E, T]` — method[0] runs on ctor 0 (False); method[1] on
    ctor 1 (True).

    `rec` at de Bruijn 2 is applied to `(nat_sub a b)` and
    `b` to perform the recursive fuel-step.  The whole
    `Succ (rec (a-b) b)` is the else-arm; the then-arm
    (`a < b`, i.e. quotient is 0) is just `Nat.Zero`. -/
private def natDivHelperSuccCase : Term :=
  let boolToNatMotive : Term := Term.lam Grade.default boolT natT
  let natSubAB : Term :=
    Term.app (Term.app (Term.const "nat_sub") (Term.var 1)) (Term.var 0)
  let recAMinusBThenB : Term :=
    Term.app (Term.app (Term.var 2) natSubAB) (Term.var 0)
  let elseArm : Term := Term.ctor "Nat" 1 [] [recAMinusBThenB]
  let thenArm : Term := Term.ctor "Nat" 0 [] []
  let ltAB : Term :=
    Term.app (Term.app (Term.const "nat_lt") (Term.var 1)) (Term.var 0)
  Term.lam Grade.default natT             -- predFuel
    (Term.lam Grade.default natToNatToNat -- rec
      (Term.lam Grade.default natT        -- a
        (Term.lam Grade.default natT      -- b
          (Term.indRec "Bool" boolToNatMotive [elseArm, thenArm] ltAB))))

/-- Full `nat_div` body.  Two layers:

  1. **Outer Bool guard on `b == 0`**: returns `Zero` when the
     divisor is 0 (matching Lean's `Nat` convention; without
     this guard the helper would run out of fuel but emit `a`
     Succs along the way, giving the surprising `a / 0 = a`).
  2. **Inner fuel-bounded helper**: `(indRec "Nat" [zeroC,
     succC] n) n m` — uses `n` as fuel, `a`, and passes `m`
     as `b`.

  Layout: `λ n. λ m.
    indRec "Bool" (λ _.Nat)
      [helperApp, Zero]
      (nat_eq m Zero)`

  At the outer scope `{n=1, m=0}`, the helper application
  nests two `app`s around the outer `indRec "Nat"`.  The Bool
  `indRec`'s method[0] (False arm = "m ≠ 0") is the helper;
  method[1] (True arm = "m = 0") is `Zero`.

  Depends on `nat_eq`, `nat_sub`, `nat_lt` at reduction time;
  seedPrelude order guarantees those three are registered
  before `nat_div` is added. -/
def natDivBody : Term :=
  let boolToNatMotive : Term := Term.lam Grade.default boolT natT
  let helperApp : Term :=
    Term.app
      (Term.app
        (Term.indRec "Nat" natToNatToNatFnMotive
          [natDivHelperZeroCase, natDivHelperSuccCase]
          (Term.var 1))
        (Term.var 1))
      (Term.var 0)
  let natZero : Term := Term.ctor "Nat" 0 [] []
  let mEqZero : Term :=
    Term.app (Term.app (Term.const "nat_eq") (Term.var 0)) natZero
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.indRec "Bool" boolToNatMotive
        [helperApp, natZero]
        mEqZero))

/-- Type of `nat_div`: same shape as `nat_add`. -/
def natDivType : Term := natAddType

/-- `nat_mod` body: derived from `nat_div` / `nat_mul` /
    `nat_sub`.  `a % b = a - (a/b) * b`.  No new recursion —
    every prelude fn this references is registered earlier in
    `seedPrelude`.  Scope after `λ a. λ b.` is `{a=1, b=0}`. -/
def natModBody : Term :=
  let divAB : Term :=
    Term.app (Term.app (Term.const "nat_div") (Term.var 1)) (Term.var 0)
  let prodDivAB_B : Term :=
    Term.app (Term.app (Term.const "nat_mul") divAB) (Term.var 0)
  Term.lam Grade.default natT
    (Term.lam Grade.default natT
      (Term.app
        (Term.app (Term.const "nat_sub") (Term.var 1))
        prodDivAB_B))

/-- Type of `nat_mod`: same shape as `nat_add`. -/
def natModType : Term := natAddType

/-! ## Seed prelude fns into a GlobalEnv -/

/-- Add every prelude fn to `globalEnv` as a transparent decl
    so `whnf` can unfold the body during reduction.  Returns
    the extended environment.  Currently seeds `nat_eq` only;
    other primitives (nat_lt, nat_add, ...) land in follow-on
    tasks. -/
def seedPrelude (globalEnv : GlobalEnv) : GlobalEnv :=
  globalEnv
    |>.addDecl "nat_eq"  natEqType  natEqBody  (transparent := true)
    |>.addDecl "nat_lt"  natLtType  natLtBody  (transparent := true)
    -- `nat_mul` depends on `nat_add` via `Term.const` — add
    -- in dependency order so seedPrelude's output is a valid
    -- closed env without dangling references.
    |>.addDecl "nat_add" natAddType natAddBody (transparent := true)
    |>.addDecl "nat_sub" natSubType natSubBody (transparent := true)
    |>.addDecl "nat_mul" natMulType natMulBody (transparent := true)
    -- `nat_div` depends on `nat_sub` and `nat_lt`; `nat_mod`
    -- depends on `nat_div`, `nat_mul`, `nat_sub`.  Q73.
    |>.addDecl "nat_div" natDivType natDivBody (transparent := true)
    |>.addDecl "nat_mod" natModType natModBody (transparent := true)

/-- A `GlobalEnv` starting from `GlobalEnv.empty` seeded with
    every prelude fn.  Drop-in replacement for
    `GlobalEnv.empty` at the top of `elabFile` etc.  Zero cost
    when unused — the prelude fns sit in the env as
    `Term.const` entries until a caller invokes them. -/
def emptyWithPrelude : GlobalEnv :=
  seedPrelude GlobalEnv.empty

end FX.Derived.PreludeFn
