// Q74: classic algorithms composing Q68-Q73 end-to-end, plus
// regression coverage for the `if`-recursion eager-evaluation
// trap fixed in `FX/Eval/Interp.lean`.
//
// Before Q74, `indRec` in the interpreter eagerly evaluated
// ALL method arms before consulting the target's ctor index.
// For an `if b == Zero; a else gcd(...) end if` desugar the
// else-arm invoked `gcd` recursively BEFORE the Bool guard
// fired — infinite recursion, OOM.
//
// The fix (Interp.lean `.indRec` case): evaluate the target
// first, then evaluate ONLY the matching method Term.  Eager
// eval of the other methods is retained ONLY for recursive-
// typed ctor args (Nat.Succ payload), where the method bodies
// are lambdas whose closures don't immediately recurse.
//
// This conformance file is the canary: if the bug comes back,
// `gcd_small`, `gcd_9_6`, `is_even`, `is_odd` will time out
// instead of computing a value.

// Small Nat ladder to avoid verbose `Succ(Succ(...))` chains.
fn zero_n() : Nat = Nat.Zero;
fn one_n() : Nat = Nat.Succ(zero_n());
fn two_n() : Nat = Nat.Succ(one_n());
fn three_n() : Nat = Nat.Succ(two_n());
fn four_n() : Nat = Nat.Succ(three_n());
fn five_n() : Nat = Nat.Succ(four_n());
fn six_n() : Nat = Nat.Succ(five_n());
fn seven_n() : Nat = Nat.Succ(six_n());
fn nine_n() : Nat = Nat.Succ(Nat.Succ(seven_n()));

// Factorial: exercises * (Q70 nat_mul) through a self-
// recursive match on Nat.  The Succ arm uses the pattern-
// bound p twice — first as `Nat.Succ(p)`, then as `factorial
// (p)` — so Nat's `@[copy]` grade (Q55 seeding) must be in
// effect for the elaborator to accept.
fn factorial(n: Nat) : Nat = match n;
  Zero    => Nat.Succ(Nat.Zero);
  Succ(p) => Nat.Succ(p) * factorial(p);
end match;

// Accumulator-style Fibonacci.  Keeps each arm's use of every
// Nat once, sidestepping any linearity friction even without
// the @[copy] promotion.
fn fib_acc(n: Nat, a: Nat, b: Nat) : Nat = match n;
  Zero    => a;
  Succ(p) => fib_acc(n: p, a: b, b: a + b);
end match;

fn fib(n: Nat) : Nat = fib_acc(n: n, a: Nat.Zero, b: Nat.Succ(Nat.Zero));

// GCD via the Euclidean algorithm — the canary program for the
// Q74 bug fix.  Pre-fix, this hung; post-fix it terminates in
// log(max(a,b)) iterations because `a % b` strictly decreases
// the pair's second component per step.  Uses `==` (Q68) for
// the guard and `%` (Q73) for the recursive arg.
fn gcd(a: Nat, b: Nat) : Nat =
  if b == Nat.Zero;
    a
  else
    gcd(a: b, b: a % b)
  end if;

// Power: pow(base, 0) = 1, pow(base, Succ(p)) = base * pow(p).
// Uses `*` (Q70) in the recursive step.
fn pow(base: Nat, exp: Nat) : Nat = match exp;
  Zero    => Nat.Succ(Nat.Zero);
  Succ(p) => base * pow(base: base, exp: p);
end match;

// Parity via `%` and `==` — two operators in one line, each
// routing through a different prelude fn.
fn is_even(n: Nat) : Bool = n % two_n() == Nat.Zero;
fn is_odd(n: Nat) : Bool = not is_even(n);

// --- Test callers (each fn's result pinned at `fxi run`) ---

fn fact_3() : Nat = factorial(three_n());        // 3! = 6
fn fact_4() : Nat = factorial(four_n());         // 4! = 24

fn fib_0() : Nat = fib(Nat.Zero);                // fib(0) = 0
fn fib_1() : Nat = fib(one_n());                 // fib(1) = 1
fn fib_5() : Nat = fib(five_n());                // fib(5) = 5
fn fib_7() : Nat = fib(seven_n());               // fib(7) = 13

// GCD cases covering: both zero, one zero, coprime, shared factor.
fn gcd_0_0() : Nat = gcd(a: zero_n(), b: zero_n());    // 0
fn gcd_5_0() : Nat = gcd(a: five_n(), b: zero_n());    // 5
fn gcd_0_5() : Nat = gcd(a: zero_n(), b: five_n());    // 5
fn gcd_6_4() : Nat = gcd(a: six_n(), b: four_n());     // 2
fn gcd_9_6() : Nat = gcd(a: nine_n(), b: six_n());     // 3
fn gcd_7_3() : Nat = gcd(a: seven_n(), b: three_n());  // 1 (coprime)

fn pow_2_3() : Nat = pow(base: two_n(), exp: three_n());  // 8
fn pow_3_2() : Nat = pow(base: three_n(), exp: two_n());  // 9
fn pow_5_0() : Nat = pow(base: five_n(), exp: zero_n());  // 1

fn even_four() : Bool = is_even(four_n());       // true
fn even_five() : Bool = is_even(five_n());       // false
fn odd_three() : Bool = is_odd(three_n());       // true
fn odd_zero() : Bool = is_odd(Nat.Zero);         // false

fn main() : Nat = fact_4();
