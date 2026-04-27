// Q60: `fxi run` pre-registers all decl bodies before the
// display loop so that a zero-arg fn whose body forward-
// references another fn renders correctly.
//
// Pre-Q60 output for this file:
//
//   consumer = ?var0[Unit.tt]    <-- garbled: Term.const
//                                   "producer" unresolved at
//                                   evaluation-display time
//   producer = 1
//   main     = 1                  <-- main worked because at
//                                   its display point both
//                                   referents were registered
//
// Post-Q60 output:
//
//   consumer = 1
//   producer = 1
//   main     = 1
//
// The kernel's forward-ref via `Term.const` was already
// correct for type-checking (Q12/Q33 two-pass invariant);
// Q60 extends the same ordering to runtime display.
fn consumer() : Nat = producer();

fn producer() : Nat = Nat.Succ(Nat.Zero);

fn main() : Nat = consumer();
