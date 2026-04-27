// M2 milestone: records + let + blocks — non-trivial program.
//
// Weaves together feature axes that earlier conformance files
// exercise only in isolation:
//
//   * 31_record_literal — ONE record with ONE projection.
//   * 07_let_simple     — ONE let in a block.
//   * 10_multi_decl     — multiple decls, no records.
//   * 08_rec_double     — self-recursion.
//   * 13_named_args     — multi-arg named calls.
//
// This file composes TWO record types, block-form fn bodies
// with multiple sequential let bindings that project record
// fields AND feed a recursive function, named-arg dispatch
// through the block, and cross-decl reference resolved by the
// two-pass checkFile (§Q33, Term.const knot).
//
// Graduation criterion for milestone M2: `fxi test` accepts
// this file; `lake build` stays green; no new axioms surface
// in the trust closure.
type server_config {
  port:    Nat;
  backlog: Nat;
};

type pool_stats {
  live: Nat;
  idle: Nat;
};

fn fresh_config() : server_config =
  server_config {
    port:    Nat.Succ(Nat.Succ(Nat.Zero)),
    backlog: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))),
  };

fn zero_stats() : pool_stats =
  pool_stats { live: Nat.Zero, idle: Nat.Zero };

fn double_count(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => Nat.Succ(Nat.Succ(double_count(p)));
end match;

fn capacity(cfg: server_config) : Nat
begin fn
  let listen_slots = cfg.backlog;
  let doubled      = double_count(listen_slots);
  let with_buffer  = Nat.Succ(doubled);
  return with_buffer;
end fn;

fn account_new(stats: pool_stats, incoming: Nat) : Nat
begin fn
  let baseline    = stats.live;
  let after_one   = Nat.Succ(baseline);
  let plus_extra  = Nat.Succ(after_one);
  return plus_extra;
end fn;

fn main() : Nat
begin fn
  let cfg           = fresh_config();
  let declared_cap  = capacity(cfg);
  let metrics       = zero_stats();
  let finalized     = account_new(stats: metrics, incoming: declared_cap);
  return finalized;
end fn;
