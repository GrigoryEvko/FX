// For-loop desugaring (task B10).  Exclusive-range `for i in
// 0..N; body end for` elaborates to `indRec "Nat" (\ _. Unit)
// [Unit.tt, \ i. \ _rec. body] N` in the kernel.  Execution
// order on the conformance runner's elaboration path: parser
// accepts the syntax, elaborator translates to indRec on Nat,
// type checker confirms `Unit` return.
//
// V1 restrictions exercised by this file:
//   * lo is literal 0
//   * body has type Unit
//   * no break/continue/inclusive range/stepped range
fn run_loop(count: Nat) : Unit = for i in 0..count; Unit.tt end for;
