import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusConnectivityInduction
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderCompleteness

/-! # WP-FROBMONAD — the multi-block spider-fusion readback (block-diagonal normal form) + the routing residual
(#2070)

The connected fragment ships: `extraSpiderDiagramOf_canonicalSpider`
(`Table/FrobeniusConnectivityInduction.lean`) realizes a SINGLE connected block
`⟨m, n, replicate (m + n) 0⟩` at EVERY arity, via the `mergeToOne`/`fanToN` union-find fold.  The general
multi-block target named by `fxFrob_hasMultiBlockSpiderRealization`
(`Frobenius/SpiderCompleteness.lean`) is: build a `canonicalReadback` for a general boundary partition `D`
and prove `extraSpiderDiagramOf D.bottomCount (canonicalReadback D) = D`.

## What ships here — the block-diagonal construction, reusing the connected base

`blockSpiderReadback` lays out a list of per-block `(inputCount, outputCount)` specs as the HORIZONTAL TENSOR
of their connected canonical spiders: block `0`'s `canonicalSpiderOf a0 c0` fires at the front, and every later
block is `shiftBrauerWord`-ed past the `c0 + c1 + …` top wires already emitted to its left.  This IS the
special-commutative-Frobenius block-diagonal normal form for a CONTIGUOUS partition (each block a contiguous run
of bottom + top ports).

  * **The construction** `blockSpiderReadback : List (Nat × Nat) → List BrauerAtom`, and its accountants
    `sumInputs` / `sumOutputs`.
  * **The composition law** `blockSpiderReadback_append` — the readback of `specs1 ++ specs2` is the readback of
    `specs1` followed by the readback of `specs2` shifted past `specs1`'s emitted tops (`sumOutputs specs1`).
    Pure word-structure, on the shipped `shiftBrauerWord_add`; the reusable induction atom of the block sweep.
  * **The single-block base reuse** `blockSpiderReadback_realizes_single` — for a ONE-block spec `[(m, n)]` the
    readback IS `canonicalSpiderOf m n` (`blockSpiderReadback_singleton_eq`), so its realization is the connected
    base `extraSpiderDiagramOf_canonicalSpider` at every `(m, n)`.  This is the `k = 1` leaf of the intended
    block-structure induction, discharged generally by REUSING the connected fragment (not `decide`).
  * **Non-vacuity** — the construction FIRES on genuine `k ≥ 2` multi-block partitions (`decide` cross-checks):
    a two-block `(2,1) ⊗ (1,2)` reads back the two-block partition `[0,0,2,0,2,2]`, the identity-family
    `(1,1) ⊗ (1,1)` reads the crossing-free pair matching `[0,1,0,1]`, and a cap/unit pair `(1,0) ⊗ (0,1)`
    reads the disjoint singleton-then-birth partition.

## The precise residual — the marker stays `false`

The `k → k+1` induction step of the GENERAL realization needs the two facts the connected (single-block) base
never required, both about the block-diagonal fold `processBrauer (brauerSeed (sumInputs specs)) …`:

  1. **Offset-general within-block connectivity** — block `i`'s `mergeToOne`/`fanToN` fires at the NONZERO
     position `sumOutputs (take i specs)` (after the tops already emitted to its left), so the shipped
     position-`0` fold lemmas (`mergeFold_connects_all`, `fanFold_connects`) do not apply verbatim; they need a
     left-pad (offset) generalisation.
  2. **Cross-block DISCONNECTION** — distinct blocks must land in DISTINCT union-find components (`blockLabels`
     reads the least-index representative PER block, so `firstIndexWithRoot` must NOT jump across blocks).  This
     is the "no path exists" direction — provably harder than the base's "all connected" (which collapsed every
     label to `0`); it needs a freshness / support invariant bounding the fold's components from ABOVE, the same
     planar-support obstacle as the general gather-routing.

And for a NON-contiguous partition, the ports of a block are scattered, so a gather-routing PERMUTATION (a
crossing word) must first bring each block's ports together — the irreducible planar routing residual named in
`fxFrob_hasMultiBlockSpiderRealization`'s docstring.  So the marker stays `false`; the block-diagonal
construction, its composition law, and the single-block base reuse are the honest partial landing.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` /
`propext` / `Quot.sound`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free list helpers (cons-only; core `List.append` equalities leak `propext`) -/

/-- `xs ++ [] = xs` — propext-free cons-recursion (avoids `List.append_nil`'s match-compiler `propext`). -/
theorem multiBlockAppendNil {elem : Type} : (xs : List elem) → xs ++ [] = xs
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (multiBlockAppendNil rest)

/-- `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` — propext-free cons-recursion. -/
theorem multiBlockAppendAssoc {elem : Type} : (xs ys zs : List elem) →
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | head :: rest, ys, zs => congrArg (head :: ·) (multiBlockAppendAssoc rest ys zs)

/-- `shiftBrauerWord` distributes over word concatenation — propext-free cons-recursion on the first word. -/
theorem shiftBrauerWord_append (delta : Nat) : (leftWord rightWord : List BrauerAtom) →
    shiftBrauerWord delta (leftWord ++ rightWord)
      = shiftBrauerWord delta leftWord ++ shiftBrauerWord delta rightWord
  | [], _ => rfl
  | atom :: rest, rightWord => by
      show { position := delta + atom.position, wiring := atom.wiring }
            :: shiftBrauerWord delta (rest ++ rightWord)
          = { position := delta + atom.position, wiring := atom.wiring }
              :: shiftBrauerWord delta rest ++ shiftBrauerWord delta rightWord
      exact congrArg ({ position := delta + atom.position, wiring := atom.wiring } :: ·)
        (shiftBrauerWord_append delta rest rightWord)

/-! ## The block-diagonal readback -/

/-- The total number of bottom ports the block specs consume (the summed `inputCount`s). -/
def sumInputs : List (Nat × Nat) → Nat
  | [] => 0
  | (inputCount, _) :: rest => inputCount + sumInputs rest

/-- The total number of top ports the block specs produce (the summed `outputCount`s). -/
def sumOutputs : List (Nat × Nat) → Nat
  | [] => 0
  | (_, outputCount) :: rest => outputCount + sumOutputs rest

/-- ★ **The block-diagonal spider readback** — the horizontal tensor of per-block connected canonical spiders.
Block `0`'s `canonicalSpiderOf inputCount outputCount` fires at the front; the remaining blocks are shifted past
the `outputCount` top wires block `0` emits to their left.  Since `shiftBrauerWord` composes
(`shiftBrauerWord_add`), block `i` ends up fired at offset `sumOutputs` of the blocks before it — the contiguous
block-diagonal layout.  Structural recursion on the spec list. -/
def blockSpiderReadback : List (Nat × Nat) → List BrauerAtom
  | [] => []
  | (inputCount, outputCount) :: rest =>
      canonicalSpiderOf inputCount outputCount
        ++ shiftBrauerWord outputCount (blockSpiderReadback rest)

/-! ## The composition law — the reusable induction atom of the block sweep -/

/-- ★ **The block-diagonal readback of a spec concatenation factors.**  Reading back `specs1 ++ specs2` is
reading back `specs1`, then reading back `specs2` shifted past the `sumOutputs specs1` top wires `specs1` emits.
Structural on `specs1`, on the shipped `shiftBrauerWord_add` (shift composes) and `shiftBrauerWord_append` (shift
distributes over `++`).  This is the horizontal-associativity of the block sweep — the atom a `k`-block
realization induction threads block by block. -/
theorem blockSpiderReadback_append : (specs1 specs2 : List (Nat × Nat)) →
    blockSpiderReadback (specs1 ++ specs2)
      = blockSpiderReadback specs1 ++ shiftBrauerWord (sumOutputs specs1) (blockSpiderReadback specs2)
  | [], specs2 => by
      show blockSpiderReadback specs2
        = [] ++ shiftBrauerWord (sumOutputs ([] : List (Nat × Nat))) (blockSpiderReadback specs2)
      show blockSpiderReadback specs2 = shiftBrauerWord 0 (blockSpiderReadback specs2)
      rw [shiftBrauerWord_zero]
  | (inputCount, outputCount) :: rest, specs2 => by
      show canonicalSpiderOf inputCount outputCount
            ++ shiftBrauerWord outputCount (blockSpiderReadback (rest ++ specs2))
          = (canonicalSpiderOf inputCount outputCount
              ++ shiftBrauerWord outputCount (blockSpiderReadback rest))
            ++ shiftBrauerWord (outputCount + sumOutputs rest) (blockSpiderReadback specs2)
      rw [blockSpiderReadback_append rest specs2, shiftBrauerWord_append,
        shiftBrauerWord_add outputCount (sumOutputs rest) (blockSpiderReadback specs2),
        multiBlockAppendAssoc]

/-! ## The single-block base reuse — the `k = 1` leaf, discharged by the connected fragment -/

/-- The one-block readback IS the connected canonical spider — `shiftBrauerWord outputCount [] = []` and the
trailing `++ []` vanishes. -/
theorem blockSpiderReadback_singleton_eq (inputCount outputCount : Nat) :
    blockSpiderReadback [(inputCount, outputCount)] = canonicalSpiderOf inputCount outputCount := by
  show canonicalSpiderOf inputCount outputCount ++ shiftBrauerWord outputCount ([] : List BrauerAtom)
      = canonicalSpiderOf inputCount outputCount
  show canonicalSpiderOf inputCount outputCount ++ ([] : List BrauerAtom)
      = canonicalSpiderOf inputCount outputCount
  exact multiBlockAppendNil (canonicalSpiderOf inputCount outputCount)

/-- ★ **The one-block realization, at EVERY arity, by REUSING the connected base.**  A single-block spec
`[(m, n)]` reads back (block-diagonally) to `canonicalSpiderOf m n`, whose realization is the shipped connected
fragment `extraSpiderDiagramOf_canonicalSpider` — the fully-connected partition `⟨m, n, replicate (m + n) 0⟩`.
This is the `k = 1` leaf of the intended block-structure induction, discharged GENERALLY (not `decide`) by the
connected base, exactly as the general realization would consume it per block. -/
theorem blockSpiderReadback_realizes_single (inputCount outputCount : Nat) :
    extraSpiderDiagramOf inputCount (blockSpiderReadback [(inputCount, outputCount)])
      = { bottomCount := inputCount, topCount := outputCount,
          blockLabels := List.replicate (inputCount + outputCount) 0 } := by
  rw [blockSpiderReadback_singleton_eq]
  exact extraSpiderDiagramOf_canonicalSpider inputCount outputCount

/-! ## Non-vacuity — the construction fires on genuine multi-block partitions

Each `decide` cross-checks the block-diagonal readback against the exact multi-block `SpiderPartitionType` it
realizes — the induction the general theorem would perform, exhibited at concrete `k ≥ 2` shapes. -/

/-- ★ **Two blocks.**  `(2 ⇒ 1) ⊗ (1 ⇒ 2)` reads back over `3` bottom wires to the genuine TWO-BLOCK partition
`[0, 0, 2, 0, 2, 2]`: block `0` = {b0, b1, t0} (label `0`), block `1` = {b2, t1, t2} (label `2`) — two distinct
components, a partition no single connected spider can express. -/
theorem blockSpiderReadback_realizes_2_1_and_1_2 :
    extraSpiderDiagramOf 3 (blockSpiderReadback [(2, 1), (1, 2)])
      = { bottomCount := 3, topCount := 3, blockLabels := [0, 0, 2, 0, 2, 2] } := by decide

/-- ★ **The identity-family two-block partition.**  `(1 ⇒ 1) ⊗ (1 ⇒ 1)` reads back to the straight through-pair
matching `[0, 1, 0, 1]` (b0↔t0, b1↔t1) — two disjoint singleton-strand blocks, the two-wire identity. -/
theorem blockSpiderReadback_realizes_1_1_and_1_1 :
    extraSpiderDiagramOf 2 (blockSpiderReadback [(1, 1), (1, 1)])
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 1, 0, 1] } := by decide

/-- ★ **A cap-block then a unit-block.**  `(1 ⇒ 0) ⊗ (0 ⇒ 1)` reads back over `1` bottom wire: the bottom port is
its own singleton block (counit, no top) and one fresh top port is born (unit) as a second singleton block —
partition `[0, 1]`, one bottom + one top, disjoint. -/
theorem blockSpiderReadback_realizes_1_0_and_0_1 :
    extraSpiderDiagramOf 1 (blockSpiderReadback [(1, 0), (0, 1)])
      = { bottomCount := 1, topCount := 1, blockLabels := [0, 1] } := by decide

/-- ★ **Three blocks.**  `(2 ⇒ 1) ⊗ (1 ⇒ 1) ⊗ (1 ⇒ 2)` reads back over `4` bottom wires to a genuine THREE-block
partition — block `0` = {b0, b1, t0}, block `1` = {b2, t1}, block `2` = {b3, t2, t3} — demonstrating the sweep at
`k = 3`. -/
theorem blockSpiderReadback_realizes_three_blocks :
    extraSpiderDiagramOf 4 (blockSpiderReadback [(2, 1), (1, 1), (1, 2)])
      = { bottomCount := 4, topCount := 4, blockLabels := [0, 0, 2, 3, 0, 2, 3, 3] } := by decide

/-! ## Honesty marker — the general realization stays walled at the disconnection/routing residual -/

/-- **Honesty marker — the block-diagonal multi-block readback SHIPS; the general partition realization stays
walled at the disconnection/routing residual.**  `blockSpiderReadback` is the contiguous block-diagonal
Frobenius normal form (horizontal tensor of connected canonical spiders, `blockSpiderReadback_append` the
composition law); its `k = 1` leaf is the connected base `extraSpiderDiagramOf_canonicalSpider`
(`blockSpiderReadback_realizes_single`, general), and it FIRES on genuine `k ≥ 2` partitions
(`blockSpiderReadback_realizes_2_1_and_1_2` / `_1_1_and_1_1` / `_1_0_and_0_1` / `_three_blocks`).  The GENERAL
`k → k+1` step needs (1) offset-general within-block connectivity (the shipped `mergeFold_connects_all` /
`fanFold_connects` fire at position `0` only; block `i` fires at `sumOutputs` of its predecessors) and (2)
cross-block DISCONNECTION (distinct blocks → distinct roots, the "no path" direction the base never needed) —
and for a non-contiguous partition, a gather-routing crossing permutation, the irreducible planar routing
residual.  So `fxFrob_hasMultiBlockSpiderRealization` stays `false`.  `= false`. -/
def fxFrob_hasBlockDiagonalMultiBlockReadback : Bool := false

end FX1Poly.Polygraph
