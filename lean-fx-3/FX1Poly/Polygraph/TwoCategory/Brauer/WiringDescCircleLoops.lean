import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCupChain
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescJoinEvents
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable

/-! # BRAUER r30 B1 — THE CIRCLE ACCOUNTING: `(processBrauer state (circleWord n)).loops = state.loops + n`

The r29 loops wall (`Brauer/WiringDescFoldLoops.lean`) named TWO legs of the missing `F.loops = d.loops` field.  This
file DISCHARGES the first — the circle-loop accounting `(processBrauer state (circleWord loops)).loops =
state.loops + loops` — as a clean structural induction on `loops`, the exact loop-tracking mirror of the shipped
`circleFold_openWires` (which already proves the OPEN-WIRE half of the same iteration by the same induction).

## The one load-bearing fact

Each `[cupAt 0, capAt 0]` iteration of `circleWord`:
  * the cup allocates a fresh CONNECTED pair `(nextFresh, nextFresh + 1)` at the front, closing NO loop
    (`stepWiring_cup_loops`: the two fresh legs are distinct fresh nodes, `isSameComponent_freshPair_eq_false`);
  * the following cap fires at position `0` on exactly that pair, now same-component
    (`stepWiring_cup_head`'s connectivity output), closing EXACTLY ONE loop
    (`stepWiring_cap_loops_ofConnected`: the cap trace's single arc is already connected).

So the pair contributes `+1` loop and is consumed, leaving the boundary untouched (`circleFold_openWires`).
`oneCircleLoops` welds the two into `+1` per circle; `circleFold_loops` folds it to `+loops`, threading freshness /
forest / `0 < nextFresh` (preserved by `wiringDescStateFresh_stepWiring`, `processBrauer_links_isUnionFindForest`,
`stepWiring_nextFresh`).

Truth-probed by eval on the seed (`circleWord 3 ↦ 3`, `circleWord 5 ↦ 5`, `bottomCount 0 ↦ 3`) and on a
preexisting-loops state (`4 + 3 = 7`) before the induction was written.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `propext`-safe
(`countJoinEventLoops` reduction, `Nat.add_comm`/`zero_add`/`add_zero`/`add_assoc` only).  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 1 — the two per-step loop lemmas (cup adds 0, cap-on-connected adds 1) -/

/-- ★ **A cup at position `0` closes NO loop.**  Via the loops reification `stepWiring_loops_eq`: the cup's decoded
arc trace is its single fresh pair `(nextFresh, nextFresh + 1)`, which is never already connected
(`isSameComponent_freshPair_eq_false`, needing only that every link child is below `nextFresh`), so
`countJoinEventLoops` contributes `0`.  The loop-tracking companion of `stepWiring_cup_head`. -/
theorem stepWiring_cup_loops (state : WireState)
    (childrenBounded : ∀ edge ∈ state.links, edge.1 < state.nextFresh) :
    (stepWiring state 0 cupWiring).loops = state.loops := by
  rw [stepWiring_loops_eq state 0 cupWiring]
  have htrace : wiringArcEvents (stepWiringInputNodes state 0 cupWiring) (stepWiringOutputNodes state cupWiring)
        cupWiring.inputCount cupWiring.arcs
      = [(state.nextFresh, state.nextFresh + 1)] := by
    show [(0 + state.nextFresh, 1 + state.nextFresh)] = [(state.nextFresh, state.nextFresh + 1)]
    rw [Nat.zero_add, Nat.add_comm 1 state.nextFresh]
  rw [htrace]
  show state.loops
      + ((isSameComponent state.links state.nextFresh (state.nextFresh + 1)).toNat
          + countJoinEventLoops [] (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)))
      + cupWiring.internalLoops = state.loops
  rw [isSameComponent_freshPair_eq_false state.nextFresh state.links childrenBounded state.nextFresh
    (Nat.le_refl _)]
  rfl

/-- ★ **A cap at position `0`, fired on an ALREADY-CONNECTED head pair, closes EXACTLY ONE loop.**  Via
`stepWiring_loops_eq`: the cap's decoded arc trace is its two consumed head wires `(firstWire, secondWire)`, and the
hypothesis `conn` makes that single arc already same-component, so `countJoinEventLoops` contributes `1`.  The
loop-tracking companion of `stepWiring_cap_head`. -/
theorem stepWiring_cap_loops_ofConnected (state : WireState) (firstWire secondWire : Nat) (rest : List Nat)
    (hopen : state.openWires = firstWire :: secondWire :: rest)
    (conn : isSameComponent state.links firstWire secondWire = true) :
    (stepWiring state 0 capWiring).loops = state.loops + 1 := by
  rw [stepWiring_loops_eq state 0 capWiring]
  have htrace : wiringArcEvents (stepWiringInputNodes state 0 capWiring) (stepWiringOutputNodes state capWiring)
        capWiring.inputCount capWiring.arcs
      = [(firstWire, secondWire)] := by
    show wiringArcEvents (natListSliceAt state.openWires 0 2) [] 2 [(0, 1)] = [(firstWire, secondWire)]
    rw [hopen]
    rfl
  rw [htrace]
  show state.loops
      + ((isSameComponent state.links firstWire secondWire).toNat
          + countJoinEventLoops [] (unionFindJoin state.links firstWire secondWire))
      + capWiring.internalLoops = state.loops + 1
  rw [conn]
  rfl

/-! ## Section 2 — the one-circle `+1` weld -/

/-- ★ **One circle (`[cupAt 0, capAt 0]`) adds exactly one loop and preserves nothing else that matters.**  The cup
prepends a fresh connected pair (loops unchanged, `stepWiring_cup_loops`) whose two legs the following cap consumes,
now same-component (`stepWiring_cup_head`), closing one loop (`stepWiring_cap_loops_ofConnected`). -/
theorem oneCircleLoops (state : WireState)
    (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links) :
    (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0))).loops
      = state.loops + 1 := by
  rw [processBrauer_append (cupWord (natReplicate 1 0)) state (capWord (natReplicate 1 0))]
  show (stepWiring (stepWiring state 0 cupWiring) 0 capWiring).loops = state.loops + 1
  obtain ⟨hCupOpen, hCupConn⟩ := stepWiring_cup_head state forest
  have hCupLoops : (stepWiring state 0 cupWiring).loops = state.loops :=
    stepWiring_cup_loops state (fun edge edgeMem => (fresh.2 edge edgeMem).1)
  rw [stepWiring_cap_loops_ofConnected (stepWiring state 0 cupWiring) (0 + state.nextFresh)
      (1 + state.nextFresh) state.openWires hCupOpen hCupConn, hCupLoops]

/-! ## Section 3 — the circle accounting (the structural induction) -/

/-- One `stepWiring` never decreases `nextFresh`. -/
private theorem stepWiring_nextFresh_le (state : WireState) (position : Nat) (desc : WiringDesc) :
    state.nextFresh ≤ (stepWiring state position desc).nextFresh := by
  rw [stepWiring_nextFresh]; exact Nat.le_add_right _ _

/-- ★★★ **THE CIRCLE ACCOUNTING.**  `(processBrauer state (circleWord loops)).loops = state.loops + loops` for every
fresh forest state with a positive fresh counter — the first of the two legs the r29 loops wall named.  Structural on
`loops`: the base is `state.loops + 0`; each step factors `circleWord (loops + 1)` as one circle then the rest
(`processBrauer_append`), the one-circle `+1` weld (`oneCircleLoops`) plus the inductive `+ loops` on the
freshness/forest-preserved intermediate (`wiringDescStateFresh_stepWiring`,
`processBrauer_links_isUnionFindForest`).  The exact loop-tracking mirror of the shipped `circleFold_openWires`. -/
theorem circleFold_loops : (loops : Nat) → (state : WireState) →
    WiringDescStateFresh state → isUnionFindForest state.links → 0 < state.nextFresh →
    (processBrauer state (circleWord loops)).loops = state.loops + loops
  | 0, state, _, _, _ => (Nat.add_zero state.loops).symm
  | loops + 1, state, fresh, forest, nfPos => by
      have hstep : processBrauer state (circleWord (loops + 1))
          = processBrauer (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0)))
              (circleWord loops) :=
        processBrauer_append (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0)) state (circleWord loops)
      have oneLoops := oneCircleLoops state fresh forest
      have forest1 : isUnionFindForest
          (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0))).links :=
        processBrauer_links_isUnionFindForest _ state forest
      have fresh1 : WiringDescStateFresh
          (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0))) := by
        rw [processBrauer_append (cupWord (natReplicate 1 0)) state (capWord (natReplicate 1 0))]
        show WiringDescStateFresh (stepWiring (stepWiring state 0 cupWiring) 0 capWiring)
        have fresh0 := wiringDescStateFresh_stepWiring state 0 cupWiring fresh nfPos
        have nfPos0 : 0 < (stepWiring state 0 cupWiring).nextFresh :=
          Nat.lt_of_lt_of_le nfPos (stepWiring_nextFresh_le state 0 cupWiring)
        exact wiringDescStateFresh_stepWiring (stepWiring state 0 cupWiring) 0 capWiring fresh0 nfPos0
      have nfPos1 : 0 < (processBrauer state (cupWord (natReplicate 1 0) ++ capWord (natReplicate 1 0))).nextFresh := by
        rw [processBrauer_append (cupWord (natReplicate 1 0)) state (capWord (natReplicate 1 0))]
        show 0 < (stepWiring (stepWiring state 0 cupWiring) 0 capWiring).nextFresh
        exact Nat.lt_of_lt_of_le nfPos
          (Nat.le_trans (stepWiring_nextFresh_le state 0 cupWiring)
            (stepWiring_nextFresh_le (stepWiring state 0 cupWiring) 0 capWiring))
      rw [hstep, circleFold_loops loops _ fresh1 forest1 nfPos1, oneLoops, Nat.add_assoc,
        Nat.add_comm 1 loops]

/-! ## Section 4 — the honesty marker -/

/-- ★★ **Honesty marker — the circle-loop accounting is SHIPPED (r30 B1).**  `circleFold_loops` proves, zero-axiom and
structural, `(processBrauer state (circleWord loops)).loops = state.loops + loops` for every fresh forest state —
the first of the two legs the r29 loops wall (`fxBrauer_hasFoldLoopsCorrectness`) named.  The one-circle `+1` weld
(`oneCircleLoops`) rests on the two new per-step loop lemmas `stepWiring_cup_loops` (a cup closes no loop, by fresh
distinctness) and `stepWiring_cap_loops_ofConnected` (a cap on an already-connected pair closes exactly one loop),
both via the shipped loops reification `stepWiring_loops_eq`.  Alone it does NOT close the loops field —
`fxBrauer_hasFoldLoopsCorrectness` stays `false` until the boundary-word-adds-0-loops leg also lands.  `= true`. -/
def fxBrauer_hasCircleLoopAccounting : Bool := true

end FX1Poly.Polygraph
