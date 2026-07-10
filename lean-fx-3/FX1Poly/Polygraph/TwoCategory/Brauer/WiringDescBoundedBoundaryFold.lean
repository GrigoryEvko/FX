import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryComponents
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescGeneratorBridge

/-! # BRAUER-MIDDLE r10 B2 — the T-DISJOINT fold lift:
`boundedBoundaryComponents` survives the WHOLE `processBrauer` fold of a well-formed Brauer word

The three per-atom T-DISJOINT preservations are shipped
(`Brauer/WiringDescBoundedBoundaryComponents.lean`): `boundedBoundaryComponents_stepCap` /
`_stepCup` / `_stepCrossing`.  But `processBrauer` fires the GENERIC engine
`stepBrauerAtom state atom = stepWiring state atom.position atom.wiring`, dispatching on `atom.wiring`; the cup /
cap preservations are stated over the hardcoded `stepCup` / `stepCap`.  The r10 B1 bridges
(`stepWiring_capWiring_eq_stepCap` / `stepWiring_cupWiring_eq_stepCup`) close that gap, so this file lifts the
per-atom preservations to the whole fold.

Two genuinely-new pieces:

  * ★ **`WellFormedBrauerFold`** — the threaded word-predicate a Brauer word must satisfy for the lift: every atom
    is one of the three generators (`isBrauerGenerator`, the ALPHABET restriction — a general/opaque wiring can
    over-connect and has no preservation) AND its firing window fits the CURRENT state's open-wire list
    (`atom.position + atom.wiring.inputCount ≤ state.openWires.length` — genuinely NOT derivable from the four
    `BrauerStateConditions`, since out-of-range firings are legal reachable states,
    `wiringDescDisjointWindowFresh_false`).

  * ★ **`boundedBoundaryComponents_stepBrauerAtom`** / **`_processBrauer`** — the per-atom dispatch (routing cup /
    cap through the B1 bridges, crossing directly) and the structural fold lift, threading the four
    `BrauerStateConditions` (`brauerStateConditions_stepBrauerAtom`) and the well-formedness alongside the
    invariant.

`boundedBoundaryComponents_reachable` reads the payoff off the seed: T-DISJOINT holds at every reachable state of
a well-formed Brauer word.  This flips the NEW sub-marker `fxBrauer_hasBoundedBoundaryFoldLift`.  It does NOT
close `fxBrauer_hasTagCorrDisjoint` (the full T-DISJOINT flip additionally needs the EXTRACTION consequence —
`partnerIndexOf` reads the `d`-partner — whose `connected` input needs the two-source T-CONNECT-arc + through-perm
connectivity assembly over the 6-phase word; that is the r11 target).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The alphabet restriction + the threaded word-predicate -/

/-- ★ **The Brauer alphabet.**  A wiring is a Brauer generator iff it is the cup, the cap, or the crossing.  The
fold lift has NO arm for a general / opaque wiring (which can over-connect and carries no per-atom preservation),
so the well-formedness predicate must carry this restriction; standard-form words satisfy it structurally (they
are built purely from `crossingAt` / `capAt` / `cupAt`). -/
def isBrauerGenerator (desc : WiringDesc) : Prop :=
  desc = cupWiring ∨ desc = capWiring ∨ desc = crossingWiring

/-- ★ **The threaded well-formedness predicate for a Brauer word.**  Along the fold from `state`, every atom must
be a Brauer generator (alphabet) AND fire in range at the CURRENT state (`position + inputCount ≤ openWires.length`
— the per-atom window-fit the three preservations each consume, and which is NOT derivable from the reachable-state
conditions).  Structural on the atom list; the state is threaded through `stepBrauerAtom`. -/
def WellFormedBrauerFold : WireState → List BrauerAtom → Prop
  | _, [] => True
  | state, atom :: rest =>
      isBrauerGenerator atom.wiring
        ∧ atom.position + atom.wiring.inputCount ≤ state.openWires.length
        ∧ WellFormedBrauerFold (stepBrauerAtom state atom) rest

/-! ## The per-atom dispatch -/

/-- ★ **One well-formed Brauer atom preserves T-DISJOINT.**  Dispatch on the generator: a cup routes through the
B1 cup bridge to `boundedBoundaryComponents_stepCup`, a cap through the B1 cap bridge to `_stepCap`, a crossing
directly to `_stepCrossing` (already in generic `stepWiring` form).  The per-atom window-fit `windowFit` supplies
each preservation's window premise (`positionLe` for the cup, `windowInRange` for cap / crossing). -/
theorem boundedBoundaryComponents_stepBrauerAtom (bottomCount : Nat) (state : WireState) (atom : BrauerAtom)
    (cond : BrauerStateConditions bottomCount state)
    (gen : isBrauerGenerator atom.wiring)
    (windowFit : atom.position + atom.wiring.inputCount ≤ state.openWires.length)
    (bounded : boundedBoundaryComponents bottomCount state) :
    boundedBoundaryComponents bottomCount (stepBrauerAtom state atom) := by
  obtain ⟨atomPosition, atomWiring⟩ := atom
  show boundedBoundaryComponents bottomCount (stepWiring state atomPosition atomWiring)
  rcases gen with hcup | hcap | hcross
  · subst hcup
    rw [stepWiring_cupWiring_eq_stepCup state atomPosition cond.fresh]
    exact boundedBoundaryComponents_stepCup bottomCount state atomPosition cond.fresh cond.forest cond.nfPos
      cond.bottomLe windowFit bounded
  · subst hcap
    rw [stepWiring_capWiring_eq_stepCap state atomPosition windowFit]
    exact boundedBoundaryComponents_stepCap bottomCount state atomPosition cond.forest windowFit bounded
  · subst hcross
    exact boundedBoundaryComponents_stepCrossing bottomCount state atomPosition cond.fresh cond.forest
      cond.nfPos cond.bottomLe windowFit bounded

/-! ## The fold lift -/

/-- ★ **The WHOLE `processBrauer` fold preserves T-DISJOINT for a well-formed Brauer word.**  Structural on the
atom list: the head atom preserves the invariant (`boundedBoundaryComponents_stepBrauerAtom`) and the four
reachable-state conditions (`brauerStateConditions_stepBrauerAtom`); the tail's well-formedness threads the new
state. -/
theorem boundedBoundaryComponents_processBrauer (bottomCount : Nat) :
    (atoms : List BrauerAtom) → (state : WireState) →
    BrauerStateConditions bottomCount state → WellFormedBrauerFold state atoms →
    boundedBoundaryComponents bottomCount state →
    boundedBoundaryComponents bottomCount (processBrauer state atoms)
  | [], _, _, _, bounded => bounded
  | atom :: rest, state, cond, wellFormed, bounded => by
      obtain ⟨gen, windowFit, wellRest⟩ := wellFormed
      exact boundedBoundaryComponents_processBrauer bottomCount rest (stepBrauerAtom state atom)
        (brauerStateConditions_stepBrauerAtom bottomCount state atom cond) wellRest
        (boundedBoundaryComponents_stepBrauerAtom bottomCount state atom cond gen windowFit bounded)

/-- ★ **T-DISJOINT holds at every reachable state of a well-formed Brauer word.**  Reads the fold lift off the
seed: the fresh seed satisfies the four reachable-state conditions (`brauerStateConditions_seed`, for
`0 < bottomCount`) and T-DISJOINT (`boundedBoundaryComponents_seed`), so every prefix of a well-formed word keeps
`boundedBoundaryComponents`. -/
theorem boundedBoundaryComponents_reachable (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (atoms : List BrauerAtom) (wellFormed : WellFormedBrauerFold (brauerSeed bottomCount) atoms) :
    boundedBoundaryComponents bottomCount (processBrauer (brauerSeed bottomCount) atoms) :=
  boundedBoundaryComponents_processBrauer bottomCount atoms (brauerSeed bottomCount)
    (brauerStateConditions_seed bottomCount bottomPos) wellFormed
    (boundedBoundaryComponents_seed bottomCount)

/-! ## Non-vacuity — a well-formed mixed-diagram word -/

/-- ★ **A well-formed two-atom mixed word.**  `[capAt 0, cupAt 0]` over `bottomCount = 2` is well-formed: cap is a
generator firing in range (`0 + 2 ≤ 2`), then over the cap's emptied open wires the cup is a generator firing in
range (`0 + 0 ≤ 0`).  So `boundedBoundaryComponents_reachable` applies non-vacuously — a mixed diagram the identity
seed does not cover. -/
theorem wellFormedBrauerFold_capThenCup :
    WellFormedBrauerFold (brauerSeed 2) [capAt 0, cupAt 0] :=
  ⟨Or.inr (Or.inl rfl), by decide, Or.inl rfl, by decide, trivial⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the T-DISJOINT fold lift is SHIPPED.**  The three shipped per-atom preservations lift to
the WHOLE `processBrauer` fold of a well-formed Brauer word: `boundedBoundaryComponents_stepBrauerAtom` dispatches
each atom (cup / cap through the r10 B1 bridges, crossing directly) and `boundedBoundaryComponents_processBrauer`
threads it structurally, so `boundedBoundaryComponents_reachable` shows T-DISJOINT holds at EVERY reachable state
of a well-formed Brauer word (`WellFormedBrauerFold` — alphabet-restricted, per-atom in range).  Non-vacuous
(`wellFormedBrauerFold_capThenCup`).  `= true`. -/
def fxBrauer_hasBoundedBoundaryFoldLift : Bool := true

/-- **Honesty marker — the FULL T-DISJOINT flip does NOT close this round.**  `boundedBoundaryComponents_reachable`
establishes the invariant (`<= 2` boundary indices per component) at every reachable state, but the full
`fxBrauer_hasTagCorrDisjoint` flip additionally needs the EXTRACTION consequence — that `partnerIndexOf` reads
exactly the `d`-partner at every boundary index — whose `connected` input requires the two-source assembly
(T-CONNECT arc pairs + through-strand perm connectivity) over the 6-phase standard-form word.  That assembly is
strictly larger than the (already-shipped) uniqueness core `findPartnerScan_returnsUnique`, and is the r11 target.
So `fxBrauer_hasTagCorrDisjoint`, the roundtrip flags, and the masters stay `false`; #2013 does NOT close.
`= false`. -/
def fxBrauer_hasTagCorrExtraction : Bool := false

end FX1Poly.Polygraph
