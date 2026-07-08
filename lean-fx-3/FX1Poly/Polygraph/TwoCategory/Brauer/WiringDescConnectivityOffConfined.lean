import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescJoinEvents
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventOffConfined

/-! # KEYSTONE10 ingredient — the CONVERSE (off-support) half of the same-component locality, at the WORD level

The connectivity-MONOTONE half is shipped at the whole-word (`processBrauer`) level
(`Brauer/WiringDescConnectivityMono.lean`, `processBrauer_isSameComponent_ofBase`): a Brauer word never
DISCONNECTS.  The CONVERSE half — a word whose join events are confined off two probes introduces NO SPURIOUS
connection between them — was shipped only at the raw event-fold granularity (`FreeTwoCell/…OffConfined.lean`,
`isSameComponent_applyJoinEvents_offConfined`, over an abstract `applyJoinEvents` trace).  This file LIFTS that
converse onto the generic `stepWiring` engine and onto the whole `processBrauer` fold, so both halves of the
same-component window-locality subsystem now live at the SAME (word) granularity.

The bridge is the join-event reification `stepWiring_links_eq_applyJoinEvents` (`Brauer/WiringDescJoinEvents.lean`):
one `stepWiring` step's links ARE the unconditional event fold of its decoded arc trace `wiringArcEvents`.  Chaining
that per atom (threaded through the evolving state, `applyJoinEvents_append`) reifies the WHOLE word's links as one
flat event fold `brauerWordJoinEvents`, over which the shipped event-fold converse applies verbatim.

## What is proved

  * ★ `stepWiring_isSameComponent_offConfined` — one generator step whose every decoded arc endpoint is base-
    disconnected from both probes leaves the two probes' same-component view EQUAL to the incoming view.  The
    single-step lift of `isSameComponent_applyJoinEvents_offConfined` through the reification.
  * ★ `brauerWordJoinEvents` / `processBrauer_links_eq_applyJoinEvents` — the WHOLE word's links reified as one
    flat `applyJoinEvents` fold of the state-threaded decoded arc traces (the Brauer-word analog of the spine's
    `spineJoinEvents` / `runMatchingCell_links_eq_applyJoinEvents`).
  * ★ `processBrauer_isSameComponent_offConfined` — the whole-word converse: a Brauer word whose every decoded arc
    endpoint (across the threaded fold) is base-disconnected from both probes preserves those probes' same-component
    view.  This is the CONVERSE companion to `processBrauer_isSameComponent_ofBase`, now at matching granularity.

## Honest scope — this does NOT flip `fxBrauer_hasBrauerSoundness`

This ships the two-sided same-component word-locality at word granularity (monotone survives base connections; this
converse forbids spurious off-support ones).  The word-level `relationAgrees` the shipped `whisker` move consumes
(`Brauer/WiringDescConv.lean`) additionally needs PORT-RECONNECTION for the IN-window boundary indices: a collapse
word's fresh top ports must read back positionally into the SAME off-window component as the base port they replace.
That conjunct is relation-specific (it is FALSE as a generic-`WiringDesc` statement — a crossing PERMUTES its window
ports), not supplied by either locality half, and remains the standing residual.  So `fxBrauer_hasBrauerSoundness`
STAYS `false`; this ships the converse building block at word granularity, not the flip.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## One `stepWiring` step: the off-support converse on the engine -/

/-- ★ **One `stepWiring` step is invisible to two off-support probes.**  If every decoded arc endpoint of the
generator (its `wiringArcEvents` trace over the fixed input / output node lists) is base-disconnected from both
`probeOne` and `probeTwo`, then firing the generator leaves the two probes' same-component view EQUAL to the
incoming view.  The single-step lift of the event-fold converse through the reification
`stepWiring_links_eq_applyJoinEvents`: `stepWiring`'s links ARE `applyJoinEvents (wiringArcEvents …) state.links`,
so `isSameComponent_applyJoinEvents_offConfined` applies verbatim. -/
theorem stepWiring_isSameComponent_offConfined (state : WireState) (position : Nat) (desc : WiringDesc)
    (forest : isUnionFindForest state.links) (probeOne probeTwo : Nat)
    (confined : ∀ pair ∈ wiringArcEvents (stepWiringInputNodes state position desc)
        (stepWiringOutputNodes state desc) desc.inputCount desc.arcs,
        isSameComponent state.links probeOne pair.1 = false
      ∧ isSameComponent state.links probeOne pair.2 = false
      ∧ isSameComponent state.links probeTwo pair.1 = false
      ∧ isSameComponent state.links probeTwo pair.2 = false) :
    isSameComponent (stepWiring state position desc).links probeOne probeTwo
      = isSameComponent state.links probeOne probeTwo := by
  rw [stepWiring_links_eq_applyJoinEvents state position desc]
  exact isSameComponent_applyJoinEvents_offConfined
    (wiringArcEvents (stepWiringInputNodes state position desc)
      (stepWiringOutputNodes state desc) desc.inputCount desc.arcs)
    state.links forest probeOne probeTwo confined

/-! ## The whole word's links as one flat event fold -/

/-- ★ **The state-threaded decoded join-event trace of a whole Brauer word.**  Each atom's decoded arc trace
(`wiringArcEvents` over the FIXED input / output node lists it reads at its incoming state) concatenated with the
tail's trace threaded through the stepped state — the Brauer-word analog of the spine's `spineJoinEvents`. -/
def brauerWordJoinEvents : WireState → List BrauerAtom → List (Nat × Nat)
  | _, [] => []
  | state, atom :: rest =>
      wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
          (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs
        ++ brauerWordJoinEvents (stepBrauerAtom state atom) rest

/-- ★ **The whole `processBrauer` fold's LINKS are one flat event fold of the state-threaded arc traces.**  The
Brauer-word analog of `runMatchingCell_links_eq_applyJoinEvents`: structural on the atom list, the head atom's
links reify by `stepWiring_links_eq_applyJoinEvents` and the tail composes by `applyJoinEvents_append`. -/
theorem processBrauer_links_eq_applyJoinEvents :
    (atoms : List BrauerAtom) → (state : WireState) →
    (processBrauer state atoms).links = applyJoinEvents (brauerWordJoinEvents state atoms) state.links
  | [], _ => rfl
  | atom :: rest, state => by
      show (processBrauer (stepBrauerAtom state atom) rest).links
        = applyJoinEvents
            (wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
                (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs
              ++ brauerWordJoinEvents (stepBrauerAtom state atom) rest)
            state.links
      rw [processBrauer_links_eq_applyJoinEvents rest (stepBrauerAtom state atom),
        applyJoinEvents_append,
        show (stepBrauerAtom state atom).links
            = applyJoinEvents
                (wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
                  (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs)
                state.links
          from stepWiring_links_eq_applyJoinEvents state atom.position atom.wiring]

/-! ## The whole-word off-support converse -/

/-- ★ **The whole Brauer word introduces no spurious off-support connection.**  If every event of the state-
threaded decoded arc trace `brauerWordJoinEvents` is base-disconnected from both probes, then firing the whole word
leaves the two probes' same-component view EQUAL to the incoming (forest) view.  Reifies the word's links as one
flat event fold (`processBrauer_links_eq_applyJoinEvents`) and applies the shipped event-fold converse
(`isSameComponent_applyJoinEvents_offConfined`) verbatim.  This is the CONVERSE companion of
`processBrauer_isSameComponent_ofBase`, now at matching (word) granularity: the monotone half survives base
connections, this half forbids spurious off-support ones. -/
theorem processBrauer_isSameComponent_offConfined (atoms : List BrauerAtom) (state : WireState)
    (forest : isUnionFindForest state.links) (probeOne probeTwo : Nat)
    (confined : ∀ pair ∈ brauerWordJoinEvents state atoms,
        isSameComponent state.links probeOne pair.1 = false
      ∧ isSameComponent state.links probeOne pair.2 = false
      ∧ isSameComponent state.links probeTwo pair.1 = false
      ∧ isSameComponent state.links probeTwo pair.2 = false) :
    isSameComponent (processBrauer state atoms).links probeOne probeTwo
      = isSameComponent state.links probeOne probeTwo := by
  rw [processBrauer_links_eq_applyJoinEvents atoms state]
  exact isSameComponent_applyJoinEvents_offConfined (brauerWordJoinEvents state atoms)
    state.links forest probeOne probeTwo confined

/-! ## Honesty marker -/

/-- **Honesty marker — the off-support (CONVERSE) half of the same-component locality is SHIPPED at WORD
granularity.**  `stepWiring_isSameComponent_offConfined` (single step) and
`processBrauer_isSameComponent_offConfined` (whole word) lift the raw event-fold converse
(`isSameComponent_applyJoinEvents_offConfined`) onto the generic wiring engine, via the whole-word link reification
`processBrauer_links_eq_applyJoinEvents` (the Brauer-word analog of `runMatchingCell_links_eq_applyJoinEvents`).
Together with the shipped monotone half (`processBrauer_isSameComponent_ofBase`), the same-component word-locality
subsystem is now two-sided at word granularity: base connections survive, off-support connections are forbidden.
The word-level `relationAgrees` the `whisker` move consumes additionally needs PORT-RECONNECTION for the IN-window
boundary indices (relation-specific, FALSE as a generic-`WiringDesc` statement — a crossing permutes its window
ports), which neither locality half supplies; so this does NOT flip `fxBrauer_hasBrauerSoundness`.  `= true`. -/
def fxBrauer_hasOffConfinedConverseAtWord : Bool := true

end FX1Poly.Polygraph
