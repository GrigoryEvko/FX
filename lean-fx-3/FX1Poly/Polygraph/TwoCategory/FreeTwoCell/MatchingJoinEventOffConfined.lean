import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # KEYSTONE9 ingredient — the CONVERSE (support-confinement) half of the same-component window-locality

The shipped connectivity-MONOTONE half (`Brauer/WiringDescConnectivityMono.lean`,
`processBrauer_isSameComponent_ofBase`) says a Brauer word never DISCONNECTS: every base same-component pair
survives the collapse word.  This file ships the honest CONVERSE, at the event-fold granularity: a word that
JOINS only within a support region introduces NO SPURIOUS connection between two probes that both sit OUTSIDE
that region.

The naive dual — "`isSameComponent (afterWord) p q = true → isSameComponent base p q = true`" — is FALSE (a join
genuinely connects previously-disconnected nodes).  The correct converse is a SUPPORT-CONFINEMENT statement: if
every join endpoint of the trace is base-DISCONNECTED from both probes, the whole fold leaves the two probes'
relative connectivity UNTOUCHED.  This is exactly the graph-connectivity fact that "adding an edge merges only
the two incident components, leaving all others unchanged" (Lehman–Leighton–Meyer §11.9), read through the
union-find `unionFindJoin`: it is the DPO-locality / interface-preservation content — the region interacts with
the rest only through its declared boundary ports, and a probe disconnected from the whole region stays put.

## What is proved (all from the flat-disjunction characterization `isSameComponent_unionFindJoin`, forest-conditioned)

  * ★ `isSameComponent_unionFindJoin_eq_ofFirstDisconnected` — one join at a pair whose FIRST endpoint is
    disconnected from BOTH probes leaves the two probes' same-component view EQUAL to the base view (the two
    off-window disjuncts vanish).
  * ★ `isSameComponent_unionFindJoin_disconnected_preserved` — one join at a pair both of whose endpoints are
    disconnected from a probe keeps that probe disconnected from any node it was already disconnected from (the
    detachment invariant survives one join).
  * ★ `isSameComponent_applyJoinEvents_offConfined` — the FOLD converse: if every event endpoint is base-
    disconnected from both probes, the whole event fold's same-component view of the two probes equals the base
    view.  Structural on the trace; the detachment of the two probes from every remaining endpoint is the
    maintained invariant (window-attachment is monotone, so the tail's confinement survives each head join).

This is the second of the two halves of the standing same-component window-locality subsystem; the MONOTONE half
survives base connections, this CONVERSE half forbids spurious off-support ones.  Combining them across a
boundary-preserving word is the word-level `relationAgrees` route.  It is the fold-level dual of
`isSameComponent_applyJoinEvents_ofBase` (which lifts base connections through the fold).

## Honest scope — this does NOT flip `fxBrauer_hasBrauerSoundness`

This closes the CONVERSE at the EVENT-FOLD level (over `applyJoinEvents`, arbitrary confined traces).  The word-
level `relationAgrees` for the five Brauer relations additionally needs PORT-RECONNECTION (the fresh in-window
top ports of a collapse word must read back into the same off-window components positionally) and, for the
overlapping-window relations (R1 capSlide, R3 Yang–Baxter), a direct cross-order partition argument whose only
known renaming route is REFUTED (`not_arcRenameRel_capCapOverlap`).  So `fxBrauer_hasBrauerSoundness` STAYS
`false`; this ships the converse building block, not the flip.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## One join: the off-support equality and the detachment-preservation steps -/

/-- ★ **One join is invisible to two off-support probes.**  If the join pair's FIRST endpoint `joinLeft` is
disconnected from both probes in the base, then joining `joinLeft`/`joinRight` leaves the two probes'
same-component view equal to the base view: in the flat-disjunction characterization the two off-support
disjuncts `(joinLeft~probeOne && …)` and `(joinLeft~probeTwo && …)` both carry the false factor.  Forest-
conditioned on the base only. -/
theorem isSameComponent_unionFindJoin_eq_ofFirstDisconnected (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probeOne probeTwo : Nat)
    (leftProbeOne : isSameComponent links joinLeft probeOne = false)
    (leftProbeTwo : isSameComponent links joinLeft probeTwo = false) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo
      = isSameComponent links probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo,
    leftProbeOne, leftProbeTwo]
  cases hbase : isSameComponent links probeOne probeTwo <;> rfl

/-- ★ **One join preserves a probe's detachment.**  If both endpoints of the join are disconnected from
`probe` in the base and `probe` is disconnected from `other` in the base, then `probe` is still disconnected
from `other` after joining `joinLeft`/`joinRight`: every disjunct of the characterization carries a false
factor.  This is the invariant that keeps a probe outside the growing support component across the fold. -/
theorem isSameComponent_unionFindJoin_disconnected_preserved (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probe other : Nat)
    (probeOther : isSameComponent links probe other = false)
    (leftProbe : isSameComponent links joinLeft probe = false)
    (probeRight : isSameComponent links probe joinRight = false) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probe other = false := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probe other,
    probeOther, leftProbe, probeRight]
  cases hleftOther : isSameComponent links joinLeft other <;> rfl

/-! ## The fold converse -/

/-- ★ **The event fold introduces no spurious off-support connection.**  If every event endpoint of the trace
is base-disconnected from BOTH probes, then the whole `applyJoinEvents` fold leaves the two probes'
same-component view EQUAL to the base view.  Structural on the trace: at the head join the two probes stay
detached from every remaining endpoint (`isSameComponent_unionFindJoin_disconnected_preserved`), so the
confinement hypothesis is re-established over the joined links for the recursive call; the head equality is the
single-join off-support equality (`isSameComponent_unionFindJoin_eq_ofFirstDisconnected`).  This is the honest
converse of `isSameComponent_applyJoinEvents_ofBase`. -/
theorem isSameComponent_applyJoinEvents_offConfined :
    (events : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    (probeOne probeTwo : Nat) →
    (∀ pair, pair ∈ events →
        isSameComponent links probeOne pair.1 = false
      ∧ isSameComponent links probeOne pair.2 = false
      ∧ isSameComponent links probeTwo pair.1 = false
      ∧ isSameComponent links probeTwo pair.2 = false) →
    isSameComponent (applyJoinEvents events links) probeOne probeTwo
      = isSameComponent links probeOne probeTwo
  | [], _, _, _, _, _ => rfl
  | (joinLeft, joinRight) :: restEvents, links, forest, probeOne, probeTwo, confined => by
      have headFacts := confined (joinLeft, joinRight) (List.Mem.head restEvents)
      have oneLeft : isSameComponent links probeOne joinLeft = false := headFacts.1
      have oneRight : isSameComponent links probeOne joinRight = false := headFacts.2.1
      have twoLeft : isSameComponent links probeTwo joinLeft = false := headFacts.2.2.1
      have twoRight : isSameComponent links probeTwo joinRight = false := headFacts.2.2.2
      have leftOne : isSameComponent links joinLeft probeOne = false :=
        (isSameComponent_symm links joinLeft probeOne).trans oneLeft
      have leftTwo : isSameComponent links joinLeft probeTwo = false :=
        (isSameComponent_symm links joinLeft probeTwo).trans twoLeft
      have forest' : isUnionFindForest (unionFindJoin links joinLeft joinRight) :=
        isUnionFindForest_unionFindJoin links joinLeft joinRight forest
      have confined' : ∀ pair, pair ∈ restEvents →
          isSameComponent (unionFindJoin links joinLeft joinRight) probeOne pair.1 = false
        ∧ isSameComponent (unionFindJoin links joinLeft joinRight) probeOne pair.2 = false
        ∧ isSameComponent (unionFindJoin links joinLeft joinRight) probeTwo pair.1 = false
        ∧ isSameComponent (unionFindJoin links joinLeft joinRight) probeTwo pair.2 = false :=
        fun pair memRest => by
          have tailFacts := confined pair (List.Mem.tail (joinLeft, joinRight) memRest)
          exact ⟨isSameComponent_unionFindJoin_disconnected_preserved links forest
                joinLeft joinRight probeOne pair.1 tailFacts.1 leftOne oneRight,
              isSameComponent_unionFindJoin_disconnected_preserved links forest
                joinLeft joinRight probeOne pair.2 tailFacts.2.1 leftOne oneRight,
              isSameComponent_unionFindJoin_disconnected_preserved links forest
                joinLeft joinRight probeTwo pair.1 tailFacts.2.2.1 leftTwo twoRight,
              isSameComponent_unionFindJoin_disconnected_preserved links forest
                joinLeft joinRight probeTwo pair.2 tailFacts.2.2.2 leftTwo twoRight⟩
      show isSameComponent (applyJoinEvents restEvents (unionFindJoin links joinLeft joinRight))
          probeOne probeTwo = isSameComponent links probeOne probeTwo
      rw [isSameComponent_applyJoinEvents_offConfined restEvents
          (unionFindJoin links joinLeft joinRight) forest' probeOne probeTwo confined']
      exact isSameComponent_unionFindJoin_eq_ofFirstDisconnected links forest
        joinLeft joinRight probeOne probeTwo leftOne leftTwo

/-! ## Honesty marker -/

/-- **Honesty marker — the CONVERSE (support-confinement) half of the same-component window-locality is
SHIPPED at event-fold granularity.**  `isSameComponent_applyJoinEvents_offConfined` proves a join-event trace
whose every endpoint is base-disconnected from both probes introduces NO spurious connection: the fold's
same-component view of the two probes equals the base view.  Together with the shipped monotone half
(`processBrauer_isSameComponent_ofBase` / `isSameComponent_applyJoinEvents_ofBase`, which survives base
connections), this is the two-sided window-locality kernel: base connections survive, off-support connections
are forbidden.  The word-level `relationAgrees` for the five Brauer relations additionally needs PORT-
RECONNECTION and — for the overlapping-window R1/R3 — a direct cross-order partition argument whose renaming
route is REFUTED (`not_arcRenameRel_capCapOverlap`); so this does NOT flip `fxBrauer_hasBrauerSoundness`.
`= true`. -/
def fxMode_hasOffConfinedConverse : Bool := true

end FX1Poly.Polygraph
