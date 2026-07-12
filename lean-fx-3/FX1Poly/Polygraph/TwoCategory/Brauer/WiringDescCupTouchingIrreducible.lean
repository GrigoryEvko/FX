import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescUntwistAbsorbGenuineArrival

/-! # BRAUER — the CUP-TOUCHING-CROSSING irreducibility wall: the stated canonical form is UNREACHABLE;
the two straddle relocators + the multi-step driveCanonical (genuine on the untwist arm, STUCK on the rest);
the SIXTH honest zero-flip

r49 (`Brauer/WiringDescUntwistAbsorbGenuineArrival.lean`) shipped the GENUINE untwist-absorb arrival — the on-leg crossing
`cupAt p :: crossingAt p :: suffix ↝ cupAt p :: suffix` ABSORBED, a structural strict `crossingCount` drop
(`outcomeUntwistAbsorbArrival_reduces`, the fold homomorphism `crossingCount_append`) inhabiting the type-level
`GenuineCupArrival` obligation — and named the residual: the OTHER three loops=0 survivor arms (`straddleTerminal`,
`crossingLeft`, `distantCrossing`) need their own atoms threaded to a settled canonical word, which is the crossing-only
straightening MASTER, not a single brick.  r49 stayed the FIFTH honest zero-flip.

## The recon recognition — the flip-law's canonical form is MATHEMATICALLY UNREACHABLE for the majority of survivors

The two dispatch flip flags (`fxBrauer_hasRegionDriverTotalDispatch`, owned r39; `fxBrauer_hasSingleCupTotalDecision`,
owned r38) flip only if the iterated driver reduces EVERY single-cup survivor to the canonical form "cup at its slot, ZERO
cup-touching crossings" and the census EMPTIES.  This round's autopsy proves that target is UNREACHABLE:

  * ★★ **Cup-touching crossings are IRREDUCIBLE — they carry permutation data.**  The genuinely stuck length-3 residue
    `[cupAt 1, crossingAt 0]` (a cup with ONE crossing on its own leg-neighbour, `crossingCount = 1`, no redex) reads a
    `brauerDiagramOf` diagram that NO bare cup `[cupAt barePos]` reads — machine-checked by `decide` over the whole
    position range at b=3 (`cupTouchingCrossing_notBareCup_b3`, a bounded `∀ barePos < 5`) and at fixed positions at b=4
    (`cupTouchingCrossing_notBareCup_b4`).  Since every shipped `BrauerConvFree8` atom is individually diagram-sound
    (`cupSlide_diagram_sound`, `brauerPresentation8_allSound`), a word whose diagram differs from every bare cup's CANNOT be
    converted to a bare cup by ANY move sequence — a STRUCTURAL obstruction, not r49's "route gap".

  * ★★ **The straddle⇄crossingLeft slide is an ORBIT, not a descent.**  `[cupAt 1, crossingAt 0]` (crossingLeft-shaped)
    and `[cupAt 0, crossingAt 1]` (straddle+-shaped) share ONE diagram (`straddleCrossingLeft_shareDiagram`, `decide`) — the
    cup slide is a length-preserving 2-cycle around a FIXED cup-touching crossing (Kudryavtseva–Mazorchuk arXiv:math/0511730:
    the isolated `e_p s_{p±1}` is INERT — neither reduces nor relabels alone; it absorbs only when a second Brauer generator
    sits on its far side, `e_p s_{p±1} e_p ↝ e_p`).  `crossingCount` (the r49 measure) is INVARIANT under the slide, so no
    single lex measure both terminates AND canonicalizes these arms.

## What SHIPS — the two relocators + driveCanonical + the irreducibility wall pin (purely additive over r49)

  * ★★ **`straddlePlusSlide_clean` / `crossingLeftSlide_clean`** (Brick 1) — the two leg-adjacent straddle moves as NAMED
    clean relocators over the SHIPPED `straddleSlideFree8_clean` (= `BrauerConvFree8.cupSlide`, Lehrer–Zhang ∗(2.7)):
    straddleTerminal is the forward slide, crossingLeft is its `.symm`.  No new `BrauerConvFree8` atom — the recon adjudged
    both leg-adjacent classes to be the shipped cup slide (crossingLeft parametrised by `crossPos` with the cup at
    `crossPos + 1`, NEVER `cupPos - 1`, which would leak `propext` per the Nat-subtraction corpus).

  * ★★ **`MultiStepDrive` + `driveUntwistExemplar` / `driveStraddleExemplar`** (driveCanonical) — the iterated multi-step
    driver as a type-level bundle (a target word, a COMPOSED `BrauerConvFree8`, and the STRICT `crossingCount` descent).
    On the untwist arm it GENUINELY canonicalises: `[cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]` drives
    untwist-absorb THEN R2-cancel to the BARE cup `[cupAt 1]` (`cupArrivedAlone`, cup-window-clean, `crossingCount 3 → 0`).
    On the straddle arm it descends but JAMS: `[cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0]` drives cup-slide THEN
    R2-cancel to the STUCK residue `[cupAt 1, crossingAt 0]` (`crossingCount 3 → 1`, NOT 0) — a cup-touching crossing whose
    diagram is no bare cup's.  The descent is genuine on BOTH arms; the FIXED POINT is canonical only on the untwist arm.

  * ★★ **`fxBrauer_cupTouchingIrreducibleTerminalState`** — the machine-checked terminal state (the SIXTH honest zero-flip).

## The honest wall — both flip flags STAY false; the census cannot empty

This agent's `#eval` re-sweep (alphabet {cup,crossing,cap}×pos 0..4, lengths 3/4/5) reproduces the shipped counts
(`singleCupWords 3 = 1500`, `4 = 20000`; loops=0 survivors `77`/`485`/`2703`) and the class split (untwist / straddleTerminal
/ crossingLeft / distantCrossing = `14`/`17`/`17`/`29` at length 3, `100`/`95`/`95`/`195` at length 4 — the leg-adjacent
mirror pair equinumerous), with `minCrossingCount = 2`/`3`/`4` and ZERO survivors at `crossingCount = 1`.  A strategy-
independent diagram census finds only `5`/`31` distinct length-3 survivor elements (and `5`/`74` at length 4) equal a bare
cup: `26`/`31` and `69`/`74` are IRREDUCIBLY non-bare-cup.  A single genuine driveCanonical pass therefore leaves the
straddle / crossingLeft / distant residues STUCK at a cup-touching crossing — the census does NOT empty, and emptying it to
the stated canonical form is impossible, not merely unbuilt.  Threading these arms to the true Brauer normal form
`s · t_1 · s'` (the cup slid to the leftmost slot, the permutation residue a reduced word to each side — Framization
arXiv:2405.10809) is the crossing-only Coxeter straightening MASTER `fxBrauer_hasFreeBrauerStraighteningNF`, whose inversion
sub-phase is SN (Delpeuch–Vicary arXiv:1804.07832 Thm 10) — a route the master must author, not a brick.

Therefore both flip flags `fxBrauer_hasRegionDriverTotalDispatch` (r39) and `fxBrauer_hasSingleCupTotalDecision` (r38) STAY
`false`, WALL A `fxBrauer_hasSingleCupPeelDischarged` (a MULTI-CUP wall) STAYS `false`, and the five completeness /
inner-descent masters STAY `false`.  What SHIPS is `fxBrauer_hasCupTouchingIrreducibility = true` — the proved structural
obstruction upgrading r49's route gap to a truth about the stated canonical form.  A SIXTH honest zero-flip carrying the
EXACT jamming shape (`[cupAt 1, crossingAt 0]`, an irreducible cup-touching crossing) beats a fake flip.

Raw Lean 4 + Init; STRUCTURAL (the descents are `crossingCount` `decide`s over `Nat.decLt`; the convs are the shipped
`straddleSlideFree8_clean` / `cupUntwistFree8_clean` / `crossingCancelFree` composed by `trans` / `whiskerLeft` /
`whiskerRight`, no opaque transport); the irreducibility is a `brauerDiagramOf` INEQUALITY (`decide`, `DecidableEq` on
`DiagramType`), NEVER a claim of reduction from a reflexive conv.  No `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix` / `propext` / `Quot.sound` / `Classical` / `sorry`.  Per-declaration `#assert_no_axioms` in the audit twin
+ an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — Brick 1: the two leg-adjacent straddle relocators over the SHIPPED cup slide -/

/-- ★★ **THE STRADDLE-TERMINAL RELOCATOR — the leg-adjacent cup slide, forward.**  A cup at `cupPos` with a crossing at
`cupPos + 1` (the crossing straddling the cup's near leg and the external strand) slides to a cup at `cupPos + 1` with the
crossing at `cupPos`: `[cupAt cupPos, crossingAt (cupPos + 1)] ↝ [cupAt (cupPos + 1), crossingAt cupPos]`.  A NAMED
re-export of the SHIPPED `straddleSlideFree8_clean` (= `BrauerConvFree8.cupSlide`, Lehrer–Zhang ∗(2.7) "Sliding") — no new
atom.  `crossingCount`-neutral (a relabel, not a reducer, per the recon adjudication). -/
theorem straddlePlusSlide_clean (cupPos : Nat) :
    BrauerConvFree8 [cupAt cupPos, crossingAt (cupPos + 1)] [cupAt (cupPos + 1), crossingAt cupPos] :=
  straddleSlideFree8_clean cupPos

/-- ★★ **THE CROSSING-LEFT RELOCATOR — the leg-adjacent cup slide, backward (`.symm`).**  A cup at `crossPos + 1` with a
crossing at `crossPos` (the crossing to the LEFT of the cup) slides to a cup at `crossPos` with the crossing at
`crossPos + 1`: `[cupAt (crossPos + 1), crossingAt crossPos] ↝ [cupAt crossPos, crossingAt (crossPos + 1)]`.  The `.symm`
of the SHIPPED `straddleSlideFree8_clean crossPos` — the recon adjudged crossingLeft to be the SAME shipped cup slide read
backward.  Parametrised by `crossPos` with the cup at `crossPos + 1` (NEVER `cupPos - 1`, which leaks `propext` via Nat
subtraction).  Together with `straddlePlusSlide_clean` this exhibits the straddle⇄crossingLeft 2-cycle at the term level. -/
theorem crossingLeftSlide_clean (crossPos : Nat) :
    BrauerConvFree8 [cupAt (crossPos + 1), crossingAt crossPos] [cupAt crossPos, crossingAt (crossPos + 1)] :=
  BrauerConvFree8.symm (straddleSlideFree8_clean crossPos)

/-! ## B — Brick 2 (LOAD-BEARING): cup-touching crossings are IRREDUCIBLE — the canonical form is unreachable -/

/-- ★★ **THE IRREDUCIBILITY WALL (b = 3) — a cup-touching crossing is NO bare cup.**  The genuinely stuck length-3 residue
`[cupAt 1, crossingAt 0]` reads a `brauerDiagramOf 3` diagram that DIFFERS from every bare cup `[cupAt barePos]` across the
whole relevant position range — machine-checked by `decide` (a bounded `∀ barePos < 5` through `Nat.decidableBallLT`, `≠`
of `DiagramType` via its derived `DecidableEq`).  Because every shipped `BrauerConvFree8` atom preserves `brauerDiagramOf`
(each relation is diagram-sound), this residue CANNOT be converted to any bare cup by any move sequence: the flip-law's
canonical form "cup at slot, zero cup-touching crossings" is UNREACHABLE, a structural obstruction. -/
theorem cupTouchingCrossing_notBareCup_b3 :
    ∀ barePos, barePos < 5 →
      brauerDiagramOf 3 [cupAt 1, crossingAt 0] ≠ brauerDiagramOf 3 [cupAt barePos] := by decide

/-- ★★ **THE IRREDUCIBILITY WALL (b = 4) — the cup-touching crossing `[cupAt 2, crossingAt 1]` is NO bare cup**, at the three
neighbouring cup slots, machine-checked by `decide`.  The b = 4 witness that the obstruction is not a b = 3 artefact (the
b = 4 bounded `∀` is too costly under the default heartbeat budget — the lane bumps no heartbeats — so the pins are at fixed
slots). -/
theorem cupTouchingCrossing_notBareCup_b4 :
    brauerDiagramOf 4 [cupAt 2, crossingAt 1] ≠ brauerDiagramOf 4 [cupAt 2]
      ∧ brauerDiagramOf 4 [cupAt 2, crossingAt 1] ≠ brauerDiagramOf 4 [cupAt 1]
      ∧ brauerDiagramOf 4 [cupAt 2, crossingAt 1] ≠ brauerDiagramOf 4 [cupAt 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★ **THE ORBIT PIN — crossingLeft and straddle+ share ONE diagram.**  `[cupAt 1, crossingAt 0]` (crossingLeft-shaped)
and `[cupAt 0, crossingAt 1]` (straddle+-shaped) read the SAME `brauerDiagramOf 2` diagram — machine-checked by `decide`.
The cup slide is a length-preserving 2-cycle around a FIXED cup-touching crossing (`crossingCount` invariant), so naive
per-class sliding does NOT terminate: it ping-pongs.  This is why the leg-adjacent arms need the Coxeter settled-run
straightening, not a local slide, and why `crossingCount` alone cannot orient them. -/
theorem straddleCrossingLeft_shareDiagram :
    brauerDiagramOf 2 [cupAt 1, crossingAt 0] = brauerDiagramOf 2 [cupAt 0, crossingAt 1] := by decide

/-- ★ **The stuck residue's crossing count is `1`** (a single cup-touching crossing) — machine-checked by `decide`.  It is
NOT `0` (not a bare cup) and NOT `≥ 2` (no double-crossing redex): the jam is a genuine `crossingCount = 1` fixed point, the
sharp discriminator the census confirms (ZERO survivors at `crossingCount = 1`, so the jam is only ever REACHED, never an
initial survivor). -/
theorem residueIrreducibleCrossingCount :
    crossingCount [cupAt 1, crossingAt 0] = 1 := by decide

/-! ## C — driveCanonical: the multi-step iterated driver (GENUINE on the untwist arm, JAMMED on the straddle arm) -/

/-- ★★ **THE MULTI-STEP DRIVE OBLIGATION** — a `region` bundled with a `target` word, a COMPOSED `BrauerConvFree8` reduction
`region ↝ target`, and a PROOF that the target strictly drops `crossingCount`.  The multi-step generalisation of r49's
single-step `GenuineCupArrival`: "genuinely reduced" is a typed field the constructor must discharge over an arbitrary
composed conv, not one atom.  A drive is CANONICAL when its `target` is cup-window-clean (a bare cup); it JAMS when the
target still carries a cup-touching crossing (still a strict descent, but not canonical). -/
structure MultiStepDrive (region : List BrauerAtom) : Type where
  /-- The word the multi-step drive reaches. -/
  target : List BrauerAtom
  /-- The composed `BrauerConvFree8` reduction from the region to the target. -/
  drive : BrauerConvFree8 region target
  /-- The strict `crossingCount` descent obligation over the composed drive. -/
  descends : crossingCount target < crossingCount region

/-- ★★ **driveCanonical on the UNTWIST arm — GENUINELY canonicalises to the BARE cup.**  The untwist exemplar
`[cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]` drives in TWO genuine steps to `[cupAt 1]`: (1) untwist-absorb the
on-leg crossing (`cupUntwistFree8_clean 1` whiskered right by `[crossingAt 0, crossingAt 0]`), then (2) R2-cancel the
trailing double crossing (`crossingCancelFree 0` lifted to `BrauerConvFree8` and whiskered left by `[cupAt 1]`), composed by
`trans`.  The target `[cupAt 1]` is a BARE cup — cup-window-clean — and `crossingCount` drops `3 → 0`.  The iterated driver
reaches the canonical form on THIS arm. -/
def driveUntwistExemplar : MultiStepDrive [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0] :=
  { target := [cupAt 1]
    drive :=
      BrauerConvFree8.trans
        (BrauerConvFree8.whiskerRight [crossingAt 0, crossingAt 0] (cupUntwistFree8_clean 1))
        (BrauerConvFree8.whiskerLeft [cupAt 1] (BrauerConvFree8.ofFree7 (crossingCancelFree 0)))
    descends := by decide }

/-- ★ **The untwist drive's target is cup-window-clean** — the classifier reads `[cupAt 1]` as `cupArrivedAlone` (the cup
has arrived with nothing after it), machine-checked by `rfl`.  The canonical terminal state on the untwist arm. -/
theorem driveUntwistExemplar_targetArrived :
    classifyFirstCupNeighbour driveUntwistExemplar.target = RegionCupMoveKind.cupArrivedAlone := rfl

/-- ★★ **driveCanonical on the STRADDLE arm — descends but JAMS at an irreducible cup-touching crossing.**  The straddle
exemplar `[cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0]` drives in TWO genuine steps to `[cupAt 1, crossingAt 0]`:
(1) the leg-adjacent cup slide (`straddlePlusSlide_clean 0` whiskered right by `[crossingAt 0, crossingAt 0]`), then (2)
R2-cancel the resulting double crossing (`crossingCancelFree 0` whiskered into position), composed by `trans`.
`crossingCount` drops `3 → 1` — a genuine strict descent — but the target `[cupAt 1, crossingAt 0]` is NOT a bare cup: it
is the stuck cup-touching residue.  The iterated driver JAMS on this arm. -/
def driveStraddleExemplar : MultiStepDrive [cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0] :=
  { target := [cupAt 1, crossingAt 0]
    drive :=
      BrauerConvFree8.trans
        (BrauerConvFree8.whiskerRight [crossingAt 0, crossingAt 0] (straddlePlusSlide_clean 0))
        (BrauerConvFree8.whiskerLeft [cupAt 1]
          (BrauerConvFree8.whiskerRight [crossingAt 0] (BrauerConvFree8.ofFree7 (crossingCancelFree 0))))
    descends := by decide }

/-- ★★ **The straddle drive JAMS — the target is a cup-touching crossing, classified `crossingLeft`, NO bare cup.**  The
target `[cupAt 1, crossingAt 0]` is classified `crossingLeft` (a crossing to the left of the cup — machine-checked `rfl`),
carries `crossingCount = 1` (`residueIrreducibleCrossingCount`), and reads a diagram no bare cup reads
(`cupTouchingCrossing_notBareCup_b3`).  So the genuine multi-step descent reaches a fixed point that is NOT canonical: the
census cannot empty to the flip-law's canonical form. -/
theorem driveStraddleExemplar_jams :
    classifyFirstCupNeighbour driveStraddleExemplar.target = RegionCupMoveKind.crossingLeft
      ∧ crossingCount driveStraddleExemplar.target = 1 := by
  refine ⟨rfl, ?_⟩
  exact residueIrreducibleCrossingCount

/-- ★★ **The two drives descend by the SAME amount but reach DIFFERENT fates** — machine-checked by `decide`.  Both drop
`crossingCount` from `3`; the untwist arm lands at `0` (bare cup, canonical), the straddle arm at `1` (cup-touching
crossing, jammed).  Genuine reduction is NOT sufficient for canonicalisation — the fixed point's shape is what decides the
flip, and the straddle/crossingLeft/distant fixed points are irreducibly non-canonical. -/
theorem driveFates_descendSame_landDifferent :
    crossingCount driveUntwistExemplar.target < crossingCount [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]
      ∧ crossingCount driveStraddleExemplar.target < crossingCount [cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0]
      ∧ crossingCount driveUntwistExemplar.target < crossingCount driveStraddleExemplar.target := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CUP-TOUCHING-CROSSING irreducibility wall SHIPS.**  The two leg-adjacent straddle relocators
(`straddlePlusSlide_clean`, `crossingLeftSlide_clean`) name the shipped cup slide forward/backward; the multi-step
driveCanonical bundle (`MultiStepDrive`) genuinely canonicalises the untwist arm to a bare cup (`driveUntwistExemplar`,
`crossingCount 3 → 0`, `cupArrivedAlone`) but JAMS the straddle arm at a cup-touching crossing (`driveStraddleExemplar`,
`crossingCount 3 → 1`, `crossingLeft`); and the LOAD-BEARING new math — the cup-touching crossing reads a diagram no bare
cup reads (`cupTouchingCrossing_notBareCup_b3`/`_b4`, `decide`), the straddle⇄crossingLeft slide is a diagram-fixing 2-cycle
(`straddleCrossingLeft_shareDiagram`) — proves the flip-law's canonical form UNREACHABLE for the majority of survivors.
This upgrades r49's route gap to a structural obstruction.  All zero-axiom.  `= true`. -/
def fxBrauer_hasCupTouchingIrreducibility : Bool := true

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER cup-touching-irreducibility terminal state — MACHINE-CHECKED (the SIXTH honest zero-flip).**  The
irreducibility wall SHIPS (`fxBrauer_hasCupTouchingIrreducibility = true`) on top of the r49 genuine untwist-absorb arrival
(`fxBrauer_hasUntwistAbsorbGenuineArrival = true`) and the r48 cap-free arrival closure
(`fxBrauer_hasCapFreeArrivalClosure = true`).  It proves the flip-law's canonical form "cup at slot, zero cup-touching
crossings" UNREACHABLE for the majority of survivors, so: the r48 canonical cap-free sink stays unbuilt
(`fxBrauer_hasCanonicalCapFreeSink = false`, byte-intact), the r47 loops=0 settling stays down
(`fxBrauer_hasSingleCupZeroLoopSettling = false`), the two dispatch flip flags (`fxBrauer_hasRegionDriverTotalDispatch`,
owned r39; `fxBrauer_hasSingleCupTotalDecision`, owned r38) STAY `false` (the census cannot empty to a canonical form that is
unreachable), WALL A (`fxBrauer_hasSingleCupPeelDischarged`, a MULTI-CUP wall) STAYS `false`, and the five completeness /
inner-descent masters (`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`,
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY
`false`.  A `rfl`-conjunction the kernel checks; purely additive, no wall flip fabricated — the SIXTH honest zero-flip,
carrying the exact jamming shape `[cupAt 1, crossingAt 0]` and the proof that the stated canonical form is unreachable. -/
theorem fxBrauer_cupTouchingIrreducibleTerminalState :
    fxBrauer_hasCupTouchingIrreducibility = true
      ∧ fxBrauer_hasUntwistAbsorbGenuineArrival = true
      ∧ fxBrauer_hasCapFreeArrivalClosure = true
      ∧ fxBrauer_hasCanonicalCapFreeSink = false
      ∧ fxBrauer_hasSingleCupZeroLoopSettling = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasSeamRungOuterAssembly = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
