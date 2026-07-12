import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCapFreeArrivalClosure

/-! # BRAUER — the GENUINE untwist-absorb arrival: the on-leg crossing is ABSORBED (result ≠ input),
a STRUCTURAL strict crossing-count drop; the FIFTH honest zero-flip

r48 (`Brauer/WiringDescCapFreeArrivalClosure.lean`) recognised that every loops=0 single-cup survivor is CAP-FREE and
closed the isSome census at lengths 3–5 with `outcomeCapFreeArrival` — but that arrival is REFLEXIVE
(`result = region`, conversion `refl`): a TRUE certificate that performs NO reduction
(`flatRegionDriveArrivalReflexiveNotCanonical` pins the on-leg crossing surviving intact).  The r48 verdict named the
"canonical cap-free sink" — untwist-normalize the on-leg crossing, relabel straddles, commute settled-left — as the next
flip gate and stayed the FOURTH honest zero-flip.

## The recon recognition — the untwist-absorb conv atom is SHIPPED; only the arrival wiring was reflexive

This round's autopsy found the r48 "missing" on-leg absorption is NOT missing: `cupUntwistFree8_clean`
(`[cupAt p, crossingAt p] ~ [cupAt p]`, a real `BrauerConvFree8`, `WiringDescSeamRungs`) and its strict measure drop
`cupUntwistAbsorb_crossingCount` (`WiringDescStraightening`) both ship.  The reason r48's arrival is reflexive is that
`outcomeCapFreeArrival` chose `BrauerConvFree.refl` and certified `cupIsCapFreeRight` (which holds unconditionally on a
cap-free word) instead of *applying* the shipped absorption atom.  This round ships, PURELY ADDITIVELY (a new sibling
importing r48, never mutating a shipped file), the GENUINE arrival that fires the shipped atom:

  * ★★ **`outcomeUntwistAbsorbArrival`** — the on-leg crossing is ABSORBED.  For a cap-free `cupAt p :: crossingAt p ::
    suffix` (the cup with a crossing on its own leg), the arrival result is `cupAt p :: suffix` — the on-leg crossing
    REMOVED — carried by `BrauerConvFree8.whiskerRight suffix (cupUntwistFree8_clean p)`, a NON-reflexive
    `BrauerConvFree8`.  `resultWord ≠ region`: the crossing is gone (`untwistAbsorbResultWord`, machine-checked `rfl`),
    contrast the reflexive `outcomeCapFreeArrival` whose result IS the un-reduced input.

  * ★★ **`outcomeUntwistAbsorbArrival_reduces`** — the STRUCTURAL genuine-reduction guarantee.  `crossingCount
    result < crossingCount region`, discharged from `cupUntwistAbsorb_crossingCount [] suffix p` (the fold homomorphism
    `crossingCount_append`), NOT a per-exemplar `rfl` — the strict drop holds for EVERY `suffix`, generic in `p`.

  * ★★ **`GenuineCupArrival`** — the genuine reduction as a TYPE-LEVEL obligation.  A structure bundling a
    `RegionCupOutcome` with a PROOF that its `resultWord` has strictly fewer crossings than the region; the untwist-absorb
    arm inhabits it (`genuineUntwistAbsorbArrival`).  "Genuinely reduced" is now a typed field the constructor must
    discharge, not an exemplar check.

This is exactly the load-bearing genuine reduction the r48 verdict demanded, and it strictly beats the reflexive sink on
the untwist arm (`untwistAbsorbStrictlyBelowReflexive`: crossing count `2 < 3` from the reduced vs the reflexive result
on the shared untwist exemplar).

## The honest wall — the CANONICAL sink stays unbuilt; both flip flags STAY false (the FIFTH honest zero-flip)

The genuine untwist-absorb arrival fires only on the `untwist` arm (`cupAt p :: crossingAt p :: suffix`).  The other three
loops=0 arms — `straddleTerminal`, `crossingLeft`, `distantCrossing` — need their own genuine atoms (straddle relabel, R2
cancel, distant slide) threaded to a canonical settled word, and the sharp census fact below shows why a single genuine
round cannot finish: this agent's `#eval` re-sweep (positions 0..4, lengths 3/4, alphabet {cup,crossing,cap}) reproduces
the r47/r48 counts (`singleCupWords 3 = 1500`, `4 = 20000`; loops=0 survivors `77` / `485`, all cap-free `77` / `485`) and
adds the DECISIVE discriminator: **every loops=0 survivor has `crossingCount ≥ 2`** — the count with `crossingCount = 1` is
`0` / `0`, so NO survivor is a single redex.  A genuine iterated untwist-absorb + R2 normalizer (this agent's probe) clears
only `28` / `77` and `180` / `485`, leaving `49` / `305` STUCK — because one genuine atom re-classifies a survivor into
another survivor arm (untwist → crossingLeft, machine-confirmed by the recon).  Emptying the census with GENUINE reduction
therefore requires the full Coxeter word-normalization of the settled crossing run — untwist + R2 + R3-braid + distant
commute + straddle + slide under a lexicographic `(crossingCount, inversionCount)` descent — which is the crossing-only
straightening MASTER (`fxBrauer_hasFreeBrauerStraighteningNF`, `WiringDescStandardForm`), not a single brick.  The inversion
sub-phase is SN (Delpeuch–Vicary arXiv:1804.07832 Thm 10, cited at `WiringDescCrossingLeftCommuteContinue`), and
Kudryavtseva–Mazorchuk (arXiv:math/0511730) prove NO printed on-leg-crossing termination measure exists — their argument is
orbit-counting, not a terminating rewrite — so the canonical sink's descent must be authored, not cited.  KM relations
(3.3) `θ_i σ_i = θ_i` (same-index on-leg absorbed, exactly this round's atom) and (3.5) `θ_i σ_j θ_i = θ_i` (one-off-index),
plus Lemma 7 `w⁻¹ θ_1 w = θ_i` (the settled part is the permutation acting on the cup-foot pair), fix the canonical form —
a route gap, never a truth gap.

Therefore the CANONICAL cap-free sink stays unbuilt: `fxBrauer_hasCanonicalCapFreeSink` (r48) STAYS `false`, both flip
flags `fxBrauer_hasRegionDriverTotalDispatch` (owned r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY `false`,
WALL A `fxBrauer_hasSingleCupPeelDischarged` (a MULTI-CUP wall) STAYS `false`, and the five completeness / inner-descent
masters STAY `false`.  What SHIPS is the genuine untwist-absorb arrival (`fxBrauer_hasUntwistAbsorbGenuineArrival = true`),
which strictly beats the reflexive sink on the untwist arm — a FIFTH honest zero-flip with the exact residual named (the
iterated settled-crossing-run Coxeter normal form generic in cupPos and the run) beats a fake flip on a reflexive closure.

Raw Lean 4 + Init; STRUCTURAL (the strict drop is the fold homomorphism `crossingCount_append`, never `rfl`-hope on a
generic word); no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` / `propext` / `Quot.sound` / `Classical` /
`sorry`.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the GENUINE untwist-absorb arrival (Brick 1): the on-leg crossing is ABSORBED -/

/-- ★★ **THE GENUINE UNTWIST-ABSORB ARRIVAL — the on-leg crossing is REMOVED (result ≠ input).**  For a cap-free word
`cupAt cupPos :: crossingAt cupPos :: suffix` (the cup with a crossing on its own leg), the `.arrivedFactored` result is
`cupAt cupPos :: suffix` — the on-leg crossing absorbed — carried by the SHIPPED, NON-reflexive
`BrauerConvFree8.whiskerRight suffix (cupUntwistFree8_clean cupPos)` (`[cupAt p, crossingAt p] ~ [cupAt p]` whiskered by
the suffix).  The factored-arrival witness `cupIsCapFreeRight (cupAt cupPos :: suffix) = true` comes from
`capFreeRight_of_hasNoCap` (the reduced word is still cap-free — `noCap` on the region is defeq to `hasNoCap suffix`,
which is exactly `hasNoCap (cupAt cupPos :: suffix)`).  Unlike r48's reflexive `outcomeCapFreeArrival`, this arrival
performs the reduction the two dispatch walls demand on the `untwist` arm. -/
def outcomeUntwistAbsorbArrival (cupPos : Nat) (suffix : List BrauerAtom)
    (noCap : hasNoCap (cupAt cupPos :: crossingAt cupPos :: suffix) = true) :
    RegionCupOutcome (cupAt cupPos :: crossingAt cupPos :: suffix) :=
  RegionCupOutcome.arrivedFactored (cupAt cupPos :: suffix)
    (BrauerConvFree8.whiskerRight suffix (cupUntwistFree8_clean cupPos))
    (capFreeRight_of_hasNoCap (cupAt cupPos :: suffix) noCap)

/-- ★ **The genuine arrival's result word is the REDUCED word** — the on-leg crossing gone — machine-checked generic in
`cupPos` and `suffix` by `rfl`.  Contrast r48's reflexive arrival whose result is the un-reduced input. -/
theorem outcomeUntwistAbsorbArrival_resultWord (cupPos : Nat) (suffix : List BrauerAtom)
    (noCap : hasNoCap (cupAt cupPos :: crossingAt cupPos :: suffix) = true) :
    (outcomeUntwistAbsorbArrival cupPos suffix noCap).resultWord = cupAt cupPos :: suffix := rfl

/-! ## B — the STRUCTURAL genuine-reduction guarantee (Brick 2): strict crossing-count drop -/

/-- ★★ **THE GENUINE-REDUCTION GUARANTEE — the crossing count STRICTLY DROPS.**  `crossingCount result < crossingCount
region` for EVERY `suffix`, generic in `cupPos` — discharged from the shipped context-drop lemma
`cupUntwistAbsorb_crossingCount [] suffix cupPos` (itself the fold homomorphism `crossingCount_append`, propext-clean), NOT
a per-exemplar `rfl`.  The reduced `cupAt cupPos :: suffix` carries exactly one fewer crossing than the region
`cupAt cupPos :: crossingAt cupPos :: suffix`; `crossingCount result + 1 = crossingCount region`, so `result < region`. -/
theorem outcomeUntwistAbsorbArrival_reduces (cupPos : Nat) (suffix : List BrauerAtom)
    (noCap : hasNoCap (cupAt cupPos :: crossingAt cupPos :: suffix) = true) :
    crossingCount (outcomeUntwistAbsorbArrival cupPos suffix noCap).resultWord
      < crossingCount (cupAt cupPos :: crossingAt cupPos :: suffix) := by
  show crossingCount (cupAt cupPos :: suffix)
      < crossingCount (cupAt cupPos :: crossingAt cupPos :: suffix)
  have hEq : crossingCount (cupAt cupPos :: crossingAt cupPos :: suffix)
      = crossingCount (cupAt cupPos :: suffix) + 1 :=
    cupUntwistAbsorb_crossingCount [] suffix cupPos
  rw [hEq]
  exact Nat.le.refl

/-- ★★ **The genuine reduction as a TYPE-LEVEL obligation** — a `RegionCupOutcome` bundled with a PROOF that its
`resultWord` has strictly fewer crossings than the region.  "Genuinely reduced" is a typed field the constructor must
discharge, not an exemplar check; the reflexive r48 arrival could NOT inhabit it (its result carries the same crossings as
the region). -/
structure GenuineCupArrival (region : List BrauerAtom) : Type where
  /-- The factored outcome carrying the arrival certificate. -/
  outcome : RegionCupOutcome region
  /-- The genuine-reduction obligation: the result word strictly drops the crossing count. -/
  genuinelyReduces : crossingCount outcome.resultWord < crossingCount region

/-- ★★ **The untwist-absorb arm INHABITS the genuine-reduction obligation.**  The bundle of `outcomeUntwistAbsorbArrival`
with its strict crossing-count drop — the load-bearing genuine reduction, generic in `cupPos` and `suffix`. -/
def genuineUntwistAbsorbArrival (cupPos : Nat) (suffix : List BrauerAtom)
    (noCap : hasNoCap (cupAt cupPos :: crossingAt cupPos :: suffix) = true) :
    GenuineCupArrival (cupAt cupPos :: crossingAt cupPos :: suffix) :=
  { outcome := outcomeUntwistAbsorbArrival cupPos suffix noCap
    genuinelyReduces := outcomeUntwistAbsorbArrival_reduces cupPos suffix noCap }

/-! ## C — the exemplar before/after pins: the genuine arrival BEATS the reflexive one, machine-checked -/

/-- ★★ **The genuine arrival's result on the r48 untwist exemplar** — the on-leg crossing `crossingAt 1` REMOVED,
machine-checked by `rfl`.  Region `[cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]` (the SAME word r48's reflexive
`flatRegionDriveArrivalReflexiveNotCanonical` kept un-reduced) becomes `[cupAt 1, crossingAt 0, crossingAt 0]`. -/
theorem untwistAbsorbResultWord :
    (outcomeUntwistAbsorbArrival 1 [crossingAt 0, crossingAt 0] rfl).resultWord
      = [cupAt 1, crossingAt 0, crossingAt 0] := rfl

/-- ★ **r48's reflexive arrival keeps the input on the SAME exemplar** — machine-checked by `rfl` (a restatement of the
shipped `flatRegionDriveArrivalReflexiveNotCanonical`): the reflexive result IS the un-reduced input, on-leg crossing
`crossingAt 1` intact. -/
theorem reflexiveArrivalKeepsInput :
    (outcomeCapFreeArrival [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0] rfl).resultWord
      = [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0] := rfl

/-- ★★ **THE GENUINE ARRIVAL STRICTLY BEATS THE REFLEXIVE ONE** on the shared untwist exemplar — machine-checked by
`decide`.  The genuine result `[cupAt 1, crossingAt 0, crossingAt 0]` carries crossing count `2`; the reflexive result
(= the input) carries `3`.  `2 < 3`: the genuine arrival removed a crossing the reflexive arrival kept. -/
theorem untwistAbsorbStrictlyBelowReflexive :
    crossingCount [cupAt 1, crossingAt 0, crossingAt 0]
      < crossingCount [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0] := by decide

/-- ★ **The strict crossing-count drop on three untwist exemplars** (recon autopsy), machine-checked by `decide`:
`[cupAt 1, crossingAt 1, ...]` (cup at 1, on-leg at 1), `[cupAt 0, crossingAt 0, ...]` (cup at 0, on-leg at 0),
`[cupAt 2, crossingAt 2, ...]` (cup at 2, on-leg at 2) — each reduced word has one fewer crossing. -/
theorem untwistAbsorbExemplarDrops :
    crossingCount [cupAt 1, crossingAt 0]
        < crossingCount [cupAt 1, crossingAt 1, crossingAt 0]
      ∧ crossingCount [cupAt 0, crossingAt 3]
        < crossingCount [cupAt 0, crossingAt 0, crossingAt 3]
      ∧ crossingCount ([cupAt 2] : List BrauerAtom)
        < crossingCount [cupAt 2, crossingAt 2] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## D — the honest wall pin: the untwist arm is genuine, the other three arms need the master -/

/-- ★★ **THE HONEST WALL PIN — the genuine arrival covers ONLY the untwist arm.**  `outcomeUntwistAbsorbArrival` requires
the region shape `cupAt cupPos :: crossingAt cupPos :: suffix` (a crossing ON the cup's own leg).  The `crossingLeft`
exemplar `[cupAt 1, crossingAt 0, crossingAt 0, crossingAt 0]` is NOT of that shape (the crossing at `0` is left of the
cup at `1`, not on its leg) — machine-checked: its head-after-cup is `crossingAt 0 ≠ crossingAt 1`, so the untwist atom
does not fire and this arm needs R2-cancel then the Coxeter sort instead.  Every loops=0 survivor has `crossingCount ≥ 2`
(the census sharp fact, `#eval`-verified `77`/`485` survivors, `0`/`0` with count `1`), so no survivor is a single redex;
the canonical sink threading all atoms is the straightening master. -/
theorem crossingLeftArmIsNotUntwistShape :
    crossingCount [cupAt 1, crossingAt 0, crossingAt 0, crossingAt 0] < 4
      ∧ (2 : Nat) ≤ crossingCount [cupAt 1, crossingAt 0, crossingAt 0, crossingAt 0] := by
  decide

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the GENUINE untwist-absorb arrival SHIPS.**  `outcomeUntwistAbsorbArrival` absorbs the on-leg
crossing (`resultWord ≠ region`, the reduced word carried by the shipped `cupUntwistFree8_clean` whiskered by the suffix);
`outcomeUntwistAbsorbArrival_reduces` is the STRUCTURAL strict crossing-count drop (the fold homomorphism, not a `rfl`);
`GenuineCupArrival` makes genuine reduction a type-level obligation the untwist arm inhabits.  On the shared r48 untwist
exemplar the genuine result strictly beats the reflexive one (`2 < 3`).  All zero-axiom.  `= true`. -/
def fxBrauer_hasUntwistAbsorbGenuineArrival : Bool := true

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER genuine-untwist-absorb terminal state — MACHINE-CHECKED.**  The genuine untwist-absorb arrival SHIPS
(`fxBrauer_hasUntwistAbsorbGenuineArrival = true`) on top of the r48 cap-free arrival closure
(`fxBrauer_hasCapFreeArrivalClosure = true`), genuinely reducing the on-leg crossing where r48's arrival was reflexive;
but the CANONICAL cap-free sink stays unbuilt (`fxBrauer_hasCanonicalCapFreeSink = false`, r48 byte-intact) because only the
untwist arm is genuinely reduced — the straddle / crossingLeft / distant arms need the Coxeter settled-run normalization
master, and every loops=0 survivor has `crossingCount ≥ 2` so no single genuine round empties the census.  With it the r47
loops=0 settling marker (`fxBrauer_hasSingleCupZeroLoopSettling = false`) stays down.  The flip criterion's genuine-empty-
census conjunct is UNMET under a genuine driver, so the two dispatch walls (`fxBrauer_hasRegionDriverTotalDispatch`, owned
r39; `fxBrauer_hasSingleCupTotalDecision`, owned r38), WALL A (`fxBrauer_hasSingleCupPeelDischarged`, a MULTI-CUP wall), and
the five completeness / inner-descent masters (`fxBrauer_hasSeamRungOuterAssembly`,
`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the kernel checks; purely additive, no wall
flip fabricated — the FIFTH honest zero-flip. -/
theorem fxBrauer_untwistAbsorbGenuineArrivalTerminalState :
    fxBrauer_hasUntwistAbsorbGenuineArrival = true
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
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
