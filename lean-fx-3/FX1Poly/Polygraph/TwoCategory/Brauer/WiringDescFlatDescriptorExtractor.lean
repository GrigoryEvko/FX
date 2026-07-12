import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTotalRegionDispatch

/-! # BRAUER r43 — the flat→descriptor EXTRACTOR (the r40 JAM D): recover a typed `SingleCupScope` from a flat word
with a Σ-bundled decode-correctness proof, then transport the r42 `totalDispatch` onto the actual flat region

r42 (`Brauer/WiringDescTotalRegionDispatch.lean`) shipped `totalDispatch : (scope : SingleCupScope) → RegionCupOutcome
(scopeWord scope)` — the TOTAL typed synthesis over the constructive descriptor.  Its flat-wall marker named the still
open piece: "the walls' 'arbitrary flat region' synthesis needs the still-unbuilt flat→descriptor EXTRACTOR (the r40
JAM D: recover a typed `List (DistantSlideStep cupPos)` from a flat tail with a decode-correctness proof)".

This round BUILDS that extractor, following the Danielsson correct-by-construction / index-by-grammar architecture
(DTP 2013) rather than the Jourdan-Pottier-Leroy separate-validator style (ESOP 2012): each extractor is Σ-BUNDLED —
it returns the descriptor TOGETHER with the roundtrip proof that its decode reproduces the input word DEFINITIONALLY, so
no separate soundness theorem is needed and the transport onto the actual flat region is a single explicit-motive
`Eq.rec` (the shipped `RegionCupOutcome.transportByRegionEq`, r41-proven zero-axiom).  Per-step positional side
conditions are carried as `Bool = true` decidable evidence recovered structurally (the Gonthier-Mahboubi small-scale
reflection discipline, JFR 2010 §6.2): no `Bool.and_eq_true`, no `Nat.sub_*`, no `Nat.beq_refl`.

## What ships

  * ★★ **`recoverDistantIndex` / `extractDistantStep` / `extractDistantTail`** (JAM D core) — the Σ-bundled typed-tail
    builder.  `extractDistantStep cupPos atom` recovers a `DistantSlideStep cupPos` from a flat crossing / cap at
    position `k + 2` with `cupPos ≤ k` (the disjointness `Prop` synthesized from the `Nat.ble` Bool via the hand-rolled
    structural `natLeOfBleExtract`), BUNDLING `distantStepAtom step = atom`; `extractDistantTail` folds it structurally,
    bundling `distantTailWord tail = word` — the roundtrip, carried in the return type.
  * ★ **`untwistRunCount` / `untwistRunRemainder` / `untwistRun_roundtrip`** — the leading-`crossingAt cupPos` run peel
    with its cons-only roundtrip `List.replicate count (crossingAt cupPos) ++ remainder = word` (NO `List.append_assoc`,
    which leaks `propext`).
  * ★★ **`extractWorkingRegion`** — the head-cup working-region extractor: from a flat word whose head is a cup, recover
    the typed `SingleCupScope` (arrivedDistant / untwistThenDistant / straddleThenDistant / crossingLeftSettled EXACT /
    loopPair BARE), Σ-bundling `scopeWord s = word`; the honest partials (snakes, the cupless prefix, the JAM-A/JAM-B
    geometries) route to `none`.
  * ★★ **`flatRegionDispatch`** — the flat synthesis: `extractWorkingRegion` then `RegionCupOutcome.transportByRegionEq`
    onto the actual word, a single explicit-motive `Eq.rec`.  Fires on every flat hostile (`flatDispatch_hostiles`): the
    three reachable in-scope words (untwist-run, straddle, high-slot distant) synthesize `some` arrived outcomes, and the
    two JAM geometries (JAM-A crossingLeft-not-exact, JAM-B loop-with-suffix) honestly route to `none`.

## The honest wall — the extractor is NECESSARY but NOT SUFFICIENT for the walls; they STAY false (adjudicated vs TEXT)

`fxBrauer_hasFlatDescriptorExtractor` is the new additive marker.  The three dispatch walls
(`fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`)
and the five completeness / inner-descent masters STAY `false`, adjudicated against the wall TEXT: both dispatch walls
demand synthesis "over an ARBITRARY region", and the r42 flat-wall names the extractor as ONE of two ingredients (the
other being "the reachability↔shape argument that every reachable single-cup working region IS in scope") PLUS the two
in-scope geometry residuals — JAM-A (`crossingLeft` NOT-exact, a distant cap wedged behind the settled crossing, needs a
commute-continue arm) and JAM-B (loop-with-nonempty-suffix, the J-loop count varies with the suffix).  This round routes
BOTH JAM geometries to `none` (an honest partial, NOT a flip), and ships neither the reachability↔shape proof nor the
snake / cupless-prefix arms.  So the extractor alone flips nothing beyond its own marker; the flips move to r44+.  Every
residual is a route / reachability gap, never a truth gap (Lehrer-Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; STRUCTURAL recursion on word lists (extractDistantTail on the tail, the untwist peel on the word);
Σ-bundled roundtrips proved by cons-only `rw` (no `List.append_assoc`); the disjointness `Prop` from `Nat.ble` via the
hand-rolled structural `natLeOfBleExtract`; the crossing / cap reconstruction by structure eta + `rw [← hc]` off the
`DecidableEq WiringDesc` equality (no `isCrossingAtom` arc-shape check); the transport a single explicit-motive `Eq.rec`
(`RegionCupOutcome.transportByRegionEq`); no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` / `propext` /
`Bool.and_eq_true` / `Nat.beq_refl` / `Nat.sub_*`.  Per-declaration `#assert_no_axioms` in the audit twin + an
independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the two-fold `Nat` boolean-to-Prop bridge + the atom reconstruction primitives -/

/-- `Nat.ble a b = true → a ≤ b`, hand-rolled structurally (the shipped `natLeOfBleWidth` is `private`; `Nat.ble`
carries no `propext` leak).  Synthesizes the `DistantSlideStep` disjointness `Prop` from the decidable `Nat.ble`. -/
theorem natLeOfBleExtract : (a b : Nat) → Nat.ble a b = true → a ≤ b
  | 0, b, _ => Nat.zero_le b
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (natLeOfBleExtract a b h)

/-- Reconstruct a CROSSING atom from a full wiring equality: `crossingAt atom.position = atom` when `atom.wiring =
crossingWiring`.  Structure eta + `rw [← hc]` — a genuine `Eq`, not the arc-shape `isCrossingAtom` check. -/
theorem crossingAt_of_wiring (atom : BrauerAtom) (hc : atom.wiring = crossingWiring) :
    crossingAt atom.position = atom := by
  show ({ position := atom.position, wiring := crossingWiring } : BrauerAtom) = atom
  rw [← hc]

/-- Reconstruct a CAP atom: `capAt atom.position = atom` when `atom.wiring = capWiring`. -/
theorem capAt_of_wiring (atom : BrauerAtom) (hc : atom.wiring = capWiring) :
    capAt atom.position = atom := by
  show ({ position := atom.position, wiring := capWiring } : BrauerAtom) = atom
  rw [← hc]

/-- Reconstruct a CUP atom: `cupAt atom.position = atom` when `atom.wiring = cupWiring`. -/
theorem cupAt_of_wiring (atom : BrauerAtom) (hc : atom.wiring = cupWiring) :
    cupAt atom.position = atom := by
  show ({ position := atom.position, wiring := cupWiring } : BrauerAtom) = atom
  rw [← hc]

/-! ## B — `recoverDistantIndex`: the boundary position `k + 2` decoder (full-arm, propext-clean) -/

/-- Recover the descriptor CORE index `k` from a boundary position `k + 2` (the "two strands right of the cup" offset a
distant generator sits at); `none` on positions `0` / `1`.  Full three-arm match (`0` / `1` / `k + 2`), propext-clean. -/
def recoverDistantIndex : Nat → Option Nat
  | 0 => none
  | 1 => none
  | k + 2 => some k

/-- The `recoverDistantIndex` roundtrip: `recoverDistantIndex p = some k → p = k + 2`.  Full-arm structural on `p`. -/
theorem recoverDistantIndex_roundtrip : (p k : Nat) → recoverDistantIndex p = some k → p = k + 2
  | 0, k, h => by
      have hnone : (none : Option Nat) = some k := h
      contradiction
  | 1, k, h => by
      have hnone : (none : Option Nat) = some k := h
      contradiction
  | n + 2, k, h => by
      have hsome : (some n : Option Nat) = some k := h
      have hnk : n = k := Option.some.inj hsome
      rw [hnk]

/-! ## C — the Σ-bundled typed-tail builder (JAM D core) -/

/-- ★★ **One flat DISTANT step, Σ-bundled.**  Recover a `DistantSlideStep cupPos` from `atom` when it is a crossing /
cap at a boundary position `k + 2` with `cupPos ≤ k` (the disjointness `Prop` synthesized from `Nat.ble` via
`natLeOfBleExtract`), returning it TOGETHER with the decode roundtrip `distantStepAtom step = atom`.  The wiring is read
off the genuine `DecidableEq WiringDesc` equality (not the arc-shape `isCrossingAtom`), so the reconstruction is a real
`Eq`.  Rejects settled crossings / straddles / loops / snakes (position not `k + 2` or `cupPos ≰ k`) as `none`. -/
def extractDistantStep (cupPos : Nat) (atom : BrauerAtom) :
    Option (PSigma (fun step : DistantSlideStep cupPos => distantStepAtom step = atom)) :=
  if hcross : atom.wiring = crossingWiring then
    match hp : recoverDistantIndex atom.position with
    | some k =>
        if hle : Nat.ble cupPos k = true then
          some ⟨DistantSlideStep.crossing k (natLeOfBleExtract cupPos k hle), by
            show crossingAt (k + 2) = atom
            have hpos : atom.position = k + 2 := recoverDistantIndex_roundtrip atom.position k hp
            have hrec : crossingAt atom.position = atom := crossingAt_of_wiring atom hcross
            rw [hpos] at hrec
            exact hrec⟩
        else none
    | none => none
  else if hcap : atom.wiring = capWiring then
    match hp : recoverDistantIndex atom.position with
    | some k =>
        if hle : Nat.ble cupPos k = true then
          some ⟨DistantSlideStep.cap k (natLeOfBleExtract cupPos k hle), by
            show capAt (k + 2) = atom
            have hpos : atom.position = k + 2 := recoverDistantIndex_roundtrip atom.position k hp
            have hrec : capAt atom.position = atom := capAt_of_wiring atom hcap
            rw [hpos] at hrec
            exact hrec⟩
        else none
    | none => none
  else none

/-- ★★ **The Σ-bundled DISTANT TAIL builder.**  Structural recursion folding `extractDistantStep` over the flat word,
returning the typed `List (DistantSlideStep cupPos)` TOGETHER with the decode roundtrip `distantTailWord tail = word`.
The whole tail extracts iff every atom is a genuine distant generator; otherwise `none`.  Cons-only roundtrip, no
`List.append_assoc`. -/
def extractDistantTail (cupPos : Nat) :
    (word : List BrauerAtom) →
    Option (PSigma (fun tail : List (DistantSlideStep cupPos) => distantTailWord tail = word))
  | [] => some ⟨[], rfl⟩
  | atom :: rest =>
      match extractDistantStep cupPos atom with
      | none => none
      | some ⟨step, hstep⟩ =>
          match extractDistantTail cupPos rest with
          | none => none
          | some ⟨restTail, hrest⟩ =>
              some ⟨step :: restTail, by
                show distantStepAtom step :: distantTailWord restTail = atom :: rest
                rw [hstep, hrest]⟩

/-- ★ **The decode roundtrip, exposed as a named theorem** (the Σ-bundle's `.snd` projected).  For any bundle
`extractDistantTail` returns, its typed tail decodes back to the input word.  This is E2 the roundtrip, stated. -/
theorem extractDistantTail_decodes (cupPos : Nat) (word : List BrauerAtom)
    (bundle : PSigma (fun tail : List (DistantSlideStep cupPos) => distantTailWord tail = word))
    (_isExtractedBundle : extractDistantTail cupPos word = some bundle) :
    distantTailWord bundle.fst = word :=
  bundle.snd

/-! ## D — the leading-untwist-run peel (cons-only roundtrip) -/

/-- Is `atom` exactly a crossing on the cup's own legs (`crossingAt cupPos`) — the leading untwist generator?  Bool test
via `Nat.beq` on the position + the full `isCrossingWiring` wiring check. -/
def isLeadingUntwistCrossing (cupPos : Nat) (atom : BrauerAtom) : Bool :=
  Nat.beq atom.position cupPos && isCrossingWiring atom.wiring

/-- `isLeadingUntwistCrossing cupPos atom = true → atom = crossingAt cupPos`, via the `&&`-split, position `Nat.beq`, and
`crossingWiring_reconstruct` + structure eta. -/
theorem atom_eq_crossingAt_of_isLeadingUntwist (cupPos : Nat) (atom : BrauerAtom)
    (h : isLeadingUntwistCrossing cupPos atom = true) : atom = crossingAt cupPos := by
  have hpos : atom.position = cupPos := Nat.eq_of_beq_eq_true (andEqTrue_left h)
  have hwiring : atom.wiring = crossingWiring := crossingWiring_reconstruct atom.wiring (andEqTrue_right h)
  have hrec : crossingAt atom.position = atom := crossingAt_of_wiring atom hwiring
  rw [hpos] at hrec
  exact hrec.symm

/-- The count of leading `crossingAt cupPos` atoms (the untwist run length). -/
def untwistRunCount (cupPos : Nat) : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isLeadingUntwistCrossing cupPos atom) (untwistRunCount cupPos rest + 1) 0

/-- The word remaining after the leading untwist run is peeled. -/
def untwistRunRemainder (cupPos : Nat) : List BrauerAtom → List BrauerAtom
  | [] => []
  | atom :: rest => cond (isLeadingUntwistCrossing cupPos atom) (untwistRunRemainder cupPos rest) (atom :: rest)

/-- ★ **The untwist-run peel roundtrip.**  `List.replicate count (crossingAt cupPos) ++ remainder = word`: replaying the
peeled run in front of the remainder reproduces the word.  Cons-only structural induction (no `List.append_assoc`). -/
theorem untwistRun_roundtrip (cupPos : Nat) : (word : List BrauerAtom) →
    List.replicate (untwistRunCount cupPos word) (crossingAt cupPos) ++ untwistRunRemainder cupPos word = word
  | [] => rfl
  | atom :: rest => by
      show List.replicate (cond (isLeadingUntwistCrossing cupPos atom) (untwistRunCount cupPos rest + 1) 0)
            (crossingAt cupPos)
            ++ cond (isLeadingUntwistCrossing cupPos atom) (untwistRunRemainder cupPos rest) (atom :: rest)
            = atom :: rest
      cases huntwist : isLeadingUntwistCrossing cupPos atom with
      | true =>
          have hatom : atom = crossingAt cupPos := atom_eq_crossingAt_of_isLeadingUntwist cupPos atom huntwist
          show crossingAt cupPos :: (List.replicate (untwistRunCount cupPos rest) (crossingAt cupPos)
                ++ untwistRunRemainder cupPos rest) = atom :: rest
          rw [untwistRun_roundtrip cupPos rest, ← hatom]
      | false =>
          show List.replicate 0 (crossingAt cupPos) ++ (atom :: rest) = atom :: rest
          rfl

/-! ## E — the head-cup working-region extractor + the flat dispatch -/

/-- ★★ **The head-cup working-region extractor.**  From a flat tail after a cup at `cupPos`, recover the typed
`SingleCupScope`, Σ-bundling `scopeWord s = cupAt cupPos :: tail'`.  Arms, in order: the empty tail (`arrivedDistant []`
= `cupArrivedAlone`); a leading untwist run (`untwistThenDistant`, the remainder a distant tail); an all-distant tail
(`arrivedDistant`); an adjacent straddle crossing at `cupPos + 1` (`straddleThenDistant`); a settled topPerm crossing
`xpos < cupPos` as the SOLE right atom (`crossingLeftSettled`, EXACT — `rest2` refined `[]`); a cap AT `cupPos` as the
SOLE right atom (`loopPair`, BARE).  Honest partials → `none`: snakes (cap at `cupPos ± 1`), the JAM-A geometry (a
settled crossing with a nonempty `rest2`), the JAM-B geometry (a loop-at-cup with a nonempty `rest2`). -/
def extractCupHead (cupPos : Nat) :
    (tail' : List BrauerAtom) → Option (PSigma (fun s : SingleCupScope => scopeWord s = cupAt cupPos :: tail'))
  | [] => some ⟨.arrivedDistant cupPos [], rfl⟩
  | next :: rest2 =>
      if huntwist : isLeadingUntwistCrossing cupPos next = true then
        match extractDistantTail cupPos (untwistRunRemainder cupPos (next :: rest2)) with
        | some ⟨tail, hrest⟩ =>
            some ⟨.untwistThenDistant cupPos (untwistRunCount cupPos (next :: rest2)) tail, by
              show cupAt cupPos :: (List.replicate (untwistRunCount cupPos (next :: rest2)) (crossingAt cupPos)
                    ++ distantTailWord tail) = cupAt cupPos :: (next :: rest2)
              rw [hrest, untwistRun_roundtrip cupPos (next :: rest2)]⟩
        | none => none
      else
        match extractDistantTail cupPos (next :: rest2) with
        | some ⟨tail, hrest⟩ =>
            some ⟨.arrivedDistant cupPos tail, by
              show cupAt cupPos :: distantTailWord tail = cupAt cupPos :: (next :: rest2)
              rw [hrest]⟩
        | none =>
            if hcross : next.wiring = crossingWiring then
              if hstr : Nat.beq next.position (cupPos + 1) = true then
                match extractDistantTail (cupPos + 1) rest2 with
                | some ⟨tail, hrest⟩ =>
                    some ⟨.straddleThenDistant cupPos tail, by
                      show cupAt cupPos :: crossingAt (cupPos + 1) :: distantTailWord tail
                            = cupAt cupPos :: next :: rest2
                      have hpos : next.position = cupPos + 1 := Nat.eq_of_beq_eq_true hstr
                      rw [hrest, ← hpos, crossingAt_of_wiring next hcross]⟩
                | none => none
              else if hlt : Nat.blt next.position cupPos = true then
                match rest2 with
                | [] =>
                    some ⟨.crossingLeftSettled cupPos next.position hlt, by
                      show (cupAt cupPos :: crossingAt next.position :: []) = cupAt cupPos :: next :: []
                      rw [crossingAt_of_wiring next hcross]⟩
                | _ :: _ => none
              else none
            else if hcap : next.wiring = capWiring then
              if hloop : Nat.beq next.position cupPos = true then
                match rest2 with
                | [] =>
                    some ⟨.loopPair cupPos, by
                      show (cupAt cupPos :: capAt cupPos :: []) = cupAt cupPos :: next :: []
                      have hpos : next.position = cupPos := Nat.eq_of_beq_eq_true hloop
                      rw [← hpos, capAt_of_wiring next hcap]⟩
                | _ :: _ => none
              else none
            else none

/-- ★★ **The flat working-region extractor.**  From an arbitrary flat word whose head is a cup, recover the typed
`SingleCupScope`, Σ-bundling `scopeWord s = word`.  A non-cup head (the cupless-prefix layer, r44) or an empty word
routes to `none`. -/
def extractWorkingRegion : (word : List BrauerAtom) →
    Option (PSigma (fun s : SingleCupScope => scopeWord s = word))
  | [] => none
  | atom :: tail' =>
      if hcup : atom.wiring = cupWiring then
        match extractCupHead atom.position tail' with
        | some ⟨s, h⟩ => some ⟨s, by rw [h, cupAt_of_wiring atom hcup]⟩
        | none => none
      else none

/-- ★★ **THE FLAT SYNTHESIS.**  Extract the typed scope from the flat word, then transport the r42 `totalDispatch`
outcome onto the ACTUAL word by the shipped explicit-motive `Eq.rec` (`RegionCupOutcome.transportByRegionEq`, r41-proven
zero-axiom).  Total as a function; `some` on the reachable in-scope words, honest `none` on the out-of-scope / JAM
geometries. -/
def flatRegionDispatch (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  match extractWorkingRegion word with
  | some ⟨s, h⟩ => some (RegionCupOutcome.transportByRegionEq h (totalDispatch s))
  | none => none

/-! ## F — the firing probes, machine-checked -/

/-- ★ **The recon flagship distant tail extracts.**  `[crossingAt 3, crossingAt 4, capAt 5]` at `cupPos 0` is a genuine
distant tail; the Σ-bundle carries the decode roundtrip `distantTailWord tail = [crossingAt 3, crossingAt 4, capAt 5]`
(via `extractDistantTail_decodes`). -/
theorem extractDistantTail_flagship :
    (extractDistantTail 0 [crossingAt 3, crossingAt 4, capAt 5]).isSome = true := rfl

/-- ★★ **THE FLAT SYNTHESIS FIRES ON EVERY HOSTILE — machine-checked by `rfl`** (pure structural extraction, no
`brauerDiagramOf`).  The three reachable in-scope words synthesize `some` outcomes over the ACTUAL flat region — the
untwist-run `[cupAt 0, crossingAt 0, crossingAt 0, crossingAt 3, capAt 4]`, the straddle `[cupAt 0, crossingAt 1,
crossingAt 3, capAt 4]`, and the high-slot distant `[cupAt 7, crossingAt 9, capAt 11]` — while the two JAM geometries
honestly route to `none`: JAM-A `[cupAt 2, crossingAt 0, capAt 9]` (a settled crossing with a distant cap wedged behind
it — `crossingLeft` NOT-exact) and JAM-B `[cupAt 2, capAt 2, capAt 9]` (a loop with a nonempty suffix). -/
theorem flatDispatch_firesOnHostiles :
    (flatRegionDispatch [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDispatch [cupAt 0, crossingAt 1, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDispatch [cupAt 7, crossingAt 9, capAt 11]).isSome = true
      ∧ (flatRegionDispatch [cupAt 2, crossingAt 0, capAt 9]).isNone = true
      ∧ (flatRegionDispatch [cupAt 2, capAt 2, capAt 9]).isNone = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **The extractor's coverage + honest partials, machine-checked.**  The two additional in-scope singleton shapes
extract (`crossingLeftSettled` on `[cupAt 1, crossingAt 0]`, `loopPair` on `[cupAt 0, capAt 0]`), and the deferred /
out-of-scope shapes route to `none`: the two snakes (`[cupAt 0, capAt 1]` snakeRight, `[cupAt 1, capAt 0]` snakeLeft, the
r44 arms) and a non-cup head (`[crossingAt 9]`, the cupless-prefix layer). -/
theorem extractWorkingRegion_coverage :
    (extractWorkingRegion [cupAt 1, crossingAt 0]).isSome = true
      ∧ (extractWorkingRegion [cupAt 0, capAt 0]).isSome = true
      ∧ (extractWorkingRegion [cupAt 0, capAt 1]).isNone = true
      ∧ (extractWorkingRegion [cupAt 1, capAt 0]).isNone = true
      ∧ (extractWorkingRegion ([crossingAt 9] : List BrauerAtom)).isNone = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the flat→descriptor EXTRACTOR SHIPS (the r40 JAM D, built).**  `extractDistantStep` /
`extractDistantTail` recover a typed `List (DistantSlideStep cupPos)` from a flat tail Σ-BUNDLED with the decode
roundtrip `distantTailWord tail = word` (`extractDistantTail_decodes`); `untwistRun_roundtrip` peels the leading untwist
run cons-only; `extractWorkingRegion` recovers the typed `SingleCupScope` from a head-cup flat word bundling `scopeWord
s = word` across the five in-scope arms; `flatRegionDispatch` transports the r42 `totalDispatch` onto the ACTUAL flat
region by the shipped explicit-motive `Eq.rec`.  `flatDispatch_firesOnHostiles` fires on all five flat hostiles (three
`some` arrived, two JAM `none`); `extractWorkingRegion_coverage` pins the crossingLeft / loop coverage + the honest
snake / cupless-prefix partials.  All zero-axiom.  `= true`. -/
def fxBrauer_hasFlatDescriptorExtractor : Bool := true

/-- **Honesty WALL marker — the flat SYNTHESIS wall + the two dispatch walls STAY `false`; the extractor is NECESSARY
but NOT SUFFICIENT (adjudicated vs the wall TEXT).**  The extractor discharges the r42-named JAM D (the flat→descriptor
recovery with a decode-correctness proof), but the walls demand synthesis "over an ARBITRARY region", and the r42
flat-wall names the extractor as ONE of two ingredients — the other being "the reachability↔shape argument that every
reachable single-cup working region IS in scope" — PLUS the two in-scope geometry residuals: JAM-A (`crossingLeft`
NOT-exact, needing a commute-continue arm) and JAM-B (loop-with-nonempty-suffix, the J-loop count varying with the
suffix).  This round routes BOTH JAM geometries to `none` (an honest partial, NOT a flip) and ships neither the
reachability↔shape proof nor the snake / cupless-prefix arms.  So `fxBrauer_hasFlatRegionDispatchSynthesis`,
`fxBrauer_hasRegionDriverTotalDispatch`, and `fxBrauer_hasSingleCupTotalDecision` STAY `false`, `fxBrauer_hasSingleCupPeelDischarged`
STAYS `false` (a MULTI-CUP wall), and the five completeness / inner-descent masters STAY `false`.  A route /
reachability gap, never a truth gap (Lehrer-Zhang arXiv:1207.5889 Thm 2.6).  This marker records that the extractor
alone flips nothing beyond its own; the wall flips move to r44+. -/
def fxBrauer_hasFlatDescriptorSynthesisGap : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r43 flat-descriptor-extractor terminal state — MACHINE-CHECKED.**  The new marker records the
honest split: the flat→descriptor EXTRACTOR SHIPS (`fxBrauer_hasFlatDescriptorExtractor = true`) over the head-cup
working region, built on the r42 `totalDispatch` assembly (`fxBrauer_hasTotalRegionDispatchAssembly = true`), while the
flat-word synthesis stays unbuilt — so the three dispatch walls (`fxBrauer_hasFlatRegionDispatchSynthesis`,
`fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`), the multi-cup peel discharge
(`fxBrauer_hasSingleCupPeelDischarged`), and the five completeness / inner-descent masters
(`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the
kernel checks; purely additive, no wall flip is fabricated (adjudicated against the wall TEXT). -/
theorem fxBrauer_flatDescriptorExtractorTerminalState :
    fxBrauer_hasFlatDescriptorExtractor = true
      ∧ fxBrauer_hasTotalRegionDispatchAssembly = true
      ∧ fxBrauer_hasFlatRegionDispatchSynthesis = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasSeamRungOuterAssembly = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
