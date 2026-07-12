import FX1Poly.Polygraph.TwoCategory.WalkingString.StringKParameterizationCensus
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelPinning

/-! # WalkingString — the N-LETTER ORIENTATION LABEL-PINNING CRUX (FC-4 r1 opener, part O2)

The `k = 2` label-pinning crux (`stringCupCod_ne_capDom`, `StringLabelPinning.lean:125`, FROZEN TRUE) proves a cup's
cod word is never a cap's dom word by cancelling the SHARED middle `G` and reducing to the single separator `F ≠ H`.
The census (`StringKParameterizationCensus`, O1) named why that route is a `k = 2` ACCIDENT: at `k ≥ 3` the shared
letter of a comparable cup-cod / cap-dom pair is not uniform (it can be the first or second position, or — for a
same-colour reversal — no aligned letter at all), so "cancel the shared middle, reduce to one inequality" has no
uniform residual and is refuted as a universal strategy (the recon `#eval` shared-aligned matrix at `k = 3` is
`[[0,1,0],[1,0,1],[0,1,0]]`).

This file ships the CORRECT `n`-letter crux, which IS uniform at every `k`: a cup cod is an ASCENDING adjacent index
pair, a cap dom is a DESCENDING one, and an ascending 2-word is never a descending 2-word.  The crux is GENERIC over
`List Nat` index words (`ascendingPair_ne_descendingPair`), then

  * **`k = 2` BRIDGE (recovers the shipped world).**  Via `pathIndexWord` (the faithful `{F,G,H} → {1,2,3}`
    abstraction, O1) the orientation crux RE-DERIVES the two shipped separators `stringFG_ne_stringHG` /
    `stringGH_ne_stringGF` and the full shipped crux `stringCupCod_ne_capDom` — a new lemma
    `stringCupCod_ne_capDom_viaOrientation` with the SAME signature as the frozen `stringCupCod_ne_capDom`, proven
    through orientation instead of shared-`G` cancellation.  This validates the orientation model against the shipped
    `k = 2` slice on the nose (the shipped separators are exactly the orientation crux at letters `L1/L2/L3`).
  * **`k = 3` FRESH FIRING (genuine new content, non-vacuity witnessed).**  The adjoint-QUADRUPLE cup/cap index words
    (`adjointStringCupCods 3 = [[1,2],[2,3],[3,4]]`, `adjointStringCapDoms 3 = [[2,1],[3,2],[4,3]]`, O1) are fed to the
    GENERIC crux over the full 3×3 grid (`quadCupCod_ne_capDom_fired`), producing genuine `≠` for every cup-cod /
    cap-dom pair.  The `k = 3` fixtures use the FRESH letter `L4` (index 4), ABSENT from the `k = 2` alphabet `{1,2,3}`
    (`carrierFixtureSpace_grows`) — so this is a genuine `k = 3` firing, NOT the `k = 2` world relabelled.

## The HONESTY LAW, discharged

An `n`-colour claim requires an `n`-colour PROOF.  The crux `ascendingPair_ne_descendingPair` is genuinely
`k`-generic (over `List Nat`), instantiated at `k = 2` (validated against the FROZEN shipped `stringCupCod_ne_capDom`
via `stringCupCod_ne_capDom_viaOrientation`, identical signature) AND fired fresh at `k = 3` with genuine adjoint-
quadruple fixtures whose fresh letter `L4` is not present at `k = 2`.  The census marker
`fxString_hasNColourOrientationLabelPinningCrux` flips `:= true` (in `StringKParameterizationCensus`, same commit).

## Parity nuance — where a fixture sub-space is trivially empty

The `k ≥ 3` SAME-COLOUR reversal `[i, i+1]` vs `[i+1, i]` (an ascending pair vs its reverse) shares no ALIGNED
letter, so the shared-middle-cancellation route cannot touch it — yet orientation still separates them
(`quadFreshPair_ne` fires exactly this shape at `L3·L4` vs `L4·L3`).  It cannot occur as an ACTUAL cup·cap adjacency
at a single endo-mode, because the unit `η_i` (mode `A`) and counit `ε_i` (mode `B`) of one colour sit at DIFFERENT
modes, so that adjacency sub-space is trivially empty at a fixed mode — documented here exactly as the shipped
even-width anti-vacuity nuance is documented at its fixtures.  The orientation crux is nonetheless TOTAL over the
index model, firing on that shape too, so the pin has no gap.

## What this does NOT do (honest round boundary)

This ships the crux + the `k = 2` bridge + the `k = 3` firing.  It does NOT flip `fxString_hasAdjointTripleCompleteness`
and does NOT touch any frozen file.  The DETERMINACY re-derivation (the `k = 3` seed inductive, the cup-restricted
COD atom-pin `stringTwoCell_domPack_uniqueOfCod_forCups` re-routing the refuted dom→cod pin, and fresh `k = 3` sort
fixtures) is the named r2+ bill (`fxString_hasNColourAtomPinReroute` stays `false`, O1); the Fuss–Catalan `k = 3`
dimension is the separately-deferred `FC-4-DIM` round (its own literature stage for the `k ≥ 3` boundary word).

ADDITIVE ONLY on the shipped WalkingString files.  Raw Lean 4 + Init; the generic crux is `congrArg` + `Bool.noConfusion`,
the bridge is `mt (congrArg pathIndexWord)`, the `k = 3` grid is `List.Mem` constructor `cases` + concrete `rfl`
orientation booleans; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic orientation crux — an ascending pair is never a descending pair -/

/-- ★★ **THE `n`-LETTER ORIENTATION CRUX (generic over `List Nat`).**  If the index word `w` is an ASCENDING adjacent
pair (`isAscendingPair w = true`) and `v` is NOT ascending (`isAscendingPair v = false` — in particular any DESCENDING
cap dom), then `w ≠ v`.  Proof: were `w = v`, applying `isAscendingPair` (`congrArg`) would force `true = false`,
refuted by `Bool.noConfusion`.  This is the uniform-at-every-`k` replacement for the `k = 2`-only "cancel the shared
middle `G`, reduce to `F ≠ H`" route: cup cods are ascending, cap doms descending, so the two are disjoint at every
number of colours, no shared-letter alignment required. -/
theorem ascendingPair_ne_descendingPair {ascendingWord descendingWord : List Nat}
    (ascendingIsAscending : isAscendingPair ascendingWord = true)
    (descendingIsNotAscending : isAscendingPair descendingWord = false) :
    ascendingWord ≠ descendingWord :=
  fun wordsEqual =>
    Bool.noConfusion
      (ascendingIsAscending.symm.trans ((congrArg isAscendingPair wordsEqual).trans descendingIsNotAscending))

/-! ## The `k = 2` bridge — orientation recovers the shipped separators + the shipped crux -/

/-- Two 1-cells with distinct INDEX WORDS are distinct (`mt (congrArg pathIndexWord)`).  `pathIndexWord` is
monomorphic, so no polymorphic-eq propext leak — the bridge from the generic `List Nat` crux back to the shipped
`ModalityPath` separators. -/
theorem paths_ne_of_indexWords_ne {sourceMode targetMode : AdjointTripleMode}
    {pathOne pathTwo : ModalityPath adjointTripleGraph sourceMode targetMode}
    (indexWordsDiffer : pathIndexWord pathOne ≠ pathIndexWord pathTwo) : pathOne ≠ pathTwo :=
  mt (congrArg pathIndexWord) indexWordsDiffer

/-- ★ **`F·G ≠ H·G` recovered via ORIENTATION** (the shipped `stringFG_ne_stringHG`, `StringLabelPinning.lean:88`,
re-derived).  The lower-unit cod `F·G` has index word `[1,2]` (ascending), the upper-counit dom `H·G` has `[3,2]`
(descending); the generic crux separates them — NO shared-`G` cancellation.  Same conclusion as the shipped separator,
by the orientation route. -/
theorem stringFG_ne_stringHG_viaOrientation : stringFG ≠ stringHG :=
  paths_ne_of_indexWords_ne
    (ascendingPair_ne_descendingPair (ascendingWord := [1, 2]) (descendingWord := [3, 2]) rfl rfl)

/-- ★ **`G·H ≠ G·F` recovered via ORIENTATION** (the shipped `stringGH_ne_stringGF`, `StringLabelPinning.lean:101`,
re-derived).  The upper-unit cod `G·H` has index word `[2,3]` (ascending), the lower-counit dom `G·F` has `[2,1]`
(descending); the generic crux separates them. -/
theorem stringGH_ne_stringGF_viaOrientation : stringGH ≠ stringGF :=
  paths_ne_of_indexWords_ne
    (ascendingPair_ne_descendingPair (ascendingWord := [2, 3]) (descendingWord := [2, 1]) rfl rfl)

/-- ★★ **THE SHIPPED LABEL-PINNING CRUX, RECOVERED VIA ORIENTATION.**  Identical signature to the FROZEN
`stringCupCod_ne_capDom` (`StringLabelPinning.lean:125`): for any cup generator (`cupDom.length = 0`) and cap generator
(`capCod.length = 0`) between the same mid-modes, the cup's cod word is never the cap's dom word.  Same `cases` shape
as the shipped proof, but the two comparable cases discharge through the ORIENTATION separators
(`stringFG_ne_stringHG_viaOrientation` / `stringGH_ne_stringGF_viaOrientation`) instead of shared-`G` cancellation —
so the generic `n`-letter crux SUBSUMES the shipped `k = 2` pin.  This is the machine-checked bridge: the orientation
model, instantiated at letters `L1/L2/L3`, reproduces the frozen shipped crux on the nose. -/
theorem stringCupCod_ne_capDom_viaOrientation
    {midSource midTarget : AdjointTripleMode}
    {cupDom cupCod : ModalityPath adjointTripleGraph midSource midTarget}
    {capDom capCod : ModalityPath adjointTripleGraph midSource midTarget}
    (cupGen : StringTwoCell cupDom cupCod) (capGen : StringTwoCell capDom capCod)
    (cupIsCup : cupDom.length = 0) (capIsCap : capCod.length = 0) :
    cupCod ≠ capDom := by
  cases cupGen with
  | unitLower =>
      cases capGen with
      | unitLower => exact absurd capIsCap (by decide)
      | counitUpper => exact stringFG_ne_stringHG_viaOrientation
  | unitUpper =>
      cases capGen with
      | unitUpper => exact absurd capIsCap (by decide)
      | counitLower => exact stringGH_ne_stringGF_viaOrientation
  | counitLower => exact absurd cupIsCup (by decide)
  | counitUpper => exact absurd cupIsCup (by decide)

/-! ## The `k = 3` fresh firing — the adjoint quadruple, over genuine fixtures -/

/-- ★★ **THE `k = 3` FRESH FIRING (the generic crux, fired over the adjoint-quadruple grid).**  Every three-colour cup
cod (`[[1,2],[2,3],[3,4]] = adjointStringCupCods 3`) is distinct from every three-colour cap dom
(`[[2,1],[3,2],[4,3]] = adjointStringCapDoms 3`).  Proven by destructuring the `List.Mem` of each fixture (constructor
`cases`, zero-axiom — never an `iff` lemma) to a concrete pair, then firing `ascendingPair_ne_descendingPair` with the
orientation booleans by `rfl`.  This is the genuine three-colour content: `9` fresh inequalities the `k = 2` world
never states (its grid is only `2×2`), including every pair involving the fresh letter `L4`. -/
theorem quadCupCod_ne_capDom_fired :
    ∀ cupCod ∈ adjointStringCupCods 3, ∀ capDom ∈ adjointStringCapDoms 3, cupCod ≠ capDom := by
  intro cupCod cupCodMem capDom capDomMem
  have cupCodAscending : isAscendingPair cupCod = true := by
    cases cupCodMem with
    | head => rfl
    | tail _ afterFirstCup =>
        cases afterFirstCup with
        | head => rfl
        | tail _ afterSecondCup =>
            cases afterSecondCup with
            | head => rfl
            | tail _ afterThirdCup => nomatch afterThirdCup
  have capDomDescending : isAscendingPair capDom = false := by
    cases capDomMem with
    | head => rfl
    | tail _ afterFirstCap =>
        cases afterFirstCap with
        | head => rfl
        | tail _ afterSecondCap =>
            cases afterSecondCap with
            | head => rfl
            | tail _ afterThirdCap => nomatch afterThirdCap
  exact ascendingPair_ne_descendingPair cupCodAscending capDomDescending

/-- ★ **The fresh-`L4` firing** — `[L3, L4] ≠ [L4, L3]` (`adjointStringCupCodAt 3 ≠ adjointStringCapDomAt 3`), the
`k = 3` cup cod / cap dom at the FRESH letter `L4` (index 4), which the `k = 2` alphabet `{1,2,3}` does not contain.
This is also the SAME-COLOUR reversal shape (ascending pair vs its exact reverse) the shared-middle route cannot
touch (no aligned letter) — orientation fires on it directly.  Witnesses the crux is genuinely new at `k = 3`, not a
`k = 2` relabelling. -/
theorem quadFreshPair_ne : adjointStringCupCodAt 3 ≠ adjointStringCapDomAt 3 :=
  ascendingPair_ne_descendingPair (ascendingWord := [3, 4]) (descendingWord := [4, 3]) rfl rfl

/-- **Non-vacuity of the `k = 3` fixture space** — the three-colour cup-cod list strictly EXTENDS the two-colour one
(`adjointStringCupCods 3 ≠ adjointStringCupCods 2`), adding the fresh `[L3, L4] = [3,4]`.  So the `k = 3` firing ranges
over strictly MORE fixtures than the `k = 2` world, the extra one carrying the fresh letter `L4`.  `by decide`. -/
theorem carrierFixtureSpace_grows : adjointStringCupCods 3 ≠ adjointStringCupCods 2 := by decide

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the orientation crux BRIDGES the shipped `k = 2` world.**  The generic
`ascendingPair_ne_descendingPair` (over `List Nat`), via the faithful `pathIndexWord` abstraction, re-derives the two
shipped colour separators (`stringFG_ne_stringHG_viaOrientation` / `stringGH_ne_stringGF_viaOrientation`) and the FULL
shipped label-pinning crux (`stringCupCod_ne_capDom_viaOrientation`, byte-identical signature to the FROZEN
`stringCupCod_ne_capDom`), through orientation instead of shared-`G` cancellation.  The `k = 2` slice validated on the
nose.  `= true`. -/
def fxString_hasOrientationCruxBridgesShipped : Bool := true

/-- **★ ESTABLISHED — the orientation crux FIRES FRESH at `k = 3`.**  The generic crux is fired over the genuine
adjoint-quadruple fixtures (`adjointStringCupCods 3` × `adjointStringCapDoms 3`, the full 3×3 grid,
`quadCupCod_ne_capDom_fired`), including every pair involving the fresh letter `L4` (`quadFreshPair_ne`), whose index
`4` is ABSENT from the `k = 2` alphabet `{1,2,3}` (`carrierFixtureSpace_grows`).  A genuine three-colour firing — the
HONESTY LAW discharged: `k`-generic statement, instantiated at `k = 2` (recovering the frozen world) AND fired fresh
at `k = 3` with non-vacuity witnessed.  `= true`. -/
def fxString_hasOrientationCruxFiredAtKThree : Bool := true

end FX1Poly.Polygraph
