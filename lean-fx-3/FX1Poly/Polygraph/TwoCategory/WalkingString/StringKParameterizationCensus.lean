import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingModel

/-! # WalkingString — the K-PARAMETERIZATION CENSUS (FC-4 r1 opener, part O1)

The shipped walking-adjoint-triple world (`StringSeed` … `StringIdentificationCapstone`) is the `k = 2` slice of a
`k`-indexed family: an adjoint STRING `L1 ⊣ L2 ⊣ … ⊣ L_{k+1}` (`k + 1` letters, `k` adjunctions, `k` Fuss–Catalan
COLOURS).  FC-4 (`#2210`) opens the extension of this lane past `k = 2`.  This file is the honest RECON RECORD: it
NAMES where `2` is baked into the shipped seed, exhibits a `k`-GENERIC index-word carrier that elaborates at `k = 2`
AND `k = 3`, machine-verifies that the shipped `k = 2` boundary words EMBED into that carrier, and posts the road
markers the crux round (O2) and the determinacy round (r2+) flip.

## The `k ↔ colour ↔ letter` bookkeeping (nailed first)

`k` = number of Fuss–Catalan COLOURS = number of adjacent adjunctions = (letter count − 1).

  * **shipped world `k = 2`** — the adjoint TRIPLE `F ⊣ G ⊣ H`, THREE letters `{F, G, H}`, TWO colours (the non-`G`
    ends `{F, H}`), TWO modes `{base, tip}`, FOUR generators (2 units + 2 counits).  `dim FC_n^{(2)} = (1/(2n+1))·
    C(3n, n) = 1, 1, 3, 12, 55`.
  * **FC-4 target `k = 3`** — the adjoint QUADRUPLE `L1 ⊣ L2 ⊣ L3 ⊣ L4`, FOUR letters, THREE colours, still TWO
    modes (letters alternate `A → B → A → B`), SIX generators (3 units + 3 counits).  `dim FC_n^{(3)} = (1/(3n+1))·
    C(4n, n)` (Shigechi arXiv:2507.23460 Prop 4.3; Bisch–Jones *Invent. Math.* 128 (1997) 89–157, the `r = k`-colour
    Fuss–Catalan tower).

Structural fact this census rests on (machine-checked below): each cup COD word is an ASCENDING adjacent index pair
`[Li, Li+1]` and each cap DOM word is a DESCENDING adjacent index pair `[Li+1, Li]`; an ascending 2-word is never a
descending 2-word, so cup cods and cap doms are DISJOINT at EVERY `k`.  This ORIENTATION invariant replaces the
`k = 2`-only "cancel the shared middle `G`, reduce to `F ≠ H`" accident (the shared middle is not uniform at `k ≥ 3`)
— the O2 crux `ascendingPair_ne_descendingPair` (`StringAdjointStringOrientationCrux`) makes it a theorem.

## The `2`-baked site census (where the shipped seed hardcodes `k = 2`)

The CONNECTIVITY engine (`matchingOf`, `stepCup`, `stepCap`, `processSpine`, `DiagramType`, `SpineTraceEquiv`, …) is
already `{signature : ModeSignature}`-POLYMORPHIC (`WalkingAdjunction/MatchingDecision.lean`) and colour-BLIND —
`stepAtom` reads arity off `generatorDom.length`/`generatorCod.length`, blind to the alphabet — so it runs at `k = 3`
UNMODIFIED.  What is baked to `2` is the SEED and the LABEL layer:

  * `AdjointTripleMode` (`StringSeed.lean:39`) — 2 modes (unchanged at `k = 3`: still 2 modes).
  * `AdjointTripleModality` (`StringSeed.lean:48`) — 3 letters `left/right/coLeft` → 4 letters at `k = 3`.
  * `stringFG/GF/GH/HG` (`StringSeed.lean:64,70,76,82`) — the 4 two-letter endo-words → 6 at `k = 3`.
  * `StringTwoCell` (`StringSeed.lean:93`) — 4 generators (2 unit / 2 counit) → 6 at `k = 3`.
  * `string_left_ne_coLeft` (`StringSeed.lean:129`) — the SINGLE colour separator `F ≠ H` → a `Li ≠ Lj` family.
  * `WireLabel` (`StringMatchingModel.lean:63`) — 3 colours `fWire/gWire/hWire` → `k + 1` labels.
  * `fcArcColour` (`StringFussCatalan.lean:82`) — "colour = the non-`G` letter" FALLS at `k ≥ 3` (no shared middle);
    colour must become the min-index of the adjacent pair.
  * `fussCatalanNumber` (`StringFussCatalan.lean:376`) — `C(3n,n)/(2n+1)` → `C((k+1)n,n)/(kn+1)` (deferred: `FC-4-DIM`).
  * the label crux `stringFG_ne_stringHG` / `stringGH_ne_stringGF` / `stringCupCod_ne_capDom`
    (`StringLabelPinning.lean:88,101,125`) — the 4-generator `cases` on the single `F ≠ H` → the O2 orientation crux.
  * the atom pin `stringTwoCell_codPack_uniqueOfDom` (`StringSpineAtomWordPin.lean:84`) — routes "dom determines cod",
    which is FALSE at `k ≥ 3` (`η1` dom `nil` cod `L1·L2`, `η3` dom `nil` cod `L3·L4`) — the r2+ COD-pin reroute.

## What this census ships (each piece zero-axiom, `#assert_no_axioms` gated in the twin)

  * `wireLabelIndex` / `pathIndexWord` — the FAITHFUL abstraction of a `{F,G,H}`-word to a `List Nat` index word
    (`F ↦ 1`, `G ↦ 2`, `H ↦ 3`), validated at `k = 2` against the shipped boundary words on the nose.
  * `isAscendingPair` — the orientation predicate (an adjacent index pair is ascending) the O2 crux fires on.
  * `adjointStringCupCods` / `adjointStringCapDoms` — the `k`-GENERIC carrier: for `k` colours, the `k` ascending cup
    cods `[i, i+1]` (`i = 1..k`) and the `k` descending cap doms `[i+1, i]`.  Elaborates at `k = 2` AND `k = 3`
    (checkable `rfl` pins).
  * the EMBEDDING pins — the shipped `k = 2` cup cods `{F·G, G·H}` and cap doms `{G·F, H·G}` coincide, via
    `pathIndexWord`, with the generic carrier at `k = 2` (`shippedCupCods_eq_carrierAtTwo`, on the nose).
  * the road markers — `fxString_hasKParameterizationCensus := true`, `fxString_hasKGenericConnectivityEngine := true`
    (documented), and the two OPEN markers `fxString_hasNColourOrientationLabelPinningCrux := false` (O2 flips) and
    `fxString_hasNColourAtomPinReroute := false` (the r2+ COD-pin reroute; the dom→cod atom pin is refuted at `k ≥ 3`).

ADDITIVE ONLY: no shipped WalkingString file is touched.  Raw Lean 4 + Init; structural recursion / full-enum
matches; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The faithful abstraction: a `{F,G,H}`-word as a `List Nat` index word -/

/-- The index of a wire label: `F ↦ 1`, `G ↦ 2`, `H ↦ 3` — the letters `L1..L_{k+1}` of the adjoint string ordered by
adjunction position (`F = L1`, `G = L2`, `H = L3` at `k = 2`).  Full-enum match, constant motive — propext-clean. -/
def wireLabelIndex : WireLabel → Nat
  | WireLabel.fWire => 1
  | WireLabel.gWire => 2
  | WireLabel.hWire => 3

/-- The **index word** of a 1-cell: its `F`/`G`/`H` label sequence (`pathLabels`) mapped to letter indices.  A
faithful `List Nat` abstraction of the boundary word — the carrier the orientation crux (O2) fires on.  Monomorphic
(`WireLabel`/`Nat`), so `congrArg pathIndexWord` carries no polymorphic-eq propext leak. -/
def pathIndexWord {sourceMode targetMode : AdjointTripleMode}
    (path : ModalityPath adjointTripleGraph sourceMode targetMode) : List Nat :=
  (pathLabels path).map wireLabelIndex

/-! ## The orientation predicate: an adjacent index pair is ascending -/

/-- Whether a 2-letter index word is an ASCENDING pair (`lowIndex < highIndex`), read via `Nat.blt`.  A cup cod
`[Li, Li+1]` is ascending; a cap dom `[Li+1, Li]` is descending (not ascending).  Full-enum match over the list shape
(`[]`, singleton, pair, length `≥ 3`) — no wildcard, propext-clean. -/
def isAscendingPair : List Nat → Bool
  | [] => false
  | [_] => false
  | [lowIndex, highIndex] => Nat.blt lowIndex highIndex
  | _ :: _ :: _ :: _ => false

/-! ## The `k`-generic adjoint-string carrier -/

/-- The cup COD word for the adjunction at letter position `letterIndex`: the ASCENDING adjacent pair
`[L_{letterIndex}, L_{letterIndex+1}]` (the unit `η_i : id ⇒ L_i·L_{i+1}` opens it). -/
def adjointStringCupCodAt (letterIndex : Nat) : List Nat := [letterIndex, letterIndex + 1]

/-- The cap DOM word for the adjunction at letter position `letterIndex`: the DESCENDING adjacent pair
`[L_{letterIndex+1}, L_{letterIndex}]` (the counit `ε_i : L_{i+1}·L_i ⇒ id` closes it). -/
def adjointStringCapDomAt (letterIndex : Nat) : List Nat := [letterIndex + 1, letterIndex]

/-- The `k` cup COD words of the adjoint string with `k` colours (letters `L1..L_{k+1}`): the ascending adjacent pairs
`[1,2], [2,3], …, [k, k+1]`.  Structural recursion on the colour count — propext-clean. -/
def adjointStringCupCods : Nat → List (List Nat)
  | 0 => []
  | Nat.succ colourCount => adjointStringCupCods colourCount ++ [adjointStringCupCodAt (colourCount + 1)]

/-- The `k` cap DOM words of the adjoint string with `k` colours: the descending adjacent pairs
`[2,1], [3,2], …, [k+1, k]`.  Structural recursion on the colour count — propext-clean. -/
def adjointStringCapDoms : Nat → List (List Nat)
  | 0 => []
  | Nat.succ colourCount => adjointStringCapDoms colourCount ++ [adjointStringCapDomAt (colourCount + 1)]

/-! ## Checkable pins — the carrier elaborates at `k = 2` and `k = 3` -/

/-- The two-colour (`k = 2`) cup cods: `[F·G, G·H]` as index words `[[1,2], [2,3]]`.  `rfl`. -/
theorem adjointStringCupCods_atTwo : adjointStringCupCods 2 = [[1, 2], [2, 3]] := rfl

/-- ★ The three-colour (`k = 3`) cup cods elaborate: `[[1,2], [2,3], [3,4]]` — the FRESH letter `L4` (index 4) is
absent from the `k = 2` alphabet `{1,2,3}`.  `rfl`. -/
theorem adjointStringCupCods_atThree : adjointStringCupCods 3 = [[1, 2], [2, 3], [3, 4]] := rfl

/-- The two-colour (`k = 2`) cap doms: `[G·F, H·G]` as index words `[[2,1], [3,2]]`.  `rfl`. -/
theorem adjointStringCapDoms_atTwo : adjointStringCapDoms 2 = [[2, 1], [3, 2]] := rfl

/-- ★ The three-colour (`k = 3`) cap doms elaborate: `[[2,1], [3,2], [4,3]]` (fresh `L4` at index 4).  `rfl`. -/
theorem adjointStringCapDoms_atThree : adjointStringCapDoms 3 = [[2, 1], [3, 2], [4, 3]] := rfl

/-! ## Checkable pins — the orientation invariant holds on the carrier at `k = 3` -/

/-- ★ Every `k = 3` cup cod is ASCENDING (`Nat.blt`-computed, on the nose).  `rfl`. -/
theorem adjointStringCupCods_allAscending_atThree :
    (adjointStringCupCods 3).all isAscendingPair = true := rfl

/-- ★ Every `k = 3` cap dom is DESCENDING (not ascending, on the nose).  Together with
`adjointStringCupCods_allAscending_atThree` this is the `k = 3` disjointness fingerprint the O2 crux discharges as a
theorem: no ascending cup cod is any descending cap dom.  `rfl`. -/
theorem adjointStringCapDoms_allDescending_atThree :
    (adjointStringCapDoms 3).all (fun word => ! isAscendingPair word) = true := rfl

/-! ## Checkable pins — the shipped `k = 2` boundary words EMBED into the carrier -/

/-- The shipped lower-unit cod word `F·G` has index word `[1, 2]` (ascending).  `rfl`. -/
theorem pathIndexWord_stringFG : pathIndexWord stringFG = [1, 2] := rfl

/-- The shipped lower-counit dom word `G·F` has index word `[2, 1]` (descending).  `rfl`. -/
theorem pathIndexWord_stringGF : pathIndexWord stringGF = [2, 1] := rfl

/-- The shipped upper-unit cod word `G·H` has index word `[2, 3]` (ascending).  `rfl`. -/
theorem pathIndexWord_stringGH : pathIndexWord stringGH = [2, 3] := rfl

/-- The shipped upper-counit dom word `H·G` has index word `[3, 2]` (descending).  `rfl`. -/
theorem pathIndexWord_stringHG : pathIndexWord stringHG = [3, 2] := rfl

/-- ★★ The shipped `k = 2` cup cods `{F·G, G·H}` coincide — via `pathIndexWord` — with the GENERIC carrier at
`k = 2` (`adjointStringCupCods 2`).  This machine-verifies the index abstraction is FAITHFUL at the shipped slice:
the two-colour world is exactly the `k = 2` instance of the family, not a re-labelling of something else.  `rfl`. -/
theorem shippedCupCods_eq_carrierAtTwo :
    [pathIndexWord stringFG, pathIndexWord stringGH] = adjointStringCupCods 2 := rfl

/-- ★★ The shipped `k = 2` cap doms `{G·F, H·G}` coincide, via `pathIndexWord`, with the generic carrier at `k = 2`
(`adjointStringCapDoms 2`).  The cap side of the faithful embedding.  `rfl`. -/
theorem shippedCapDoms_eq_carrierAtTwo :
    [pathIndexWord stringGF, pathIndexWord stringHG] = adjointStringCapDoms 2 := rfl

/-! ## Road markers -/

/-- **★ ESTABLISHED — the `k`-parameterization census is shipped.**  The shipped walking-adjoint-triple world is the
`k = 2` slice of the `k`-indexed adjoint-string family; this file NAMES the `2`-baked seed/label sites (header
table), exhibits the `k`-generic index-word carrier (`adjointStringCupCods`/`adjointStringCapDoms`) elaborating at
`k = 2` (`adjointStringCupCods_atTwo`) and `k = 3` (`adjointStringCupCods_atThree`, with the fresh letter `L4`), and
machine-verifies the shipped `k = 2` boundary words embed into it faithfully (`shippedCupCods_eq_carrierAtTwo` /
`shippedCapDoms_eq_carrierAtTwo`, on the nose).  `= true`. -/
def fxString_hasKParameterizationCensus : Bool := true

/-- **★ DOCUMENTED — the connectivity engine is already `k`-generic (colour-blind).**  The Joyal–Street boundary
matching (`matchingOf`, `stepCup`, `stepCap`, `processSpine`, `DiagramType`, `SpineTraceEquiv`, …,
`WalkingAdjunction/MatchingDecision.lean`) is `{signature : ModeSignature}`-polymorphic and reads arity off word
lengths, blind to the alphabet, so it runs at `k = 3` UNMODIFIED — the extension work is confined to the SEED
(6 generators), the LABEL layer (`k + 1` colours), and the label-pinning / atom-pin bricks (the O2 crux + the r2+
COD-pin reroute), not the connectivity spine.  Documented (the genericity is a property of the shipped engine's
signature-polymorphism, established by the file:line evidence in the header, not restated as a Lean pin here since a
`k = 3` `matchingOf` instantiation awaits the r2+ `k = 3` seed).  `= true`. -/
def fxString_hasKGenericConnectivityEngine : Bool := true

/-- **OPEN — the `n`-colour orientation label-pinning crux is NOT yet proven (O2 flips this).**  The census records
the orientation invariant (cup cods ascending, cap doms descending, disjoint at every `k`,
`adjointStringCupCods_allAscending_atThree` + `adjointStringCapDoms_allDescending_atThree`) but does NOT yet ship the
GENERIC inequality `ascendingPair_ne_descendingPair` nor its `k = 2` bridge / `k = 3` firing — that is the O2
deliverable (`StringAdjointStringOrientationCrux`), which flips this marker `:= true` in the same commit.  Held
`false` here so the census is honest about what it has and has not delivered.  `= false`. -/
def fxString_hasNColourOrientationLabelPinningCrux : Bool := false

/-- **OPEN — the `k ≥ 3` atom-pin reroute is a NAMED r2+ bill, not delivered here.**  The shipped determinacy brick's
atom pin routes through `stringTwoCell_codPack_uniqueOfDom` ("dom determines cod", `StringSpineAtomWordPin.lean:84`),
which is FALSE at `k ≥ 3`: the units `η1` (dom `nil`, cod `L1·L2`) and `η3` (dom `nil`, cod `L3·L4`) share dom `nil`
but differ in cod, so "dom determines cod" is refuted.  The re-derivation re-routes the shared-cod pin through a
cup-restricted COD pin (`stringTwoCell_domPack_uniqueOfCod_forCups`, "among cups, cod word determines the generator",
probed true) — that plus the `k = 3` seed and fresh `k = 3` sort fixtures is the r2+ determinacy bill; the
connectivity spine ports for free.  `= false`. -/
def fxString_hasNColourAtomPinReroute : Bool := false

end FX1Poly.Polygraph
