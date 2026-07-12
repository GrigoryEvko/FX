import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyProgress
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjacentPairLocate

/-! # WalkingString — the CUP-RESTRICTED COD ATOM-PIN REROUTE + the `k = 3` ENGINE FIRE (FC-4 r2, bricks R2 + R1/R3)

The shipped determinacy atom pin routes through `stringTwoCell_codPack_uniqueOfDom` ("the DOM word alone determines a
generator's (cod, cell) pack", `StringSpineAtomWordPin.lean`).  The census (`StringKParameterizationCensus`, O1) named
why that direction is REFUTED at `k ≥ 3`: on the adjoint quadruple the units `η1` (dom `nil`, cod `L1·L2`) and `η3`
(dom `nil`, cod `L3·L4`) SHARE dom `nil` at `base→base` but differ in cod — so "dom determines cod" is false.

## The graveyard discipline, obeyed

`stringTwoCell_codPack_uniqueOfDom` is REFUTED at `k ≥ 3` and is NEVER proved here.  Instead this file:

  * **PINS the refutation** (`quad_dom_does_not_determine_cod`) — the dom-pack of `η1` is NOT the dom-pack of `η3`,
    proven by pushing the would-be cod equality `L1·L2 = L3·L4` through `quadIndexWord` to the false `[1,2] = [3,4]`.
    The dom→cod direction is shown STILL refuted at `k = 3` by the `η1`/`η3` witness, as a PIN — never proven.
  * **REROUTES to the CUP-RESTRICTED COD direction** (`stringQuadTwoCell_domPack_uniqueOfCod_forCups`) — among cups
    (dom length 0), the COD word determines the (dom, cell) pack, because cup cods are pairwise-distinct ascending
    pairs.  This is the direction that survives at `k ≥ 3` (the census probe: cup cods injective).
  * **SHIPS the CAP DUAL** (`stringQuadTwoCell_codPack_uniqueOfDom_forCaps`) — among caps (cod length 0), the DOM word
    determines the (cod, cell) pack (cap doms are distinct descending pairs).  The `base→base`/`tip→tip` asymmetry (two
    cups collide on dom `nil`, two caps collide on cod `nil`) forces BOTH restricted pins: cups injective in COD, caps
    injective in DOM.

## The wide truth-probe (the reroute is de-risked BEFORE any universal)

The COD/DOM injectivity powering the pins is truth-probed over the census carrier at `k = 3` AND `k = 4` (per the
LIVE-TREE LAW: wide-probe the cup-restricted COD direction at `k = 3` AND `k = 4` before any universal): cup cods all
pairwise distinct (`cupCods_allDistinct_atThree` / `_atFour`), cap doms all distinct, cup cods cross-disjoint from cap
doms (`cupCapCrossDisjoint_atThree` / `_atFour`), and the collapse witness — cup DOMS all `nil`, hence NOT distinct
(`collapsedCupDoms_notAllDistinct`) — the exact refutation the reroute steps around.  The COD direction is wide-true;
no graveyard trigger.

## The `k = 3` ENGINE FIRE (R1) — the colour-blind connectivity engine machine-fired at three colours

The census marker `fxString_hasKGenericConnectivityEngine` was DOCUMENTED (a property of the shipped signature-
polymorphism, no `k = 3` `matchingOf` instance).  Here the engine is MACHINE-FIRED at `k = 3`: `matchingOfSpineList`
run on a genuine adjoint-quadruple cup atom (`quadEngineCupFires` — two top ports, partner `[1,0]`) and on a full
cup·cap spine that closes a loop (`quadEngineCupCapClosesLoop` — one loop, no open wires), plus the LOCATE
(`locateAdjacentCupCapSplit`) firing on a `k = 3` cup-then-cap spine and declining on cup-then-cup.  A NEW marker
`fxString_hasKGenericConnectivityEngineFired` records the machine fire (the soft shipped census marker is untouched).

## What this does NOT do (honest round boundary)

The determinacy-brick RE-DERIVATION (the `k = 3` keystone `stringSpineAtom_eq_of_wordReadOffs` with a cod-word
hypothesis, routing cups through the cup COD pin and caps through the cap DOM pin, plus its four consumers) is the
NAMED r3 bill — the census marker `fxString_hasNColourAtomPinReroute` stays `false` (it bundles determinacy, which r2
does not complete).  This ships the seed's two restricted pins + the wide truth tables + the `k = 3` engine/LOCATE
fixtures; the connectivity spine ports for free.

ADDITIVE ONLY on the shipped WalkingString files.  Raw Lean 4 + Init; the pins are `cases`-`cases` with automatic
index-clash discharge and concrete-length `by decide` guards, the refutation is `congrArg quadIndexWord` to a false
`List Nat` equality, the truth tables and engine/LOCATE fixtures are `rfl` on structural Bool / `DiagramType`
computations; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The refutation pin — dom does NOT determine cod at `k = 3` (the graveyard, marked not proved) -/

/-- ★ **The dom→cod atom pin is STILL REFUTED at `k = 3` — pinned by the `η1`/`η3` witness.**  The unit `η1`
(dom `nil`, cod `L1·L2`) and the unit `η3` (dom `nil`, cod `L3·L4`) share dom `nil` at `base→base` but their
cod-packs DIFFER: were the packs equal, the cod projection would force `L1·L2 = L3·L4`, which `quadIndexWord` sends to
the false `[1, 2] = [3, 4]`.  This is the exact refutation of the shipped `stringTwoCell_codPack_uniqueOfDom` at
`k ≥ 3` — the reroute target, marked as a PIN, never proved as a universal. -/
theorem quad_dom_does_not_determine_cod :
    (⟨quadL1L2, StringQuadTwoCell.unitOne⟩ :
        PSigma fun cod =>
          StringQuadTwoCell (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) cod)
      ≠ ⟨quadL3L4, StringQuadTwoCell.unitThree⟩ := by
  intro packsEqual
  have codsEqual : quadL1L2 = quadL3L4 := congrArg (fun pack => pack.fst) packsEqual
  have wordsEqual : quadIndexWord quadL1L2 = quadIndexWord quadL3L4 := congrArg quadIndexWord codsEqual
  exact absurd wordsEqual (by decide)

/-! ## The cup-restricted COD pin (the reroute) and the cap DOM dual -/

/-- ★★ **The CUP-RESTRICTED COD pin (the reroute).**  Among cups (`cupDom.length = 0`), the COD word alone determines
the (dom, cell) pack.  Casing the first cell, the cap constructors are killed by `absurd cupFirst` (their dom length is
2, not 0); the surviving cup fixes `cupCod` to a concrete ascending pair, and casing the second cell discards every
non-matching cup by the cod-index clash — so `rfl`.  This is the `k ≥ 3` replacement for the refuted
`stringTwoCell_codPack_uniqueOfDom`: the cup's dom (hence cell) is read off its COD, the direction that survives
because cup cods are pairwise-distinct ascending pairs (`cupCods_allDistinct_atThree`). -/
theorem stringQuadTwoCell_domPack_uniqueOfCod_forCups
    {midSource midTarget : AdjointQuadrupleMode}
    {cupCod : ModalityPath adjointQuadrupleGraph midSource midTarget}
    {cupDomFirst cupDomSecond : ModalityPath adjointQuadrupleGraph midSource midTarget}
    (cellFirst : StringQuadTwoCell cupDomFirst cupCod)
    (cellSecond : StringQuadTwoCell cupDomSecond cupCod)
    (cupFirst : cupDomFirst.length = 0) (cupSecond : cupDomSecond.length = 0) :
    (⟨cupDomFirst, cellFirst⟩ : PSigma fun cupDom => StringQuadTwoCell cupDom cupCod)
      = ⟨cupDomSecond, cellSecond⟩ := by
  cases cellFirst <;> cases cellSecond <;>
    first
      | rfl
      | exact absurd cupFirst (by decide)
      | exact absurd cupSecond (by decide)

/-- ★★ **The CAP-RESTRICTED DOM pin (the dual).**  Among caps (`capCod.length = 0`), the DOM word alone determines the
(cod, cell) pack.  The byte-mirror of the cup COD pin with dom↔cod swapped: casing the first cell, cups are killed by
`absurd capFirst` (cod length 2), the surviving cap fixes `capDom` to a concrete descending pair, and the second cell
is discarded by the dom-index clash — so `rfl`.  The direction that survives for caps (cap doms are distinct descending
pairs, `capDoms_allDistinct_atThree`); the `base→base`/`tip→tip` asymmetry demands this dual alongside the cup pin. -/
theorem stringQuadTwoCell_codPack_uniqueOfDom_forCaps
    {midSource midTarget : AdjointQuadrupleMode}
    {capDom : ModalityPath adjointQuadrupleGraph midSource midTarget}
    {capCodFirst capCodSecond : ModalityPath adjointQuadrupleGraph midSource midTarget}
    (cellFirst : StringQuadTwoCell capDom capCodFirst)
    (cellSecond : StringQuadTwoCell capDom capCodSecond)
    (capFirst : capCodFirst.length = 0) (capSecond : capCodSecond.length = 0) :
    (⟨capCodFirst, cellFirst⟩ : PSigma fun capCod => StringQuadTwoCell capDom capCod)
      = ⟨capCodSecond, cellSecond⟩ := by
  cases cellFirst <;> cases cellSecond <;>
    first
      | rfl
      | exact absurd capFirst (by decide)
      | exact absurd capSecond (by decide)

/-! ## The wide truth-probe tables — cod/dom injectivity at `k = 3` AND `k = 4` -/

/-- Monomorphic boolean equality of `List Nat` index words (full-enum `[]`/`cons` cases, `Nat.beq` on heads) — kept
monomorphic per the polymorphic-list-eq propext trap, so the truth tables stay propext-clean. -/
def natListEqB : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | firstHead :: firstTail, secondHead :: secondTail =>
      (firstHead == secondHead) && natListEqB firstTail secondTail

/-- Whether every word in a list of index words is distinct from every later word — the pairwise-distinctness probe. -/
def natWordListAllDistinct : List (List Nat) → Bool
  | [] => true
  | word :: rest => rest.all (fun other => ! natListEqB word other) && natWordListAllDistinct rest

/-- Whether no left index word equals any right index word — the cross-family disjointness probe. -/
def natWordListsCrossDisjoint (leftWords rightWords : List (List Nat)) : Bool :=
  leftWords.all (fun leftWord => rightWords.all (fun rightWord => ! natListEqB leftWord rightWord))

/-- ★ Cup cods pairwise distinct at `k = 3` (`[[1,2],[2,3],[3,4]]`): COD determines the cup.  `rfl`. -/
theorem cupCods_allDistinct_atThree : natWordListAllDistinct (adjointStringCupCods 3) = true := rfl

/-- ★ Cup cods pairwise distinct at `k = 4` (`+ [4,5]`): the reroute holds one colour past the target.  `rfl`. -/
theorem cupCods_allDistinct_atFour : natWordListAllDistinct (adjointStringCupCods 4) = true := rfl

/-- ★ Cap doms pairwise distinct at `k = 3` (`[[2,1],[3,2],[4,3]]`): DOM determines the cap.  `rfl`. -/
theorem capDoms_allDistinct_atThree : natWordListAllDistinct (adjointStringCapDoms 3) = true := rfl

/-- ★ Cap doms pairwise distinct at `k = 4`.  `rfl`. -/
theorem capDoms_allDistinct_atFour : natWordListAllDistinct (adjointStringCapDoms 4) = true := rfl

/-- ★ No cup cod is any cap dom at `k = 3` (ascending vs descending): cup-COD and cap-DOM families are cross-disjoint.
`rfl`. -/
theorem cupCapCrossDisjoint_atThree :
    natWordListsCrossDisjoint (adjointStringCupCods 3) (adjointStringCapDoms 3) = true := rfl

/-- ★ Cross-disjoint one colour past the target (`k = 4`).  `rfl`. -/
theorem cupCapCrossDisjoint_atFour :
    natWordListsCrossDisjoint (adjointStringCupCods 4) (adjointStringCapDoms 4) = true := rfl

/-- ★ **The collapse witness (the refuted DOM direction).**  Collapsing the three `k = 3` cup DOMS to their common
`nil` gives `[[],[],[]]`, which is NOT pairwise distinct — so the DOM does NOT determine the cup, the exact refutation
`quad_dom_does_not_determine_cod` the reroute steps around.  `rfl`. -/
theorem collapsedCupDoms_notAllDistinct : natWordListAllDistinct [[], [], []] = false := rfl

/-! ## The `k = 3` engine + LOCATE fixtures — the colour-blind connectivity engine machine-fired -/

/-- A `k = 3` CUP spine atom: the unit `η1` (dom `nil`, cod `L1·L2`) with empty whiskering contexts at `base→base`.
Its generator-dom length is 0, so `stepAtom` reads it as a cup. -/
def quadCupAtomBase :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- A `k = 3` CAP spine atom: the counit `ε2` (dom `L3·L2`, cod `nil`) with empty whiskering at `base→base`.  Its
generator-dom length is 2, its cod length 0, so `stepAtom` reads it as a cap.  Composable after `quadCupAtomBase`
(both `base→base`) into a genuine `k = 3` cup·cap spine. -/
def quadCapAtomBase :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := quadL3L2
  generatorCod := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generator := StringQuadTwoCell.counitTwo
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- Smoke: the `k = 3` cup atom reads as a cup (`isCupAtom = true`, generator-dom length 0).  `rfl`. -/
theorem quadCupAtom_isCup : quadCupAtomBase.isCupAtom = true := rfl

/-- Smoke: the `k = 3` cap atom reads as a cap (`isCupAtom = false`, generator-dom length 2).  `rfl`. -/
theorem quadCapAtom_isCap : quadCapAtomBase.isCupAtom = false := rfl

/-- ★★ **The connectivity engine MACHINE-FIRED at `k = 3` — a lone cup.**  `matchingOfSpineList` run on the genuine
adjoint-quadruple cup atom yields two top-boundary ports matched to each other (`partner = [1, 0]`), no loops — the
colour-blind engine (which reads arity off generator-dom/cod word lengths, blind to the four-letter alphabet)
elaborates and COMPUTES on a `k = 3` spine, unmodified.  `rfl` (`DiagramType` is a flat `Nat`/`List Nat` datum). -/
theorem quadEngineCupFires :
    matchingOfSpineList 0 [quadCupAtomBase]
      = { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 } := rfl

/-- ★★ **The engine MACHINE-FIRED at `k = 3` — a cup·cap closes a loop.**  `matchingOfSpineList` on the full
adjoint-quadruple cup-then-cap spine: the cup allocates two connected wires, the cap consumes exactly them, detecting
a closed loop — one loop, no open wires.  The end-to-end `k = 3` engine fire (allocate + connect + close).  `rfl`. -/
theorem quadEngineCupCapClosesLoop :
    matchingOfSpineList 0 [quadCupAtomBase, quadCapAtomBase]
      = { bottomCount := 0, topCount := 0, partner := [], loops := 1 } := rfl

/-- ★ **The signature-polymorphic LOCATE fires at `k = 3`.**  `locateAdjacentCupCapSplit` finds the adjacent cup-then-
cap pair in a genuine `k = 3` spine (`isSome = true`) — the `{signature : ModeSignature}`-polymorphic locate runs
unmodified on the adjoint-quadruple signature.  `rfl`. -/
theorem quadLocateFiresOnCupThenCap :
    (locateAdjacentCupCapSplit [quadCupAtomBase, quadCapAtomBase]).isSome = true := rfl

/-- ★ **The LOCATE declines (negative control) at `k = 3`.**  On a cup-then-cup spine there is no adjacent cup·cap
pair, so `locateAdjacentCupCapSplit` returns `none` (`isSome = false`) — the locate is not vacuously firing.  `rfl`. -/
theorem quadLocateDeclinesOnCupThenCup :
    (locateAdjacentCupCapSplit [quadCupAtomBase, quadCupAtomBase]).isSome = false := rfl

/-! ## Road markers -/

/-- **★ ESTABLISHED — the cup-restricted COD atom-pin reroute is shipped (FC-4 r2).**  The refuted dom→cod pin
(`stringTwoCell_codPack_uniqueOfDom`) is REPLACED at `k ≥ 3` by the cup-restricted COD pin
(`stringQuadTwoCell_domPack_uniqueOfCod_forCups`, "among cups, cod determines the (dom, cell) pack") plus the cap DOM
dual (`stringQuadTwoCell_codPack_uniqueOfDom_forCaps`), with the refutation itself pinned by the `η1`/`η3` witness
(`quad_dom_does_not_determine_cod`, marked never proved).  The reroute is wide-truth-probed over the census carrier at
`k = 3` AND `k = 4` (cup cods / cap doms pairwise distinct, cross-disjoint; the collapse witness for the refuted DOM
direction) before any universal — the LIVE-TREE / graveyard discipline discharged.  `= true`. -/
def fxString_hasQuadrupleAtomPinReroute : Bool := true

/-- **★ ESTABLISHED — the colour-blind connectivity engine is MACHINE-FIRED at `k = 3`.**  The census marker
`fxString_hasKGenericConnectivityEngine` was DOCUMENTED (signature-polymorphism, no `k = 3` instance); this NEW marker
records the machine fire: `matchingOfSpineList` run on genuine adjoint-quadruple spines (`quadEngineCupFires` — two top
ports matched `[1,0]`; `quadEngineCupCapClosesLoop` — a cup·cap closing one loop) and the `{signature}`-polymorphic
LOCATE firing / declining on `k = 3` spines (`quadLocateFiresOnCupThenCap` / `quadLocateDeclinesOnCupThenCup`).  The
soft shipped census marker is left byte-intact; this fired marker is the machine-checked upgrade.  `= true`. -/
def fxString_hasKGenericConnectivityEngineFired : Bool := true

end FX1Poly.Polygraph
