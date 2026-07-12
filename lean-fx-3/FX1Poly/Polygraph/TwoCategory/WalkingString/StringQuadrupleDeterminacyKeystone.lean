import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleAtomPinReroute
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineAtomWordPin

/-! # WalkingString — the `k = 3` DETERMINACY KEYSTONE: the dual arity-keyed atom pin, re-founded past the refuted
dom→cod node (FC-4 r3, brick K1 + K2)

The shipped `k = 2` determinacy keystone (`stringSpineAtom_eq_of_wordReadOffs`, `StringSpineAtomWordPin`) pins a spine
atom from its DOMAIN boundary word by two `composePath_splitPackEqOfPrefixLengthEq` peels, then reads the generator
(hence its cod) off the dom by `stringTwoCell_codPack_uniqueOfDom` ("dom determines the (cod, cell) pack").  At the
adjoint QUADRUPLE (`k = 3`, `L1 ⊣ L2 ⊣ L3 ⊣ L4`, `StringQuadrupleSeed`) that final node is REFUTED: the units `η1`
(dom `nil`, cod `L1·L2`) and `η3` (dom `nil`, cod `L3·L4`) share dom `nil` at `base→base` but differ in cod
(`quad_dom_does_not_determine_cod`, `StringQuadrupleAtomPinReroute`).  So the `k = 2` keystone body does NOT port —
the FROZEN r2 file already pinned the refutation and shipped the two RESTRICTED replacement pins.

## The dual keystone (the graveyard obeyed, both pins consumed)

The `base→base`/`tip→tip` mode-partition asymmetry (two cups collide on dom `nil`, two caps collide on cod `nil`)
means neither word alone determines a generator — but cup cods are pairwise-distinct ascending pairs and cap doms are
pairwise-distinct descending pairs.  So the honest keystone is the arity-keyed DUAL PAIR, each half consuming exactly
the one r2 restricted pin that survives at `k ≥ 3`:

  * ★★ `stringQuadCapSpineAtom_eq_of_domWordReadOffs` — the CAP keystone.  Byte-mirror of the `k = 2` keystone: two
    `composePath_splitPackEqOfPrefixLengthEq` peels off the shared DOM word, then the generator is read off its dom by
    the CAP-restricted pin `stringQuadTwoCell_codPack_uniqueOfDom_forCaps` (needs `generatorCod.length = 0`).  The
    dom→cod direction survives among caps because cap doms are distinct.
  * ★★ `stringQuadCupSpineAtom_eq_of_codWordReadOffs` — the CUP keystone (the exact DUAL).  Two peels off the shared
    COD word, then the generator is read off its cod by the CUP-restricted pin
    `stringQuadTwoCell_domPack_uniqueOfCod_forCups` (needs `generatorDom.length = 0`), which pins the (dom, cell) pack
    at once — so the dom is pinned by the SAME pack step, no length-zero uniqueness lemma is needed.

The unrestricted `stringQuadTwoCell_codPack_uniqueOfDom` (dom→cod, refuted by `η1`/`η3`) is NEVER proved here — both
keystones route strictly through r2's restricted pins.  The subsingleton `stringQuadTwoCell_unique_of_wordBoundaries`
(parallel `k = 3` generators are equal, the `4 → 6`-generator generalization of the shipped `k = 2`
`stringTwoCell_unique_of_wordBoundaries`) is shipped alongside as the base structural fact.

## The genuinely-reachable consumers (K2), fired fresh at `k = 3` on `L4`-carrying fixtures

Two of the `k = 2` keystone's atom-level consumers become genuinely reachable at `k = 3` through the dual keystone:

  * `stringQuadCapAtom_eq_of_sharedDom_sameWindow` (the cap identify/LOCATE step) — supplies `generatorDom.length = 2`,
    the arity bridge `quadCapCodZero_ofDomTwo` derives `generatorCod.length = 0`, and the cap keystone concludes.
  * `stringQuadCupAtom_eq_of_sharedCod_sameWindow` (the width-`0` last-cup peel) — supplies `generatorDom.length = 0`
    DIRECTLY into the cup keystone.  It does NOT reuse the `k = 2` cod→dom adapter
    (`stringLastCupDomWord_eq_of_sharedCod_sameWindow`) — that adapter walks exactly the refuted direction; the cup
    keystone folds the surviving cod→(dom,cell) pack step in one shot.

Both keystones AND both consumers are fired fresh at `k = 3` on genuine `L4`-carrying fixtures (`η3` cod `L3·L4`,
index `[3, 4]`; `ε3` dom `L4·L3`, index `[4, 3]`; the fresh letter `L4` absent from the `k = 2` alphabet), with
NEGATIVE controls: distinct cups (`η1`/`η3`) sharing dom `nil` are distinguishable by their COD read-off (`[1,2]` vs
`[3,4]`) — the refuted dom-only direction, pinned as a genuine distinction at atom granularity — and dually distinct
caps (`ε1`/`ε3`) sharing cod `nil` are distinguishable by their DOM read-off (`[2,1]` vs `[4,3]`).

## What this file does NOT do (the honest round boundary — the census marker STAYS `false`)

The census marker `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) bundles the FULL determinacy /
width-`0` sort bill (its docstring: "that plus the `k = 3` seed and fresh `k = 3` sort fixtures is the r2+ determinacy
bill").  r3 lands the ATOM PIN (the dual keystone + the two atom-level consumers), NOT the base-case singleton block
(`stringWordChainedSingletonBlock_eq_of_readOffs`, a dom-word-only SORT brick that is refuted AS STATED at `k = 3`
because two whisker-identical cups `η1`/`η3` satisfy its dom-word hypotheses yet are unequal — it needs a COD
co-chain) nor the full width-`0` sort assembly.  So the census marker stays `false` HONESTLY, and this file records
the atom-pin delivery in a NEW marker `fxString_hasNColourAtomPinKeystone`; the base-case cod-co-chain + the full
width-`0` quad sort are the named r4 residual, and `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`)
stays `false` regardless.

ADDITIVE ONLY: no shipped WalkingString file is touched; the FROZEN `StringQuadrupleSeed` / `StringQuadrupleAtomPinReroute`
are consumed, never edited.  Raw Lean 4 + Init; the subsingleton and arity bridge are `cases` with automatic
index-clash / concrete-`decide` discharge, the two keystones are the shipped `k = 2` two-split-pack derivation with the
final node swapped for the surviving restricted pin, the fixtures / negative controls are `rfl` and
`congrArg quadIndexWord` to false `List Nat` equalities; `propext` / `Quot.sound` / `Classical` / `sorry` /
`native_decide` / `omega`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The subsingleton and the cap-arity bridge -/

/-- ★ **Parallel `k = 3` generators are equal.**  Two `StringQuadTwoCell` at the SAME dom and cod word are equal: the
six constructors (three units, three counits) sit at pairwise-incompatible (dom, cod) boundaries, so after casing the
first every off-diagonal second constructor is discarded by index unification (a `nil`-vs-`cons` clash on the dom or
cod word, or a `base`/`tip` mode clash).  The `4 → 6`-generator generalization of the shipped `k = 2`
`stringTwoCell_unique_of_wordBoundaries`; full-enum `cases`-`cases` (no wildcard), propext-clean. -/
theorem stringQuadTwoCell_unique_of_wordBoundaries
    {sourceMode targetMode : AdjointQuadrupleMode}
    {quadDom quadCod : ModalityPath adjointQuadrupleGraph sourceMode targetMode}
    (cellFirst cellSecond : StringQuadTwoCell quadDom quadCod) : cellFirst = cellSecond := by
  cases cellFirst <;> cases cellSecond <;> rfl

/-- ★ **The cap-arity bridge: a length-`2` dom forces a length-`0` cod.**  Among the six quadruple generators the
caps (`counitOne`/`counitTwo`/`counitThree`) are exactly the ones whose dom has length `2`, and each of those has cod
`nil` (length `0`); the three cups have dom `nil` (length `0`), so `domTwo` refutes them by a concrete `decide`.  This
converts the cap consumer's supplied dom arity into the `generatorCod.length = 0` the cap keystone consumes.  Full-enum
`cases` on a monomorphic `Nat` length — propext-clean. -/
theorem quadCapCodZero_ofDomTwo
    {sourceMode targetMode : AdjointQuadrupleMode}
    {quadDom quadCod : ModalityPath adjointQuadrupleGraph sourceMode targetMode}
    (generator : StringQuadTwoCell quadDom quadCod)
    (domTwo : quadDom.length = 2) : quadCod.length = 0 := by
  cases generator <;> first | rfl | exact absurd domTwo (by decide)

/-! ## The dual keystone — the CAP pin (dom-word read-off) -/

/-- ★★ **The `k = 3` CAP determinacy keystone.**  Two spine atoms firing at the SAME domain boundary WORD
(`leftContext · generatorDom · rightContext`) with equal left-context and generator-dom read-off LENGTHS, both CAPS
(`generatorCod.length = 0`), are EQUAL.  Byte-mirror of the shipped `k = 2` `stringSpineAtom_eq_of_wordReadOffs`: peel
the left context off the shared dom word by `composePath_splitPackEqOfPrefixLengthEq` (pins the left mid mode + left
context + the residual `generatorDom · rightContext`), then peel the generator dom off that residual (pins the right
mid mode + generator dom + right context), and read the generator (hence its cod) off the dom by the CAP-restricted pin
`stringQuadTwoCell_codPack_uniqueOfDom_forCaps` — the direction that survives at `k ≥ 3` because cap doms are distinct.
NO unrestricted `stringQuadTwoCell_codPack_uniqueOfDom` (refuted by `η1`/`η3`) is used. -/
theorem stringQuadCapSpineAtom_eq_of_domWordReadOffs
    {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget)
    (domBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (domLengthsEqual : atomFirst.generatorDom.length = atomSecond.generatorDom.length)
    (capCodZeroFirst : atomFirst.generatorCod.length = 0)
    (capCodZeroSecond : atomSecond.generatorCod.length = 0) :
    atomFirst = atomSecond := by
  obtain ⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, generatorCodFirst,
    generatorFirst, rightContextFirst⟩ := atomFirst
  obtain ⟨leftMidSecond, rightMidSecond, leftContextSecond, generatorDomSecond, generatorCodSecond,
    generatorSecond, rightContextSecond⟩ := atomSecond
  dsimp only at domBoundaryWordsEqual leftLengthsEqual domLengthsEqual capCodZeroFirst capCodZeroSecond
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    leftContextFirst (composePath generatorDomFirst rightContextFirst)
    leftContextSecond (composePath generatorDomSecond rightContextSecond)
    domBoundaryWordsEqual leftLengthsEqual
  have leftMidEqual : leftMidFirst = leftMidSecond := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _leftFstEqual innerLeftPack
  injection innerLeftPack with leftContextEqual suffixesEqual
  subst leftContextEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    generatorDomFirst rightContextFirst generatorDomSecond rightContextSecond
    suffixesEqual domLengthsEqual
  have rightMidEqual : rightMidFirst = rightMidSecond := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with generatorDomEqual rightContextEqual
  subst generatorDomEqual
  subst rightContextEqual
  exact congrArg
    (fun pack =>
      (⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, pack.fst, pack.snd,
          rightContextFirst⟩ :
        SpineAtom adjointQuadrupleModeSignature overallSource overallTarget))
    (stringQuadTwoCell_codPack_uniqueOfDom_forCaps generatorFirst generatorSecond
      capCodZeroFirst capCodZeroSecond)

/-! ## The dual keystone — the CUP pin (cod-word read-off) -/

/-- ★★ **The `k = 3` CUP determinacy keystone (the DUAL).**  Two spine atoms firing at the SAME codomain boundary WORD
(`leftContext · generatorCod · rightContext`) with equal left-context and generator-cod read-off LENGTHS, both CUPS
(`generatorDom.length = 0`), are EQUAL.  The exact dual of the cap keystone: peel the left context off the shared COD
word, then the generator cod off the residual, and read the generator AND its dom off the cod by the CUP-restricted
pin `stringQuadTwoCell_domPack_uniqueOfCod_forCups` — which pins the (dom, cell) pack in one step, so the length-`0`
dom is fixed by that same pack, with NO auxiliary length-zero-path uniqueness lemma.  The cod→(dom,cell) direction
survives at `k ≥ 3` because cup cods are distinct.  NO unrestricted dom→cod pin is used. -/
theorem stringQuadCupSpineAtom_eq_of_codWordReadOffs
    {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget)
    (codBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (codLengthsEqual : atomFirst.generatorCod.length = atomSecond.generatorCod.length)
    (cupDomZeroFirst : atomFirst.generatorDom.length = 0)
    (cupDomZeroSecond : atomSecond.generatorDom.length = 0) :
    atomFirst = atomSecond := by
  obtain ⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, generatorCodFirst,
    generatorFirst, rightContextFirst⟩ := atomFirst
  obtain ⟨leftMidSecond, rightMidSecond, leftContextSecond, generatorDomSecond, generatorCodSecond,
    generatorSecond, rightContextSecond⟩ := atomSecond
  dsimp only at codBoundaryWordsEqual leftLengthsEqual codLengthsEqual cupDomZeroFirst cupDomZeroSecond
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    leftContextFirst (composePath generatorCodFirst rightContextFirst)
    leftContextSecond (composePath generatorCodSecond rightContextSecond)
    codBoundaryWordsEqual leftLengthsEqual
  have leftMidEqual : leftMidFirst = leftMidSecond := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _leftFstEqual innerLeftPack
  injection innerLeftPack with leftContextEqual codSuffixesEqual
  subst leftContextEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    generatorCodFirst rightContextFirst generatorCodSecond rightContextSecond
    codSuffixesEqual codLengthsEqual
  have rightMidEqual : rightMidFirst = rightMidSecond := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with generatorCodEqual rightContextEqual
  subst generatorCodEqual
  subst rightContextEqual
  exact congrArg
    (fun pack =>
      (⟨leftMidFirst, rightMidFirst, leftContextFirst, pack.fst, generatorCodFirst, pack.snd,
          rightContextFirst⟩ :
        SpineAtom adjointQuadrupleModeSignature overallSource overallTarget))
    (stringQuadTwoCell_domPack_uniqueOfCod_forCups generatorFirst generatorSecond
      cupDomZeroFirst cupDomZeroSecond)

/-! ## The genuinely-reachable consumers (K2) -/

/-- ★★ **The `k = 3` cap word pin (shared DOM, NO adapter) — consumer C2.**  Two CAP spine atoms firing at the SAME
domain boundary WORD with equal windows (left-context lengths) are EQUAL.  Both being caps (dom length `2`), the
generator-dom read-off lengths agree, and the cap-arity bridge `quadCapCodZero_ofDomTwo` supplies the length-`0` cod
each side needs, so the cap keystone `stringQuadCapSpineAtom_eq_of_domWordReadOffs` applies DIRECTLY — the `k = 3`
re-founding of the shipped `k = 2` `stringCapAtom_eq_of_sharedDom_sameWindow`, colour-AWARE, over the quadruple
signature. -/
theorem stringQuadCapAtom_eq_of_sharedDom_sameWindow
    {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    (capFirst capSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget)
    (domBoundaryWordsEqual :
      composePath capFirst.leftContext (composePath capFirst.generatorDom capFirst.rightContext)
        = composePath capSecond.leftContext
            (composePath capSecond.generatorDom capSecond.rightContext))
    (windowEqual : capFirst.leftContext.length = capSecond.leftContext.length)
    (capDomFirst : capFirst.generatorDom.length = 2)
    (capDomSecond : capSecond.generatorDom.length = 2) :
    capFirst = capSecond :=
  stringQuadCapSpineAtom_eq_of_domWordReadOffs capFirst capSecond domBoundaryWordsEqual windowEqual
    (capDomFirst.trans capDomSecond.symm)
    (quadCapCodZero_ofDomTwo capFirst.generator capDomFirst)
    (quadCapCodZero_ofDomTwo capSecond.generator capDomSecond)

/-- ★★ **The `k = 3` shared-top last-cup pin (shared COD) — consumer C3, DIRECT (no cod→dom adapter).**  Two width-`0`
CUP spine atoms sharing a COD boundary word, firing at the same window with equal cod read-off length, are EQUAL: the
dom lengths are `0` DIRECTLY, so the cup keystone `stringQuadCupSpineAtom_eq_of_codWordReadOffs` concludes.  This is the
`k = 3` re-founding of the shipped `k = 2` `stringSpineAtom_eq_of_sharedCod_sameWindow`, but it does NOT thread the
`k = 2` cod→dom adapter `stringLastCupDomWord_eq_of_sharedCod_sameWindow` — that adapter reconstructs the dom word from
the cod word, exactly the direction refuted at `k ≥ 3`; the cup keystone reads the cod straight to the (dom, cell)
pack. -/
theorem stringQuadCupAtom_eq_of_sharedCod_sameWindow
    {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    (cupFirst cupSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget)
    (codBoundaryWordsEqual :
      composePath cupFirst.leftContext (composePath cupFirst.generatorCod cupFirst.rightContext)
        = composePath cupSecond.leftContext
            (composePath cupSecond.generatorCod cupSecond.rightContext))
    (windowEqual : cupFirst.leftContext.length = cupSecond.leftContext.length)
    (cupCodLengthsEqual : cupFirst.generatorCod.length = cupSecond.generatorCod.length)
    (cupDomZeroFirst : cupFirst.generatorDom.length = 0)
    (cupDomZeroSecond : cupSecond.generatorDom.length = 0) :
    cupFirst = cupSecond :=
  stringQuadCupSpineAtom_eq_of_codWordReadOffs cupFirst cupSecond codBoundaryWordsEqual windowEqual
    cupCodLengthsEqual cupDomZeroFirst cupDomZeroSecond

/-! ## The `k = 3` `L4`-carrying fixtures (fresh letter `L4`, index `4`) -/

/-- A fresh `k = 3` CUP atom carrying the new letter `L4`: the unit `η3` (dom `nil`, cod `L3·L4`, index `[3, 4]`) at
`base→base` with empty whiskering.  Its cod word contains index `4` (= `L4`), absent from the `k = 2` alphabet. -/
def quadCupAtomBaseFresh :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL3L4
  generator := StringQuadTwoCell.unitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- A fresh `k = 3` CAP atom carrying the new letter `L4`: the counit `ε3` (dom `L4·L3`, index `[4, 3]`, cod `nil`) at
`tip→tip` with empty whiskering.  Its dom word contains index `4` (= `L4`). -/
def quadCapAtomTipFresh :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.tip AdjointQuadrupleMode.tip where
  leftMidMode := AdjointQuadrupleMode.tip
  rightMidMode := AdjointQuadrupleMode.tip
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip
  generatorDom := quadL4L3
  generatorCod := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip
  generator := StringQuadTwoCell.counitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip

/-- A fresh `k = 3` CAP atom for the negative control: the counit `ε1` (dom `L2·L1`, index `[2, 1]`, cod `nil`) at
`tip→tip`.  Shares cod `nil` with `ε3` but has a DISTINCT dom word. -/
def quadCapAtomTipOne :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.tip AdjointQuadrupleMode.tip where
  leftMidMode := AdjointQuadrupleMode.tip
  rightMidMode := AdjointQuadrupleMode.tip
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip
  generatorDom := quadL2L1
  generatorCod := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip
  generator := StringQuadTwoCell.counitOne
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip

/-- Smoke: the fresh cup atom's cod word genuinely carries `L4` (index `4`) — its `quadIndexWord` is `[3, 4]`.  `rfl`. -/
theorem quadCupFreshCod_carriesL4 : quadIndexWord quadCupAtomBaseFresh.generatorCod = [3, 4] := rfl

/-- Smoke: the fresh cap atom's dom word genuinely carries `L4` (index `4`) — its `quadIndexWord` is `[4, 3]`.  `rfl`. -/
theorem quadCapFreshDom_carriesL4 : quadIndexWord quadCapAtomTipFresh.generatorDom = [4, 3] := rfl

/-! ## The keystones + consumers fired at `k = 3` on the `L4`-carrying fixtures -/

/-- ★ **The CUP keystone fires at `k = 3` on the fresh `L4`-carrying cup.**  A determinacy pin has no distinct-atom
witness — any pair satisfying the hypotheses is equal — so non-vacuity is exactly "the hypotheses are inhabited by a
real `L4`-carrying cup", confirmed here (shared cod word, equal window, equal cod length, dom length `0` all `rfl`). -/
theorem stringQuadCupKeystone_firesOnFreshL4Cup :
    quadCupAtomBaseFresh = quadCupAtomBaseFresh :=
  stringQuadCupSpineAtom_eq_of_codWordReadOffs quadCupAtomBaseFresh quadCupAtomBaseFresh
    rfl rfl rfl rfl rfl

/-- ★ **The CAP keystone fires at `k = 3` on the fresh `L4`-carrying cap.**  Non-vacuity by a real `L4`-carrying cap:
shared dom word, equal window, equal dom length, cod length `0` all `rfl`. -/
theorem stringQuadCapKeystone_firesOnFreshL4Cap :
    quadCapAtomTipFresh = quadCapAtomTipFresh :=
  stringQuadCapSpineAtom_eq_of_domWordReadOffs quadCapAtomTipFresh quadCapAtomTipFresh
    rfl rfl rfl rfl rfl

/-- ★ **Consumer C3 (cup shared-cod pin) fires at `k = 3` on the fresh `L4`-carrying cup.** -/
theorem stringQuadCupConsumer_firesOnFreshL4Cup :
    quadCupAtomBaseFresh = quadCupAtomBaseFresh :=
  stringQuadCupAtom_eq_of_sharedCod_sameWindow quadCupAtomBaseFresh quadCupAtomBaseFresh
    rfl rfl rfl rfl rfl

/-- ★ **Consumer C2 (cap shared-dom pin) fires at `k = 3` on the fresh `L4`-carrying cap.** -/
theorem stringQuadCapConsumer_firesOnFreshL4Cap :
    quadCapAtomTipFresh = quadCapAtomTipFresh :=
  stringQuadCapAtom_eq_of_sharedDom_sameWindow quadCapAtomTipFresh quadCapAtomTipFresh
    rfl rfl rfl rfl

/-! ## Negative controls — genuine distinguishability + the refuted directions pinned -/

/-- ★ **Negative control (cup): distinct cups sharing dom `nil` are distinguishable by their COD read-off.**  The unit
`η1` (cod `L1·L2`, index `[1, 2]`) and the fresh unit `η3` (cod `L3·L4`, index `[3, 4]`) as spine atoms are UNEQUAL —
were they equal, their cod words would agree, forcing `[1, 2] = [3, 4]` (false).  This is the exact refutation of the
dom→cod direction (both share dom `nil`) pinned at ATOM granularity: the keystone genuinely distinguishes them, and
must route through COD, not DOM. -/
theorem quadCupAtoms_distinctByCodReadOff :
    quadCupAtomBase ≠ quadCupAtomBaseFresh := by
  intro atomsEqual
  have codWordsEqual :
      quadIndexWord quadCupAtomBase.generatorCod = quadIndexWord quadCupAtomBaseFresh.generatorCod :=
    congrArg (fun atom => quadIndexWord atom.generatorCod) atomsEqual
  exact absurd codWordsEqual (by decide)

/-- ★ **The refuted dom-only direction, pinned: `η1` and `η3` share the same DOM boundary word (`nil`).**  Combined
with `quadCupAtoms_distinctByCodReadOff` (they are UNEQUAL atoms), this is the literal statement that the dom word does
NOT determine the atom at `k = 3` — the graveyard node the cup keystone steps around by reading the COD.  `rfl`. -/
theorem quadCupAtoms_shareDomWord :
    composePath quadCupAtomBase.leftContext
        (composePath quadCupAtomBase.generatorDom quadCupAtomBase.rightContext)
      = composePath quadCupAtomBaseFresh.leftContext
          (composePath quadCupAtomBaseFresh.generatorDom quadCupAtomBaseFresh.rightContext) := rfl

/-- ★ **Negative control (cap, dual): distinct caps sharing cod `nil` are distinguishable by their DOM read-off.**  The
counit `ε1` (dom `L2·L1`, index `[2, 1]`) and the fresh counit `ε3` (dom `L4·L3`, index `[4, 3]`) as spine atoms are
UNEQUAL — equality would force `[2, 1] = [4, 3]` (false).  The dual refutation (both share cod `nil`): the cap keystone
must route through DOM, not COD. -/
theorem quadCapAtoms_distinctByDomReadOff :
    quadCapAtomTipOne ≠ quadCapAtomTipFresh := by
  intro atomsEqual
  have domWordsEqual :
      quadIndexWord quadCapAtomTipOne.generatorDom = quadIndexWord quadCapAtomTipFresh.generatorDom :=
    congrArg (fun atom => quadIndexWord atom.generatorDom) atomsEqual
  exact absurd domWordsEqual (by decide)

/-- ★ **The refuted cod-only direction, pinned: `ε1` and `ε3` share the same COD boundary word (`nil`).**  Combined
with `quadCapAtoms_distinctByDomReadOff`, the cod word does NOT determine the cap at `k = 3` — the dual graveyard node
the cap keystone steps around by reading the DOM.  `rfl`. -/
theorem quadCapAtoms_shareCodWord :
    composePath quadCapAtomTipOne.leftContext
        (composePath quadCapAtomTipOne.generatorCod quadCapAtomTipOne.rightContext)
      = composePath quadCapAtomTipFresh.leftContext
          (composePath quadCapAtomTipFresh.generatorCod quadCapAtomTipFresh.rightContext) := rfl

/-! ## Road marker -/

/-- **★ ESTABLISHED — the `k = 3` atom-pin determinacy keystone is machine-checked (FC-4 r3, K1 + K2).**  The dual
arity-keyed keystone re-founds the atom pin past the refuted dom→cod node: `stringQuadCapSpineAtom_eq_of_domWordReadOffs`
(caps, DOM-word read-off, routed through `stringQuadTwoCell_codPack_uniqueOfDom_forCaps`) and
`stringQuadCupSpineAtom_eq_of_codWordReadOffs` (cups, COD-word read-off, routed through
`stringQuadTwoCell_domPack_uniqueOfCod_forCups`) — both consuming ONLY the FROZEN r2 restricted pins, never the
refuted unrestricted `stringQuadTwoCell_codPack_uniqueOfDom`.  The two atom-level consumers
`stringQuadCapAtom_eq_of_sharedDom_sameWindow` (C2) and `stringQuadCupAtom_eq_of_sharedCod_sameWindow` (C3, DIRECT, no
cod→dom adapter) are re-founded at `k = 3`, and both keystones + both consumers FIRE fresh on genuine `L4`-carrying
fixtures (`η3` cod `[3, 4]`, `ε3` dom `[4, 3]`) with negative controls (distinct cups distinguishable by COD, distinct
caps by DOM; the refuted dom-only / cod-only directions pinned).

  What this marker does NOT close: the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` — its bill bundles the full determinacy / width-`0` SORT (the
  base-case singleton block `stringWordChainedSingletonBlock_eq_of_readOffs`, a dom-word-only sort brick refuted AS
  STATED at `k = 3`, needing a COD co-chain; plus the full width-`0` sort assembly), the named r4 residual.
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false` regardless.  This marker records
  exactly the ATOM PIN landed at `k = 3`, honestly.  `= true`. -/
def fxString_hasNColourAtomPinKeystone : Bool := true

end FX1Poly.Polygraph
