import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleDeterminacyKeystone
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord

/-! # WalkingString — the `k = 3` SINGLETON-BLOCK `(dom, cod)` READ-OFF-PAIR brick, past the refuted dom-word-only
sort node (FC-4 r4, brick B1 + the ported width-0 links fired at `k = 3`)

The shipped `k = 2` sort's base-case singleton block `stringWordChainedSingletonBlock_eq_of_readOffs`
(`StringCapBlockGodementStep`) equates two singleton spines `[atomFirst] = [atomSecond]` from a DOM-WORD-only chain
(`SpineBoundaryWordChained`) plus left-context / generator-dom length matches, feeding the `k = 2` keystone
`stringSpineAtom_eq_of_wordReadOffs` — which reads the generator off the DOM by `stringTwoCell_codPack_uniqueOfDom`
("dom determines cod").  That final node is REFUTED at the adjoint QUADRUPLE (`k = 3`): the units `η1` (dom `nil`, cod
`L1·L2`, index `[1, 2]`) and `η3` (dom `nil`, cod `L3·L4`, index `[3, 4]`) both satisfy the dom-word-only singleton
hypotheses (same DOM word `nil`, same window, same dom length) yet are UNEQUAL cups — so the dom-word-only singleton
block is refuted AS STATED at `k = 3` and needs a COD co-chain.

## The honest re-founding: the `(dom, cod)` READ-OFF PAIR

The dual of the DOM boundary-word chain is NOT a new inductive — it is the shipped `{signature}`-generic FUNCTION
`spineListTopWord` (`StringSpineTopWord`): `spineListTopWord bottomWord [atom]` reduces to the atom's COD boundary word
`leftContext · generatorCod · rightContext`.  Feeding a `topWordEq : spineListTopWord bottomWord [atomFirst] =
spineListTopWord bottomWord [atomSecond]` supplies exactly the shared-COD hypothesis the cup pin needs — mirroring the
plumbing the shipped `k = 2` width-`0` sort already uses (its atom pin is COD-driven, not dom-word-only).  So the
honest `k = 3` singleton block reads BOTH boundary words off the pair:

  * ★★ `stringQuadChainedSingletonBlock_eq_of_readOffPair` — from the two DOM chains (`SpineBoundaryWordChained`) plus
    `topWordEq` (the COD co-chain) plus the three read-off lengths (left context, generator dom, generator cod), the
    two singletons are equal.  A THIN dispatcher over the FROZEN r3 dual keystone: it cases the atom arity through the
    standalone helper `quadAtomDomLenZeroOrTwo` (avoiding the free-variable trap of casing a `.length` hypothesis after
    destructuring the atom), routes CUPS (dom length `0`) through the cod-word consumer
    `stringQuadCupAtom_eq_of_sharedCod_sameWindow` (C3) and CAPS (dom length `2`) through the dom-word consumer
    `stringQuadCapAtom_eq_of_sharedDom_sameWindow` (C2), and lifts the atom equality to the singleton list by
    `congrArg`.  Every hard part (atom determinacy from either side, arity gates) is the r3 keystone; r4 supplies the
    `(dom, cod)`-pair packaging + the arity dispatch.

## The ported width-`0` links, fired at `k = 3` (brick B2, the ported/plugged steps)

The two `{signature}`-generic carriers the sort threads BOTH port to the quadruple seed unchanged and are fired here:

  * `SpineBoundaryWordChained` (the DOM chain) — the `L4`-carrying fixtures `quadCupAtomBaseFresh` / `quadCapAtomTipFresh`
    build genuine `k = 3` dom chains (`quadCupAtomBaseFresh_domChained`, `quadCapAtomTipFresh_domChained`);
  * `spineListTopWord` (the COD co-chain carrier) — reduces on `k = 3` singletons to the atom's cod index word
    (`quadSingletonTopWord_computesCupCod` = `[3, 4]` for `η3`, carrying the fresh `L4`;
    `quadSingletonTopWord_computesCapCod` = `[]` for the cap `ε3`).

The atom pins C2 / C3 are the shipped FROZEN r3 keystone; the fueled width-`0` cup SORT DRIVER
(`stringMatchingPureCupSpineSortFueled` and its LOCATE / drop-injectivity / last-cup short-chord / valley reducer
descent, ~3200 lines hardcoded to the adjoint-TRIPLE signature) is the honestly-NAMED r5+ residual — NOT attempted
here.  So the census marker stays `false` (below).

## Fires + negative controls (the HONESTY LAW: `k = 3` claims on genuine `L4` fixtures)

The brick FIRES on the fresh `L4`-carrying cup `η3` (cod `[3, 4]`, cup arm) and cap `ε3` (dom `[4, 3]`, cap arm).  The
NEGATIVE control is the pin the graveyard demands: the `η1` / `η3` pair satisfies the dom-word-only singleton
hypotheses (both dom-chained at `nil`, equal window, equal dom length) yet the singletons are UNEQUAL — the dom-only
`k = 2` statement is refuted at `k = 3` (`quadDomOnlySingletonBlock_refutedAtThree`) — while their COD co-chain words
genuinely DIFFER (`[1, 2] ≠ [3, 4]`, `quadCupSingletonTopWords_differ`), so the honest brick's `topWordEq` is
unsatisfiable for the pair and it correctly does NOT equate them.

The shipped `k = 2` adjoint-TRIPLE word problem is fully decided (`fxString_hasAdjointTripleCompleteness = true`,
`StringMatchingCompleteness`); this file is the disjoint `k = 3` atom-granularity floor of the width-`0` sort, not a
statement about the triple.

ADDITIVE ONLY: no shipped WalkingString file is touched; the FROZEN `StringQuadrupleSeed` /
`StringQuadrupleAtomPinReroute` / `StringQuadrupleDeterminacyKeystone` are consumed, never edited.  Raw Lean 4 + Init;
the arity helper is a full-enum `cases` on the six generators with concrete-length `rfl`, the brick is
`obtain`/`cases`/`congrArg`, the fixtures / fires are `SpineBoundaryWordChained.cons _ rfl` and `rfl`, the negative
controls are `injection` + `congrArg quadIndexWord` to a false `List Nat` equality by `decide`;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The arity helper — a quadruple generator's dom is length `0` (cup) or length `2` (cap) -/

/-- ★ **A quadruple generator's dom word has length `0` (cup) or `2` (cap).**  The three units (`unitOne`/`unitTwo`/
`unitThree`) have dom `nil` (length `0`); the three counits (`counitOne`/`counitTwo`/`counitThree`) have a length-`2`
dom (`quadL2L1`/`quadL3L2`/`quadL4L3`).  Full-enum `cases` on the six generators, each arm a concrete-length `rfl` —
propext-clean.  Standalone (not `cases` on a `.length` hypothesis after destructuring an atom) so the brick's arity
dispatch dodges the free-variable trap. -/
theorem quadAtomDomLenZeroOrTwo
    {sourceMode targetMode : AdjointQuadrupleMode}
    {quadDom quadCod : ModalityPath adjointQuadrupleGraph sourceMode targetMode}
    (generator : StringQuadTwoCell quadDom quadCod) :
    quadDom.length = 0 ∨ quadDom.length = 2 := by
  cases generator <;> first | exact Or.inl rfl | exact Or.inr rfl

/-! ## The brick — the `k = 3` `(dom, cod)` read-off-pair singleton block -/

/-- ★★ **The `k = 3` singleton-block `(dom, cod)` read-off-pair brick.**  Two singleton spines `[atomFirst]` /
`[atomSecond]` that (i) DOM-chain from the same bottom boundary word (`SpineBoundaryWordChained bottomWord [·]`), (ii)
COD-co-chain equally (`spineListTopWord bottomWord [atomFirst] = spineListTopWord bottomWord [atomSecond]`, i.e. their
cod boundary words agree), and (iii) read off equal left-context / generator-dom / generator-cod lengths, are EQUAL
singletons.  The `(dom, cod)`-pair re-founding of the dom-word-only `stringWordChainedSingletonBlock_eq_of_readOffs`,
refuted AS STATED at `k = 3`.  Proof: the DOM chains' cons inversion (`spineBoundaryWordChained_tail`) gives the shared
DOM boundary word; `topWordEq` reduces (`spineListTopWord`) to the shared COD boundary word; the standalone arity
helper `quadAtomDomLenZeroOrTwo` dispatches — cups (dom length `0`) through the cod-word consumer C3
(`stringQuadCupAtom_eq_of_sharedCod_sameWindow`), caps (dom length `2`) through the dom-word consumer C2
(`stringQuadCapAtom_eq_of_sharedDom_sameWindow`) — and the atom equality lifts to the singleton by `congrArg`.  Routes
strictly through the FROZEN r2/r3 restricted pins; the refuted unrestricted dom→cod pin is NEVER used. -/
theorem stringQuadChainedSingletonBlock_eq_of_readOffPair
    {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    {bottomWord : ModalityPath adjointQuadrupleGraph overallSource overallTarget}
    {atomFirst atomSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget}
    (domChainedFirst : SpineBoundaryWordChained bottomWord [atomFirst])
    (domChainedSecond : SpineBoundaryWordChained bottomWord [atomSecond])
    (topWordEq : spineListTopWord bottomWord [atomFirst] = spineListTopWord bottomWord [atomSecond])
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (domLengthsEqual : atomFirst.generatorDom.length = atomSecond.generatorDom.length)
    (codLengthsEqual : atomFirst.generatorCod.length = atomSecond.generatorCod.length) :
    [atomFirst] = [atomSecond] := by
  obtain ⟨firstDomFires, _firstTailChained⟩ := spineBoundaryWordChained_tail domChainedFirst
  obtain ⟨secondDomFires, _secondTailChained⟩ := spineBoundaryWordChained_tail domChainedSecond
  have domBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext) :=
    firstDomFires.symm.trans secondDomFires
  have codBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext) := by
    dsimp only [spineListTopWord] at topWordEq
    exact topWordEq
  cases quadAtomDomLenZeroOrTwo atomFirst.generator with
  | inl firstDomZero =>
      have secondDomZero : atomSecond.generatorDom.length = 0 := domLengthsEqual.symm.trans firstDomZero
      exact congrArg (fun atom => [atom])
        (stringQuadCupAtom_eq_of_sharedCod_sameWindow atomFirst atomSecond codBoundaryWordsEqual
          leftLengthsEqual codLengthsEqual firstDomZero secondDomZero)
  | inr firstDomTwo =>
      have secondDomTwo : atomSecond.generatorDom.length = 2 := domLengthsEqual.symm.trans firstDomTwo
      exact congrArg (fun atom => [atom])
        (stringQuadCapAtom_eq_of_sharedDom_sameWindow atomFirst atomSecond domBoundaryWordsEqual
          leftLengthsEqual firstDomTwo secondDomTwo)

/-! ## The ported width-`0` links fired at `k = 3` — the DOM chain -/

/-- The `k = 3` cup `η1` (dom `nil`, contexts `nil`) DOM-chains from the empty boundary word.  `SpineBoundaryWordChained`
ports to the quadruple seed unchanged; `headFires` is `rfl` because the cup's dom boundary word `nil · nil · nil`
reduces to `nil`. -/
theorem quadCupAtomBase_domChained :
    SpineBoundaryWordChained
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBase] :=
  SpineBoundaryWordChained.cons quadCupAtomBase rfl (SpineBoundaryWordChained.nil _)

/-- The fresh `L4`-carrying `k = 3` cup `η3` (dom `nil`, cod `L3·L4`) DOM-chains from the empty boundary word. -/
theorem quadCupAtomBaseFresh_domChained :
    SpineBoundaryWordChained
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBaseFresh] :=
  SpineBoundaryWordChained.cons quadCupAtomBaseFresh rfl (SpineBoundaryWordChained.nil _)

/-- The fresh `L4`-carrying `k = 3` cap `ε3` (dom `L4·L3`, cod `nil`) DOM-chains from its dom word `L4·L3`. -/
theorem quadCapAtomTipFresh_domChained :
    SpineBoundaryWordChained quadL4L3 [quadCapAtomTipFresh] :=
  SpineBoundaryWordChained.cons quadCapAtomTipFresh rfl (SpineBoundaryWordChained.nil _)

/-! ## The ported width-`0` links fired at `k = 3` — the COD co-chain carrier -/

/-- The COD co-chain carrier `spineListTopWord` reduces on the fresh `L4`-carrying cup singleton to the cup's cod index
word `[3, 4]` (carrying the fresh letter `L4`).  The dual-of-the-DOM-chain carrier ports to `k = 3` unchanged.  `rfl`. -/
theorem quadSingletonTopWord_computesCupCod :
    quadIndexWord
        (spineListTopWord
          (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBaseFresh])
      = [3, 4] := rfl

/-- The COD co-chain carrier reduces on the fresh `L4`-carrying cap singleton to the cap's cod index word `[]` (the cap
cod is `nil`).  `rfl`. -/
theorem quadSingletonTopWord_computesCapCod :
    quadIndexWord (spineListTopWord quadL4L3 [quadCapAtomTipFresh]) = [] := rfl

/-! ## The brick fired at `k = 3` on genuine `L4`-carrying fixtures -/

/-- ★ **The brick FIRES at `k = 3` on the fresh `L4`-carrying cup (cup arm, through C3).**  A determinacy brick has no
distinct-atom witness, so non-vacuity is exactly "the hypotheses are inhabited by a real `L4`-carrying cup": the two
DOM chains, the COD co-chain (`rfl`), and the three read-off lengths (`rfl`) all hold for `η3` (cod `[3, 4]`), and the
brick concludes `[η3] = [η3]`. -/
theorem stringQuadSingletonBlock_firesOnFreshL4Cup :
    ([quadCupAtomBaseFresh] :
        List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base))
      = [quadCupAtomBaseFresh] :=
  stringQuadChainedSingletonBlock_eq_of_readOffPair
    quadCupAtomBaseFresh_domChained quadCupAtomBaseFresh_domChained rfl rfl rfl rfl

/-- ★ **The brick FIRES at `k = 3` on the fresh `L4`-carrying cap (cap arm, through C2).**  Non-vacuity by a real
`L4`-carrying cap `ε3` (dom `[4, 3]`): the two DOM chains from `L4·L3`, the COD co-chain (`rfl`), and the three read-off
lengths (`rfl`) hold, and the brick concludes `[ε3] = [ε3]` through the cap arm. -/
theorem stringQuadSingletonBlock_firesOnFreshL4Cap :
    ([quadCapAtomTipFresh] :
        List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.tip AdjointQuadrupleMode.tip))
      = [quadCapAtomTipFresh] :=
  stringQuadChainedSingletonBlock_eq_of_readOffPair
    quadCapAtomTipFresh_domChained quadCapAtomTipFresh_domChained rfl rfl rfl rfl

/-! ## Negative controls — the dom-only singleton block refuted at `k = 3`, the COD co-chain distinguishing -/

/-- ★ **The dom-word-only singleton block is REFUTED AS STATED at `k = 3`.**  The unit `η1` (cod `[1, 2]`) and the
fresh unit `η3` (cod `[3, 4]`) BOTH satisfy the dom-word-only singleton hypotheses — both DOM-chain from `nil`, with
equal left-context length and equal generator-dom length — yet the singletons `[η1]` and `[η3]` are UNEQUAL (equal
singletons would force `η1 = η3`, whose cod read-offs `[1, 2]` and `[3, 4]` disagree, refuted by
`quadCupAtoms_distinctByCodReadOff`).  So no dom-word-only rule can decide the `k = 3` singleton block; the honest brick
requires the COD co-chain.  Pinned, never proved as a universal. -/
theorem quadDomOnlySingletonBlock_refutedAtThree :
    SpineBoundaryWordChained
        (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBase]
      ∧ SpineBoundaryWordChained
          (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBaseFresh]
      ∧ quadCupAtomBase.leftContext.length = quadCupAtomBaseFresh.leftContext.length
      ∧ quadCupAtomBase.generatorDom.length = quadCupAtomBaseFresh.generatorDom.length
      ∧ ([quadCupAtomBase] :
            List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base))
          ≠ [quadCupAtomBaseFresh] := by
  refine ⟨quadCupAtomBase_domChained, quadCupAtomBaseFresh_domChained, rfl, rfl, ?_⟩
  intro singletonsEqual
  injection singletonsEqual with headEqual _tailEqual
  exact quadCupAtoms_distinctByCodReadOff headEqual

/-- ★ **The COD co-chain distinguishes the `η1` / `η3` pair the dom-only rule cannot.**  `spineListTopWord` on the two
cup singletons yields their cod index words `[1, 2]` (`η1`) and `[3, 4]` (`η3`), which DIFFER — so the honest brick's
`topWordEq` hypothesis is unsatisfiable for the pair, and the brick correctly declines to equate them.  `decide`. -/
theorem quadCupSingletonTopWords_differ :
    quadIndexWord
        (spineListTopWord
          (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBase])
      ≠ quadIndexWord
          (spineListTopWord
            (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBaseFresh]) := by
  decide

/-! ## Road marker -/

/-- **★ ESTABLISHED — the `k = 3` singleton-block `(dom, cod)` read-off-pair brick is machine-checked (FC-4 r4, B1).**
`stringQuadChainedSingletonBlock_eq_of_readOffPair` re-founds the dom-word-only singleton block past its refuted `k = 3`
node by threading the COD co-chain (the shipped `{signature}`-generic `spineListTopWord`) alongside the DOM chain
(`SpineBoundaryWordChained`) and casing the atom arity (`quadAtomDomLenZeroOrTwo`) through the FROZEN r3 dual keystone —
cups through C3 (`stringQuadCupAtom_eq_of_sharedCod_sameWindow`), caps through C2
(`stringQuadCapAtom_eq_of_sharedDom_sameWindow`).  Both ported width-`0` carriers fire at `k = 3` (the DOM chain on the
`L4` fixtures, `spineListTopWord` computing `[3, 4]` / `[]`), the brick fires on the fresh `L4`-carrying cup `η3` and
cap `ε3`, and the negative control pins the refutation (`quadDomOnlySingletonBlock_refutedAtThree`: the `η1`/`η3` pair
satisfies the dom-only hypotheses yet is unequal; `quadCupSingletonTopWords_differ`: their COD words distinguish them).

  What this marker does NOT close: the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` — its bill bundles the FULL width-`0` quad SORT, and r4 lands only its
  base-case singleton block (this brick), NOT the fueled cup-sort driver (`stringMatchingPureCupSpineSortFueled` + its
  LOCATE / drop-injectivity / last-cup short-chord / valley-reducer descent, ~3200 lines hardcoded to the
  adjoint-triple signature), the honestly-named r5+ residual.  The shipped `k = 2` adjoint-triple completeness
  (`fxString_hasAdjointTripleCompleteness = true`, `StringMatchingCompleteness`) is a separate, already-decided problem.
  This marker records exactly the base-case singleton block landed at `k = 3`, honestly.  `= true`. -/
def fxString_hasNColourSingletonBlockCoChainBrick : Bool := true

end FX1Poly.Polygraph
