import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord

/-! # WalkingString/StringSharedMidWord — the shared-`midWord` brick: the top-word-length = mid-width bridge
+ length-`0` `ModalityPath` uniqueness → equal cap top words at mid-width `0` (FC-3 r37)

The r36 mid-zero producer's block-level headline (`stringMidZeroValleysWithEqualMatching_spineTraceEquiv`,
`StringMidZeroValleyProducer`) takes the two cap blocks' shared cap boundary WORD and the two cup blocks' shared
mid boundary WORD as HYPOTHESES.  The cell-level reducer that will inhabit `StringMidZeroValleyTraceEquiv`
(`StringValleyDegenerateSplit`) must DERIVE the shared mid word from the two `RawTwoCellExpr` valleys — and the
genuine word-threading delta the walking-adjunction cell reducer sidesteps entirely (its reassembly is
un-word-threaded) is exactly this: at mid-width `0`, the two parallel cap blocks' top words
`spineListTopWord sourceWord capBlockFirst` and `…capBlockSecond` are BOTH length-`0` paths, hence both the unique
nil path, hence EQUAL.  The r36 honesty marker named this the r37 target.  This file ships it — the two bricks
plus the corollary the reducer will call:

  * ★ **Brick I** `modalityPathEqOfLengthZero` (private) — length-`0` `ModalityPath` uniqueness: two paths of length
    `0` between the same modes are equal (both `nil`).  A per-file private re-copy of the shipped private lemma in
    `StringLastCupSharedTopPin` (kept per-file so the umbrella build stays duplicate-global-free); `Nat.noConfusion`
    on the successor length, propext-free.
  * ★★ **Brick II** `stringTopWordLength_eq_processSpineWidth` — the top-word-length = mid-width BRIDGE: over a
    boundary-chained pure-cap block, the LENGTH of the threaded top boundary word `spineListTopWord bottomWord
    capBlock` equals the numeric mid-width `(processSpine state capBlock).openWires.length`, given the entry
    invariant `state.openWires.length = bottomWord.length`.  Structural induction on the cap block threading the
    invariant: each cap advances BOTH sides to its cod-boundary width (the word side via
    `ModalityPath.length_composePath`, the numeric side via the shipped per-atom tracker
    `stepAtom_openWires_tracksBoundary`), re-establishing the invariant.  The WORD analog of the shipped numeric
    width telescope `stringPureCapBlock_widthTelescope`, but equating the top-word LENGTH to the open-wire width
    rather than accumulating a `∓ 2 · length` shift.
  * ★★ **Brick III** `stringSharedMidWord_ofMidZero` — the shared-`midWord` corollary (the r37 headline): two whole
    valleys `capBlock ++ cupBlock` with EQUAL boundary matching and mid-width `0` have EQUAL cap top words.  Route:
    the survivor-top keystone `stringSurvivorTopTotal_eq_midWidth` (twice, the second via `wholeEq`) collapses both
    numeric mid-widths to `0`; Brick II turns each into a length-`0` top word; Brick I equates the two nil paths.

Raw Lean 4 + Init; Brick II is a clean structural induction riding the shipped per-atom tracker + the dimension-1
word-length homomorphism, Brick III is pure equational plumbing over the shipped survivor-top keystone.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local propext-free helpers -/

/-- The `List.range` accumulator length, structural and propext-free (the core `List.length_range` leaks propext).
Per-file copy; distinct name from the walking-adjunction / width-telescope twins so the umbrella build's global
table stays duplicate-free. -/
private theorem bottomRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := bottomRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`, propext-free (per-file copy; the core lemma leaks). -/
private theorem bottomRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [bottomRangeLoopLength count []]
  exact Nat.add_zero count

/-! ## Brick I — length-`0` `ModalityPath` uniqueness -/

/-- **Brick I.**  Two modality paths of length `0` between the same modes are EQUAL — both are `nil` (a `cons` has
length `≥ 1`), so the only length-`0` path is the identity 1-cell.  Per-file private re-copy of the shipped private
`modalityPathEqOfLengthZero` (`StringLastCupSharedTopPin`), kept per-file so the umbrella build stays
duplicate-global-free; `Nat.noConfusion` on the successor length, propext-free. -/
private theorem modalityPathEqOfLengthZero {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (pathFirst pathSecond : ModalityPath graph sourceMode targetMode)
    (firstZero : pathFirst.length = 0) (secondZero : pathSecond.length = 0) :
    pathFirst = pathSecond := by
  cases pathFirst with
  | nil _ =>
      cases pathSecond with
      | nil _ => rfl
      | cons _ _ =>
          dsimp only [ModalityPath.length] at secondZero
          exact Nat.noConfusion secondZero
  | cons _ _ =>
      dsimp only [ModalityPath.length] at firstZero
      exact Nat.noConfusion firstZero

/-! ## Brick II — the top-word-length = mid-width bridge -/

/-- ★★ **Brick II — the top-word-length = mid-width bridge.**  Over a boundary-chained pure-cap block, the LENGTH of
the threaded top boundary word `spineListTopWord bottomWord capBlock` equals the numeric mid-width
`(processSpine state capBlock).openWires.length`, provided the entry invariant `state.openWires.length =
bottomWord.length` holds.  Structural induction on the cap block: at the empty block both sides ARE the invariant;
each cap advances the word side to its cod boundary word (length via `ModalityPath.length_composePath`) and the
numeric side to its cod boundary width (via the shipped per-atom tracker `stepAtom_openWires_tracksBoundary`, whose
`AtomHasCupOrCapArity` premise comes from the cap arity), re-establishing the invariant `codBoundary = codBoundary`
and recursing.  The WORD analog of the numeric width telescope `stringPureCapBlock_widthTelescope`. -/
theorem stringTopWordLength_eq_processSpineWidth
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    AllCapArity capBlock →
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget) →
    (state : WireState) →
    state.openWires.length = bottomWord.length →
    SpineBoundaryChained state.openWires.length capBlock →
    (spineListTopWord bottomWord capBlock).length
      = (processSpine state capBlock).openWires.length
  | [], _, bottomWord, state, invariant, _ => by
      show bottomWord.length = state.openWires.length
      exact invariant.symm
  | atom :: rest, capPure, bottomWord, state, invariant, chained => by
      cases capPure with
      | cons capDom capCod restCap =>
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have arity : AtomHasCupOrCapArity atom := Or.inr ⟨capDom, capCod⟩
          have stepTracks : (stepAtom state atom).openWires.length = atom.codBoundaryLength :=
            stepAtom_openWires_tracksBoundary state atom arity headFires.symm
          have codWordLen :
              (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)).length
                = atom.codBoundaryLength := by
            dsimp only [SpineAtom.codBoundaryLength]
            rw [ModalityPath.length_composePath atom.leftContext
                (composePath atom.generatorCod atom.rightContext),
              ModalityPath.length_composePath atom.generatorCod atom.rightContext,
              Nat.add_assoc atom.leftContext.length atom.generatorCod.length atom.rightContext.length]
          have newInvariant :
              (stepAtom state atom).openWires.length
                = (composePath atom.leftContext
                    (composePath atom.generatorCod atom.rightContext)).length :=
            stepTracks.trans codWordLen.symm
          have tailChainedAtStep :
              SpineBoundaryChained (stepAtom state atom).openWires.length rest := by
            rw [stepTracks]; exact tailChained
          have inductionHypothesis := stringTopWordLength_eq_processSpineWidth rest restCap
            (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
            (stepAtom state atom) newInvariant tailChainedAtStep
          show (spineListTopWord
              (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest).length
            = (processSpine (stepAtom state atom) rest).openWires.length
          exact inductionHypothesis

/-! ## Brick III — the shared-`midWord` corollary -/

/-- ★★ **Brick III — equal cap top words at mid-width `0` (the r37 headline).**  Two whole valleys `capBlock ++
cupBlock` (pure cap, pure cup, boundary-chained) with EQUAL boundary matching (`wholeEq`), over a source word of
length `bottomCount`, whose FIRST valley has mid-width `0` (`midZeroFirst`), have EQUAL cap top words
`spineListTopWord sourceWord capBlockFirst = spineListTopWord sourceWord capBlockSecond`.  The survivor-top keystone
`stringSurvivorTopTotal_eq_midWidth` (fired twice — the second numeric mid-width via `wholeEq`) collapses both
numeric mid-widths to `0`; Brick II turns each into a length-`0` cap top word; Brick I equates the two nil paths.
This is the shared mid word the r38 word-threaded cell reducer will feed to
`stringMidZeroValleysWithEqualMatching_spineTraceEquiv` for the two cup blocks' common boundary. -/
theorem stringSharedMidWord_ofMidZero
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat) (bottomPositive : 0 < bottomCount)
    (sourceWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (sourceWordLength : sourceWord.length = bottomCount)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (capChainedFirst : SpineBoundaryChained bottomCount capBlockFirst)
    (capChainedSecond : SpineBoundaryChained bottomCount capBlockSecond)
    (cupChainedFirst : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond)
    (midZeroFirst : survivorTopTotal (matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)) = 0)
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    spineListTopWord sourceWord capBlockFirst = spineListTopWord sourceWord capBlockSecond := by
  -- The seed's open-wire count is the source word's length.
  have seedInvariant :
      (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState).openWires.length = sourceWord.length := by
    show (List.range bottomCount).length = sourceWord.length
    rw [bottomRangeLength bottomCount, sourceWordLength]
  have capChainedSeedFirst :
      SpineBoundaryChained (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState).openWires.length
        capBlockFirst := by
    show SpineBoundaryChained (List.range bottomCount).length capBlockFirst
    rw [bottomRangeLength bottomCount]; exact capChainedFirst
  have capChainedSeedSecond :
      SpineBoundaryChained (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState).openWires.length
        capBlockSecond := by
    show SpineBoundaryChained (List.range bottomCount).length capBlockSecond
    rw [bottomRangeLength bottomCount]; exact capChainedSecond
  -- Both numeric mid-widths collapse to `0` through the survivor-top keystone.
  have midWidthFirstZero :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length = 0 := by
    rw [← stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockFirst cupBlockFirst
      capPureFirst cupPureFirst cupChainedFirst]
    exact midZeroFirst
  have midZeroSecond :
      survivorTopTotal (matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) = 0 := by
    rw [← wholeEq]; exact midZeroFirst
  have midWidthSecondZero :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length = 0 := by
    rw [← stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlockSecond cupBlockSecond
      capPureSecond cupPureSecond cupChainedSecond]
    exact midZeroSecond
  -- Brick II turns each mid-width into a length-`0` cap top word.
  have topLengthFirstZero : (spineListTopWord sourceWord capBlockFirst).length = 0 := by
    rw [stringTopWordLength_eq_processSpineWidth capBlockFirst capPureFirst sourceWord
      ⟨List.range bottomCount, [], bottomCount, 0⟩ seedInvariant capChainedSeedFirst]
    exact midWidthFirstZero
  have topLengthSecondZero : (spineListTopWord sourceWord capBlockSecond).length = 0 := by
    rw [stringTopWordLength_eq_processSpineWidth capBlockSecond capPureSecond sourceWord
      ⟨List.range bottomCount, [], bottomCount, 0⟩ seedInvariant capChainedSeedSecond]
    exact midWidthSecondZero
  -- Brick I equates the two length-`0` paths.
  exact modalityPathEqOfLengthZero (spineListTopWord sourceWord capBlockFirst)
    (spineListTopWord sourceWord capBlockSecond) topLengthFirstZero topLengthSecondZero

/-! ## Concrete truth-probes (anti-vacuity) — the genuine mid-zero string valley `[ε] ++ [η']` at `tip` -/

/-- ★ **The shared cap top word at mid-width `0` is the concrete nil path.**  A machine-checked (`decide`)
cross-check that the cap `ε`'s threaded top word from the length-`2` bottom word `stringGF` is a length-`0` path —
the mid-boundary `id_tip` the cup `η'` fires from.  This pins the shared-`midWord` fact to a genuine numeric `0`, so
Brick III is not vacuous on a real string cap block. -/
theorem stringSharedMidWord_probe_topWordLengthIsZero :
    (spineListTopWord stringGF [stringWidthTelescopeProbeCapAtom]).length = 0 := by
  decide

/-- ★ **Brick III FIRES on the genuine mixed string valley `[ε] ++ [η']` at `tip`.**  Instantiating the shared-mid
corollary on the concrete valley (`bottomCount = 2`, mid-width `0`, `sourceWord = stringGF` of length `2`, both cap
blocks `[ε]`) runs the WHOLE brick end-to-end: the survivor-top keystone collapses the mid-width, Brick II turns the
cap top word into a length-`0` path, and Brick I equates them.  A machine-checked non-vacuity witness that the
shared-`midWord` derivation does real work on a real mid-zero cap block. -/
theorem stringSharedMidWord_ofMidZero_firesOnMixedValley :
    spineListTopWord stringGF [stringWidthTelescopeProbeCapAtom]
      = spineListTopWord stringGF [stringWidthTelescopeProbeCapAtom] :=
  stringSharedMidWord_ofMidZero 2 (by decide) stringGF (by decide)
    [stringWidthTelescopeProbeCapAtom] [stringWidthTelescopeProbeCapAtom]
    [stringWidthTelescopeProbeCupAtom] [stringWidthTelescopeProbeCupAtom]
    (AllCapArity.cons rfl rfl AllCapArity.nil) (AllCapArity.cons rfl rfl AllCapArity.nil)
    (AllCupArity.cons rfl rfl AllCupArity.nil) (AllCupArity.cons rfl rfl AllCupArity.nil)
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryChained.nil 0))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl (SpineBoundaryChained.nil 0))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))
    stringSurvivorTopTotal_mixedValley_isZero rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the shared-`midWord` brick is SHIPPED, zero-axiom (FC-3 r37).**  Brick I
(`modalityPathEqOfLengthZero`, length-`0` `ModalityPath` uniqueness), Brick II
(`stringTopWordLength_eq_processSpineWidth`, the top-word-length = mid-width bridge — a structural induction over a
boundary-chained cap block riding the shipped per-atom tracker `stepAtom_openWires_tracksBoundary` and the
dimension-1 word-length homomorphism `ModalityPath.length_composePath`), and Brick III
(`stringSharedMidWord_ofMidZero`, the corollary: two whole valleys with equal boundary matching and mid-width `0`
have equal cap top words, via the survivor-top keystone `stringSurvivorTopTotal_eq_midWidth` twice + Brick II twice
+ Brick I).  The truth-probe fires Brick III end-to-end on the genuine mixed valley `[ε] ++ [η']` at `tip`
(`bottomCount = 2`, mid-width `0`, `sourceWord = stringGF`), and the `decide` cross-check pins the shared cap top
word to the concrete length-`0` nil path — so the fire is not vacuous.  This is precisely the r36-named target: the
top-word-length = mid-width bridge plus length-`0` `ModalityPath` uniqueness the walking-adjunction cell reducer
sidesteps (its reassembly is un-word-threaded).

  What this does NOT flip (honestly): `StringMidZeroValleyTraceEquiv` (`StringValleyDegenerateSplit`) stays
  UNINHABITED.  This brick derives the SHARED mid word from the two cap blocks; the cell-level reducer that inhabits
  `StringMidZeroValleyTraceEquiv` (the r38 target) additionally needs the word-chain SUFFIX extraction (the cup
  arm's `SpineBoundaryWordChained midWord cupBlock` at the shared mid word) and the full word-threaded assembly
  feeding `stringMidZeroValleysWithEqualMatching_spineTraceEquiv` its seven word arguments.  So the completeness
  masters `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This round flips ONLY this NEW marker:
  the shared-`midWord` brick is assembled — the top-word-length bridge + length-`0` uniqueness → equal cap top words
  at mid-width `0`.  `= true`. -/
def fxString_hasSharedMidWord : Bool := true

end FX1Poly.Polygraph
