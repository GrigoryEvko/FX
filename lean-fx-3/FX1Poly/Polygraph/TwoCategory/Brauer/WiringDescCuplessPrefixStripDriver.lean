import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupTotalDriver

/-! # BRAUER r46 — the CUPLESS-PREFIX STRIP driver: arrived+annihilated deep-tail closure, the loop-behind-prefix
honestly walled, both flip flags STAY false (the honest zero-flip)

r45 (`Brauer/WiringDescSingleCupTotalDriver.lean`) shipped `driveRegion` / `flatRegionDrive` — the recursive fuel-structural
total driver iterating `flatRegionDispatchDriven` and, on a jam, applying ONE `reduceLeadingDistantSlide` step and recursing
through the shipped `RegionCupOutcome.prepend`.  r45 pinned the exact wall: the reducer GENUINELY fires on the deep-tail
`[cupAt 2, crossingAt 4, crossingAt 1, capAt 9]` (`reduceLeadingDistantSlideFiresOnDeepTail`), but its residual
`crossingAt 2 :: cupAt 2 :: crossingAt 1 :: capAt 9` exposes a CUPLESS SETTLED-crossing prefix in front of the working
region, and the cup-head-requiring static dispatch cannot re-dispatch it — so `flatRegionDrive` on the deep-tail STAYS
honestly `none` (`flatRegionDriveDeepTailStaysNone`).  r45 named the reachability↔shape re-founding (strip the cupless
prefix, re-drive the working region, whisker back) as the missing ingredient.

This round ships, PURELY ADDITIVELY (a new sibling extending the shipped r29–r45 files by import, never mutating one):

  * ★★ **S1 — the STRIP/RE-DRIVE/WHISKER architecture (all three fates through the SHIPPED cupless-prefix prepends).**
    `whiskerNonLoopOutcome` case-splits a driven `RegionCupOutcome` and re-attaches a cupless prefix through the r42
    combinators: the ARRIVED fate whiskers via `prependCuplessPrefixArrived` (cap-freeness transparent to a cupless prefix,
    `cupIsCapFreeRight_prefixCupless`), the ANNIHILATED fate via `prependCuplessPrefixAnnihilated` (the strict `countAtoms`
    drop survives any prefix), and the LOOP fate returns `none` — the opaque `.loop` `isBubble` witness
    (`brauerDiagramOf bc result ≠ brauerDiagramOf bc []`) cannot be transported through a left-prepend (an arrived diagram
    is also `≠` empty), so no abstract loop-whisker exists.  The printed shape this mirrors is the block induction of the
    Temperley–Lieb Jones-form loop-freeness (Fokkink–Lickorish, arXiv:math/0405267 Prop A.3): isolate the last block, and
    "the previous blocks constitute a reduced word of Jones form … by the induction hypothesis" — our settled cupless
    prefix IS the previously-processed blocks whiskered back, and the permutation part factors to one side as the staircase
    `s'` of the Brauer normal form `s·t₁t₃…·s'` (Framization/deframization, arXiv:2405.10809).

  * ★★ **S2 — the deep-tail discharge: the r45 rfl counterexample now FIRES `some`.**  `driveRegionStripped` adds, on the
    DOUBLE-JAM non-cup-head branch (both `flatRegionDispatchDriven` and `reduceLeadingDistantSlide` decline and the head is
    not a cup), a single-atom cupless peel: strip the leading non-cup atom, re-drive the tail, and whisker the atom back
    through `whiskerNonLoopOutcome`.  Because `[atom] ++ rest` reduces to `atom :: rest` DEFINITIONALLY, the whisker lands
    the reindexed outcome with NO `Eq.rec` transport (the r45 `transportByRegionEq` is not needed).  The r45 deep-tail
    hostile `[cupAt 2, crossingAt 4, crossingAt 1, capAt 9]` now drives to a `some` ARRIVED outcome
    (`driveStrippedFiresOnDeepTail`), together with the cap-prefix, the pre-existing-cupless-prefix, and the
    snake-behind-prefix residuals of the recon census.

  * ★★ **S3/E6 — the TOTALITY THEOREM jams on the loop-behind-prefix; the honest ZERO-FLIP with the exact counterexample.**
    The two dispatch walls demand synthesis "over an ARBITRARY (single-cup) region", i.e. the totality
    `∀ word, cupCount word = 1 → (flatRegionDrive word).isSome = true` (r45 criterion).
    `driveStrippedTotalityRefutedByLoopBehindPrefix` machine-checks the exact UNMET criterion: the single-cup word
    `[cupAt 2, crossingAt 4, capAt 2, capAt 9]` has `cupCount = 1`, yet BOTH the shipped `flatRegionDrive` AND the new
    `flatRegionDriveStripped` return `none`.  The residual after the slide is `crossingAt 2 :: cupAt 2 :: capAt 2 :: capAt 9`;
    stripping `crossingAt 2` re-drives to the LOOP-with-suffix `[cupAt 2, capAt 2, capAt 9]`, whose `.loop` outcome
    `whiskerNonLoopOutcome` refuses to whisker (the loop-witness weakness).  So the totality is FALSE for both drivers and
    NEITHER flip flag flips — a genuine route / engine-lemma gap (the accumulator driver keeping the loop cup-cap-headed
    across nesting + the state-generic `stepCupCapClosesLoop : (processBrauer state [cupAt p, capAt p]).loops =
    state.loops + 1`), never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6; the fuel-sufficiency template is
    `repeat_matcher_terminates`, arXiv:2403.11919 Fig. 14, measure `|u| + k(u)`).

## The honest wall — S1+S2 SHIP additively; both flip flags STAY false; the NEXT wall named in-file (r47 + beyond)

`fxBrauer_hasCuplessPrefixStripArrivedAnnihilated = true` records the arrived+annihilated strip closure.
`fxBrauer_hasCuplessPrefixLoopWhisker = false` walls the loop-behind-prefix: the r47 flip gate is the loop-whisker
`prependCuplessPrefixLoop` built from the state-generic `stepCupCapClosesLoop` + `processBrauer_append` +
`processFoldLoopsNonDecreasing` (`.loops ≥ 1 ⇒ ≠ empty` via `Nat.not_succ_le_zero`) THREADED through an ACCUMULATOR driver
that keeps the loop cup-cap-headed across nesting; and beyond that the MULTI-CUP masters road (the outer `arcCountFuel`
fold over EVERY cup + the cap-side ∗-dual + the `DiagramType` driver).  Therefore `fxBrauer_hasRegionDriverTotalDispatch`
(owned r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY `false`, WALL A `fxBrauer_hasSingleCupPeelDischarged`
(a MULTI-CUP wall) STAYS `false`, and the five completeness / inner-descent masters STAY `false`.  Purely additive; no wall
flip is fabricated.

Raw Lean 4 + Init; STRUCTURAL recursion on the `Nat` fuel (no `termination_by` / `WellFounded.fix` — the r45 `driveRegion`
pattern); the single-atom cupless peel reindexes by DEFINITIONAL `[atom] ++ rest = atom :: rest` (no `Eq.rec`); no `omega`
/ `simp`-AC / `native_decide` / `propext` / `Quot.sound` / `Classical` / `Nat.succ_ne_zero`.  Per-declaration
`#assert_no_axioms` in the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — S1: the single-atom cupless witness + the three-fated prefix whisker -/

/-- ★ **A single non-cup atom is a cupless prefix.**  `hasNoCup [atom]` unfolds to `cond (isCupAtom atom) false (hasNoCup
[])`; with `isCupAtom atom = false` it is `hasNoCup [] = true`.  The one-atom instance of the r36 `hasNoCup`, used by the
driver's single-atom peel — propext-clean (`cond` reduces structurally). -/
theorem hasNoCup_singleton_of_not_cup (atom : BrauerAtom) (notCup : isCupAtom atom = false) :
    hasNoCup [atom] = true := by
  show cond (isCupAtom atom) false (hasNoCup ([] : List BrauerAtom)) = true
  rw [notCup]
  rfl

/-- ★★ **The three-fated cupless-prefix whisker — all three fates through the SHIPPED r42 prepends.**  Case-splits a driven
`RegionCupOutcome region` and re-attaches a cupless `prefixWord` in front of the region: the ARRIVED fate whiskers via
`prependCuplessPrefixArrived` (cap-freeness right of the cup is transparent to a cupless prefix), the ANNIHILATED fate via
`prependCuplessPrefixAnnihilated` (the strict `countAtoms` drop survives ANY prefix), and the LOOP fate honestly returns
`none` — the opaque `.loop` non-emptiness witness cannot be transported through a left-prepend (see the file header's
loop-witness-weakness note).  This is the strip half of the reachability↔shape re-founding, arrived+annihilated built,
loop honestly deferred. -/
def whiskerNonLoopOutcome (prefixWord : List BrauerAtom) (cupless : hasNoCup prefixWord = true)
    {region : List BrauerAtom} :
    RegionCupOutcome region → Option (RegionCupOutcome (prefixWord ++ region))
  | .arrivedFactored result conv capFreeRight =>
      some (prependCuplessPrefixArrived prefixWord region result cupless conv capFreeRight)
  | .annihilated result conv shrank =>
      some (prependCuplessPrefixAnnihilated prefixWord region result conv shrank)
  | .loop _ _ _ _ => none

/-- ★ **The whisker preserves the ARRIVED and ANNIHILATED fates and declines the LOOP fate, machine-checked by `rfl`.**  A
cupless `crossingAt 5` prefix whiskered onto a shipped straddle-arrival keeps the arrived fate; onto a shipped S1 snake
annihilation keeps the annihilated fate; onto a shipped loop-with-suffix outcome it is `none`.  Documents "all three
fates" of S1. -/
theorem whiskerNonLoopOutcomePreservesFate :
    Option.map RegionCupOutcome.fate
        (whiskerNonLoopOutcome [crossingAt 5]
          (hasNoCup_singleton_of_not_cup (crossingAt 5) (isCupAtom_crossingAt 5))
          (outcomeArrivedFactoredStraddle 0)) = some SingleCupFate.arrivedFate
      ∧ Option.map RegionCupOutcome.fate
          (whiskerNonLoopOutcome [crossingAt 5]
            (hasNoCup_singleton_of_not_cup (crossingAt 5) (isCupAtom_crossingAt 5))
            (outcomeAnnihilatedFactoredS1 3 [])) = some SingleCupFate.annihilatedFate
      ∧ (whiskerNonLoopOutcome [crossingAt 5]
          (hasNoCup_singleton_of_not_cup (crossingAt 5) (isCupAtom_crossingAt 5))
          (outcomeLoopWithSuffix 3 [])).isNone = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## B — S2: the strip-augmented recursive driver -/

/-- ★★ **THE CUPLESS-PREFIX STRIP DRIVER.**  The r45 `driveRegion` extended, on its final `none` branch, by a single-atom
cupless PEEL: when `flatRegionDispatchDriven` and `reduceLeadingDistantSlide` both decline and the head is NOT a cup, strip
the one non-cup head atom, re-drive the tail on the same decremented fuel, and whisker the atom back through
`whiskerNonLoopOutcome`.  Because `[atom] ++ rest` reduces to `atom :: rest` DEFINITIONALLY, the whisker's result index
lands on `word` with NO `Eq.rec` transport.  The slide branch still threads the shipped `RegionCupOutcome.prepend`.
STRUCTURAL on the `Nat` fuel — no `termination_by`, no `WellFounded.fix`; both recursive calls hand `fuel` (one less than
`fuel + 1`).  A word whose head IS a cup but which both the dispatch and the reducer decline (a loop-behind-prefix, a stuck
neighbour) is genuinely `none` — the honest deep-tail wall's residual shape. -/
def driveRegionStripped : Nat → (word : List BrauerAtom) → Option (RegionCupOutcome word)
  | 0, _ => none
  | fuel + 1, word =>
      match flatRegionDispatchDriven word with
      | some outcome => some outcome
      | none =>
          match reduceLeadingDistantSlide word with
          | some ⟨reducedWord, slideConv, lengthLe⟩ =>
              (driveRegionStripped fuel reducedWord).map (RegionCupOutcome.prepend slideConv lengthLe)
          | none =>
              match word with
              | [] => none
              | atom :: rest =>
                  match hcup : isCupAtom atom with
                  | true => none
                  | false =>
                      (driveRegionStripped fuel rest).bind
                        (whiskerNonLoopOutcome [atom] (hasNoCup_singleton_of_not_cup atom hcup))

/-- ★★ **THE FLAT STRIP DRIVE — the strip driver at the shipped `driverFuel`.**  Runs `driveRegionStripped` with the r45
probe-confirmed lex-pair `driverFuel word = countAtoms word + legLexFuel 2 word`, the sufficient budget for the local
descent through the slide + strip steps.  The total-function surface a future flip gate would prove `isSome` over every
single-cup region — jammed this round only by the loop-behind-prefix residual. -/
def flatRegionDriveStripped (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  driveRegionStripped (driverFuel word) word

/-! ## C — S2 fires: the deep-tail residuals now synthesise; the census regresses -/

/-- ★★ **THE DEEP-TAIL DISCHARGE — the r45 `none` residuals now FIRE `some`, machine-checked by `rfl`.**  The r45
counterexample `[cupAt 2, crossingAt 4, crossingAt 1, capAt 9]` (a settled crossing behind a distant crossing) now drives
to an ARRIVED outcome; the cap-prefix `[cupAt 2, capAt 5, crossingAt 1, capAt 9]`, the PRE-EXISTING cupless prefix
`[crossingAt 5, cupAt 2, crossingAt 4, capAt 9]` (both dispatch and reducer decline at the top; only the strip fires), and
the snake-behind-prefix `[cupAt 3, crossingAt 5, capAt 2, capAt 9]` (an annihilated fate) all synthesise through the
strip. -/
theorem driveStrippedFiresOnDeepTail :
    (flatRegionDriveStripped [cupAt 2, crossingAt 4, crossingAt 1, capAt 9]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 2, capAt 5, crossingAt 1, capAt 9]).isSome = true
      ∧ (flatRegionDriveStripped [crossingAt 5, cupAt 2, crossingAt 4, capAt 9]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 3, crossingAt 5, capAt 2, capAt 9]).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **The strip discharges the correct FATES — arrived for the settled-crossing deep-tail, annihilated for the
snake-behind-prefix — machine-checked by `rfl`.**  Confirms S1's two live fates thread the full driver: the deep-tail
`[cupAt 2, crossingAt 4, crossingAt 1, capAt 9]` arrives, the snake-behind-prefix `[cupAt 3, crossingAt 5, capAt 2, capAt
9]` annihilates. -/
theorem driveStrippedFates :
    Option.map RegionCupOutcome.fate
        (flatRegionDriveStripped [cupAt 2, crossingAt 4, crossingAt 1, capAt 9]) = some SingleCupFate.arrivedFate
      ∧ Option.map RegionCupOutcome.fate
          (flatRegionDriveStripped [cupAt 3, crossingAt 5, capAt 2, capAt 9]) = some SingleCupFate.annihilatedFate :=
  ⟨rfl, rfl⟩

/-- ★★ **The strip driver SUBSUMES the r45 census + the JAM-B loop-with-suffix, machine-checked by `rfl`.**  Every word the
r45 `driveRegionFiresOnCensus` / `flatRegionDriveFiresOnJamB` recorded as `isSome` still synthesises through the strip
driver — the strip branch only ever fires where the shipped `driveRegion` returned `none`, so the shipped coverage is
preserved verbatim. -/
theorem driveStrippedSubsumesCensus :
    (flatRegionDriveStripped [cupAt 0]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 0, crossingAt 0, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 0, crossingAt 1, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 7, crossingAt 9, capAt 11]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 0, capAt 5]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 2, crossingAt 0, capAt 9]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 2, capAt 2, capAt 9]).isSome = true
      ∧ (flatRegionDriveStripped [cupAt 0, capAt 0, crossingAt 3]).isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## D — S3/E6: the totality jams on the loop-behind-prefix; the honest counterexample -/

/-- ★★ **The loop-behind-a-cupless-prefix STAYS honestly `none` through the strip driver — the exact residual shape, `rfl`.**
On `[cupAt 2, crossingAt 4, capAt 2, capAt 9]` the reducer slides the cup past the distant `crossingAt 4`, leaving
`crossingAt 2 :: cupAt 2 :: capAt 2 :: capAt 9`; stripping `crossingAt 2` re-drives to the LOOP-with-suffix
`[cupAt 2, capAt 2, capAt 9]`, and `whiskerNonLoopOutcome` DECLINES the `.loop` fate (the opaque non-emptiness witness does
not transport through the left-prepend).  So the strip driver dead-ends `none` on the loop-behind-prefix — the precise
residual the r47 loop-whisker + accumulator driver must resolve. -/
theorem driveStrippedLoopBehindPrefixStaysNone :
    (flatRegionDriveStripped [cupAt 2, crossingAt 4, capAt 2, capAt 9]).isNone = true := rfl

/-- ★★ **THE TOTALITY REFUTATION — the exact UNMET flip criterion + counterexample, machine-checked by `rfl`.**  The flip
gate demands `∀ word, cupCount word = 1 → (flatRegionDrive word).isSome = true`.  The single-cup word
`[cupAt 2, crossingAt 4, capAt 2, capAt 9]` has `cupCount = 1`, yet BOTH the shipped r45 `flatRegionDrive` AND the new r46
`flatRegionDriveStripped` return `none`.  This is the literal counterexample that keeps the totality FALSE and BOTH flip
flags unflipped this round — the loop-behind-prefix residual, a route / engine-lemma gap (the r47 accumulator driver +
`stepCupCapClosesLoop`), never a truth gap. -/
theorem driveStrippedTotalityRefutedByLoopBehindPrefix :
    cupCount [cupAt 2, crossingAt 4, capAt 2, capAt 9] = 1
      ∧ (flatRegionDrive [cupAt 2, crossingAt 4, capAt 2, capAt 9]).isNone = true
      ∧ (flatRegionDriveStripped [cupAt 2, crossingAt 4, capAt 2, capAt 9]).isNone = true :=
  ⟨rfl, rfl, rfl⟩

/-- ★ **The out-of-scope arms stay `none` through the strip driver, machine-checked.**  A cupless region and a two-cup
region are correctly out of single-cup scope — the strip does not over-fire beyond its mandate (a cupless region strips to
the empty tail and dead-ends; a second cup is never reached because the first-cup dispatch owns the head). -/
theorem driveStrippedOutOfScopeStaysNone :
    (flatRegionDriveStripped ([crossingAt 9] : List BrauerAtom)).isNone = true
      ∧ (flatRegionDriveStripped [cupAt 0, cupAt 2]).isNone = true :=
  ⟨rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CUPLESS-PREFIX STRIP for the ARRIVED + ANNIHILATED fates SHIPS (S1 + S2).**  `whiskerNonLoopOutcome`
re-attaches a cupless prefix to a driven outcome through the shipped r42 `prependCuplessPrefixArrived` /
`prependCuplessPrefixAnnihilated` (`whiskerNonLoopOutcomePreservesFate`); `driveRegionStripped` adds the single-atom peel on
the double-jam non-cup-head branch (definitional reindex, no `Eq.rec`), turning the r45 deep-tail `none` residuals into
`some` outcomes (`driveStrippedFiresOnDeepTail` / `driveStrippedFates`) while subsuming the r45 census
(`driveStrippedSubsumesCensus`).  All zero-axiom, fuel-structural.  `= true`. -/
def fxBrauer_hasCuplessPrefixStripArrivedAnnihilated : Bool := true

/-- **Honesty WALL marker — the LOOP-behind-prefix whisker is NOT built; the totality jams, both flip flags STAY `false`.**
`whiskerNonLoopOutcome` declines the `.loop` fate (`driveStrippedLoopBehindPrefixStaysNone`), so the single-cup word
`[cupAt 2, crossingAt 4, capAt 2, capAt 9]` (`cupCount = 1`) drives to `none` under BOTH the shipped `flatRegionDrive` and
the new `flatRegionDriveStripped` (`driveStrippedTotalityRefutedByLoopBehindPrefix`) — the exact counterexample refuting the
totality `∀ word, cupCount word = 1 → (flatRegionDrive word).isSome = true`.  The r47 flip gate is the loop-whisker
`prependCuplessPrefixLoop` from the state-generic `stepCupCapClosesLoop : (processBrauer state [cupAt p, capAt p]).loops =
state.loops + 1` (via `processBrauer_append` + `processFoldLoopsNonDecreasing`, `.loops ≥ 1 ⇒ ≠ empty` by
`Nat.not_succ_le_zero`) threaded through an ACCUMULATOR driver that keeps the loop cup-cap-headed across nesting; and beyond
it the MULTI-CUP masters road (the outer `arcCountFuel` fold over EVERY cup + the cap-side ∗-dual + the `DiagramType`
driver).  So `fxBrauer_hasRegionDriverTotalDispatch` (owned r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY
`false`, WALL A `fxBrauer_hasSingleCupPeelDischarged` (a MULTI-CUP wall) STAYS `false`, and the five completeness /
inner-descent masters STAY `false`.  A route / engine-lemma gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).
`= false`. -/
def fxBrauer_hasCuplessPrefixLoopWhisker : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r46 cupless-prefix-strip-driver terminal state — MACHINE-CHECKED.**  The arrived+annihilated strip
SHIPS (`fxBrauer_hasCuplessPrefixStripArrivedAnnihilated = true`) on top of the r45 recursive total driver
(`fxBrauer_hasRecursiveTotalDriver = true`), while the loop-behind-prefix whisker stays unbuilt
(`fxBrauer_hasCuplessPrefixLoopWhisker = false`) and with it the r45 deep-tail reachability↔shape marker
(`fxBrauer_hasDeepTailReachabilityShape = false`).  So the two dispatch walls (`fxBrauer_hasRegionDriverTotalDispatch`,
owned r39; `fxBrauer_hasSingleCupTotalDecision`, owned r38), WALL A (`fxBrauer_hasSingleCupPeelDischarged`, a MULTI-CUP
wall), and the five completeness / inner-descent masters (`fxBrauer_hasSeamRungOuterAssembly`,
`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the kernel checks; purely additive, no wall
flip is fabricated — the honest zero-flip. -/
theorem fxBrauer_cuplessPrefixStripDriverTerminalState :
    fxBrauer_hasCuplessPrefixStripArrivedAnnihilated = true
      ∧ fxBrauer_hasRecursiveTotalDriver = true
      ∧ fxBrauer_hasCuplessPrefixLoopWhisker = false
      ∧ fxBrauer_hasDeepTailReachabilityShape = false
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
