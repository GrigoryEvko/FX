import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionDescent
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDisorder

/-! # WalkingString — the STAIRCASE DRIVER: the redex LOCATOR + the descent STEP, and the PINNING WALL (FC-7)

FC-3/FC-3b read off the termination measure `lex(generatorCount, size, commutePotential)` and machine-checked every
mode's structural-weight descent + the `commutePotential` combinatorics (`StringFussCatalanStaircase`,
`StringFussCatalanPotential`); FC-6 (`StringMatchingReconstructionInterface` / `…Descent`) reduced the whole
adjoint-triple completeness + decision to ONE interface obligation per route (`StringFcNormalizer` = `normalize` +
`convToNormalize` + `matchingInjectiveOnNormalForms`) and shipped the per-mode CONV descent kit.  The single missing
piece was the redex-locating DRIVER (`fxString_hasStaircaseDriver`): the scan that CHOOSES which mode to fire and
WHERE, and the terminating fold that sequences the shipped steps.

This file ships the FIRST HALF of that driver — the LOCATOR and the descent STEP — and then SURFACES, with a
machine-checked witness, the exact design gap that walls the SECOND half (the fold + the matching-injectivity):

## P1 — the spine-tag LOCATOR (`locateStringStaircaseRedex`), sound and complete

  * `locateAdjacentCupThenCap` — a STRUCTURAL scan (no `decide`, a fold over the spine tags) returning the position
    of the FIRST adjacent `cup`-then-`cap` (the snake / straighten redex), reusing the shipped cup/cap tag
    `SpineAtom.isCupAtom`.  `locateStringStaircaseRedex cell` runs it on `cell.spine`.
  * `IsStaircaseNormal cell` — the spine-tag NORMAL predicate: the spine is a `cap`-block-then-`cup`-block valley
    (`isCapThenCupValley`, the shipped valley predicate).  `Decidable` (a `Bool = true`).
  * ★ `stringStaircaseLocate_none_iff_normal` — SOUNDNESS + COMPLETENESS in one iff: `locate cell = none ↔
    IsStaircaseNormal cell`.  So `locate = none` EXACTLY on normal cells, and any `locate = some k` exposes a genuine
    adjacent-cup-then-cap redex (`stringStaircaseLocate_some_exposesRedex`, via the shipped
    `hasAdjacentCupThenCap_of_not_valley`).

## P2 — the descent STEP (`stringStaircaseSwap`), strictly measure-decreasing

  * `stringStaircaseSwap cell` — fire the located redex at the tag level (the shipped `swapFirstCupCap`).
  * ★ `stringStaircaseStep_dropsDisorder` — firing on a non-normal cell strictly DROPS the spine disorder
    (`spineDisorder`, the inversion count of the cup/cap tags), the shipped strictly-decreasing measure
    (`swapFirstCupCap_disorder_lt`).  The cell-level lex tuple `lex(generatorCount, size, commutePotential)` descents
    for the four modes are the SHIPPED `stringLexDescent_cancelF` / `_extend` / `_commute` (Potential.lean); this ties
    the LOCATOR to those descents through the fuel-structural `valleyDescentDriver` already proven terminating +
    valley-correct in `WalkingAdjunction/SpineValleyDisorder`.

## P3 — STOP: the PINNING WALL (the honest FC-2 canonical-form finding, machine-witnessed)

The driver is HALTED before the fold + the matching-injectivity, for a REAL reason, not a failure — the FC-2
canonical form is UNDERDETERMINED for the injectivity leg the normalizer needs.  Two obstructions, one PROVEN:

  1. ★ **EXTEND-invisibility — the spine-tag normal form is NOT matching-determined (PROVEN).**
     `matchingOf` reads ONLY the spine (`matchingOf = matchingOfSpineList sourcePath.length cell.spine`), and so does
     `IsStaircaseNormal` — but the spine does NOT determine the raw term: `id`-slots (EXTEND) are spine-INVISIBLE
     (`spineDiff … .id _ rest = rest`), whisker-splits and vcomp-nesting collapse.  Witness
     (`stringStaircaseNormalForm_not_matchingDetermined`): `id_G` and `id_G ⊟ id_G` are BOTH `IsStaircaseNormal`
     (empty spine), have EQUAL `matchingOf`, yet are DISTINCT raw terms.  So `StringFcNormalizer`'s
     `matchingInjectiveOnNormalForms` (`matchingOf (nf A) = matchingOf (nf B) → nf A = nf B`) CANNOT be met by any
     normalizer landing in the spine-tag valleys: it must pin a canonical RAW representative per spine.
  2. ★ **Cross-colour interleave pinning — no total colour order is sound (design-lock #2 + Cartier–Foata).**
     Pinning the raw representative means sorting cross-colour disjoint blocks to `commutePotential = 0` against a
     canonical colour-key order.  But `fxString_hasNormalFormDesignLock` §2 forbids a GLOBAL colour order (reducing
     all colour-1 then all colour-2 REORDERS arcs across the shared middle `G` and VIOLATES planarity), while
     `commutePotential = countInversions` (naive `Nat` `<` of the colour-key word) IMPOSES exactly such a global
     order — so the third-coordinate measure over-counts the shared-`G`-adjacent pairs that do NOT commute.  This is
     the classical Cartier–Foata gap (a commutation normal form is unique ONLY once a total order on independent
     letters is fixed) specialized to a PLANARITY-constrained order that is not a total colour order — the
     spine-atom → colour-key binding + the window-disjointness gating are UNDEFINED, exactly the FC-3c driver
     `StringFussCatalanPotential` / `StringFussCatalanStaircase` wall.

Hence the fold + `matchingInjectiveOnNormalForms` cannot be closed this round; `fxString_hasStaircaseDriver`,
`fxString_hasStaircaseFoldFromPotential` (Potential/Staircase), and `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) STAY `false`, honestly.  The frontier moved from "no locator" to "sound+complete
locator + strictly-decreasing descent step shipped; fold + injectivity walled by a MACHINE-WITNESSED pinning gap".

Raw Lean 4 + Init; the scan is a full-enum structural fold (no wildcard), the iff a 3-case structural induction, the
step a one-line reuse of the shipped disorder drop, the witness `rfl`/soundness/`noConfusion`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The reduction-mode census (documentation of the four FC modes at the spine level) -/

/-- ★ The **FC staircase reduction-mode census** — the moves the straightening driver fires, tagged by their effect
on the lex measure `lex(generatorCount, size, commutePotential)`.  CANCEL (four colours) is the substantive snake
collapse (coord-1 drop, `stringCancelSnake*`); EXTEND absorbs a reducible `id` slot (coord-2 drop,
`stringExtendByIdentity`) — spine-INVISIBLE, see the P3 wall; COMMUTE / INTERLEAVE transpose a disjoint pair
(coord-3 drop, `stringCommuteDisjoint` / `stringInterleaveCrossColour`).  At the pure spine-tag level only the
cup-then-cap ADJACENCY is visible; the colour classification is the walled FC-3c binding. -/
inductive StringStaircaseRedexMode where
  /-- A snake collapse of colour 1 (`F`) — `stringCancelSnakeF`, drops `generatorCount`. -/
  | cancelF
  /-- A snake collapse of colour 1 on the shared `G` (`stringCancelSnakeGlo`). -/
  | cancelGlo
  /-- A snake collapse of colour 2 on the shared `G` (`stringCancelSnakeGhi`). -/
  | cancelGhi
  /-- A snake collapse of colour 2 (`H`) — `stringCancelSnakeH`. -/
  | cancelH
  /-- Absorb a reducible `id` slot — `stringExtendByIdentity`, drops `size`; spine-invisible. -/
  | extend
  /-- Transpose a disjoint (same- or cross-colour) pair — `stringCommuteDisjoint` / `stringInterleaveCrossColour`,
  drops `commutePotential`. -/
  | commute
deriving DecidableEq

/-! ## P1 — the spine-tag locator -/

/-- ★ **The adjacent-cup-then-cap LOCATOR (structural).**  Scan a tag word left to right and return the position of
the FIRST place a `cup` (`isCup = true`) is immediately followed by a `cap` (`isCup = false`) — the snake / straighten
redex.  A full four-way enumeration of the two head tags (NO wildcard, so the recursor is `propext`-clean); structural
recursion on the tail `secondCell :: rest`. -/
def locateAdjacentCupThenCap {α : Type u} (isCup : α → Bool) : List α → Option Nat
  | [] => none
  | [_single] => none
  | firstCell :: secondCell :: rest =>
      match isCup firstCell with
      | false => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)
      | true =>
          match isCup secondCell with
          | false => some 0
          | true => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)

/-- ★ **The FC staircase redex locator.**  Run `locateAdjacentCupThenCap` on the cell's cup/cap-tagged spine —
returns the position of the first snake redex, or `none` when the spine is already a valley (normal). -/
def locateStringStaircaseRedex {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) : Option Nat :=
  locateAdjacentCupThenCap SpineAtom.isCupAtom cell.spine

/-- ★ **The spine-tag STAIRCASE-NORMAL predicate.**  A cell is staircase-normal when its cup/cap-tagged spine is a
`cap`-block-then-`cup`-block valley (`isCapThenCupValley`) — no adjacent cup-then-cap snake redex remains.  This is
the SPINE-tag normal form; it is NOT the matching-determined FC canonical raw term (see the P3 wall). -/
def IsStaircaseNormal {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) : Prop :=
  isCapThenCupValley SpineAtom.isCupAtom cell.spine = true

/-- Staircase-normality is decidable — a `Bool = true`. -/
instance instDecidableIsStaircaseNormal {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (IsStaircaseNormal cell) :=
  inferInstanceAs (Decidable (isCapThenCupValley SpineAtom.isCupAtom cell.spine = true))

/-! ## P1 — soundness + completeness of the locator (the `none ↔ valley` bridge) -/

/-- A mapped option is `none` only when the source is `none`. -/
private theorem optionMapEqNone {α : Type u} {β : Type u} (f : α → β) {opt : Option α}
    (mappedNone : opt.map f = none) : opt = none := by
  cases opt with
  | none => rfl
  | some value => nomatch mappedNone

/-- Locator reduction on a `cap`-headed cons-cons word: the outer match takes the `false` arm. -/
private theorem locateAdjacentCupThenCap_capHead {α : Type u} (isCup : α → Bool)
    (firstCell secondCell : α) (rest : List α) (isCapFirst : isCup firstCell = false) :
    locateAdjacentCupThenCap isCup (firstCell :: secondCell :: rest)
      = (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1) := by
  show (match isCup firstCell with
        | false => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)
        | true =>
            match isCup secondCell with
            | false => some 0
            | true => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1))
      = (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)
  rw [isCapFirst]

/-- Locator reduction on a `cup`-then-`cap` cons-cons word: the redex is at position `0`. -/
private theorem locateAdjacentCupThenCap_cupThenCap {α : Type u} (isCup : α → Bool)
    (firstCell secondCell : α) (rest : List α) (isCupFirst : isCup firstCell = true)
    (isCapSecond : isCup secondCell = false) :
    locateAdjacentCupThenCap isCup (firstCell :: secondCell :: rest) = some 0 := by
  show (match isCup firstCell with
        | false => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)
        | true =>
            match isCup secondCell with
            | false => some 0
            | true => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1))
      = some 0
  rw [isCupFirst, isCapSecond]

/-- Locator reduction on a `cup`-then-`cup` cons-cons word: the inner match takes the `true` arm. -/
private theorem locateAdjacentCupThenCap_cupThenCup {α : Type u} (isCup : α → Bool)
    (firstCell secondCell : α) (rest : List α) (isCupFirst : isCup firstCell = true)
    (isCupSecond : isCup secondCell = true) :
    locateAdjacentCupThenCap isCup (firstCell :: secondCell :: rest)
      = (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1) := by
  show (match isCup firstCell with
        | false => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)
        | true =>
            match isCup secondCell with
            | false => some 0
            | true => (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1))
      = (locateAdjacentCupThenCap isCup (secondCell :: rest)).map (· + 1)
  rw [isCupFirst, isCupSecond]

/-- ★ **`locate = none ⟹ normal` (COMPLETENESS).**  If the scan finds no adjacent cup-then-cap, the tag word is a
`cap`-then-`cup` valley.  Structural induction on the tail; the head-tag cases mirror the locator's enumeration. -/
theorem locateAdjacentCupThenCap_none_imp_valley {α : Type u} (isCup : α → Bool) :
    ∀ {tags : List α}, locateAdjacentCupThenCap isCup tags = none → isCapThenCupValley isCup tags = true
  | [], _ => rfl
  | [single], _ => by
      show (match isCup single with | true => allCups isCup [] | false => isCapThenCupValley isCup []) = true
      cases isCup single <;> rfl
  | firstCell :: secondCell :: rest, locNone => by
      rw [isCapThenCupValley_cons_cons]
      cases hFirst : isCup firstCell with
      | false =>
          rw [locateAdjacentCupThenCap_capHead isCup firstCell secondCell rest hFirst] at locNone
          have recNone := optionMapEqNone _ locNone
          exact locateAdjacentCupThenCap_none_imp_valley isCup recNone
      | true =>
          cases hSecond : isCup secondCell with
          | false =>
              rw [locateAdjacentCupThenCap_cupThenCap isCup firstCell secondCell rest hFirst hSecond] at locNone
              nomatch locNone
          | true =>
              rw [locateAdjacentCupThenCap_cupThenCup isCup firstCell secondCell rest hFirst hSecond] at locNone
              have recNone := optionMapEqNone _ locNone
              have valleyTail := locateAdjacentCupThenCap_none_imp_valley isCup recNone
              show allCups isCup (secondCell :: rest) = true
              show (isCup secondCell && allCups isCup rest) = true
              rw [hSecond, Bool.true_and]
              have step : (match isCup secondCell with
                    | true => allCups isCup rest
                    | false => isCapThenCupValley isCup rest) = true := valleyTail
              rw [hSecond] at step
              exact step

/-- ★ **`normal ⟹ locate = none` (the reverse bridge).**  A valley tag word has no adjacent cup-then-cap, so the
scan returns `none`.  Structural induction; the head-tag cases mirror the locator. -/
theorem locateAdjacentCupThenCap_valley_imp_none {α : Type u} (isCup : α → Bool) :
    ∀ {tags : List α}, isCapThenCupValley isCup tags = true → locateAdjacentCupThenCap isCup tags = none
  | [], _ => rfl
  | [_single], _ => rfl
  | firstCell :: secondCell :: rest, valley => by
      rw [isCapThenCupValley_cons_cons] at valley
      cases hFirst : isCup firstCell with
      | false =>
          rw [hFirst] at valley
          have recNone := locateAdjacentCupThenCap_valley_imp_none isCup valley
          rw [locateAdjacentCupThenCap_capHead isCup firstCell secondCell rest hFirst, recNone]; rfl
      | true =>
          rw [hFirst] at valley
          have valleyAnd : (isCup secondCell && allCups isCup rest) = true := valley
          cases hSecond : isCup secondCell with
          | false =>
              rw [hSecond, Bool.false_and] at valleyAnd
              nomatch valleyAnd
          | true =>
              rw [hSecond, Bool.true_and] at valleyAnd
              have valleyTail : isCapThenCupValley isCup (secondCell :: rest) = true := by
                show (match isCup secondCell with
                      | true => allCups isCup rest
                      | false => isCapThenCupValley isCup rest) = true
                rw [hSecond]; exact valleyAnd
              have recNone := locateAdjacentCupThenCap_valley_imp_none isCup valleyTail
              rw [locateAdjacentCupThenCap_cupThenCup isCup firstCell secondCell rest hFirst hSecond, recNone]; rfl

/-- ★★ **The locator is SOUND and COMPLETE**: `locate cell = none ↔ IsStaircaseNormal cell`.  So the scan returns
`none` EXACTLY on staircase-normal cells; the two directions are the completeness (`none ⟹ normal`) and the reverse
bridge (`normal ⟹ none`). -/
theorem stringStaircaseLocate_none_iff_normal {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    locateStringStaircaseRedex cell = none ↔ IsStaircaseNormal cell :=
  ⟨locateAdjacentCupThenCap_none_imp_valley SpineAtom.isCupAtom,
    locateAdjacentCupThenCap_valley_imp_none SpineAtom.isCupAtom⟩

/-- ★ **A located redex is a GENUINE snake redex (soundness).**  If the scan returns `some k`, the spine is not a
valley, so it contains an adjacent cup-then-cap (`hasAdjacentCupThenCap_of_not_valley`) — a real straighten / commute
redex, not a spurious hit. -/
theorem stringStaircaseLocate_some_exposesRedex {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) (position : Nat)
    (located : locateStringStaircaseRedex cell = some position) :
    HasAdjacentCupThenCap SpineAtom.isCupAtom cell.spine := by
  have notNormal : ¬ IsStaircaseNormal cell := by
    intro isNormal
    rw [(stringStaircaseLocate_none_iff_normal cell).mpr isNormal] at located
    nomatch located
  have notValley : isCapThenCupValley SpineAtom.isCupAtom cell.spine = false := by
    cases hval : isCapThenCupValley SpineAtom.isCupAtom cell.spine with
    | true => exact absurd hval notNormal
    | false => rfl
  exact hasAdjacentCupThenCap_of_not_valley SpineAtom.isCupAtom notValley

/-! ## P2 — the descent step (strictly disorder-decreasing) -/

/-- ★ **The staircase descent STEP.**  Fire the located snake redex at the tag level: swap the first adjacent
cup-then-cap of the spine (the shipped `swapFirstCupCap`), returning the reduced tag word.  Bubble-sorts the spine
toward the caps-then-cups valley. -/
def stringStaircaseSwap {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    List (SpineAtom adjointTripleModeSignature sourceMode targetMode) :=
  swapFirstCupCap SpineAtom.isCupAtom cell.spine

/-- ★★ **The descent step strictly DROPS the disorder measure.**  On a non-normal cell the swap decreases the spine
disorder (`spineDisorder`, the inversion count of the cup/cap tags) — the shipped strictly-decreasing measure
(`swapFirstCupCap_disorder_lt`) that makes the fuel-structural `valleyDescentDriver` terminate.  This wires the
LOCATOR (a non-normal cell HAS a redex) to the shipped descent well-foundedness. -/
theorem stringStaircaseStep_dropsDisorder {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (notNormal : ¬ IsStaircaseNormal cell) :
    spineDisorder (stringStaircaseSwap cell) < spineDisorder cell.spine := by
  have notValley : isCapThenCupValley SpineAtom.isCupAtom cell.spine = false := by
    cases hval : isCapThenCupValley SpineAtom.isCupAtom cell.spine with
    | true => exact absurd hval notNormal
    | false => rfl
  exact swapFirstCupCap_disorder_lt SpineAtom.isCupAtom notValley

/-! ## P1/P2 non-vacuity — the locator separates a real redex from a normal cell -/

/-- The identity 2-cell on `F` is staircase-normal (empty spine). -/
theorem stringIdentityF_isStaircaseNormal : IsStaircaseNormal stringIdentityF := rfl

/-- ★ **The `F`-snake is NOT staircase-normal — the locator finds its redex.**  `stringSnakeF`'s spine is a cup
(`unitLower`) immediately followed by a cap (`counitLower`), so the valley check fails and the scan returns a
position; the locator genuinely fires on the shipped snake. -/
theorem stringSnakeF_not_isStaircaseNormal : ¬ IsStaircaseNormal stringSnakeF := by
  intro isNormal
  exact Bool.noConfusion isNormal

/-! ## P3 — the PINNING WALL: the spine-tag normal form is NOT matching-determined (PROVEN) -/

/-- `id_G ⊟ id_G` is staircase-normal (empty spine — both `id` slots are spine-invisible). -/
theorem stringIdentityG_vcomp_isStaircaseNormal :
    IsStaircaseNormal (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG) := rfl

/-- `id_G` and `id_G ⊟ id_G` have EQUAL boundary matching — both reduce to the same (empty) spine, so `matchingOf`
(which reads only the spine + source length) agrees; equivalently, the shipped soundness applied to the EXTEND
convertibility `id_G ⊟ id_G ≈ id_G`. -/
theorem stringIdentityG_matchingOf_vcomp_eq :
    matchingOf (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG) = matchingOf stringIdentityG :=
  stringSaturatedConv_matchingOf_eq_final (stringExtendByIdentity stringIdentityG)

/-- `id_G` and `id_G ⊟ id_G` are DISTINCT raw terms (different head constructors: `id` vs `vcomp`). -/
theorem stringIdentityG_ne_vcomp :
    stringIdentityG ≠ RawTwoCellExpr.vcomp stringIdentityG stringIdentityG := by
  intro equalTerms
  nomatch equalTerms

/-- ★★ **The spine-tag normal form is NOT matching-determined (the machine-witnessed PINNING finding).**  There are
TWO distinct raw cells — `id_G` and `id_G ⊟ id_G` — that are BOTH `IsStaircaseNormal`, have EQUAL `matchingOf`, yet
are NOT equal as raw terms.  So no normalizer landing in the spine-tag valleys can satisfy `StringFcNormalizer`'s
`matchingInjectiveOnNormalForms` (`matchingOf (nf A) = matchingOf (nf B) → nf A = nf B`): the raw term carries
strictly more information than `(spine, matchingOf)` (EXTEND `id`-slots, whisker-splits, vcomp-nesting all collapse
to the same spine), so a matching-INJECTIVE normal form must pin a canonical RAW representative per spine — the FC
canonical-word data structure whose cross-colour interleave order is the undefined FC-3c binding.  This is the exact
obstruction that walls the fold + injectivity; recorded, not fabricated. -/
theorem stringStaircaseNormalForm_not_matchingDetermined :
    IsStaircaseNormal stringIdentityG
      ∧ IsStaircaseNormal (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG)
      ∧ matchingOf (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG) = matchingOf stringIdentityG
      ∧ stringIdentityG ≠ RawTwoCellExpr.vcomp stringIdentityG stringIdentityG :=
  ⟨rfl, rfl, stringIdentityG_matchingOf_vcomp_eq, stringIdentityG_ne_vcomp⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the FC staircase redex LOCATOR + descent STEP are shipped, sound and complete.**  The
structural scan `locateStringStaircaseRedex` returns the first adjacent cup-then-cap of the cell's cup/cap-tagged
spine; it is SOUND and COMPLETE (`stringStaircaseLocate_none_iff_normal`: `none ↔ IsStaircaseNormal`), a `some` result
exposing a genuine snake redex (`stringStaircaseLocate_some_exposesRedex`).  `IsStaircaseNormal` (the spine is a
cap-then-cup valley) is `Decidable`, and the descent step `stringStaircaseSwap` strictly DROPS the disorder measure on
any non-normal cell (`stringStaircaseStep_dropsDisorder`, the shipped `swapFirstCupCap_disorder_lt`), wiring the
locator to the fuel-structural `valleyDescentDriver` already proven terminating + valley-correct.  Non-vacuous: `id_F`
is normal, `stringSnakeF` is not (the locator fires).  All UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxString_hasStaircaseRedexLocator : Bool := true

/-- **OPEN (honest) — the FOLD + matching-INJECTIVITY are WALLED by a MACHINE-WITNESSED pinning gap.**  Assembling
`StringFcNormalizer` (`normalize` + `convToNormalize` + `matchingInjectiveOnNormalForms`) from the locator + the
shipped per-mode conv/lex descents is BLOCKED, and the block is exhibited, not asserted:

  1. ★ PROVEN — the spine-tag normal form is NOT matching-determined
     (`stringStaircaseNormalForm_not_matchingDetermined`): `id_G` and `id_G ⊟ id_G` are both `IsStaircaseNormal`,
     matching-EQUAL, yet DISTINCT raw terms (EXTEND `id`-slots are spine-invisible).  So `matchingInjectiveOnNormalForms`
     cannot hold for any normalizer landing in the spine-tag valleys — it must pin a canonical RAW representative per
     spine.
  2. ★ The canonical raw representative needs the cross-colour interleave order (sort disjoint blocks to
     `commutePotential = 0`), but `fxString_hasNormalFormDesignLock` §2 forbids a GLOBAL colour order (planarity across
     the shared `G`) while `commutePotential = countInversions` IMPOSES one — the Cartier–Foata "uniqueness needs a
     fixed total order on independent letters" gap, here a PLANARITY-constrained order that is not a total colour
     order.  The spine-atom → colour-key binding + window-disjointness gating are UNDEFINED (the FC-3c wall shared with
     `StringFussCatalanPotential.fxString_hasStaircaseFoldFromPotential`).
  3. The cell-level CONV lift (spine position → cell subterm at bare `TwoCellConv`) is open upstream
     (`WalkingAdjunction/SpineValleyDisorder` honesty marker), and full injectivity additionally rides the FC-4 P4
     planar-survivor.

So `fxString_hasStaircaseDriver` (Staircase), `fxString_hasStaircaseFoldFromPotential` (Potential), and
`fxString_hasAdjointTripleCompleteness` (Completeness) STAY `false`, honestly — the driver's LOCATE + STEP halves ship,
the FOLD + INJECTIVITY halves are walled by a machine-witnessed FC-2 canonical-form pinning gap, not a failed attempt.
`= false`. -/
def fxString_hasStaircaseDriverFold : Bool := false

end FX1Poly.Polygraph
