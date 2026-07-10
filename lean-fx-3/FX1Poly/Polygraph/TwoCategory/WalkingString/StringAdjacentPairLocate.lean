import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDisorder

/-! # WalkingString — the DATA-valued adjacent cup·cap LOCATE (FC-3 r8, B1)

The descent-oracle wire-up (`StringStraightenOracleWireUp`) reduced the per-step oracle to a per-step verdict
DISPATCH `stringDescentDispatch_ofLocatedPair` that consumes an adjacent cup·cap split AS DATA (`prefixCells`,
`cupAtom`, `capAtom`, `rest`, the `sourceSplit` equation, the two tag proofs).  But a non-valley cell only exposes
its adjacent cup·cap pair through the Prop-`∃` `hasAdjacentCupThenCap_split` (`SpineValleyProgress`), which
`Exists.casesOn` CANNOT eliminate into the Type-valued `StringCellDescentResult`.  So the dispatch cannot be fed
from the Prop witness; a DATA-valued locate is required.

The shipped `locateAdjacentCupThenCap` (`StringFussCatalanStaircaseDriver`) returns only the POSITION
(`Option Nat`) — it locates the redex but does not carry the split as data usable in a `Type` result.  This file
ships the data twin:

  * ★ **`SpineAdjacentCupCapSplit spine`** — a Type-valued carrier of the split
    `spine = prefixCells ++ cupAtom :: capAtom :: rest` with `cupAtom` a cup and `capAtom` a cap.  A bespoke
    `structure` (not a nested `Σ'`), so the projections eliminate into `Type` freely — the exact shape
    `stringDescentDispatch_ofLocatedPair` takes.
  * ★ **`locateAdjacentCupCapSplit`** — a TOTAL structural scan returning `Option (SpineAdjacentCupCapSplit spine)`:
    the data twin of `locateAdjacentCupThenCap` fused with `hasAdjacentCupThenCap_split`.  Structural recursion on
    the tail (a full-enum two-tag match, `propext`-clean); the found head-pair returns the empty-prefix split, a
    deeper hit is prepended via `SpineAdjacentCupCapSplit.cons` (cons-rebuild, `propext`-free).
  * ★ **`locateAdjacentCupCapSplit_eq_none_isValley`** — the COMPLETENESS bridge: `locate = none → the spine is a
    cap-block-then-cup-block valley`.  A pure `List`/`Bool` structural induction (Nat-FREE — no width arithmetic,
    so none of the `Nat.le.dest` / cancellation traps apply), mirroring the shipped positional
    `locateAdjacentCupThenCap_none_imp_valley`.  This is what lets a hypothesis-free descent oracle discharge its
    `none` branch: `Option.casesOn` gives the split into `Type` on the `some` branch, and this bridge turns the
    `none` branch into `False` from the oracle's `notValley` hypothesis via `Bool.noConfusion`.

Truth-probe: `locateAdjacentCupCapSplit` returns `some` on the concrete NON-valley snake `[η, ε]` (a lower cup then
a lower cap) and `none` on the VALLEY `[ε, η]` (a cap then a cup) — the locate genuinely fires on a real redex and
genuinely declines on a valley.

Raw Lean 4 + Init; the locate is a full-enum structural fold, the completeness a 3-case structural induction, the
probes `rfl`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The Type-valued split carrier -/

/-- ★ **A located adjacent cup·cap split, AS DATA.**  Certifies `spine = prefixCells ++ cupAtom :: capAtom :: rest`
with `cupAtom` a cup (`isCupAtom = true`) and `capAtom` a cap (`isCupAtom = false`).  A bespoke `structure` so its
projections eliminate into `Type` — the exact located-pair shape `stringDescentDispatch_ofLocatedPair` consumes. -/
structure SpineAdjacentCupCapSplit {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (spine : List (SpineAtom signature sourceMode targetMode)) where
  /-- The atoms before the located cup. -/
  prefixCells : List (SpineAtom signature sourceMode targetMode)
  /-- The located cup atom. -/
  cupAtom : SpineAtom signature sourceMode targetMode
  /-- The located cap atom (immediately after the cup). -/
  capAtom : SpineAtom signature sourceMode targetMode
  /-- The atoms after the located cap. -/
  rest : List (SpineAtom signature sourceMode targetMode)
  /-- The split equation. -/
  splitEq : spine = prefixCells ++ cupAtom :: capAtom :: rest
  /-- The located cup atom is a cup. -/
  isCupCup : cupAtom.isCupAtom = true
  /-- The located cap atom is a cap. -/
  isCapCap : capAtom.isCupAtom = false

/-- Prepend one atom to a located split — the deeper-hit constructor of the locate.  The split equation rebuilds by
`congrArg (atom :: ·)` (cons-rebuild, `List.cons_append` definitional), so it stays `propext`-free. -/
def SpineAdjacentCupCapSplit.cons {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode)
    {spine : List (SpineAtom signature sourceMode targetMode)}
    (split : SpineAdjacentCupCapSplit spine) :
    SpineAdjacentCupCapSplit (atom :: spine) where
  prefixCells := atom :: split.prefixCells
  cupAtom := split.cupAtom
  capAtom := split.capAtom
  rest := split.rest
  splitEq := congrArg (atom :: ·) split.splitEq
  isCupCup := split.isCupCup
  isCapCap := split.isCapCap

/-! ## The DATA-valued structural locate -/

/-- ★ **The DATA-valued adjacent cup·cap locate.**  Scan the spine left to right; return the FIRST place a cup
(`isCupAtom = true`) is immediately followed by a cap (`isCupAtom = false`), packaged as the split DATA.  A full
four-way enumeration of the two head tags (NO wildcard — `propext`-clean), structural recursion on the tail
`secondCell :: rest`.  The data twin of `locateAdjacentCupThenCap` fused with `hasAdjacentCupThenCap_split`. -/
def locateAdjacentCupCapSplit {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (spine : List (SpineAtom signature sourceMode targetMode)) →
    Option (SpineAdjacentCupCapSplit spine)
  | [] => none
  | [_single] => none
  | firstCell :: secondCell :: rest =>
      if hFirst : firstCell.isCupAtom = true then
        if hSecond : secondCell.isCupAtom = false then
          some ⟨[], firstCell, secondCell, rest, rfl, hFirst, hSecond⟩
        else
          (locateAdjacentCupCapSplit (secondCell :: rest)).map (SpineAdjacentCupCapSplit.cons firstCell)
      else
        (locateAdjacentCupCapSplit (secondCell :: rest)).map (SpineAdjacentCupCapSplit.cons firstCell)

/-! ## The completeness bridge -/

/-- A mapped option is `none` only when the source is `none`. -/
private theorem optionMapEqNoneSplit {alpha : Type u} {beta : Type u} (mapFn : alpha → beta)
    {opt : Option alpha} (mappedNone : opt.map mapFn = none) : opt = none := by
  cases opt with
  | none => rfl
  | some value => nomatch mappedNone

/-- The definitional unfold of the locate on a cons-cons spine (structural recursion reduces on constructor input,
so this is `rfl` — propext-FREE, unlike a `simp only`-unfold of the recursive def). -/
private theorem locateAdjacentCupCapSplit_consCons {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (firstCell secondCell : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    locateAdjacentCupCapSplit (firstCell :: secondCell :: rest)
      = (if hFirst : firstCell.isCupAtom = true then
          (if hSecond : secondCell.isCupAtom = false then
            some ⟨[], firstCell, secondCell, rest, rfl, hFirst, hSecond⟩
          else (locateAdjacentCupCapSplit (secondCell :: rest)).map (SpineAdjacentCupCapSplit.cons firstCell))
        else (locateAdjacentCupCapSplit (secondCell :: rest)).map (SpineAdjacentCupCapSplit.cons firstCell)) := rfl

/-- Locate reduction on a `cap`-headed cons-cons spine: the outer tag condition fails. -/
private theorem locateAdjacentCupCapSplit_capHead {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (firstCell secondCell : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode)) (isCapFirst : firstCell.isCupAtom = false) :
    locateAdjacentCupCapSplit (firstCell :: secondCell :: rest)
      = (locateAdjacentCupCapSplit (secondCell :: rest)).map (SpineAdjacentCupCapSplit.cons firstCell) := by
  have hne : firstCell.isCupAtom ≠ true := fun isTrue => Bool.noConfusion (isCapFirst.symm.trans isTrue)
  rw [locateAdjacentCupCapSplit_consCons, dif_neg hne]

/-- Locate reduction on a `cup`-then-`cap` cons-cons spine: the head pair is the located split. -/
private theorem locateAdjacentCupCapSplit_cupThenCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (firstCell secondCell : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode)) (isCupFirst : firstCell.isCupAtom = true)
    (isCapSecond : secondCell.isCupAtom = false) :
    locateAdjacentCupCapSplit (firstCell :: secondCell :: rest)
      = some ⟨[], firstCell, secondCell, rest, rfl, isCupFirst, isCapSecond⟩ := by
  rw [locateAdjacentCupCapSplit_consCons, dif_pos isCupFirst, dif_pos isCapSecond]

/-- Locate reduction on a `cup`-then-`cup` cons-cons spine: the inner tag condition fails. -/
private theorem locateAdjacentCupCapSplit_cupThenCup {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (firstCell secondCell : SpineAtom signature sourceMode targetMode)
    (rest : List (SpineAtom signature sourceMode targetMode)) (isCupFirst : firstCell.isCupAtom = true)
    (isCupSecond : secondCell.isCupAtom = true) :
    locateAdjacentCupCapSplit (firstCell :: secondCell :: rest)
      = (locateAdjacentCupCapSplit (secondCell :: rest)).map (SpineAdjacentCupCapSplit.cons firstCell) := by
  have hne : secondCell.isCupAtom ≠ false := fun isFalse => Bool.noConfusion (isCupSecond.symm.trans isFalse)
  rw [locateAdjacentCupCapSplit_consCons, dif_pos isCupFirst, dif_neg hne]

/-- ★ **THE COMPLETENESS BRIDGE — `locate = none ⟹ the spine is a valley`.**  If the data scan finds no adjacent
cup-then-cap, the spine is a `cap`-block-then-`cup`-block valley.  Structural induction on the tail; the head-tag
cases mirror the locate's enumeration.  Nat-FREE — a pure `List`/`Bool` induction, so none of the width-arithmetic
traps apply.  This turns a hypothesis-free descent oracle's `none` branch into `False` from its `notValley`
hypothesis. -/
theorem locateAdjacentCupCapSplit_eq_none_isValley {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    ∀ (spine : List (SpineAtom signature sourceMode targetMode)),
      locateAdjacentCupCapSplit spine = none →
        isCapThenCupValley SpineAtom.isCupAtom spine = true
  | [], _ => rfl
  | [single], _ => by
      show (match single.isCupAtom with
            | true => allCups SpineAtom.isCupAtom []
            | false => isCapThenCupValley SpineAtom.isCupAtom []) = true
      cases single.isCupAtom <;> rfl
  | firstCell :: secondCell :: rest, locNone => by
      rw [isCapThenCupValley_cons_cons]
      cases hFirst : firstCell.isCupAtom with
      | false =>
          rw [locateAdjacentCupCapSplit_capHead firstCell secondCell rest hFirst] at locNone
          have recNone := optionMapEqNoneSplit _ locNone
          exact locateAdjacentCupCapSplit_eq_none_isValley (secondCell :: rest) recNone
      | true =>
          cases hSecond : secondCell.isCupAtom with
          | false =>
              rw [locateAdjacentCupCapSplit_cupThenCap firstCell secondCell rest hFirst hSecond] at locNone
              nomatch locNone
          | true =>
              rw [locateAdjacentCupCapSplit_cupThenCup firstCell secondCell rest hFirst hSecond] at locNone
              have recNone := optionMapEqNoneSplit _ locNone
              have valleyTail :=
                locateAdjacentCupCapSplit_eq_none_isValley (secondCell :: rest) recNone
              show allCups SpineAtom.isCupAtom (secondCell :: rest) = true
              show (secondCell.isCupAtom && allCups SpineAtom.isCupAtom rest) = true
              rw [hSecond, Bool.true_and]
              have step : (match secondCell.isCupAtom with
                    | true => allCups SpineAtom.isCupAtom rest
                    | false => isCapThenCupValley SpineAtom.isCupAtom rest) = true := valleyTail
              rw [hSecond] at step
              exact step

/-! ## Truth-probes — the locate fires on a real redex, declines on a valley -/

/-- The concrete lower cup `η : id_base ⇒ F·G` as a spine atom (its generator source is empty — a cup). -/
def stringProbeCupAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
    StringTwoCell.unitLower, singletonModalityPath AdjointTripleModality.left⟩

/-- The concrete lower cap `ε : G·F ⇒ id_tip` as a spine atom (its generator source is `G·F`, width 2 — a cap). -/
def stringProbeCapAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip, singletonModalityPath AdjointTripleModality.left, stringGF,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip, StringTwoCell.counitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- ★ **Truth-probe (fires): the locate returns `some` on the non-valley snake `[η, ε]`.**  A lower cup immediately
followed by a lower cap is a genuine straighten redex; the data locate finds it. -/
theorem stringProbeLocate_fires :
    (locateAdjacentCupCapSplit [stringProbeCupAtom, stringProbeCapAtom]).isSome = true := rfl

/-- ★ **Truth-probe (declines): the locate returns `none` on the valley `[ε, η]`.**  A cap then a cup is a valley
(cap-block then cup-block); the data locate correctly declines. -/
theorem stringProbeLocate_declines :
    (locateAdjacentCupCapSplit [stringProbeCapAtom, stringProbeCupAtom]).isSome = false := rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the DATA-valued adjacent cup·cap LOCATE + its completeness bridge are machine-checked
(FC-3 r8, B1).**  `SpineAdjacentCupCapSplit spine` carries the split `spine = prefixCells ++ cupAtom :: capAtom ::
rest` as `Type` data (bespoke structure, projections eliminate into `Type`), the exact located-pair shape
`stringDescentDispatch_ofLocatedPair` consumes.  `locateAdjacentCupCapSplit` is the total structural scan returning
that split (full-enum two-tag match, `propext`-clean; `SpineAdjacentCupCapSplit.cons` prepends via cons-rebuild),
the data twin of the shipped positional `locateAdjacentCupThenCap` fused with `hasAdjacentCupThenCap_split`.
`locateAdjacentCupCapSplit_eq_none_isValley` proves `locate = none → valley = true` by a Nat-FREE `List`/`Bool`
induction — the bridge that lets a hypothesis-free descent oracle discharge its `none` branch via `Bool.noConfusion`
against `notValley`.  Truth-probed: `some` on the concrete snake `[η, ε]`, `none` on the valley `[ε, η]`.

  What this marker does NOT close (gates stay `false`): the locate is HALF of the oracle wire-up — the RIGHT-handed
  straighten producer (the second oracle input) is still owed, and Piece II (`StringCellValleyTraceEquiv`) is
  separate.  `StringCellDescentStepOracle` is NOT yet inhabited, so `fxString_hasAdjointTripleCompleteness` stays
  `false`.  `= true`. -/
def fxString_hasStringDataValuedLocate : Bool := true

end FX1Poly.Polygraph
