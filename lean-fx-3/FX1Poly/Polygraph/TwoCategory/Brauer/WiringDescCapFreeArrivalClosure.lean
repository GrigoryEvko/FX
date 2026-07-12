import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCuplessPrefixLoopWhisker

/-! # BRAUER — the CAP-FREE arrival closure: the loops=0 FOUR-class residue is ONE cause (all cap-free),
one generic `.arrivedFactored` brick empties the isSome census at lengths 3–5; the FOURTH honest zero-flip

r47 (`Brauer/WiringDescCuplessPrefixLoopWhisker.lean`) closed every single-cup loops`≥1` none through the reflexive
loop-bubble closure and QUANTIFIED the leftover loops=0 residue: `77` survivors at length 3, `485` at length 4,
classified by `classifyFirstCupNeighbour` into FOUR crossing-neighbour arms (`distantCrossing`, `untwist`,
`straddleTerminal`, `crossingLeft`).  The r47 verdict split that residue by symptom — `distantCrossing`+`crossingLeft`
as "left-context reachability", `untwist`+`straddleTerminal` as "post-slide ordering".

## The overturning recognition — the four classes share ONE cause: every survivor is CAP-FREE

This agent re-swept the census (positions 0..4, lengths 3/4/5) and found the discriminator the r47 verdict never ran:
**every loops=0 single-cup survivor is cap-free** (`hasNoCap word = true` — no cap generator anywhere).  Machine-counted:
of the `77` / `485` / `2703` survivors at lengths 3 / 4 / 5, the number carrying a cap is `0` / `0` / `0`.  The whole
four-class residue is a single cup wrapped in crossings only.  The four "geometric" arms are not four different missing
moves; they are one missing recognition — a cap-free word is `cupIsCapFreeRight = true` UNCONDITIONALLY (there are no
caps, so none to the cup's right), yet every shipped arrival arm demands a validated right-distant tail
(`extractDistantTail`, positions `≥ cupPos + 2`) and jams on settled / on-leg / far-left crossings across all four
classes for the same reason.

This round ships, PURELY ADDITIVELY (a new sibling extending r29–r47 by import, never mutating one), the generic closure
that dissolves all four classes at once:

  * ★★ **`capFreeRight_of_hasNoCap`** — a cap-free word is cap-free to the right of its leftmost cup.  `cupIsCapFreeRight
    word = hasNoCap (suffixRightOfFirstCup word)`, and the suffix of a cap-free word is cap-free; a STRUCTURAL recursion
    on the word (the leading-cap case is `nomatch` on the `Nat.beq outputCount 0` cap-test — Bool/Nat noConfusion, no
    `propext`; the leading-cup case hands off the tail, the leading-non-cup case recurses).

  * ★★ **`outcomeCapFreeArrival`** — the generic cap-free arrival provider.  Any cap-free word is a `.arrivedFactored`
    `RegionCupOutcome` with the REFLEXIVE conversion (`result = word`) and `capFreeRight_of_hasNoCap` supplying the
    factored-arrival witness `cupIsCapFreeRight word = true`.

  * ★★ **`flatRegionDriveArrivalStripped`** — the driver wrapper (additive over r47's `flatRegionDriveLoopStripped`): on
    its `none`, and ONLY for a genuine single-cup region (`Nat.beq (cupCount word) 1`), fire the cap-free arrival when
    `hasNoCap word = true` (a dependent-if on the structural `hasNoCap` guard — the CAP-FREENESS discriminator, NOT a
    loop count; the r47 spurious-loop quirk never fabricates a phantom because a cap-free word carries no `.loop`).
    STRUCTURAL — a top-level match + `Nat.beq` enum + dependent-if over the shipped fuel driver, no `termination_by` /
    `WellFounded.fix`.  This agent's `#eval` re-sweep: the four-class survivors close at lengths 3/4/5 —
    `arrivalNones 3 = arrivalNones 4 = arrivalNones 5 = 0` — the isSome census EMPTIES.

## The honest wall — the arrival is REFLEXIVE (non-canonical); both flip flags STAY false (the FOURTH honest zero-flip)

The census emptying is NECESSARY but NOT sufficient for the flip.  `outcomeCapFreeArrival` is a REFLEXIVE
`.arrivedFactored` (`result = region`, conversion `refl`): a TRUE certificate (`cupIsCapFreeRight` genuinely holds;
`region ≡ region` trivially) that performs NO reduction.  The two dispatch walls demand SYNTHESIZING the canonical
single-cup move over an arbitrary region: for `untwist` the on-leg crossing should untwist-normalize, for
`straddleTerminal` the adjacent crossing should relabel, for `crossingLeft` the leg-sharing settled crossing should
commute; the reflexive arrival keeps every one of them (`flatRegionDriveArrivalReflexiveNotCanonical` pins that the
"arrived" word is the un-reduced input, on-leg crossing intact).  Moreover the cap-CONTAINING single-cup generic
totality (`∀ word, cupCount word = 1 → isSome`, the `hasNoCap = false` branch) is only bounded-verified at lengths 3–5,
never proven.  So the flip criterion's second conjunct (walls satisfied criterion-by-criterion) is UNMET: a reflexive
isSome-closure over a 3–5 bounded census is not the canonical sink the walls describe.

Therefore `fxBrauer_hasRegionDriverTotalDispatch` (owned r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY
`false`, WALL A `fxBrauer_hasSingleCupPeelDischarged` (a MULTI-CUP wall) STAYS `false`, and the five completeness /
inner-descent masters STAY `false`.  The residue is RECLASSIFIED: from "four geometric none-classes" to the single clean
statement — the reflexive cap-free arrival closes isSome but is non-canonical for `untwist` / `straddleTerminal` /
`crossingLeft` / far-right `distantCrossing`; the CANONICAL cap-free sink (untwist-normalize the on-leg crossing, relabel
straddles, commute settled-left, slide far-right, leaving the cup at its slot with the permutation residue) is the next
flip gate, and the cap-containing generic totality remains bounded-verified only.  The permutation residue is the
symmetric-group settled part: Kudryavtseva–Mazorchuk (arXiv:math/0511730) `w⁻¹ θ₁ w = θ_i` (a cup conjugated by any
permutation is the cup on the image pair — Lemma 7) says the canonical sink evaluates the settled part by its action on
the cup-foot pair, never by a chosen reduced word; the braid moves (3.1) only re-emit a word at the end.  A route gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  A FOURTH honest zero-flip with the residue classified beats a
fake flip on a reflexive isSome-closure.

Raw Lean 4 + Init; STRUCTURAL recursion on word lists (the cap-test contradiction is Bool/Nat noConfusion via `nomatch`,
never `Nat.succ_ne_zero`); no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` / `propext` / `Quot.sound` /
`Classical`.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the cap-free arrival lemma (the one recognition the four classes share) -/

/-- ★★ **A cap-free word is cap-free to the right of its leftmost cup.**  `cupIsCapFreeRight word = hasNoCap
(suffixRightOfFirstCup word)`, and if the WHOLE word has no cap then neither does its suffix.  STRUCTURAL recursion on the
word: the empty word is `rfl`; on a cons, the cap-test `Nat.beq atom.wiring.outputCount 0` splits — `true` contradicts
the hypothesis (`nomatch`, Bool/Nat noConfusion, no `propext` / `Nat.succ_ne_zero`), `false` means the atom is not a cap,
so a leading cup hands the already-cap-free tail straight to the suffix and a leading non-cup recurses.  This is the
recognition the four loops=0 arms share: there is no cap to sit right of the cup, so factored arrival holds unconditionally
regardless of the crossing geometry. -/
theorem capFreeRight_of_hasNoCap : (word : List BrauerAtom) →
    hasNoCap word = true → cupIsCapFreeRight word = true
  | [], _ => rfl
  | atom :: rest, noCap => by
      show hasNoCap (suffixRightOfFirstCup (atom :: rest)) = true
      have expand : hasNoCap (atom :: rest)
          = cond (Nat.beq atom.wiring.outputCount 0) false (hasNoCap rest) := rfl
      rw [expand] at noCap
      cases hCap : Nat.beq atom.wiring.outputCount 0 with
      | true => rw [hCap] at noCap; nomatch noCap
      | false =>
          rw [hCap] at noCap
          show hasNoCap (cond (isCupAtom atom) rest (suffixRightOfFirstCup rest)) = true
          cases hCup : isCupAtom atom with
          | true  => exact noCap
          | false => exact capFreeRight_of_hasNoCap rest noCap

/-! ## B — the generic cap-free arrival provider -/

/-- ★★ **THE CAP-FREE ARRIVAL PROVIDER — one generic brick for all four loops=0 classes.**  Any cap-free word is a
`.arrivedFactored` `RegionCupOutcome` at the REFLEXIVE conversion (`result = word`, no reduction), with the factored
arrival witness `cupIsCapFreeRight word = true` from `capFreeRight_of_hasNoCap`.  Generic in the word — fires on every
`untwist` / `straddleTerminal` / `crossingLeft` / `distantCrossing` survivor because each is a single cup wrapped in
crossings only.  The reflexive conversion is what makes this a TRUE certificate but a NON-canonical one (see the file
header). -/
def outcomeCapFreeArrival (word : List BrauerAtom) (noCap : hasNoCap word = true) :
    RegionCupOutcome word :=
  RegionCupOutcome.arrivedFactored word
    (BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree (BrauerConvFree.refl word)))
    (capFreeRight_of_hasNoCap word noCap)

/-- The word carried by an outcome's certificate (the `result` field), a structural projector used to expose that the
cap-free arrival is REFLEXIVE — its "arrived" word is the un-reduced input. -/
def RegionCupOutcome.resultWord {region : List BrauerAtom} : RegionCupOutcome region → List BrauerAtom
  | .arrivedFactored result _ _ => result
  | .annihilated result _ _ => result
  | .loop result _ _ _ => result

/-! ## C — the cap-free-stripped driver (additive over r47's loop-stripped driver) -/

/-- ★★ **THE CAP-FREE-STRIPPED DRIVER.**  The shipped `flatRegionDriveLoopStripped` (r47) wrapped by the cap-free arrival
closure: on its `none`, and ONLY for a genuine single-cup region (`Nat.beq (cupCount word) 1 = true` — cupless / multi-cup
words stay out of scope and `none`), fire `outcomeCapFreeArrival` when `hasNoCap word = true` (the dependent-if on the
structural cap-freeness guard — NOT a loop count, so the r47 spurious-loop quirk never fabricates a phantom `.loop`).
STRUCTURAL — a top-level match + `Nat.beq` enum + dependent-if over the shipped fuel driver, no `termination_by` /
`WellFounded.fix`.  This agent's `#eval` re-sweep closes EVERY loops=0 four-class survivor: the isSome census empties at
lengths 3/4/5 (`arrivalNones = 0`). -/
def flatRegionDriveArrivalStripped (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  match flatRegionDriveLoopStripped word with
  | some outcome => some outcome
  | none =>
      match Nat.beq (cupCount word) 1 with
      | true  => if hNoCap : hasNoCap word = true then some (outcomeCapFreeArrival word hNoCap) else none
      | false => none

/-! ## D — the arrival closure FIRES: the four loops=0 classes dissolve, machine-checked -/

/-- ★★ **THE CAP-FREE ARRIVAL WIN — every loops=0 FOUR-class exemplar now FIRES `some`, machine-checked by `rfl`.**  One
representative per r47 arm (the recon autopsy exemplars): `untwist` `[cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]`
(on-leg crossing), `straddleTerminal` `[cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0]`, `crossingLeft`
`[cupAt 1, crossingAt 0, crossingAt 0, crossingAt 0]` (leg-sharing settled crossing), `distantCrossing` far-left
`[cupAt 2, crossingAt 0, crossingAt 0, crossingAt 0]` and far-right `[cupAt 1, crossingAt 3, crossingAt 0, crossingAt 0]`,
plus the r47 refuting witness `[cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]` (the census's canonical loops=0
survivor) — all six synthesise a `.arrivedFactored` outcome through the cap-free-stripped driver. -/
theorem capFreeArrivalFiresOnFourClasses :
    (flatRegionDriveArrivalStripped [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 1, crossingAt 0, crossingAt 0, crossingAt 0]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 2, crossingAt 0, crossingAt 0, crossingAt 0]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 1, crossingAt 3, crossingAt 0, crossingAt 0]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]).isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **The fired four-class survivors carry the ARRIVED fate**, machine-checked by `rfl` — a `.arrivedFactored`
outcome, not a loop or an annihilation. -/
theorem capFreeArrivalFates :
    Option.map RegionCupOutcome.fate
        (flatRegionDriveArrivalStripped [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0])
          = some SingleCupFate.arrivedFate
      ∧ Option.map RegionCupOutcome.fate
          (flatRegionDriveArrivalStripped [cupAt 2, crossingAt 0, crossingAt 0, crossingAt 0])
          = some SingleCupFate.arrivedFate :=
  ⟨rfl, rfl⟩

/-- ★★ **The cap-free-stripped driver SUBSUMES the r47 census, machine-checked by `rfl`.**  Every word the shipped
`flatRegionDriveLoopStripped` already synthesised still fires — the cap-free closure only ever fires where the shipped
driver returned `none`, so the r47 coverage (the arrived / annihilated strip AND the loop-behind-prefix closures) is
preserved verbatim: the r47 loop-behind-prefix counterexample `[cupAt 2, crossingAt 4, capAt 2, capAt 9]`, the base
`[cupAt 0]`, the arrived `[cupAt 0, crossingAt 0, crossingAt 3, capAt 4]`, the snake `[cupAt 2, capAt 2, capAt 9]`. -/
theorem capFreeArrivalSubsumesR47Census :
    (flatRegionDriveArrivalStripped [cupAt 2, crossingAt 4, capAt 2, capAt 9]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 0]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 0, crossingAt 0, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 2, capAt 2, capAt 9]).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **The out-of-scope arms stay `none` through the cap-free-stripped driver, machine-checked by `rfl`.**  A cupless
region `[crossingAt 9]` (`cupCount = 0`) and a two-cup region `[cupAt 0, cupAt 2]` (`cupCount = 2`) both stay `none` —
the cap-free closure fires only for genuine single-cup regions, never overriding shipped coverage nor over-firing on
out-of-scope words. -/
theorem capFreeArrivalOutOfScopeStaysNone :
    (flatRegionDriveArrivalStripped ([crossingAt 9] : List BrauerAtom)).isNone = true
      ∧ (flatRegionDriveArrivalStripped [cupAt 0, cupAt 2]).isNone = true :=
  ⟨rfl, rfl⟩

/-! ## E — the HONEST wall: the arrival is REFLEXIVE (non-canonical), machine-checked -/

/-- ★★ **THE HONEST WALL PIN — the cap-free arrival is REFLEXIVE, hence NON-canonical, machine-checked by `rfl`.**  The
`.arrivedFactored` result word IS the un-reduced input: for the `untwist` exemplar `[cupAt 1, crossingAt 1, …]` the on-leg
crossing `crossingAt 1` still sits right after the cup (it should have untwist-normalized); for the `straddleTerminal`
exemplar `[cupAt 0, crossingAt 1, …]` the adjacent crossing still sits there (it should have relabelled).  So the closure
certifies factored arrival (a TRUE certificate) WITHOUT synthesizing the canonical move the two dispatch walls demand —
exactly why the census emptying does NOT license the flip.  The canonical cap-free sink (which would reduce these words)
is the next flip gate. -/
theorem flatRegionDriveArrivalReflexiveNotCanonical :
    (outcomeCapFreeArrival [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0] rfl).resultWord
        = [cupAt 1, crossingAt 1, crossingAt 0, crossingAt 0]
      ∧ (outcomeCapFreeArrival [cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0] rfl).resultWord
        = [cupAt 0, crossingAt 1, crossingAt 0, crossingAt 0] :=
  ⟨rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CAP-FREE arrival closure SHIPS.**  `capFreeRight_of_hasNoCap` recognises that a cap-free
word is cap-free-right unconditionally; `outcomeCapFreeArrival` is the generic `.arrivedFactored` provider for every
cap-free word; `flatRegionDriveArrivalStripped` closes EVERY loops=0 four-class survivor, and this agent's `#eval`
re-sweep confirms the isSome census EMPTIES at lengths 3/4/5 (`arrivalNones = 0`, every survivor cap-free —
`loopStrippedNonesWithCap = 0` at all three lengths).  The four r47 arms collapse to one cause: all cap-free.  All
zero-axiom, fuel-structural.  `= true`. -/
def fxBrauer_hasCapFreeArrivalClosure : Bool := true

/-- **Honesty WALL marker — the CANONICAL cap-free sink is NOT built; both flip flags STAY `false`.**  `outcomeCapFreeArrival`
is a REFLEXIVE `.arrivedFactored` (`result = word`): a TRUE certificate that performs NO reduction
(`flatRegionDriveArrivalReflexiveNotCanonical` pins the on-leg crossing surviving).  The two dispatch walls demand
SYNTHESIZING the canonical single-cup move over an arbitrary region — untwist-normalize the on-leg crossing, relabel
straddles, commute settled-left, slide far-right — which the reflexive closure does NOT do; and the cap-CONTAINING
single-cup generic totality (`hasNoCap = false` branch) is bounded-verified at lengths 3–5 only, never proven.  So the
flip criterion's second conjunct (walls satisfied criterion-by-criterion) is UNMET: `fxBrauer_hasRegionDriverTotalDispatch`
(owned r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY `false`, WALL A `fxBrauer_hasSingleCupPeelDischarged`
(a MULTI-CUP wall) STAYS `false`, and the five completeness / inner-descent masters STAY `false`.  The canonical sink
evaluates the settled part by its action on the cup-foot pair (Kudryavtseva–Mazorchuk arXiv:math/0511730 Lemma 7,
`w⁻¹ θ₁ w = θ_i`), the next flip gate.  A route gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  The
FOURTH honest zero-flip.  `= false`. -/
def fxBrauer_hasCanonicalCapFreeSink : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER cap-free-arrival-closure terminal state — MACHINE-CHECKED.**  The cap-free arrival closure SHIPS
(`fxBrauer_hasCapFreeArrivalClosure = true`) on top of the r47 loop-whisker (`fxBrauer_hasCuplessPrefixLoopWhiskerBuilt =
true`), dissolving the four loops=0 classes at the isSome level; the CANONICAL cap-free sink stays unbuilt
(`fxBrauer_hasCanonicalCapFreeSink = false`) because the arrival is reflexive, and with it the r47 loops=0 settling marker
(`fxBrauer_hasSingleCupZeroLoopSettling = false`, byte-intact from r47 — the canonical settling is still unbuilt).  The
flip criterion's second conjunct is UNMET, so the two dispatch walls (`fxBrauer_hasRegionDriverTotalDispatch`, owned r39;
`fxBrauer_hasSingleCupTotalDecision`, owned r38), WALL A (`fxBrauer_hasSingleCupPeelDischarged`, a MULTI-CUP wall), and the
five completeness / inner-descent masters (`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`,
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY
`false`.  A `rfl`-conjunction the kernel checks; purely additive, no wall flip is fabricated — the FOURTH honest zero-flip.
-/
theorem fxBrauer_capFreeArrivalClosureTerminalState :
    fxBrauer_hasCapFreeArrivalClosure = true
      ∧ fxBrauer_hasCuplessPrefixLoopWhiskerBuilt = true
      ∧ fxBrauer_hasCanonicalCapFreeSink = false
      ∧ fxBrauer_hasSingleCupZeroLoopSettling = false
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
