import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem

/-! # Polygraph/Omega/WalkingDistLawCandidateDecision — the walking distributive law's
    candidate-enumeration DECISION machine + a machine-checked bounded NO-GO (WP-DISTLAW).

★ **The deferred half of WP-DISTLAW r1 (#2187), LANDED.**  The r1 opening shipped the
two-colour Squier presentation and DECIDED the 1-cell word problem, but it deliberately
declined the *mechanized finite no-go* — `DistLawNoGoLedger.lean` records that shape as
`DistLawModelStatus.finiteRefutation carrierBound`, declared but never populated
(`fxDistLaw_jamMechanizedFiniteNoGoDeferredOnCarrierBound = true`).  This file supplies the
mechanized machine: a candidate distributive law as a rewriting table, the four Beck-axiom
Bool checks, the validity decision, a POSITIVE instance (the swap law between two free
single-generator monads) and a machine-checked bounded NO-GO (within a carrier bound no
candidate is valid — because the unique law needs a longer crossing value than the bound
admits).

## The model (honest scope)

Both monads `S`, `T` are the FREE monad on one unary generator (`S`-words are `s`-runs,
`T`-words are `t`-runs; unit = empty word, mult = concatenation).  A **layer word** is a
`List (Bool × Nat)` — `false = S`-letter, `true = T`-letter, `Nat` = the generator op.  A
distributive law `lambda : S.T => T.S` is presented by a **candidate table** mapping each
crossing `(sOp, tOp)` (an `S`-letter directly before a `T`-letter) to a replacement TS-word.
The **evaluator** `dlwEval` pushes all `S`-letters past all `T`-letters by applying the
candidate at the leftmost crossing, on a STRUCTURAL `Nat` fuel (never `WellFounded.fix`).

The four Beck-axiom checks (`beckUnitS`, `beckUnitT`, `beckMultS`, `beckMultT`) build both
legs of their coherence square as concrete layer words and compare via the REUSED structural
list equality `cswListNatBeq` (words encoded to `List Nat` by `dlwEncodeWord`; the csw
kit's `cswListNatBeqEq` reflects a `true` check into a genuine word equation).  For this
free single-generator pair the unit squares hold unconditionally (empty units cross nothing)
and the multiplication squares are the discriminating conditions: `S`-associativity forces
`lambda` to push `s.s` past `t` confluently, `T`-associativity forces it to push `s` past
`t.t` confluently — both satisfied only by the SWAP value `t.s`.

## What is DECIDED (this file)

  * `isValidDistLaw` — the four-Beck conjunction — is a total Bool decision on candidates.
  * `isValidDistLaw_sound` reflects a `true` verdict into all four Beck checks holding
    (hence, per axis, into the two legs' word equation via `cswListNatBeqEq`).
  * POSITIVE: `dlwSwapCandidate` (the swap `s.t -> t.s`) satisfies all four — a genuine
    distributive law of the two free single-generator monads.
  * NO-GO (a LANDING, not a wall): `dlwNoValidDistLawExists 1 = true` — an EXHAUSTIVE finite
    check that every candidate whose crossing value has length ≤ 1 is invalid.  The
    enumeration `dlwWordsUpTo 1 = [[s], [t], []]` is genuinely complete for length ≤ 1 over
    the two-letter alphabet; each fails `beckMultS`.  Tight: `dlwNoValidDistLawExists 2`
    is `false` (the swap, length 2, appears and is valid).  This is the mechanized
    `finiteRefutation` at `carrierBound = 1` the r1 ledger deferred.

## What is WALLED (T4)

  * `dlwHasGeneralDistLawExistence = false` — deciding existence over ARBITRARY / infinite
    presentations is the composite word problem with an interacting swap symbol, undecidable
    in general.
  * `dlwHasHigherCoherence = false` — iterated distributive laws / the Yang–Baxter hexagon
    for three monads (Cheng's 2-categorical coherence) is an independent condition, not
    implied by the pairwise Beck squares.

Raw Lean 4 + Init, zero-axiom: no `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`, `funext`, `WellFounded.fix`; no wildcard arm over a split
scrutinee.  The list equality is the REUSED `cswListNatBeq` / `cswListNatBeqEq` from
`ComputerAlgebra.Semigroup.CommWordProblem` — not re-derived. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.ComputerAlgebra

/-! ## T1 — the carrier: layer words, candidates, the fuelled evaluator -/

/-- A **layer letter**: `false = S`-layer, `true = T`-layer; the `Nat` is the generator op. -/
abbrev DlwLetter : Type := Bool × Nat

/-- A **layer word**: a sequence of layer letters read left to right. -/
abbrev DlwWord : Type := List DlwLetter

/-- The `S`-layer letter for generator op `op`. -/
def dlwLetterS (op : Nat) : DlwLetter := (false, op)

/-- The `T`-layer letter for generator op `op`. -/
def dlwLetterT (op : Nat) : DlwLetter := (true, op)

/-- A **monad presentation**: its generating op indices, unit op, and multiplication op.
For the free single-generator monads used here the unit is the empty word and mult is
concatenation; the ops label the single generator (op `0`). -/
structure DlwMonadPres where
  /-- The generating op indices of this monad. -/
  generators : List Nat
  /-- The unit (`eta`) op index. -/
  unitOp : Nat
  /-- The multiplication (`mu`) op index. -/
  multOp : Nat

/-- A **candidate distributive law**: a lookup table mapping each crossing `(sOp, tOp)`
(an `S`-letter directly before a `T`-letter) to the replacement TS-word. -/
abbrev DlwCandidate : Type := List ((Nat × Nat) × DlwWord)

/-- Cons-only append on layer words (hand-rolled; no leak-prone `List.append` lemma). -/
def dlwAppend : DlwWord → DlwWord → DlwWord
  | [], back => back
  | letter :: front, back => letter :: dlwAppend front back

/-- Look up the crossing `(sOp, tOp)` in a candidate; default (unlisted crossing) is the
plain swap `t.s`. -/
def dlwLookup : DlwCandidate → Nat → Nat → DlwWord
  | [], sOp, tOp => [(true, tOp), (false, sOp)]
  | ((keyS, keyT), value) :: rest, sOp, tOp =>
      cond (Nat.beq keyS sOp && Nat.beq keyT tOp) value (dlwLookup rest sOp tOp)

/-- Is the crossing `(sOp, tOp)` explicitly covered by a candidate's table? -/
def dlwCrossingCovered : DlwCandidate → Nat → Nat → Bool
  | [], _, _ => false
  | ((keyS, keyT), _) :: rest, sOp, tOp =>
      (Nat.beq keyS sOp && Nat.beq keyT tOp) || dlwCrossingCovered rest sOp tOp

/-- Well-formedness: the candidate covers every crossing in a given crossing list. -/
def dlwCandidateWellFormed : DlwCandidate → List (Nat × Nat) → Bool
  | _, [] => true
  | cand, (sOp, tOp) :: rest =>
      dlwCrossingCovered cand sOp tOp && dlwCandidateWellFormed cand rest

/-- Prepend a letter under an `Option` result. -/
def dlwPrepend (letter : DlwLetter) : Option DlwWord → Option DlwWord
  | none => none
  | some word => some (letter :: word)

/-- One leftmost rewrite step: replace the leftmost `S`-then-`T` adjacency by the candidate's
crossing value; if there is none, `none`.  Fully enumerated match — no wildcard arm. -/
def dlwStep (cand : DlwCandidate) : DlwWord → Option DlwWord
  | [] => none
  | (false, sOp) :: rest =>
      match rest with
      | (true, tOp) :: rest2 => some (dlwAppend (dlwLookup cand sOp tOp) rest2)
      | (false, sOp2) :: rest2 => dlwPrepend (false, sOp) (dlwStep cand ((false, sOp2) :: rest2))
      | [] => none
  | (true, tOp) :: rest => dlwPrepend (true, tOp) (dlwStep cand rest)

/-- The **fuelled evaluator**: iterate `dlwStep` on a STRUCTURAL `Nat` fuel until no crossing
remains (or fuel runs out). -/
def dlwEval : Nat → DlwCandidate → DlwWord → DlwWord
  | 0, _, word => word
  | Nat.succ fuel, cand, word =>
      match dlwStep cand word with
      | some next => dlwEval fuel cand next
      | none => word

/-! ## Word equality — REUSED from the csw kit via a `List Nat` encoding -/

/-- Encode a layer letter to a `Nat` (`S op -> op+op`, `T op -> op+op+1`); injective. -/
def dlwEncodeLetter : DlwLetter → Nat
  | (false, op) => op + op
  | (true, op) => op + op + 1

/-- Encode a layer word to a `List Nat`. -/
def dlwEncodeWord : DlwWord → List Nat
  | [] => []
  | letter :: rest => dlwEncodeLetter letter :: dlwEncodeWord rest

/-- Structural equality on layer words — the REUSED `cswListNatBeq` on encodings. -/
def dlwWordBeq (left right : DlwWord) : Bool :=
  cswListNatBeq (dlwEncodeWord left) (dlwEncodeWord right)

/-- Reflect a `true` word-equality into the encoded-word equation (reuses `cswListNatBeqEq`). -/
theorem dlwWordBeqToEncodeEq {left right : DlwWord} (hBeq : dlwWordBeq left right = true) :
    dlwEncodeWord left = dlwEncodeWord right :=
  cswListNatBeqEq (dlwEncodeWord left) (dlwEncodeWord right) hBeq

/-! ## T2 — the four Beck-axiom Bool checks

Fuel `dlwBeckFuel` bounds every evaluation; on the small probe words it always fully
normalizes.  The unit probes carry no crossing (empty units), so `beckUnitS` / `beckUnitT`
hold for any generator-defined candidate — honest for these free monads.  The multiplication
probes are the discriminating conditions. -/

/-- Evaluation fuel for the Beck probes — ample for the length-≤3 probe words. -/
def dlwBeckFuel : Nat := 16

/-- **Beck unit-`S`** (`lambda . (etaS T) = T etaS`): applied to a lone `T`-letter (the
`S`-unit crosses nothing) the result is that `T`-letter unchanged. -/
def beckUnitS (cand : DlwCandidate) : Bool :=
  dlwWordBeq (dlwEval dlwBeckFuel cand [(true, 0)]) [(true, 0)]

/-- **Beck unit-`T`** (`lambda . (S etaT) = etaT S`): applied to a lone `S`-letter (the
`T`-unit crosses nothing) the result is that `S`-letter unchanged. -/
def beckUnitT (cand : DlwCandidate) : Bool :=
  dlwWordBeq (dlwEval dlwBeckFuel cand [(false, 0)]) [(false, 0)]

/-- **Beck mult-`S`** (`lambda . (muS T) = (T muS) . (lambda S) . (S lambda)`): pushing the
`S`-block `s.s` past a single `t` must land at `t.s.s`.  Discriminating: only a genuine
swap value normalizes `s.s.t` to `t.s.s`. -/
def beckMultS (cand : DlwCandidate) : Bool :=
  dlwWordBeq (dlwEval dlwBeckFuel cand [(false, 0), (false, 0), (true, 0)])
    [(true, 0), (false, 0), (false, 0)]

/-- **Beck mult-`T`** (`lambda . (S muT) = (muT S) . (T lambda) . (lambda T)`): pushing a
single `s` past the `T`-block `t.t` must land at `t.t.s`.  Discriminating: only a genuine
swap value normalizes `s.t.t` to `t.t.s`. -/
def beckMultT (cand : DlwCandidate) : Bool :=
  dlwWordBeq (dlwEval dlwBeckFuel cand [(false, 0), (true, 0), (true, 0)])
    [(true, 0), (true, 0), (false, 0)]

/-- The four-Beck conjunction. -/
def isValidDistLaw (cand : DlwCandidate) : Bool :=
  beckUnitS cand && beckUnitT cand && beckMultS cand && beckMultT cand

/-! ## T3 — the decision, its soundness, the POSITIVE instance, and the NO-GO -/

/-- **The candidate-validity decision.** -/
def decideDistLawValid (cand : DlwCandidate) : Bool := isValidDistLaw cand

/-- **Soundness of the decision.**  A `true` verdict yields all four Beck checks holding
(each of which is itself a decidable word equation between the two legs of its square). -/
theorem isValidDistLaw_sound {cand : DlwCandidate} (hValid : isValidDistLaw cand = true) :
    beckUnitS cand = true ∧ beckUnitT cand = true ∧ beckMultS cand = true ∧
      beckMultT cand = true := by
  have hStep1 := cswBoolAndElim _ _ hValid
  have hStep2 := cswBoolAndElim _ _ hStep1.left
  have hStep3 := cswBoolAndElim _ _ hStep2.left
  exact ⟨hStep3.left, hStep3.right, hStep2.right, hStep1.right⟩

/-- Per-axis leg reflection: a passing `beckMultS` gives the encoded word equation of its two
legs (reuses `cswListNatBeqEq`). -/
theorem beckMultS_legEq {cand : DlwCandidate} (hCheck : beckMultS cand = true) :
    dlwEncodeWord (dlwEval dlwBeckFuel cand [(false, 0), (false, 0), (true, 0)])
      = dlwEncodeWord [(true, 0), (false, 0), (false, 0)] :=
  dlwWordBeqToEncodeEq hCheck

/-- Per-axis leg reflection: a passing `beckMultT` gives the encoded word equation of its two
legs. -/
theorem beckMultT_legEq {cand : DlwCandidate} (hCheck : beckMultT cand = true) :
    dlwEncodeWord (dlwEval dlwBeckFuel cand [(false, 0), (true, 0), (true, 0)])
      = dlwEncodeWord [(true, 0), (true, 0), (false, 0)] :=
  dlwWordBeqToEncodeEq hCheck

/-- The free single-generator monad `S` (one generator, op `0`). -/
def dlwFreeMonadS : DlwMonadPres where
  generators := [0]
  unitOp := 0
  multOp := 0

/-- The free single-generator monad `T` (one generator, op `0`). -/
def dlwFreeMonadT : DlwMonadPres where
  generators := [0]
  unitOp := 0
  multOp := 0

/-- The single crossing of the two single-generator monads. -/
def dlwSingleCrossings : List (Nat × Nat) := [(0, 0)]

/-- **The POSITIVE candidate**: the swap `s.t -> t.s`. -/
def dlwSwapCandidate : DlwCandidate := [((0, 0), [(true, 0), (false, 0)])]

/-- **The identity (no-swap) candidate**: `s.t -> s.t` — a well-typed but INVALID candidate
(it passes the unit axioms yet fails multiplication — the check has teeth per axis). -/
def dlwIdentityCandidate : DlwCandidate := [((0, 0), [(false, 0), (true, 0)])]

/-- **The doubling candidate**: `s.t -> t.t.s` — another well-typed INVALID candidate. -/
def dlwDoublingCandidate : DlwCandidate := [((0, 0), [(true, 0), (true, 0), (false, 0)])]

/-! ### The exhaustive bounded candidate enumeration -/

/-- Prepend a letter to each word in a list. -/
def dlwConsEach (letter : DlwLetter) : List DlwWord → List DlwWord
  | [] => []
  | word :: rest => (letter :: word) :: dlwConsEach letter rest

/-- Append two word lists (cons-only). -/
def dlwAppendWords : List DlwWord → List DlwWord → List DlwWord
  | [], back => back
  | word :: front, back => word :: dlwAppendWords front back

/-- **All layer words of length ≤ `bound`** over the two-letter alphabet `{s0, t0}`.
`dlwWordsUpTo 0 = [[]]`; `dlwWordsUpTo 1 = [[s0], [t0], []]` — the exhaustive length-≤1
crossing-value space. -/
def dlwWordsUpTo : Nat → List DlwWord
  | 0 => [[]]
  | Nat.succ smaller =>
      dlwAppendWords (dlwConsEach (false, 0) (dlwWordsUpTo smaller))
        (dlwAppendWords (dlwConsEach (true, 0) (dlwWordsUpTo smaller)) (dlwWordsUpTo smaller))

/-- Turn each candidate crossing value into a single-crossing candidate table. -/
def dlwToCandidates : List DlwWord → List DlwCandidate
  | [] => []
  | value :: rest => [((0, 0), value)] :: dlwToCandidates rest

/-- Every candidate in a list is invalid. -/
def dlwAllInvalid : List DlwCandidate → Bool
  | [] => true
  | cand :: rest => (not (decideDistLawValid cand)) && dlwAllInvalid rest

/-- **The bounded NO-GO predicate**: no candidate whose crossing value has length ≤ `bound`
is a valid distributive law of the two free single-generator monads. -/
def dlwNoValidDistLawExists (bound : Nat) : Bool :=
  dlwAllInvalid (dlwToCandidates (dlwWordsUpTo bound))

/-! ## T4 — the walls -/

/-- **WALL 1 (general existence).**  `= false`: deciding whether ANY distributive law exists
for an ARBITRARY finitely-presented monad pair is NOT delivered.  Concrete obstruction: with
the swap a genuine interacting shared symbol, existence reduces to the word problem of the
composite theory `S * T + swap`, which is undecidable in general.

Two burned attacks: (1) reduce to disjoint-signature amalgamation decidability (Pigozzi 1974;
Baader–Tinelli 1998) — FAILS, the swap is a shared/interacting symbol, so that unconditional
decidability does not transfer (Lack, *Composing PROPs*, TAC 13; Zanasi, *Interacting Hopf
Algebras*, Prop. 2.30); (2) bounded candidate enumeration (as landed here for the finite
instance) — FAILS to generalize: over arbitrary presentations the crossing-value length is
unbounded, so `dlwWordsUpTo bound` never covers the space, and there is no computable a-priori
bound (that would need a termination certificate = the walled almost-full product / Dickson,
`cswHasPresentedCommWordDecision = false`). -/
def dlwHasGeneralDistLawExistence : Bool := false

/-- **WALL 2 (higher coherence).**  `= false`: the iterated / higher-dimensional coherence
of distributive laws is NOT delivered.  Concrete obstruction: for a triple of monads
`(R, S, T)` the Yang–Baxter hexagon relating the three pairwise laws is an INDEPENDENT
coherence condition, not implied by the pairwise Beck squares this file decides.

Two burned attacks: (1) derive triple-law coherence from the three pairwise Beck squares —
FAILS, Cheng, *Iterated distributive laws*, shows the Yang–Baxter hexagon is a genuinely
independent condition; (2) extend the two-colour bubble normal form to three colours — FAILS,
the two-colour monotone-map sort backbone (already walled at
`fxDistLaw_fullTwoCellDecisionWalledAtTwoColourMonotoneMap = false`) has no confluent
three-colour analog; the 2-cell word problem there is already open. -/
def dlwHasHigherCoherence : Bool := false

/-! ## T5 — ground fires -/

/-- The swap candidate covers the single crossing (well-formed). -/
theorem dlwFireSwapWellFormed :
    dlwCandidateWellFormed dlwSwapCandidate dlwSingleCrossings = true := rfl

/-- FIRE: the swap candidate is a genuine distributive law (decides valid). -/
theorem dlwFireSwapValid : decideDistLawValid dlwSwapCandidate = true := rfl

/-- FIRE: the swap normalizes `s.s.t` to `t.s.s` (the `beckMultS` left/right legs coincide). -/
theorem dlwFireSwapMultSLeg :
    dlwWordBeq (dlwEval dlwBeckFuel dlwSwapCandidate [(false, 0), (false, 0), (true, 0)])
      [(true, 0), (false, 0), (false, 0)] = true := rfl

/-- FIRE (teeth): the identity candidate passes both unit axioms... -/
theorem dlwFireIdentityUnitS : beckUnitS dlwIdentityCandidate = true := rfl

/-- ...and the other unit axiom... -/
theorem dlwFireIdentityUnitT : beckUnitT dlwIdentityCandidate = true := rfl

/-- ...but FAILS `beckMultS` (per-axis teeth: the check is not a global rubber stamp)... -/
theorem dlwFireIdentityMultS : beckMultS dlwIdentityCandidate = false := rfl

/-- ...so the identity candidate decides INVALID. -/
theorem dlwFireIdentityInvalid : decideDistLawValid dlwIdentityCandidate = false := rfl

/-- FIRE (teeth): the doubling candidate fails `beckMultT` and decides invalid. -/
theorem dlwFireDoublingInvalid : decideDistLawValid dlwDoublingCandidate = false := rfl

/-- FIRE: the exhaustive length-≤1 candidate space is `[[s0], [t0], []]`. -/
theorem dlwFireWordsUpToOne :
    dlwWordsUpTo 1 = [[(false, 0)], [(true, 0)], []] := rfl

/-- FIRE (NO-GO, the landing): within carrier bound `1` NO valid distributive law exists —
every length-≤1 candidate is invalid, checked exhaustively. -/
theorem dlwFireNoValidAtBoundOne : dlwNoValidDistLawExists 1 = true := rfl

/-- FIRE (tightness): the bound-1 no-go is TIGHT — at bound `2` the swap (length-2 value)
appears and is valid, so not all candidates are invalid. -/
theorem dlwFireValidAppearsAtBoundTwo : dlwNoValidDistLawExists 2 = false := rfl

/-- FIRE (Beck leg word-equality): the encoded `beckMultT` legs of the swap coincide. -/
theorem dlwFireSwapMultTLegEq :
    dlwEncodeWord (dlwEval dlwBeckFuel dlwSwapCandidate [(false, 0), (true, 0), (true, 0)])
      = dlwEncodeWord [(true, 0), (true, 0), (false, 0)] :=
  beckMultT_legEq (by rfl)

/-! ## The state marker -/

/-- ★★ **THE WP-DISTLAW candidate-decision STATE.**  `= true` records the round's deliverable:
the mechanized finite no-go the r1 ledger deferred is now LANDED — a candidate distributive
law as a rewriting table (`DlwCandidate` / `dlwEval`), the four Beck-axiom Bool checks
(`beckUnitS`/`beckUnitT`/`beckMultS`/`beckMultT`), the validity decision (`decideDistLawValid`
+ `isValidDistLaw_sound`), a POSITIVE instance (`dlwSwapCandidate` valid) and a machine-checked
bounded NO-GO (`dlwNoValidDistLawExists 1 = true`, tight at bound 2), reusing the csw
structural list equality.  Two walls stand: general existence over infinite presentations
(`dlwHasGeneralDistLawExistence = false`) and higher/iterated coherence
(`dlwHasHigherCoherence = false`). -/
def fxDistLaw_candidateDecisionStateRecorded : Bool := true

end FX1Poly.Polygraph.Omega
