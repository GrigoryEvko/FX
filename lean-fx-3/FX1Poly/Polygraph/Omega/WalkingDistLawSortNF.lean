import FX1Poly.Polygraph.Omega.WalkingDistLawPresentation

/-! # Polygraph/Omega/WalkingDistLawSortNF — the distributive law's 1-cell sorted normal form and word
problem decision (WP-DISTLAW r1, B2 + B3)

★ **The tractable backbone the recon adjudicated as landable at r1.**  The walking distributive law's swap
`s.t => t.s` reads at the 1-cell level as an oriented rewrite `s.t -> t.s` on `{s, t}`-words (the free monoid
`{s, t}*`).  This file ships:

  * **(B2) THE SORTED NORMAL FORM** — every word bubble-sorts to `t^m s^n` (all `t`s left of all `s`s), by a
    swap bubble step (`distLawBubbleStep`, the leftmost `s.t` redex swapped to `t.s`), with termination by an
    INVERSION COUNT (`distLawInversions`, the number of `(s, t)` out-of-order pairs) that each step strictly
    decreases (`distLawInversions_step`).  The sort runs on a STRUCTURAL `Nat` fuel (`distLawSortFueled`,
    never `WellFounded.fix` — the Init-only propext trap the census names), and reaches the normal form in at
    most `inversions w` steps (`distLawSortReachesNf`).  Confluence is ORTHOGONAL (no two `s.t` redexes
    overlap — they would share the middle letter, but `t.s != s.t`), so the normal form is unique: it is a
    function of the letter counts only (`distLawSortConfluent`), and it is genuinely terminal (zero
    inversions, `distLawInversions_nf`).

  * **(B3) THE 1-CELL WORD PROBLEM DECISION** — two words are convertible under the swap-generated congruence
    (`DistLawWordConv`: swap adjacent `s.t <-> t.s`, closed under cons-congruence / refl / symm / trans) iff
    they have the same letter counts (`distLawConv_iffSameCount`), which is DECIDABLE.  Both verdicts are
    exercised on concrete word pairs: `distLawWordDecisionYes` proves `[s, t] ~ [t, s]` (YES), and
    `distLawWordDecisionNo` proves `[s, s, t]` is NOT convertible to `[s, t]` (NO, refuted by the count
    invariant).

## The recon-adjudicated scope (honest)

This is the 1-cell theory, which sorts and decides cleanly.  The FULL decidable 2-cell word problem is WALLED
at the two-colour monotone-map model (`monadPath_normalForm` false for two colours), recorded in the sibling
`WalkingDistLawPresentation.lean` marker.  The pure-swap 1-cell rewrite generates the free COMMUTATIVE monoid
on `{s, t}` (swapping `s` and `t` makes them commute), so convertibility is exactly Parikh-vector (letter
count) equality — the concrete reason the 1-cell decision is clean while the 2-cell one is not (the 2-cell
Beck axioms genuinely interact, cf. the Amalgam lane's shared-symbol undecidability caveat).

## The transposition-atom precedent (NAMED, not imported)

The bubble step is an adjacent transposition — the WalkingString lane's `StringInterleavedWindowSort` /
`SpineAtomSwap` colour-blind transposition atom is the shipped precedent for this backbone (a two-colour
interleaved window sort where any adjacent horizontally-independent pair transposes as one trace step,
reading NO colour).  That precedent is NAMED here; this file re-derives the combinatorial sort natively over a
self-contained `List DistLawColour` model (no cross-lane import), bridged to the presentation carrier by
`distLawWordToCell`.

Raw Lean 4 + Init, STRUCTURAL only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The two-colour alphabet -/

/-- The **1-cell alphabet** of the walking distributive law: the two colours `s` and `t`.  Words are
`List DistLawColour` (the free monoid `{s, t}*`).  Two constructors — full case splits stay propext-clean. -/
inductive DistLawColour where
  /-- The colour `s`. -/
  | s
  /-- The colour `t`. -/
  | t

/-! ## The swap bubble step (the leftmost `s.t` redex) -/

/-- ★ The **swap bubble step** — swap the LEFTMOST adjacent `s.t` to `t.s`, returning `none` when the word is
already sorted (`t^m s^n`).  Fully enumerated (no wildcard — propext-clean); structural recursion descends the
list.  Reading `swap : s.t => t.s` at the 1-cell level as the oriented rewrite `s.t -> t.s`. -/
def distLawBubbleStep : List DistLawColour → Option (List DistLawColour)
  | [] => none
  | DistLawColour.t :: rest =>
      match distLawBubbleStep rest with
      | some rest' => some (DistLawColour.t :: rest')
      | none => none
  | DistLawColour.s :: [] => none
  | DistLawColour.s :: DistLawColour.s :: tail =>
      match distLawBubbleStep (DistLawColour.s :: tail) with
      | some rest' => some (DistLawColour.s :: rest')
      | none => none
  | DistLawColour.s :: DistLawColour.t :: tail => some (DistLawColour.t :: DistLawColour.s :: tail)

/-- Equation lemma: the step at a `t` head recurses into the tail. -/
theorem distLawBubbleStep_tHead (rest : List DistLawColour) :
    distLawBubbleStep (DistLawColour.t :: rest)
      = match distLawBubbleStep rest with | some r => some (DistLawColour.t :: r) | none => none := rfl

/-- Equation lemma: the step at an `s.s` head recurses into the second-onward tail. -/
theorem distLawBubbleStep_ssHead (tail : List DistLawColour) :
    distLawBubbleStep (DistLawColour.s :: DistLawColour.s :: tail)
      = match distLawBubbleStep (DistLawColour.s :: tail) with
        | some r => some (DistLawColour.s :: r) | none => none := rfl

/-- Equation lemma: the step at an `s.t` head FIRES the swap. -/
theorem distLawBubbleStep_stHead (tail : List DistLawColour) :
    distLawBubbleStep (DistLawColour.s :: DistLawColour.t :: tail)
      = some (DistLawColour.t :: DistLawColour.s :: tail) := rfl

/-! ## The letter counts and the inversion measure -/

/-- The number of `t`s in a word — a structural fold (full enumeration, propext-clean). -/
def distLawCountT : List DistLawColour → Nat
  | [] => 0
  | DistLawColour.t :: rest => distLawCountT rest + 1
  | DistLawColour.s :: rest => distLawCountT rest

/-- The number of `s`s in a word. -/
def distLawCountS : List DistLawColour → Nat
  | [] => 0
  | DistLawColour.s :: rest => distLawCountS rest + 1
  | DistLawColour.t :: rest => distLawCountS rest

/-- ★ The **inversion count** — the number of out-of-order `(s, t)` pairs: for each `s`, the number of `t`s
after it.  The termination measure of the bubble sort; each swap step decreases it by exactly one. -/
def distLawInversions : List DistLawColour → Nat
  | [] => 0
  | DistLawColour.s :: rest => distLawCountT rest + distLawInversions rest
  | DistLawColour.t :: rest => distLawInversions rest

/-! ## The normal form `t^m s^n` (cons-only, no `List.append`) -/

/-- The word `s^n` (all `s`s) — cons-only (avoids the `List.append` propext trap). -/
def distLawSPower : Nat → List DistLawColour
  | 0 => []
  | n + 1 => DistLawColour.s :: distLawSPower n

/-- The word `t^m s^n` — `m` copies of `t` prepended to `s^n`, cons-only. -/
def distLawTThenS : Nat → Nat → List DistLawColour
  | 0, numS => distLawSPower numS
  | numT + 1, numS => DistLawColour.t :: distLawTThenS numT numS

/-- ★ The **sorted normal form** of a word: `t^(countT w) s^(countS w)` — a function of the letter counts
only. -/
def distLawNf (w : List DistLawColour) : List DistLawColour :=
  distLawTThenS (distLawCountT w) (distLawCountS w)

/-! ## The structural-fuel bubble sort -/

/-- ★ The **fueled bubble sort** — apply `distLawBubbleStep` up to `fuel` times, stopping early when the word
is sorted.  STRUCTURAL recursion on the `Nat` fuel (never `WellFounded.fix`). -/
def distLawSortFueled : Nat → List DistLawColour → List DistLawColour
  | 0, w => w
  | fuel + 1, w =>
      match distLawBubbleStep w with
      | some w' => distLawSortFueled fuel w'
      | none => w

/-- Equation lemma: one fueled step when a redex fires. -/
theorem distLawSortFueled_stepSome {w w' : List DistLawColour} {fuel : Nat}
    (h : distLawBubbleStep w = some w') :
    distLawSortFueled (fuel + 1) w = distLawSortFueled fuel w' := by rw [distLawSortFueled, h]

/-- Equation lemma: a fueled step on a sorted word is a no-op. -/
theorem distLawSortFueled_stepNone {w : List DistLawColour} {fuel : Nat}
    (h : distLawBubbleStep w = none) :
    distLawSortFueled (fuel + 1) w = w := by rw [distLawSortFueled, h]

/-! ## Termination — each step strictly decreases the inversion count -/

/-- Arithmetic helper: `a + b = 0` forces `a = 0` (case on `b`, since `Nat.add` recurses on its second
argument; propext-clean via `nomatch` on the successor case). -/
theorem distLawAddEqZeroLeft {a b : Nat} (h : a + b = 0) : a = 0 := by
  cases b with
  | zero => exact h
  | succ k => nomatch h

/-- Count preservation: a bubble step preserves the `t` count. -/
theorem distLawCountT_step {w w' : List DistLawColour} (h : distLawBubbleStep w = some w') :
    distLawCountT w = distLawCountT w' := by
  induction w generalizing w' with
  | nil => nomatch h
  | cons head rest ih =>
    cases head with
    | t =>
      cases hb : distLawBubbleStep rest with
      | none => rw [distLawBubbleStep_tHead, hb] at h; nomatch h
      | some rest' =>
        have step : distLawCountT rest = distLawCountT rest' := ih hb
        have he : distLawBubbleStep (DistLawColour.t :: rest) = some (DistLawColour.t :: rest') := by
          rw [distLawBubbleStep_tHead, hb]
        have hw : w' = DistLawColour.t :: rest' := Option.some.inj (h.symm.trans he)
        subst hw; exact congrArg (· + 1) step
    | s =>
      cases rest with
      | nil => nomatch h
      | cons head2 tail =>
        cases head2 with
        | t =>
          have hw : w' = DistLawColour.t :: DistLawColour.s :: tail :=
            Option.some.inj (h.symm.trans (distLawBubbleStep_stHead tail))
          subst hw; rfl
        | s =>
          cases hb : distLawBubbleStep (DistLawColour.s :: tail) with
          | none => rw [distLawBubbleStep_ssHead, hb] at h; nomatch h
          | some rest' =>
            have step : distLawCountT (DistLawColour.s :: tail) = distLawCountT rest' := ih hb
            have he : distLawBubbleStep (DistLawColour.s :: DistLawColour.s :: tail)
                = some (DistLawColour.s :: rest') := by rw [distLawBubbleStep_ssHead, hb]
            have hw : w' = DistLawColour.s :: rest' := Option.some.inj (h.symm.trans he)
            subst hw; exact step

/-- Count preservation: a bubble step preserves the `s` count. -/
theorem distLawCountS_step {w w' : List DistLawColour} (h : distLawBubbleStep w = some w') :
    distLawCountS w = distLawCountS w' := by
  induction w generalizing w' with
  | nil => nomatch h
  | cons head rest ih =>
    cases head with
    | t =>
      cases hb : distLawBubbleStep rest with
      | none => rw [distLawBubbleStep_tHead, hb] at h; nomatch h
      | some rest' =>
        have step : distLawCountS rest = distLawCountS rest' := ih hb
        have he : distLawBubbleStep (DistLawColour.t :: rest) = some (DistLawColour.t :: rest') := by
          rw [distLawBubbleStep_tHead, hb]
        have hw : w' = DistLawColour.t :: rest' := Option.some.inj (h.symm.trans he)
        subst hw; exact step
    | s =>
      cases rest with
      | nil => nomatch h
      | cons head2 tail =>
        cases head2 with
        | t =>
          have hw : w' = DistLawColour.t :: DistLawColour.s :: tail :=
            Option.some.inj (h.symm.trans (distLawBubbleStep_stHead tail))
          subst hw; rfl
        | s =>
          cases hb : distLawBubbleStep (DistLawColour.s :: tail) with
          | none => rw [distLawBubbleStep_ssHead, hb] at h; nomatch h
          | some rest' =>
            have step : distLawCountS (DistLawColour.s :: tail) = distLawCountS rest' := ih hb
            have he : distLawBubbleStep (DistLawColour.s :: DistLawColour.s :: tail)
                = some (DistLawColour.s :: rest') := by rw [distLawBubbleStep_ssHead, hb]
            have hw : w' = DistLawColour.s :: rest' := Option.some.inj (h.symm.trans he)
            subst hw; exact congrArg (· + 1) step

/-- ★ **THE TERMINATION LEMMA** — a bubble step strictly decreases the inversion count by exactly one.  Since
`distLawInversions` is a `Nat`, the sort therefore terminates in at most `inversions w` steps.  The `s.t`
head case is where the swap removes exactly one inversion; the `s.s` case chains the inductive hypothesis
across the preserved `t` count. -/
theorem distLawInversions_step {w w' : List DistLawColour} (h : distLawBubbleStep w = some w') :
    distLawInversions w = distLawInversions w' + 1 := by
  induction w generalizing w' with
  | nil => nomatch h
  | cons head rest ih =>
    cases head with
    | t =>
      cases hb : distLawBubbleStep rest with
      | none => rw [distLawBubbleStep_tHead, hb] at h; nomatch h
      | some rest' =>
        have step : distLawInversions rest = distLawInversions rest' + 1 := ih hb
        have he : distLawBubbleStep (DistLawColour.t :: rest) = some (DistLawColour.t :: rest') := by
          rw [distLawBubbleStep_tHead, hb]
        have hw : w' = DistLawColour.t :: rest' := Option.some.inj (h.symm.trans he)
        subst hw; exact step
    | s =>
      cases rest with
      | nil => nomatch h
      | cons head2 tail =>
        cases head2 with
        | t =>
          have hw : w' = DistLawColour.t :: DistLawColour.s :: tail :=
            Option.some.inj (h.symm.trans (distLawBubbleStep_stHead tail))
          subst hw
          show distLawCountT tail + 1 + distLawInversions tail
              = distLawCountT tail + distLawInversions tail + 1
          exact Nat.add_right_comm (distLawCountT tail) 1 (distLawInversions tail)
        | s =>
          cases hb : distLawBubbleStep (DistLawColour.s :: tail) with
          | none => rw [distLawBubbleStep_ssHead, hb] at h; nomatch h
          | some rest' =>
            have hct : distLawCountT (DistLawColour.s :: tail) = distLawCountT rest' :=
              distLawCountT_step hb
            have hiv : distLawInversions (DistLawColour.s :: tail) = distLawInversions rest' + 1 := ih hb
            have he : distLawBubbleStep (DistLawColour.s :: DistLawColour.s :: tail)
                = some (DistLawColour.s :: rest') := by rw [distLawBubbleStep_ssHead, hb]
            have hw : w' = DistLawColour.s :: rest' := Option.some.inj (h.symm.trans he)
            subst hw
            show distLawCountT (DistLawColour.s :: tail) + distLawInversions (DistLawColour.s :: tail)
                = distLawCountT rest' + distLawInversions rest' + 1
            rw [hct, hiv, Nat.add_assoc]

/-! ## Convergence — the sort reaches the normal form -/

/-- A sorted word (no redex) has zero inversions. -/
theorem distLawBubbleNone_inversionsZero {w : List DistLawColour}
    (h : distLawBubbleStep w = none) : distLawInversions w = 0 := by
  induction w with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | t =>
      cases hb : distLawBubbleStep rest with
      | some rest' => rw [distLawBubbleStep_tHead, hb] at h; nomatch h
      | none => show distLawInversions rest = 0; exact ih hb
    | s =>
      cases rest with
      | nil => rfl
      | cons head2 tail =>
        cases head2 with
        | t => rw [distLawBubbleStep_stHead] at h; nomatch h
        | s =>
          cases hb : distLawBubbleStep (DistLawColour.s :: tail) with
          | some rest' => rw [distLawBubbleStep_ssHead, hb] at h; nomatch h
          | none =>
            have hiv : distLawInversions (DistLawColour.s :: tail) = 0 := ih hb
            show distLawCountT tail + distLawInversions (DistLawColour.s :: tail) = 0
            rw [distLawAddEqZeroLeft hiv, hiv]

/-- A word with no `t`s is `s^(countS w)`. -/
theorem distLawAllColourS_ofCountTZero {w : List DistLawColour} (h : distLawCountT w = 0) :
    w = distLawSPower (distLawCountS w) := by
  induction w with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | t => nomatch h
    | s =>
      have hrest : rest = distLawSPower (distLawCountS rest) := ih h
      show DistLawColour.s :: rest = distLawSPower (distLawCountS rest + 1)
      show DistLawColour.s :: rest = DistLawColour.s :: distLawSPower (distLawCountS rest)
      exact congrArg (DistLawColour.s :: ·) hrest

/-- A word with zero inversions IS its normal form (already sorted). -/
theorem distLawInversionsZero_eqNf {w : List DistLawColour} (h : distLawInversions w = 0) :
    w = distLawNf w := by
  induction w with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | t =>
      have hrest : rest = distLawNf rest := ih h
      show DistLawColour.t :: rest = distLawTThenS (distLawCountT rest + 1) (distLawCountS rest)
      show DistLawColour.t :: rest
          = DistLawColour.t :: distLawTThenS (distLawCountT rest) (distLawCountS rest)
      exact congrArg (DistLawColour.t :: ·) hrest
    | s =>
      have hct0 : distLawCountT rest = 0 := distLawAddEqZeroLeft h
      have hrest : rest = distLawSPower (distLawCountS rest) := distLawAllColourS_ofCountTZero hct0
      show DistLawColour.s :: rest = distLawTThenS (distLawCountT rest) (distLawCountS rest + 1)
      rw [hct0]
      show DistLawColour.s :: rest = DistLawColour.s :: distLawSPower (distLawCountS rest)
      exact congrArg (DistLawColour.s :: ·) hrest

/-- A bubble step preserves the normal form (the counts are preserved). -/
theorem distLawNf_step {w w' : List DistLawColour} (h : distLawBubbleStep w = some w') :
    distLawNf w = distLawNf w' := by
  show distLawTThenS (distLawCountT w) (distLawCountS w)
      = distLawTThenS (distLawCountT w') (distLawCountS w')
  rw [distLawCountT_step h, distLawCountS_step h]

/-- ★★ **THE SORT REACHES THE NORMAL FORM.**  With `fuel = inversions w` (the exact termination budget), the
fueled bubble sort of `w` equals its sorted normal form `t^m s^n`.  Structural induction on the fuel: the base
case is the already-sorted word (zero inversions); the step case fires a redex (which decreases inversions,
preserves the normal form) and recurses. -/
theorem distLawSortReachesNf :
    ∀ (fuel : Nat) (w : List DistLawColour),
      distLawInversions w = fuel → distLawSortFueled fuel w = distLawNf w
  | 0, w, h => distLawInversionsZero_eqNf h
  | k + 1, w, h => by
      cases hb : distLawBubbleStep w with
      | none => rw [distLawBubbleNone_inversionsZero hb] at h; nomatch h
      | some w' =>
          have hinv : distLawInversions w' = k := Nat.succ.inj ((distLawInversions_step hb).symm.trans h)
          rw [distLawSortFueled_stepSome hb, distLawSortReachesNf k w' hinv, distLawNf_step hb]

/-- The sort with its own inversion count as fuel reaches the normal form (the clean corollary). -/
theorem distLawSortReachesNf_atInversions (w : List DistLawColour) :
    distLawSortFueled (distLawInversions w) w = distLawNf w :=
  distLawSortReachesNf (distLawInversions w) w rfl

/-! ## Confluence — the normal form is unique and terminal (orthogonal pure swap) -/

/-- `s^n` has no `t`s. -/
theorem distLawCountT_sPower : ∀ n : Nat, distLawCountT (distLawSPower n) = 0
  | 0 => rfl
  | n + 1 => by show distLawCountT (distLawSPower n) = 0; exact distLawCountT_sPower n

/-- `s^n` has zero inversions. -/
theorem distLawInversions_sPower : ∀ n : Nat, distLawInversions (distLawSPower n) = 0
  | 0 => rfl
  | n + 1 => by
      show distLawCountT (distLawSPower n) + distLawInversions (distLawSPower n) = 0
      rw [distLawCountT_sPower n, distLawInversions_sPower n]

/-- `t^m s^n` has zero inversions (all `t`s precede all `s`s). -/
theorem distLawInversions_tThenS : ∀ (numT numS : Nat), distLawInversions (distLawTThenS numT numS) = 0
  | 0, numS => distLawInversions_sPower numS
  | numT + 1, numS => by
      show distLawInversions (distLawTThenS numT numS) = 0; exact distLawInversions_tThenS numT numS

/-- ★ **The normal form is TERMINAL** — `distLawNf w` has zero inversions, so no bubble step applies.  The
orthogonal pure-swap system's normal form is a genuine fixed point of the rewrite. -/
theorem distLawInversions_nf (w : List DistLawColour) : distLawInversions (distLawNf w) = 0 :=
  distLawInversions_tThenS (distLawCountT w) (distLawCountS w)

/-- ★ **CONFLUENCE / UNIQUENESS OF THE NORMAL FORM** — two words with equal letter counts have the SAME
normal form.  Since every rewrite step preserves counts and reaches the count-determined normal form, the
pure-swap system is confluent: the normal form is unique (a function of `(countT, countS)` only). -/
theorem distLawSortConfluent {w1 w2 : List DistLawColour}
    (hT : distLawCountT w1 = distLawCountT w2) (hS : distLawCountS w1 = distLawCountS w2) :
    distLawNf w1 = distLawNf w2 := by
  show distLawTThenS (distLawCountT w1) (distLawCountS w1)
      = distLawTThenS (distLawCountT w2) (distLawCountS w2)
  rw [hT, hS]

/-! ## B3 — the 1-cell word problem convertibility and its decision -/

/-- ★ The **1-cell word convertibility** generated by the swap: swap an adjacent `s.t <-> t.s` at the head
(`swapHere`), closed under cons-congruence (a swap under a context), reflexivity, symmetry, and transitivity.
Its symmetric closure makes `s` and `t` commute, so it is the free-commutative-monoid equivalence on
`{s, t}`.  `++`-free (cons-only) so no `List.append` propext trap. -/
inductive DistLawWordConv : List DistLawColour → List DistLawColour → Prop where
  /-- Swap an adjacent `s.t` to `t.s` at the head, over any suffix. -/
  | swapHere (post : List DistLawColour) :
      DistLawWordConv (DistLawColour.s :: DistLawColour.t :: post)
        (DistLawColour.t :: DistLawColour.s :: post)
  /-- Congruence: a convertibility holds under a prefixed colour. -/
  | consCongr (colour : DistLawColour) {a b : List DistLawColour} :
      DistLawWordConv a b → DistLawWordConv (colour :: a) (colour :: b)
  /-- Reflexivity. -/
  | refl (w : List DistLawColour) : DistLawWordConv w w
  /-- Symmetry. -/
  | symm {a b : List DistLawColour} : DistLawWordConv a b → DistLawWordConv b a
  /-- Transitivity. -/
  | trans {a b c : List DistLawColour} : DistLawWordConv a b → DistLawWordConv b c → DistLawWordConv a c

/-- ★ **SOUNDNESS OF THE DECISION** — convertible words have equal letter counts (the swap preserves both
counts, and congruence / refl / symm / trans propagate the equalities). -/
theorem distLawSameCount_ofConv {w1 w2 : List DistLawColour} (hconv : DistLawWordConv w1 w2) :
    distLawCountT w1 = distLawCountT w2 ∧ distLawCountS w1 = distLawCountS w2 := by
  induction hconv with
  | swapHere post => exact ⟨rfl, rfl⟩
  | consCongr colour _ ih =>
      cases colour with
      | s => exact ⟨ih.1, congrArg (· + 1) ih.2⟩
      | t => exact ⟨congrArg (· + 1) ih.1, ih.2⟩
  | refl w => exact ⟨rfl, rfl⟩
  | symm _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩

/-- Each bubble step is a convertibility step (the head swap is `swapHere`, the recursive descents are
`consCongr`). -/
theorem distLawBubbleStep_conv {w w' : List DistLawColour} (h : distLawBubbleStep w = some w') :
    DistLawWordConv w w' := by
  induction w generalizing w' with
  | nil => nomatch h
  | cons head rest ih =>
    cases head with
    | t =>
      cases hb : distLawBubbleStep rest with
      | none => rw [distLawBubbleStep_tHead, hb] at h; nomatch h
      | some rest' =>
        have step : DistLawWordConv rest rest' := ih hb
        have he : distLawBubbleStep (DistLawColour.t :: rest) = some (DistLawColour.t :: rest') := by
          rw [distLawBubbleStep_tHead, hb]
        have hw : w' = DistLawColour.t :: rest' := Option.some.inj (h.symm.trans he)
        subst hw; exact DistLawWordConv.consCongr DistLawColour.t step
    | s =>
      cases rest with
      | nil => nomatch h
      | cons head2 tail =>
        cases head2 with
        | t =>
          have hw : w' = DistLawColour.t :: DistLawColour.s :: tail :=
            Option.some.inj (h.symm.trans (distLawBubbleStep_stHead tail))
          subst hw; exact DistLawWordConv.swapHere tail
        | s =>
          cases hb : distLawBubbleStep (DistLawColour.s :: tail) with
          | none => rw [distLawBubbleStep_ssHead, hb] at h; nomatch h
          | some rest' =>
            have step : DistLawWordConv (DistLawColour.s :: tail) rest' := ih hb
            have he : distLawBubbleStep (DistLawColour.s :: DistLawColour.s :: tail)
                = some (DistLawColour.s :: rest') := by rw [distLawBubbleStep_ssHead, hb]
            have hw : w' = DistLawColour.s :: rest' := Option.some.inj (h.symm.trans he)
            subst hw; exact DistLawWordConv.consCongr DistLawColour.s step

/-- A word is convertible to any fueled-sort of itself (each step is a convertibility step). -/
theorem distLawConv_toSortFueled :
    ∀ (fuel : Nat) (w : List DistLawColour), DistLawWordConv w (distLawSortFueled fuel w)
  | 0, w => DistLawWordConv.refl w
  | k + 1, w => by
      cases hb : distLawBubbleStep w with
      | none => rw [distLawSortFueled_stepNone hb]; exact DistLawWordConv.refl w
      | some w' =>
          rw [distLawSortFueled_stepSome hb]
          exact DistLawWordConv.trans (distLawBubbleStep_conv hb) (distLawConv_toSortFueled k w')

/-- ★ A word is convertible to its normal form (the sort is a chain of convertibility steps). -/
theorem distLawConv_toNf (w : List DistLawColour) : DistLawWordConv w (distLawNf w) :=
  (distLawSortReachesNf_atInversions w) ▸ (distLawConv_toSortFueled (distLawInversions w) w)

/-- ★ **COMPLETENESS OF THE DECISION** — words with equal letter counts ARE convertible (each is convertible
to its normal form; equal counts give equal normal forms; compose through the shared normal form). -/
theorem distLawConv_ofSameCount {w1 w2 : List DistLawColour}
    (hT : distLawCountT w1 = distLawCountT w2) (hS : distLawCountS w1 = distLawCountS w2) :
    DistLawWordConv w1 w2 := by
  have hnf : distLawNf w1 = distLawNf w2 := distLawSortConfluent hT hS
  exact DistLawWordConv.trans (hnf ▸ distLawConv_toNf w1) (DistLawWordConv.symm (distLawConv_toNf w2))

/-- ★ The **decision predicate**: two words have the same letter counts.  Decidable (via `Nat.decEq`); by
`distLawConv_iffSameCount` it decides `DistLawWordConv`. -/
def DistLawWordSameCount (w1 w2 : List DistLawColour) : Prop :=
  distLawCountT w1 = distLawCountT w2 ∧ distLawCountS w1 = distLawCountS w2

/-- The decision predicate is decidable (conjunction of `Nat` equalities). -/
instance (w1 w2 : List DistLawColour) : Decidable (DistLawWordSameCount w1 w2) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- ★★ **THE 1-CELL WORD PROBLEM DECISION.**  Convertibility under the swap-generated congruence is EQUIVALENT
to same-letter-counts — a decidable predicate.  This is the decision the recon adjudicated as landable at r1
(the pure-swap 1-cell theory decides; the full 2-cell theory is walled). -/
theorem distLawConv_iffSameCount (w1 w2 : List DistLawColour) :
    DistLawWordConv w1 w2 ↔ DistLawWordSameCount w1 w2 :=
  ⟨fun hconv => distLawSameCount_ofConv hconv, fun hsc => distLawConv_ofSameCount hsc.1 hsc.2⟩

/-! ## Both verdicts on concrete word pairs -/

/-- The word `s.t`. -/
def distLawWordST : List DistLawColour := [DistLawColour.s, DistLawColour.t]

/-- The word `t.s`. -/
def distLawWordTS : List DistLawColour := [DistLawColour.t, DistLawColour.s]

/-- The word `s.s.t`. -/
def distLawWordSST : List DistLawColour := [DistLawColour.s, DistLawColour.s, DistLawColour.t]

/-- ★ **THE YES VERDICT** — `s.t` IS convertible to `t.s` (one swap).  Exercises the decision's positive
outcome on a concrete pair. -/
theorem distLawWordDecisionYes : DistLawWordConv distLawWordST distLawWordTS :=
  DistLawWordConv.swapHere []

/-- ★ **THE NO VERDICT** — `s.s.t` is NOT convertible to `s.t` (different `s` counts, `2 != 1`, refuted by the
count invariant).  Exercises the decision's negative outcome on a concrete pair. -/
theorem distLawWordDecisionNo : ¬ DistLawWordConv distLawWordSST distLawWordST := by
  intro hconv
  have hcount : distLawCountS distLawWordSST = distLawCountS distLawWordST :=
    (distLawSameCount_ofConv hconv).2
  exact Nat.noConfusion (Nat.succ.inj hcount)

/-! ## The bridge to the presentation carrier (NAMED realization) -/

/-- Realize a colour as its 1-cell generator over the presentation computad. -/
def distLawColourGen : DistLawColour → CellExpr distLawOmegaComputad 1
  | DistLawColour.s => distLawSGen
  | DistLawColour.t => distLawTGen

/-- ★ **The bridge to the presentation carrier** — realize a `{s, t}`-word as a right-nested vertical
composite of colour generators (ending in the identity 1-cell).  Ties the combinatorial sort model to the
`CellExpr distLawOmegaComputad 1` carrier of `WalkingDistLawPresentation.lean`; the swap 2-cell
`distLawSwapGen` realizes the bubble step on the canonical `s.t`/`t.s` (NAMED correspondence). -/
def distLawWordToCell : List DistLawColour → CellExpr distLawOmegaComputad 1
  | [] => distLawIdOne
  | colour :: rest => CellExpr.vcomp (distLawColourGen colour) (distLawWordToCell rest)

/-! ## Non-vacuity probes -/

#eval distLawInversions distLawWordSST
#eval distLawInversions distLawWordST
#eval distLawCountS distLawWordSST
#eval decide (DistLawWordSameCount distLawWordST distLawWordTS)
#eval decide (DistLawWordSameCount distLawWordSST distLawWordST)
#eval cellSize (distLawWordToCell distLawWordST)

/-! ## The honesty markers -/

/-- ★ **ESTABLISHED (B2).**  The walking distributive law's 1-cell theory sorts to `t^m s^n` by a swap bubble
sort (`distLawBubbleStep` / `distLawSortFueled`) with termination by an inversion count that each step
strictly decreases (`distLawInversions_step`), reaching the normal form on structural fuel
(`distLawSortReachesNf`).  Confluence is orthogonal: the normal form is unique (`distLawSortConfluent`) and
terminal (`distLawInversions_nf`).  `= true`. -/
def fxDistLaw_oneCellSortedNormalFormShipped : Bool := true

/-- ★ **ESTABLISHED (B3).**  The 1-cell word problem is DECIDED: convertibility under the swap-generated
congruence is equivalent to same-letter-counts (`distLawConv_iffSameCount`), a decidable predicate.  BOTH
verdicts are exercised on concrete word pairs — `distLawWordDecisionYes` (`s.t ~ t.s`) and
`distLawWordDecisionNo` (`s.s.t` NOT `~ s.t`).  `= true`. -/
def fxDistLaw_oneCellWordProblemDecided : Bool := true

/-- ★ **WALL (honest, restated at the sort layer).**  `= false` records that the 1-cell decision does NOT lift
to the full 2-cell word problem: the pure-swap 1-cell theory is the free commutative monoid on `{s, t}`
(Parikh-vector equality), but the 2-cell Beck axioms genuinely interact, so the full decision is walled at the
two-colour monotone-map model (`fxDistLaw_fullTwoCellDecisionWalledAtTwoColourMonotoneMap` in
`WalkingDistLawPresentation.lean`).  The shipped content is the 1-cell sort + decision, not the 2-cell
decision. -/
def fxDistLaw_oneCellDecisionDoesNotLiftToTwoCell : Bool := false

end FX1Poly.Polygraph.Omega
