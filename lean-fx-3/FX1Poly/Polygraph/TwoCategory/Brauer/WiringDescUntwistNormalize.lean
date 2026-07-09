import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescInsertion

/-! # WP-BRAUER terminal T1 — untwist NORMALIZATION: the redex finder + the fueled fold + output redex-freeness

The r12 pivot (`Brauer/WiringDescInsertion.lean`) shipped the two Lehrer–Zhang untwist rows as
length-DECREASING context rewrites (`cupUntwist_inContext` / `capUntwist_inContext`, each `2` atoms → `1`,
`untwist_rewrite_lengthDrops`).  It named the SCANNER + FUEL assembling the full untwist normal form as the next
round.  This file lands exactly that assembly — and NOTHING beyond the honest, length-founded fragment:

  * **`findUntwistRedex`** — a structural leftmost-redex scanner over the word.  It fires on the two adjacent,
    same-position patterns the untwist rows fire on (`[cupAt p, crossingAt p]` and `[crossingAt p, capAt p]`),
    returning the canonical decomposition `(prefix, kind, position, suffix)` so the fold feeds the r12 kit with
    ZERO index arithmetic.  Written with the DEPENDENT-if on the DecidableEq-derived wiring equality (never `==`),
    so its scan-soundness reconstruction is propext-free (`Decidable.rec`, structure-eta) — the recon's care-point.
  * **`untwistNormalize`** — the STRUCTURAL-on-fuel fold: at `0` return the word (redex-free once the fuel is
    seeded at the word length); at `fuel+1` scan, and on a hit `trans` the r12 in-context rewrite with the recursion
    at the length-dropped reduct.  Every rewrite is `2 → 1`, so seeding fuel at `w.length` always suffices.
  * **`untwistNormalize_conv`** — HYPOTHESIS-FREE convertibility: for ANY fuel and word, `w ~ untwistNormalize fuel w`
    in `BrauerConvFree7` (the seven-relation over-approximation), by fuel induction — each step is one shipped r12
    kit rewrite `trans`-composed with the IH, the base is reflexivity.
  * **`findUntwistRedex_untwistNormalize_none`** — the output is redex-free: seeded at `w.length` the scanner finds
    NO further redex in `untwistNormalize`'s output.  A SEPARATE fuel induction (the `some`-branch defers to the IH,
    so freeness is not readable off the fold's definition), on the `fuel ≥ w.length` invariant that the length-drop
    preserves.

## Honest scope — this is the untwist FRAGMENT only, not completeness

`untwistNormalize` removes every cup/crossing and crossing/cap adjacency; it does NOT sort cups above caps, and it
does NOT canonicalize the crossing (`S_n`) block — that block is the WALLED braid-ascent leaf
(`fxBrauer_hasBraidAscentLeafWalled`, `Brauer/WiringDescInsertion.lean`, Regime A definitive).  So this file flips
`fxBrauer_hasUntwistNormalization` and NOTHING above it: `fxBrauer_hasBrauerCompleteness` /
`fxBrauer_hasCrossingOnlyStraightening` / `fxBrauer_hasCrossingStraighteningInsertionResidual` stay `false`.  The
honest founding contrast is the r12 marker's own: the untwist measure is a plateau-free structural word length,
UNLIKE the crossing straightening whose `inversionCount` is frozen across the ascent.

Raw Lean 4 + Init; STRUCTURAL recursion (Nat fuel + list), no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The redex kind + the leftmost-redex scanner -/

/-- Which of the two untwist rows a found redex fires: `cup` for `[cupAt p, crossingAt p] ~ [cupAt p]`, `cap` for
`[crossingAt p, capAt p] ~ [capAt p]`.  A flat two-constructor tag. -/
inductive UntwistKind where
  /-- The cup untwist `σ ∘ cup = cup` — a crossing after a cup. -/
  | cup
  /-- The cap untwist `cap ∘ σ = cap` — a crossing before a cap. -/
  | cap

/-- ★ **The leftmost untwist redex.**  Scan the word for the first adjacent, same-position pair the untwist rows
fire on, returning `(prefix, kind, position, suffix)` so `w = prefix ++ (redex ++ suffix)` in canonical form.  The
DEPENDENT-if on the DecidableEq-derived wiring equality (never `==`) hands the field equalities to the soundness
proof directly.  Structural on the list — the `[]` / singleton guards make length `≤ 1` redex-free by `rfl`. -/
def findUntwistRedex :
    List BrauerAtom → Option (List BrauerAtom × UntwistKind × Nat × List BrauerAtom)
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if _ : first.wiring = cupWiring ∧ second.wiring = crossingWiring
           ∧ first.position = second.position then
        some ([], UntwistKind.cup, first.position, rest)
      else if _ : first.wiring = crossingWiring ∧ second.wiring = capWiring
           ∧ first.position = second.position then
        some ([], UntwistKind.cap, first.position, rest)
      else
        match findUntwistRedex (second :: rest) with
        | none => none
        | some (foundPrefix, foundKind, foundOffset, foundSuffix) =>
            some (first :: foundPrefix, foundKind, foundOffset, foundSuffix)

/-! ## Scan soundness — the found decomposition reconstructs the word (propext-free) -/

/-- ★ **Cup-redex scan soundness.**  If the scanner reports a `cup` redex `(prefix, cup, offset, suffix)`, the word
IS `prefix ++ (cupAt offset :: crossingAt offset :: suffix)`.  Structural on the word; at the firing base the
dependent-if hands `first.wiring = cupWiring`, `second.wiring = crossingWiring`, `first.position = second.position`,
and structure-eta closes `first = cupAt first.position`, `second = crossingAt first.position`. -/
theorem findUntwistRedex_cup_sound : (word foundPrefix foundSuffix : List BrauerAtom) → (foundOffset : Nat) →
    findUntwistRedex word = some (foundPrefix, UntwistKind.cup, foundOffset, foundSuffix) →
    word = foundPrefix ++ (cupAt foundOffset :: crossingAt foundOffset :: foundSuffix)
  | [], _, _, _, hyp => nomatch hyp
  | [_], _, _, _, hyp => nomatch hyp
  | first :: second :: rest, foundPrefix, foundSuffix, foundOffset, hyp => by
      dsimp only [findUntwistRedex] at hyp
      split at hyp
      · rename_i hFire
        obtain ⟨hCup, hCross, hPos⟩ := hFire
        injection hyp with hyp1
        injection hyp1 with ePrefix hyp2
        injection hyp2 with _eKind hyp3
        injection hyp3 with eOffset eSuffix
        subst ePrefix; subst eOffset; subst eSuffix
        cases first with
        | mk firstPos firstWiring =>
          cases second with
          | mk secondPos secondWiring =>
            subst hCup; subst hCross; subst hPos; rfl
      · split at hyp
        · injection hyp with hyp1
          injection hyp1 with _ePrefix hyp2
          injection hyp2 with eKind _hyp3
          exact UntwistKind.noConfusion eKind
        · split at hyp
          · nomatch hyp
          · rename_i innerPrefix innerKind innerOffset innerSuffix heqInner
            injection hyp with hyp1
            injection hyp1 with ePrefix hyp2
            injection hyp2 with eKind hyp3
            injection hyp3 with eOffset eSuffix
            subst eKind; subst eOffset; subst eSuffix; subst ePrefix
            exact congrArg (first :: ·)
              (findUntwistRedex_cup_sound (second :: rest) innerPrefix innerSuffix innerOffset heqInner)

/-- ★ **Cap-redex scan soundness.**  If the scanner reports a `cap` redex, the word IS
`prefix ++ (crossingAt offset :: capAt offset :: suffix)`.  Symmetric to the cup case. -/
theorem findUntwistRedex_cap_sound : (word foundPrefix foundSuffix : List BrauerAtom) → (foundOffset : Nat) →
    findUntwistRedex word = some (foundPrefix, UntwistKind.cap, foundOffset, foundSuffix) →
    word = foundPrefix ++ (crossingAt foundOffset :: capAt foundOffset :: foundSuffix)
  | [], _, _, _, hyp => nomatch hyp
  | [_], _, _, _, hyp => nomatch hyp
  | first :: second :: rest, foundPrefix, foundSuffix, foundOffset, hyp => by
      dsimp only [findUntwistRedex] at hyp
      split at hyp
      · injection hyp with hyp1
        injection hyp1 with _ePrefix hyp2
        injection hyp2 with eKind _hyp3
        exact UntwistKind.noConfusion eKind
      · split at hyp
        · rename_i hFire
          obtain ⟨hCross, hCap, hPos⟩ := hFire
          injection hyp with hyp1
          injection hyp1 with ePrefix hyp2
          injection hyp2 with _eKind hyp3
          injection hyp3 with eOffset eSuffix
          subst ePrefix; subst eOffset; subst eSuffix
          cases first with
          | mk firstPos firstWiring =>
            cases second with
            | mk secondPos secondWiring =>
              subst hCross; subst hCap; subst hPos; rfl
        · split at hyp
          · nomatch hyp
          · rename_i innerPrefix innerKind innerOffset innerSuffix heqInner
            injection hyp with hyp1
            injection hyp1 with ePrefix hyp2
            injection hyp2 with eKind hyp3
            injection hyp3 with eOffset eSuffix
            subst eKind; subst eOffset; subst eSuffix; subst ePrefix
            exact congrArg (first :: ·)
              (findUntwistRedex_cap_sound (second :: rest) innerPrefix innerSuffix innerOffset heqInner)

/-! ## The fueled fold -/

/-- ★ **Untwist normalization.**  STRUCTURAL on the `Nat` fuel: at `0` the word is returned (redex-free once fuel is
seeded at `w.length`); at `fuel+1` scan for the leftmost redex, and on a hit recurse at the length-dropped reduct
(the crossing after a cup / before a cap deleted).  Seed at `w.length` — each rewrite drops the length by `1`. -/
def untwistNormalize : Nat → List BrauerAtom → List BrauerAtom
  | 0, word => word
  | fuel + 1, word =>
      match findUntwistRedex word with
      | none => word
      | some (foundPrefix, UntwistKind.cup, foundOffset, foundSuffix) =>
          untwistNormalize fuel (foundPrefix ++ (cupAt foundOffset :: foundSuffix))
      | some (foundPrefix, UntwistKind.cap, foundOffset, foundSuffix) =>
          untwistNormalize fuel (foundPrefix ++ (capAt foundOffset :: foundSuffix))

/-- ★ **The untwist normal form** — the fold seeded with fuel equal to the word length (always enough, since every
rewrite drops the length by one). -/
def untwistNF (word : List BrauerAtom) : List BrauerAtom :=
  untwistNormalize word.length word

/-! ## Convertibility — the output is `BrauerConvFree7`-convertible to the input (hypothesis-free) -/

/-- ★★ **The fold is convertibility-sound (hypothesis-free).**  For ANY fuel and word,
`BrauerConvFree7 word (untwistNormalize fuel word)`.  Fuel induction: the base is reflexivity
(`ofFree (BrauerConvFree.refl _)`); each rewrite step `trans`-composes the shipped r12 in-context rewrite
(`cupUntwist_inContext` / `capUntwist_inContext`, after `findUntwistRedex_*_sound` names the word's shape) with the
IH at the reduct. -/
theorem untwistNormalize_conv : (fuel : Nat) → (word : List BrauerAtom) →
    BrauerConvFree7 word (untwistNormalize fuel word)
  | 0, word => BrauerConvFree7.ofFree (BrauerConvFree.refl word)
  | fuel + 1, word => by
      dsimp only [untwistNormalize]
      split
      · exact BrauerConvFree7.ofFree (BrauerConvFree.refl word)
      · rename_i foundPrefix foundOffset foundSuffix heq
        rw [findUntwistRedex_cup_sound word foundPrefix foundSuffix foundOffset heq]
        exact BrauerConvFree7.trans (cupUntwist_inContext foundPrefix foundSuffix foundOffset)
          (untwistNormalize_conv fuel (foundPrefix ++ (cupAt foundOffset :: foundSuffix)))
      · rename_i foundPrefix foundOffset foundSuffix heq
        rw [findUntwistRedex_cap_sound word foundPrefix foundSuffix foundOffset heq]
        exact BrauerConvFree7.trans (capUntwist_inContext foundPrefix foundSuffix foundOffset)
          (untwistNormalize_conv fuel (foundPrefix ++ (capAt foundOffset :: foundSuffix)))

/-- ★ **The normal form is convertible to its input** — the seeded specialization. -/
theorem untwistNF_conv (word : List BrauerAtom) : BrauerConvFree7 word (untwistNF word) :=
  untwistNormalize_conv word.length word

/-! ## Output redex-freeness -/

/-- The reduct KEEPING the first atom drops the word length by one (the cup case: `cupAt` kept, `crossingAt`
deleted).  Structural on the prefix. -/
private theorem lengthReductKeepFirst : (redexPrefix : List BrauerAtom) → (atomA atomB : BrauerAtom) →
    (redexSuffix : List BrauerAtom) →
    (redexPrefix ++ (atomA :: atomB :: redexSuffix)).length
      = (redexPrefix ++ (atomA :: redexSuffix)).length + 1
  | [], _, _, _ => rfl
  | _ :: rest, atomA, atomB, redexSuffix => congrArg (· + 1) (lengthReductKeepFirst rest atomA atomB redexSuffix)

/-- The reduct KEEPING the second atom drops the word length by one (the cap case: `capAt` kept, `crossingAt`
deleted).  Structural on the prefix. -/
private theorem lengthReductKeepSecond : (redexPrefix : List BrauerAtom) → (atomA atomB : BrauerAtom) →
    (redexSuffix : List BrauerAtom) →
    (redexPrefix ++ (atomA :: atomB :: redexSuffix)).length
      = (redexPrefix ++ (atomB :: redexSuffix)).length + 1
  | [], _, _, _ => rfl
  | _ :: rest, atomA, atomB, redexSuffix => congrArg (· + 1) (lengthReductKeepSecond rest atomA atomB redexSuffix)

/-- ★★ **The output is redex-free.**  When fuel meets or exceeds the word length, the scanner finds NO redex in
`untwistNormalize`'s output.  A SEPARATE fuel induction (the fold's `some`-branch returns the recursive result, so
freeness is the IH, not readable off the definition): the `fuel = 0` bound forces the empty word (`rfl`); at
`fuel+1` the `none` branch returns the already-scanned word, and each rewrite branch preserves the `≥` invariant via
the length drop (`lengthReductKeep*`) and defers to the IH. -/
theorem findUntwistRedex_untwistNormalize_none : (fuel : Nat) → (word : List BrauerAtom) →
    word.length ≤ fuel → findUntwistRedex (untwistNormalize fuel word) = none
  | 0, [], _ => rfl
  | 0, _ :: _, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | fuel + 1, word, hLe => by
      dsimp only [untwistNormalize]
      split
      · rename_i heqNone
        exact heqNone
      · rename_i foundPrefix foundOffset foundSuffix heq
        have hshape := findUntwistRedex_cup_sound word foundPrefix foundSuffix foundOffset heq
        have hbound : (foundPrefix ++ (cupAt foundOffset :: foundSuffix)).length ≤ fuel := by
          rw [hshape,
            lengthReductKeepFirst foundPrefix (cupAt foundOffset) (crossingAt foundOffset) foundSuffix] at hLe
          exact Nat.le_of_succ_le_succ hLe
        exact findUntwistRedex_untwistNormalize_none fuel
          (foundPrefix ++ (cupAt foundOffset :: foundSuffix)) hbound
      · rename_i foundPrefix foundOffset foundSuffix heq
        have hshape := findUntwistRedex_cap_sound word foundPrefix foundSuffix foundOffset heq
        have hbound : (foundPrefix ++ (capAt foundOffset :: foundSuffix)).length ≤ fuel := by
          rw [hshape,
            lengthReductKeepSecond foundPrefix (crossingAt foundOffset) (capAt foundOffset) foundSuffix] at hLe
          exact Nat.le_of_succ_le_succ hLe
        exact findUntwistRedex_untwistNormalize_none fuel
          (foundPrefix ++ (capAt foundOffset :: foundSuffix)) hbound

/-- ★ **The normal form is redex-free** — the seeded specialization (`fuel = word.length`). -/
theorem findUntwistRedex_untwistNF_none (word : List BrauerAtom) : findUntwistRedex (untwistNF word) = none :=
  findUntwistRedex_untwistNormalize_none word.length word (Nat.le_refl word.length)

/-! ## Non-vacuity on real words -/

/-- Non-vacuity — a single cup untwist normalizes: `[cupAt 0, crossingAt 0]` reduces to the bare cup. -/
theorem untwistNF_cup_single : untwistNF [cupAt 0, crossingAt 0] = [cupAt 0] := by decide

/-- Non-vacuity — a single cap untwist normalizes: `[crossingAt 0, capAt 0]` reduces to the bare cap. -/
theorem untwistNF_cap_single : untwistNF [crossingAt 0, capAt 0] = [capAt 0] := by decide

/-- Non-vacuity — a CASCADE: `[cupAt 0, crossingAt 0, crossingAt 0]` untwists twice (the first rewrite re-exposes a
new cup/crossing adjacency the scanner then fires on), reaching the bare cup. -/
theorem untwistNF_cup_cascade : untwistNF [cupAt 0, crossingAt 0, crossingAt 0] = [cupAt 0] := by decide

/-- Non-vacuity — the scanner leaves a redex-free word ALONE: `[crossingAt 0]` (no adjacency) is its own normal
form, and a position-mismatched pair `[cupAt 0, crossingAt 1]` (DIFFERENT positions ⇒ NOT a redex, the
same-position guard load-bearing) is untouched. -/
theorem untwistNF_fixed_points :
    untwistNF [crossingAt 0] = [crossingAt 0]
      ∧ untwistNF [cupAt 0, crossingAt 1] = [cupAt 0, crossingAt 1] := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Non-vacuity — the redex-freeness certificate fires on a real reduced form. -/
theorem findUntwistRedex_untwistNF_cascade_none :
    findUntwistRedex (untwistNF [cupAt 0, crossingAt 0, crossingAt 0]) = none :=
  findUntwistRedex_untwistNF_none [cupAt 0, crossingAt 0, crossingAt 0]

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — WP-BRAUER terminal T1: untwist NORMALIZATION is SHIPPED.**  `findUntwistRedex` is the
structural leftmost-redex scanner for the two untwist adjacencies (`[cupAt p, crossingAt p]`,
`[crossingAt p, capAt p]`), written with the dependent-if on the DecidableEq wiring equality so its scan soundness
(`findUntwistRedex_cup_sound` / `findUntwistRedex_cap_sound`) is propext-free.  `untwistNormalize` is the
STRUCTURAL-on-fuel fold; `untwistNF` seeds it at the word length.  The fold is HYPOTHESIS-FREE convertibility-sound
(`untwistNormalize_conv` : `BrauerConvFree7 word (untwistNormalize fuel word)` for ANY fuel — each step a shipped
r12 in-context rewrite `trans` the IH) and its seeded output is redex-free (`findUntwistRedex_untwistNF_none`, via
the `fuel ≥ length` fuel induction with the `lengthReductKeep*` drop).  Non-vacuous on real words
(`untwistNF_cup_single` / `untwistNF_cap_single` / `untwistNF_cup_cascade` re-exposing a fresh redex /
`untwistNF_fixed_points` with the same-position guard load-bearing).  HONEST SCOPE: this is the untwist FRAGMENT —
it removes cup/crossing and crossing/cap adjacencies only, NOT the cups-above-caps sort and NOT the walled crossing
(`S_n`) block; `fxBrauer_hasBrauerCompleteness` / `fxBrauer_hasCrossingOnlyStraightening` stay `false`.  `= true`. -/
def fxBrauer_hasUntwistNormalization : Bool := true

end FX1Poly.Polygraph
