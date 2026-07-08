import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCases

/-! # WalkingMonad — WORD MULTIPLICATIVITY under whiskering (the two whisker `normalize` cases)

`WalkingMonad/MonadNormalizeCases` closed three of the six `normalizeCell` cases (`gen eta`, `gen mu`, `id`).  The
two WHISKER cases (`whiskerLeft W body`, `whiskerRight W body`) reduce — after the shipped `whiskerLeftCongr` /
`whiskerRightCongr` congruences thread the induction hypothesis — to WORD MULTIPLICATIVITY under whiskering:
whiskering a canonical Eilenberg–Zilber word by a `t`-power is convertible to the canonical word with the counts
list PREPENDED (left) / APPENDED (right) by a run of ones (each new strand hit exactly once, the identity block).

## What this file ships (each piece zero-axiom)

  * **`monadTPower_add`** — `t^(a+b) = t^a · t^b` (the ordinal-sum on `t`-powers; `composePath` associativity).
  * **`countsDomainPath_consReplicate_one`** — the domain 1-cell of a ones-prefixed word is `t^k`-prefixed.
  * **`wordFromCounts_consOne_conv`** — a leading `1`-gadget (`= id_t`) of a word peels to a left-`t`-whisker
    (`hcomp id_t W ≈ t ◁ W` — the shipped `wordFromCounts_monadOnes_succ_conv` pattern, generalized off `ones`).
  * ★ **`wordMul_whiskerLeft`** — `t^k ◁ (word counts) ≈ word (1^k ++ counts)`, structural induction on `k`
    (`whiskerLeftComp` splits `t^(k+1)`, the IH threads under a `t`-whisker, `wordFromCounts_consOne_conv` re-folds
    the leading `1`).  The LEFT whisker word multiplicativity — no monad law.

The RIGHT-whisker analog (`wordMul_whiskerRight`, appending a ones run via `whiskerRightVcomp` + `whiskerRightComp`
+ `whiskerExchange`) and the counts identity `countsOf_embedLocalMap_left` that lines the word up with `canon`, plus
the `vcomp` word multiplicativity (the `gadgetMerge` mu-tree amalgamation using the three monad laws), are the named
residuals — see the honesty markers.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion on
`Nat` (the whisker length) / `List Nat` (the counts).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## `t`-power ordinal sum + the ones-prefixed domain path -/

/-- ★ **`t^(a+b) = t^a · t^b`.**  The `t`-power is the free-monoid exponent; adding exponents is `composePath`
(`composePath_assoc` threads the `a+1` step).  Structural recursion on `a`. -/
theorem monadTPower_add : ∀ (a b : Nat),
    monadTPower (a + b) = composePath (monadTPower a) (monadTPower b)
  | 0, b => by rw [Nat.zero_add]; rfl
  | a + 1, b => by
      rw [Nat.succ_add]
      show composePath monadT (monadTPower (a + b))
        = composePath (composePath monadT (monadTPower a)) (monadTPower b)
      rw [monadTPower_add a b]
      exact (composePath_assoc monadT (monadTPower a) (monadTPower b)).symm

/-- The domain 1-cell of a `k`-ones-prefixed word is `t^k` prepended to the tail's domain.  Structural recursion on
`k` (the head `1`-gadget prepends one `t`; `composePath` associativity threads). -/
theorem countsDomainPath_consReplicate_one : ∀ (k : Nat) (counts : List Nat),
    countsDomainPath (consReplicate 1 k counts) = composePath (monadTPower k) (countsDomainPath counts)
  | 0, _ => rfl
  | k + 1, counts => by
      show composePath (monadTPower 1) (countsDomainPath (consReplicate 1 k counts))
        = composePath (monadTPower (k + 1)) (countsDomainPath counts)
      rw [countsDomainPath_consReplicate_one k counts]
      show composePath monadT (composePath (monadTPower k) (countsDomainPath counts))
        = composePath (composePath monadT (monadTPower k)) (countsDomainPath counts)
      exact (composePath_assoc monadT (monadTPower k) (countsDomainPath counts)).symm

/-! ## A leading `1`-gadget peels to a left-`t`-whisker -/

/-- ★ **A leading `1` of a word is a left-`t`-whisker.**  `wordFromCounts (1 :: rest)` — a horizontal composite
`hcomp id_t (wordFromCounts rest)` — reduces to `t ◁ wordFromCounts rest` by dropping the right-whisker identity
(`whiskerRightId`) and the left identity factor (`vcompIdLeft`).  The `wordFromCounts_monadOnes_succ_conv` pattern,
generalized to an arbitrary tail `rest`.  Pure free-2-category, no monad law. -/
theorem wordFromCounts_consOne_conv (rest : List Nat) :
    MonadSaturatedTwoCellConv (wordFromCounts (1 :: rest))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest)) := by
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest)))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft _
      (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT (countsDomainPath rest))))) ?_
  exact MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
    (TwoCellStep.vcompIdLeft (signature := monadModeSignature) _))

/-! ## The LEFT-whisker word multiplicativity -/

/-- The codomain 1-cell of a `k`-ones-prefixed word is `t^k · t^(counts.length)` — the boundary the LEFT whisker
by `t^k` produces on the codomain side.  `consReplicate` length + `monadTPower_add` (with an `add_comm`). -/
theorem monadTPower_length_consReplicate_one (k : Nat) (counts : List Nat) :
    monadTPower (consReplicate 1 k counts).length
      = composePath (monadTPower k) (monadTPower counts.length) := by
  rw [consReplicate_length, Nat.add_comm counts.length k, monadTPower_add]

/-- ★ **LEFT-whisker word multiplicativity.**  Whiskering the canonical word of `counts` on the left by `t^k` is
saturated-convertible to the canonical word of the `k`-ones-PREFIXED counts (the `k` new strands each hit their own
fresh target once — the identity block).  Structural induction on `k`: `k = 0` is the unit-1-cell whisker
(`whiskerLeftUnit`); the `k + 1` step splits `t^(k+1) = t · t^k` (`whiskerLeftComp`), threads the induction
hypothesis under a `t`-whisker (`whiskerLeftCongr`, pulling the boundary cast out via `whiskerLeft_castBoundary` and
fusing via `castBoundary_castBoundary`), and re-folds the leading `1` (`wordFromCounts_consOne_conv`).  The residual
boundary casts coincide by proof-irrelevance (same endpoints).  Pure free-2-category — no monad law. -/
theorem wordMul_whiskerLeft : ∀ (k : Nat) (counts : List Nat),
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower k) (wordFromCounts counts))
      (RawTwoCellExpr.castBoundary (countsDomainPath_consReplicate_one k counts)
        (monadTPower_length_consReplicate_one k counts)
        (wordFromCounts (consReplicate 1 k counts)))
  | 0, counts => MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (wordFromCounts counts))
  | k + 1, counts => by
      show MonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature)
          (composePath monadT (monadTPower k)) (wordFromCounts counts))
        (RawTwoCellExpr.castBoundary (countsDomainPath_consReplicate_one (k + 1) counts)
          (monadTPower_length_consReplicate_one (k + 1) counts)
          (wordFromCounts (consReplicate 1 (k + 1) counts)))
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftComp monadT (monadTPower k) (wordFromCounts counts))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.castBoundaryCongr _ _
          (MonadSaturatedTwoCellConv.whiskerLeftCongr monadT (wordMul_whiskerLeft k counts))) ?_
      rw [monadWhiskerLeft_castBoundary]
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.castBoundaryCongr _ _
          (MonadSaturatedTwoCellConv.castBoundaryCongr _ _
            (MonadSaturatedTwoCellConv.symm (wordFromCounts_consOne_conv (consReplicate 1 k counts))))) ?_
      rw [monadCastBoundary_castBoundary]
      exact MonadSaturatedTwoCellConv.refl _

/-! ## Honesty markers -/

/-- **ESTABLISHED — the LEFT-whisker WORD MULTIPLICATIVITY is CLOSED, zero-axiom.**  Whiskering the canonical
Eilenberg–Zilber word of `counts` on the left by a `t`-power `t^k` is `MonadSaturatedTwoCellConv`-convertible to the
canonical word of the `k`-ones-PREFIXED counts (`wordMul_whiskerLeft` — `t^k ◁ word counts ≈ word (1^k ++ counts)`),
using ONLY the completed free-strict-2-category laws (`whiskerLeftUnit`, `whiskerLeftComp`, `whiskerRightId`,
`vcompIdLeft` via `wordFromCounts_consOne_conv`) — no monad law.  This is the combinatorial heart of the `whiskerLeft`
`normalizeCell` case: the LEFT whisker prepends a run of identity strands, i.e. prepends a run of `1`s to the counts
vector.  `= true`. -/
def fxMonad_hasWordMulWhiskerLeft : Bool := true

/-- **Honesty marker — the RIGHT-whisker word multiplicativity, the counts-alignment, and the two whisker
`normalizeCell` cases are NOT yet assembled; the `vcomp` case is untouched.**  `wordMul_whiskerLeft` closes the
LEFT-whisker WORD-level multiplicativity.  What is NOT landed:

  * **`wordMul_whiskerRight`** — the RIGHT dual `t^k ▷ word counts ≈ word (counts ++ 1^k)` (append a ones run),
    provable by the same STRUCTURAL induction on `counts` via `whiskerRightVcomp` + `whiskerRightComp` +
    `whiskerExchange` + the counts-domain-path append identity (`countsDomainPath (consAppend a b) = cdp a · cdp b`)
    — no monad law, but the three whisker laws each carry a `composePath`-associativity boundary cast.
  * **`countsOf_embedLocalMap_left` / `_right`** — the counts-level identities lining the multiplicativity word up
    with `canon`: `countsOf (a+c) 0 (embedLocalMap a c 0 v) = 1^a ++ countsOf c 0 v` (and the right analog).  These
    plus `monadMonotoneMapOf_whiskerLeft` / `_whiskerRight` + the `oneCell = t^(oneCell.length)` boundary transport
    (`monadPath_normalForm`) assemble `wordMul_whisker*` into the two whisker `normalizeCell` cases
    `whiskerLeft/Right oneCell body ≈ canon (whiskerLeft/Right oneCell body)`.
  * **`wordMul_vcomp`** — the VERTICAL word multiplicativity (the `gadgetMerge` mu-tree amalgamation using all three
    monad laws), the faithfulness-weight brick, the SOLE `normalizeCell` case using the monad LAWS.

Until ALL five compound cases land (both whiskers assembled + `vcomp`), `normalize : MonadNormalizesToCanon` is not
inhabited, so `MonadSaturatedCanonicalization.convOfMapEq` is not inhabited and `fxMonad_hasMonotoneMapDecisionAssembled`
/ `fxMonad_hasConvOfMapEqNormalization` / `fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= false`. -/
def fxMonad_hasWordMulWhiskerRightAndVcomp : Bool := false

end FX1Poly.Polygraph
