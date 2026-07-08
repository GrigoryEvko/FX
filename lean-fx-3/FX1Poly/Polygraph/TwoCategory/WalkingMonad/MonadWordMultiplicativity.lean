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

/-! ## The RIGHT-whisker word multiplicativity: append a ones run

The RIGHT dual appends the identity strands at the TOP of the counts vector.  The induction is on `counts`: the
`whiskerRight (t^k)` passes THROUGH the head gadget's `hcomp = vcomp (whiskerRight _) (whiskerLeft _)` structure via
`whiskerRightVcomp` (distribute over the vcomp), `whiskerRightComp` (merge the two right whiskers on the gadget), and
`whiskerExchange` (swap the right whisker past the left whisker on the recursive word) — no `hcomp`-associativity, no
monad law. -/

/-- Cons-only append (no `List.append`, propext-safe): `consAppend a b` puts `b` after `a`. -/
def consAppend : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: consAppend xs ys

/-- `consAppend` length is additive. -/
theorem consAppend_length : ∀ (a b : List Nat), (consAppend a b).length = a.length + b.length
  | [], b => by show b.length = 0 + b.length; rw [Nat.zero_add]
  | x :: xs, b => by
      show (consAppend xs b).length + 1 = xs.length + 1 + b.length
      rw [consAppend_length xs b, Nat.succ_add]

/-- The domain 1-cell of an appended word is the `composePath` of the two domains.  Structural recursion on `a`
(`composePath` associativity threads the cons step). -/
theorem countsDomainPath_consAppend : ∀ (a b : List Nat),
    countsDomainPath (consAppend a b) = composePath (countsDomainPath a) (countsDomainPath b)
  | [], _ => rfl
  | x :: xs, b => by
      show composePath (monadTPower x) (countsDomainPath (consAppend xs b))
        = composePath (composePath (monadTPower x) (countsDomainPath xs)) (countsDomainPath b)
      rw [countsDomainPath_consAppend xs b]
      exact (composePath_assoc (monadTPower x) (countsDomainPath xs) (countsDomainPath b)).symm

/-- The domain 1-cell of a `k`-ones-APPENDED word is `(cdp counts) · t^k`. -/
theorem countsDomainPath_consAppend_ones (counts : List Nat) (k : Nat) :
    countsDomainPath (consAppend counts (monadOnes k))
      = composePath (countsDomainPath counts) (monadTPower k) := by
  rw [countsDomainPath_consAppend, countsDomainPath_monadOnes]

/-- The codomain 1-cell of a `k`-ones-APPENDED word is `t^(counts.length) · t^k`. -/
theorem monadTPower_length_consAppend_ones (counts : List Nat) (k : Nat) :
    monadTPower (consAppend counts (monadOnes k)).length
      = composePath (monadTPower counts.length) (monadTPower k) := by
  rw [consAppend_length, length_monadOnes, monadTPower_add]

/-! ## Honesty markers -/

/-- **ESTABLISHED — the LEFT-whisker WORD MULTIPLICATIVITY is CLOSED, zero-axiom.**  Whiskering the canonical
Eilenberg–Zilber word of `counts` on the left by a `t`-power `t^k` is `MonadSaturatedTwoCellConv`-convertible to the
canonical word of the `k`-ones-PREFIXED counts (`wordMul_whiskerLeft` — `t^k ◁ word counts ≈ word (1^k ++ counts)`),
using ONLY the completed free-strict-2-category laws (`whiskerLeftUnit`, `whiskerLeftComp`, `whiskerRightId`,
`vcompIdLeft` via `wordFromCounts_consOne_conv`) — no monad law.  This is the combinatorial heart of the `whiskerLeft`
`normalizeCell` case: the LEFT whisker prepends a run of identity strands, i.e. prepends a run of `1`s to the counts
vector.  `= true`. -/
def fxMonad_hasWordMulWhiskerLeft : Bool := true

/-- **Honesty marker — the RIGHT-whisker APPEND SKELETON is shipped; its multiplicativity, the counts-alignment,
and the whisker/`vcomp` `normalizeCell` cases are the named residuals.**  `wordMul_whiskerLeft` closes the
LEFT-whisker WORD-level multiplicativity, and the RIGHT-whisker path skeleton is SHIPPED zero-axiom: `consAppend`,
its length (`consAppend_length`), its domain-path homomorphism (`countsDomainPath_consAppend`), and the two
ones-appended boundary identities (`countsDomainPath_consAppend_ones : cdp (counts ++ 1^k) = cdp counts · t^k`,
`monadTPower_length_consAppend_ones`).  What is NOT landed:

  * **`wordMul_whiskerRight`** — the RIGHT dual `t^k ▷ word counts ≈ word (counts ++ 1^k)`, by STRUCTURAL induction
    on `counts`.  The head-gadget step passes `whiskerRight (t^k)` THROUGH `hcomp (gadget count) (word rest) =
    vcomp (whiskerRight _ (gadget count)) (whiskerLeft t (word rest))` via `whiskerRightVcomp` (distribute over the
    vcomp), `whiskerRightComp` (merge the two right whiskers on the gadget factor), and `whiskerExchange` (swap the
    right whisker past the left whisker on the recursive-word factor, then thread the IH under a `t`-whisker) — no
    monad law, but the SOLE remaining difficulty (beyond the whiskerLeft-style cast bookkeeping) is the VCOMP
    REASSEMBLY: the two per-factor `composePath`-associativity casts must extrude to the whole vertical composite
    (`RawTwoCellExpr.vcomp_castBoundaryLeft` + a right-factor analog) and reconcile with the head-gadget's stored
    right-context (the `countsDomainPath_consAppend_ones` left-factor path rewrite) — the exact exchange that blocks.
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
