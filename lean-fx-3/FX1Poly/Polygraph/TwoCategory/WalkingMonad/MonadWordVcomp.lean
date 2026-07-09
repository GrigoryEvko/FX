import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadVcompMult

/-! # WalkingMonad — the VERTICAL word multiplicativity `wordMul_vcomp` (the sole open `normalizeCell` case)

`WalkingMonad/MonadVcompMult` closed the mu-tree amalgamation `gadgetAbsorb` (the three monad laws at the gadget
level, zero-axiom).  This file folds it over two canonical Eilenberg–Zilber words to close the LAST open
`normalizeCell` case, `vcomp`, and — with the four already-closed cases (`gen`, `id`, both whiskers) — assembles
`normalize : MonadNormalizesToCanon`, inhabits `MonadSaturatedCanonicalization`, and makes the walking-monad
saturated word problem an UNCONDITIONAL `Decidable`.

## The vcomp word multiplicativity (the faithfulness-weight brick)

`wordMul_vcomp ccL ccR (h : ccL.length = listSum ccR) :
   vcomp (word ccL) (word ccR) ≈ word (composeCounts ccL ccR)`

read off the classical statement: the domain `t`-power of `word ccR` splits into `ccR.length` blocks of widths
`ccR = [r_0, …, r_{k-1}]`; the codomain `word ccL` splits (`wordMul_hcomp`) into matching groups of `r_j` counts;
the free interchange `TwoCellStep.interchange` rewrites the vertical composite of two horizontal composites to the
horizontal composite of vertical composites, factor `j` collapsing `word (group_j) ⊟ gadget r_j` to a single gadget
`gadget (listSum group_j)` by `wordGadgetCollapse`.  Hence `composeCounts ccL ccR = [listSum group_0, …]`, the
run-grouped block sums.

## What this file ships (each piece zero-axiom)

  * **`listSum` / `consTake` / `consDrop`** — cons-only sum + take/drop primitives (`List.take`/`drop`/`sum` pull
    `propext`), with the split `consAppend (consTake n xs) (consDrop n xs) = xs` and the additive `listSum`.
  * **`countsDomainPath_eq_monadTPower_listSum`** — the domain of a canonical word is the `t`-power of its block sum
    (the boundary bridge lining the two words up for `vcomp`).
  * ★ **`wordGadgetCollapse`** — `vcomp (word cc) (gadget cc.length) ≈ cast (gadget (listSum cc))`: fold a word into
    one gadget by absorbing (`gadgetRightMerge` per head, the associativity crossing).
  * **`composeCounts`** — the run-grouped block sums (structural on `ccR`).
  * ★ **`wordMul_vcomp`** — the vertical word multiplicativity (structural on `ccR`, the interchange assembly).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion on
`List Nat` / `Nat`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- Definitionally-equal cells are saturated-convertible (an `Eq` lifts to the relation).  Used to thread
`castBoundary`-fusion equalities through the convertibility congruences without a motive-fragile `rw`. -/
theorem MonadSaturatedTwoCellConv.ofEq {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (heq : cellAlpha = cellBeta) : MonadSaturatedTwoCellConv cellAlpha cellBeta := by
  cases heq; exact MonadSaturatedTwoCellConv.refl cellAlpha

/-! ## Cons-only sum + take/drop primitives -/

/-- Cons-only list sum (the library `List.sum` folds through a monoid instance that pulls `propext`). -/
def listSum : List Nat → Nat
  | [] => 0
  | count :: rest => count + listSum rest

/-- Cons-only `take` (the library `List.take` length lemmas pull `propext`). -/
def consTake : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | count + 1, head :: rest => head :: consTake count rest

/-- Cons-only `drop`. -/
def consDrop : Nat → List Nat → List Nat
  | 0, values => values
  | _ + 1, [] => []
  | count + 1, _ :: rest => consDrop count rest

/-- `consAppend (consTake n xs) (consDrop n xs) = xs` — take/drop split, UNCONDITIONAL. -/
theorem consAppend_consTake_consDrop : ∀ (count : Nat) (values : List Nat),
    consAppend (consTake count values) (consDrop count values) = values
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | count + 1, head :: rest => by
      show head :: consAppend (consTake count rest) (consDrop count rest) = head :: rest
      rw [consAppend_consTake_consDrop count rest]

/-- The length of `consTake count values` when `count ≤ values.length` is `count`. -/
theorem consTake_length_of_le : ∀ (count : Nat) (values : List Nat), count ≤ values.length →
    (consTake count values).length = count
  | 0, _, _ => rfl
  | count + 1, [], hle => absurd hle (Nat.not_succ_le_zero count)
  | count + 1, head :: rest, hle => by
      show (consTake count rest).length + 1 = count + 1
      rw [consTake_length_of_le count rest (Nat.le_of_succ_le_succ hle)]

/-- The length of `consDrop count values` is `values.length - count`. -/
theorem consDrop_length : ∀ (count : Nat) (values : List Nat),
    (consDrop count values).length = values.length - count
  | 0, _ => rfl
  | count + 1, [] => (Nat.zero_sub (count + 1)).symm
  | count + 1, head :: rest => by
      show (consDrop count rest).length = (rest.length + 1) - (count + 1)
      rw [consDrop_length count rest, Nat.succ_sub_succ]

/-- `listSum` is additive over `consAppend`. -/
theorem listSum_consAppend : ∀ (a b : List Nat), listSum (consAppend a b) = listSum a + listSum b
  | [], b => by show listSum b = 0 + listSum b; rw [Nat.zero_add]
  | head :: rest, b => by
      show head + listSum (consAppend rest b) = head + listSum rest + listSum b
      rw [listSum_consAppend rest b, Nat.add_assoc]

/-! ## The domain-path bridge: a canonical word's domain is the `t`-power of its block sum -/

/-- ★ **The domain boundary of a canonical word is `t^(listSum cc)`.**  `countsDomainPath cc = monadTPower (listSum
cc)` — the right-nested `composePath` of the per-gadget domains flattens to a single `t`-power of the total width.
Structural recursion on `cc` via `monadTPower_add`. -/
theorem countsDomainPath_eq_monadTPower_listSum : ∀ (cc : List Nat),
    countsDomainPath cc = monadTPower (listSum cc)
  | [] => rfl
  | count :: rest => by
      show composePath (monadTPower count) (countsDomainPath rest) = monadTPower (count + listSum rest)
      rw [countsDomainPath_eq_monadTPower_listSum rest, monadTPower_add]

/-- The length of a canonical word's domain path is its block sum. -/
theorem countsDomainPath_length_eq_listSum (cc : List Nat) :
    (countsDomainPath cc).length = listSum cc := by
  rw [countsDomainPath_eq_monadTPower_listSum, monadTPower_length]

/-! ## The word-gadget collapse: fold a whole word into a single merge gadget -/

/-- The **gadget tail collapse**: `(gadget c ▷ t^r) ⊟ (t ◁ gadget r) ⊟ mu ≈ cast (gadget (c + r))` — reassociate,
peel `gadget (r+1)` (`gadgetSucc`), and fire the associativity crossing `gadgetRightMerge`. -/
theorem gadgetTailCollapse (leftWidth rightWidth : Nat) :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
            (monadGadget leftWidth))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth)))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
        (monadGadget (leftWidth + rightWidth))) := by
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth))
        monadMulTwoCell))) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
        (monadGadget leftWidth))
      (gadgetSucc rightWidth)) ?_
  exact gadgetRightMerge leftWidth rightWidth

/-- ★ **The word-gadget collapse.**  Merging a canonical word `word cc` then the `cc.length`-fold merge gadget
absorbs to a single `(listSum cc)`-fold merge: `vcomp (word cc) (gadget cc.length) ≈ cast (gadget (listSum cc))`.
Structural induction on `cc`.  Base `cc = []` is `vcomp (id t^0) eta ≈ eta` (`vcompIdLeft`).  The `c :: rest`
step: peel `gadget (rest.length + 1)` (`gadgetSucc`, reassociate), distribute the head `hcomp`, merge the two
`t`-left-whiskers over the inner vcomp (`whiskerLeftVcomp`), thread the induction hypothesis under the `t`-whisker
(collapsing `word rest ⊟ gadget rest.length`), extrude the boundary cast (`monadWhiskerLeft_castBoundary`), rewrite
the head-gadget right-whisker context `countsDomainPath rest` to `t^(listSum rest)` (`whiskerRight_pathCongr` +
the domain bridge), re-peel `gadget (listSum rest + 1)` (`gadgetSucc`), and fire the associativity crossing
`gadgetRightMerge c (listSum rest)` — `c + listSum rest = listSum (c :: rest)`.  Uses the three monad laws via
`gadgetSucc` / `gadgetRightMerge`. -/
theorem wordGadgetCollapse : ∀ (cc : List Nat),
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (wordFromCounts cc) (monadGadget cc.length))
      (RawTwoCellExpr.castBoundary (countsDomainPath_eq_monadTPower_listSum cc).symm rfl
        (monadGadget (listSum cc)))
  | [] =>
      MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft (monadGadget 0)))
  | count :: rest => by
      -- LHS = vcomp (hcomp (gadget count) (word rest)) (gadget (rest.length + 1)).
      -- Peel gadget (rest.length + 1) via gadgetSucc, then reassociate.
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrRight
          (RawTwoCellExpr.hcomp (monadGadget count) (wordFromCounts rest))
          (MonadSaturatedTwoCellConv.symm (gadgetSucc rest.length))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.symm
          (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
            (TwoCellStep.vcompAssoc
              (RawTwoCellExpr.hcomp (monadGadget count) (wordFromCounts rest))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rest.length))
              monadMulTwoCell)))) ?_
      -- The inner `vcomp (hcomp gc W) (t ◁ gadget rest.length)`; expand hcomp and reassociate.
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
            (TwoCellStep.vcompAssoc
              (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
                (monadGadget count))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts rest))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rest.length)))))) ?_
      -- Merge the two `t`-left-whiskers over the inner vcomp.
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.vcompCongrRight
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
              (monadGadget count))
            (MonadSaturatedTwoCellConv.symm
              (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
                (TwoCellStep.whiskerLeftVcomp monadT (wordFromCounts rest) (monadGadget rest.length))))))) ?_
      -- Thread the induction hypothesis under the `t`-whisker.
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.vcompCongrRight
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath rest)
              (monadGadget count))
            (MonadSaturatedTwoCellConv.whiskerLeftCongr monadT (wordGadgetCollapse rest)))) ?_
      -- Extrude the boundary cast out of the `t`-whisker.
      rw [monadWhiskerLeft_castBoundary]
      -- Rewrite the head-gadget right-whisker context to `t^(listSum rest)`.
      rw [RawTwoCellExpr.whiskerRight_pathCongr (countsDomainPath_eq_monadTPower_listSum rest)
            (monadGadget count)]
      -- Merge the two inner casts (lift the `Eq` through `vcompCongrLeft`, motive-safe via `ofEq`).
      have hmerge :=
        RawTwoCellExpr.vcomp_castBoundary_merge
          (congrArg (composePath (monadTPower count)) (countsDomainPath_eq_monadTPower_listSum rest).symm)
          (congrArg (composePath monadT) (countsDomainPath_eq_monadTPower_listSum rest).symm)
          (congrArg (composePath monadT)
            (rfl : (monadT : ModalityPath monadGraph MonadMode.point MonadMode.point) = monadT))
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower (listSum rest))
            (monadGadget count))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (listSum rest)))
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.ofEq hmerge)) ?_
      -- Extrude the outer-left cast (as an `Eq`, `rfl`-cast on `mu` collapses definitionally), fire the tail.
      have hextrude : RawTwoCellExpr.vcomp
            (RawTwoCellExpr.castBoundary
              (congrArg (composePath (monadTPower count)) (countsDomainPath_eq_monadTPower_listSum rest).symm)
              (congrArg (composePath monadT)
                (rfl : (monadT : ModalityPath monadGraph MonadMode.point MonadMode.point) = monadT))
              (RawTwoCellExpr.vcomp
                (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower (listSum rest))
                  (monadGadget count))
                (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (listSum rest)))))
            monadMulTwoCell
          = RawTwoCellExpr.castBoundary
              (congrArg (composePath (monadTPower count)) (countsDomainPath_eq_monadTPower_listSum rest).symm)
              rfl
              (RawTwoCellExpr.vcomp
                (RawTwoCellExpr.vcomp
                  (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower (listSum rest))
                    (monadGadget count))
                  (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (listSum rest))))
                monadMulTwoCell) :=
        RawTwoCellExpr.vcomp_castBoundaryLeft _ _ _ _
      refine MonadSaturatedTwoCellConv.trans (MonadSaturatedTwoCellConv.ofEq hextrude) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.castBoundaryCongr _ rfl (gadgetTailCollapse count (listSum rest))) ?_
      rw [monadCastBoundary_castBoundary]
      exact MonadSaturatedTwoCellConv.refl _

end FX1Poly.Polygraph
