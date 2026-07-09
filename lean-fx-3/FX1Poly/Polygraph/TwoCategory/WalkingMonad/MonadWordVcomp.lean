import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadVcompMult

/-! # WalkingMonad — the word-gadget collapse + block-sum composition (toward `wordMul_vcomp`)

`WalkingMonad/MonadVcompMult` closed the mu-tree amalgamation `gadgetAbsorb` (the three monad laws at the gadget
level, zero-axiom).  Toward the LAST open `normalizeCell` case `vcomp` — the vertical word multiplicativity
`wordMul_vcomp : vcomp (word ccL) (word ccR) ≈ word (composeCounts ccL ccR)` — this file ships the per-block
collapse that fires on each block of the vertical composite, plus the block-sum composition data.

## The classical picture

The domain `t`-power of `word ccR` splits into `ccR.length` blocks of widths `ccR = [r_0, …, r_{k-1}]`; the codomain
`word ccL` splits (`wordMul_hcomp`) into matching groups of `r_j` counts; the free interchange
`TwoCellStep.interchange` rewrites the vertical composite of two horizontal composites to the horizontal composite of
vertical composites, factor `j` collapsing `word (group_j) ⊟ gadget r_j` to a single gadget `gadget (listSum
group_j)` by `wordGadgetCollapse`.  Hence `composeCounts ccL ccR = [listSum group_0, …]`, the run-grouped block sums.

## What this file ships (each piece zero-axiom)

  * **`listSum` / `consTake` / `consDrop`** — cons-only sum + take/drop primitives (`List.take`/`drop`/`sum` pull
    `propext`), with the split `consAppend (consTake n xs) (consDrop n xs) = xs` and the additive `listSum`.
  * **`countsDomainPath_eq_monadTPower_listSum`** — the domain of a canonical word is the `t`-power of its block sum
    (the boundary bridge lining the two words up for `vcomp`).
  * ★ **`wordGadgetCollapse`** — `vcomp (word cc) (gadget cc.length) ≈ cast (gadget (listSum cc))`: fold a word into
    one gadget by absorbing (`gadgetRightMerge` per head, the associativity crossing).  The monad-law-bearing
    per-block collapse.
  * **`composeCounts`** (+ `composeCounts_length`, `listSum_composeCounts`) — the run-grouped block sums.
  * **`wordMul_vcomp_hmid` / `wordMul_vcomp_hdom`** — the boundary-cast statements the vcomp step needs.

The assembly `wordMul_vcomp` itself (the multi-cast interchange re-sort) is the NAMED residual — see
`fxMonad_hasVcompWordMultiplicativity`.

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

/-! ## The LEFT-factor `hcomp` cast / congruence lemmas (the mirrors of the shipped RIGHT variants)

The `wordMul_vcomp` interchange assembly extrudes a boundary cast out of the LEFT `hcomp` factor and threads a
convertibility through the LEFT `hcomp` factor — the mirrors of the shipped `hcomp_castBoundaryRight` /
`hcompCongrRight` (whose Right factor was the whisker-in-context).  Left and right whiskering are the two partial
applications of the ONE horizontal-composition bifunctor (nLab: `bicategory`, `whiskering`), so each Right
coherence identity has a Left dual with no hidden asymmetry — the interchange IS that bifunctoriality. -/

/-- Pull a boundary cast out of the LEFT `hcomp` factor: a cast on the left factor's boundary becomes a cast of the
whole horizontal composite, the RIGHT whisker context `oneCellGDom` / `oneCellGCod` appended by `congrArg`.  The
LEFT mirror of `RawTwoCellExpr.hcomp_castBoundaryRight` (`cases`-collapse of the two seams; `cases hcod` is
load-bearing because the derived `hcomp`'s right whisker factor is gated by the LEFT factor's codomain). -/
theorem RawTwoCellExpr.hcomp_castBoundaryLeft {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFDom' oneCellFCod oneCellFCod' :
      ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (hdom : oneCellFDom = oneCellFDom') (hcod : oneCellFCod = oneCellFCod')
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    RawTwoCellExpr.hcomp (RawTwoCellExpr.castBoundary hdom hcod cellAlpha) cellBeta
      = RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCellGDom) hdom)
          (congrArg (fun path => composePath path oneCellGCod) hcod)
          (RawTwoCellExpr.hcomp cellAlpha cellBeta) := by
  cases hdom; cases hcod; rfl

/-- Congruence in the LEFT factor of a horizontal composite on the saturated relation: replacing the left factor by
a saturated-convertible (parallel) one gives a saturated-convertible horizontal composite.  `hcomp α β = vcomp
(whiskerRight β_dom α) (whiskerLeft α_cod β)`; the right `whiskerLeft` factor is unchanged (parallel `α` share a
codomain), the left `whiskerRight` factor threads the convertibility (`whiskerRightCongr`).  The LEFT mirror of
`MonadSaturatedTwoCellConv.hcompCongrRight`. -/
theorem MonadSaturatedTwoCellConv.hcompCongrLeft {sourceMode middleMode targetMode : MonadMode}
    {oneCellFDom oneCellFCod : ModalityPath monadModeSignature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath monadModeSignature.graph middleMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellFDom oneCellFCod}
    (conv : MonadSaturatedTwoCellConv cellAlpha cellAlpha')
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellGDom oneCellGCod) :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha' cellBeta) :=
  MonadSaturatedTwoCellConv.vcompCongrLeft _
    (MonadSaturatedTwoCellConv.whiskerRightCongr oneCellGDom conv)

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

/-- Left-cancellation of `Nat` subtraction, propext-clean (the library `Nat.add_sub_cancel` / `_left` pull
`propext`; this structural induction on the cancelled summand does not). -/
theorem natAddSubCancelLeft : ∀ (base offset : Nat), base + offset - base = offset
  | 0, offset => Nat.zero_add offset
  | base + 1, offset => by
      show base + 1 + offset - (base + 1) = offset
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeft base offset

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

/-- Taking exactly the first block back off a `consAppend` returns it. -/
theorem consTake_consAppend : ∀ (a b : List Nat), consTake a.length (consAppend a b) = a
  | [], _ => rfl
  | head :: rest, b => by
      show head :: consTake rest.length (consAppend rest b) = head :: rest
      rw [consTake_consAppend rest b]

/-- Dropping exactly the first block off a `consAppend` returns the second. -/
theorem consDrop_consAppend : ∀ (a b : List Nat), consDrop a.length (consAppend a b) = b
  | [], _ => rfl
  | head :: rest, b => by
      show consDrop rest.length (consAppend rest b) = b
      exact consDrop_consAppend rest b

/-! ## The block-sum composition of two counts lists -/

/-- ★ **The block-sum composition** of two counts lists.  Grouping `ccL` into consecutive blocks of the widths
`ccR = [r_0, r_1, …]` and summing each block: `composeCounts ccL (r :: ccR') = listSum (take r ccL) ::
composeCounts (drop r ccL) ccR'`.  Structural recursion on the TOP word `ccR` (the block widths).  This is the
data shadow of the vertical composite's canonical word — the block sums are the per-target merge multiplicities. -/
def composeCounts : List Nat → List Nat → List Nat
  | _, [] => []
  | ccL, r :: ccR' => listSum (consTake r ccL) :: composeCounts (consDrop r ccL) ccR'

/-- `composeCounts` produces exactly `ccR.length` block sums (one per top-word block). -/
theorem composeCounts_length : ∀ (ccL ccR : List Nat), (composeCounts ccL ccR).length = ccR.length
  | _, [] => rfl
  | ccL, r :: ccR' => by
      show (composeCounts (consDrop r ccL) ccR').length + 1 = ccR'.length + 1
      rw [composeCounts_length (consDrop r ccL) ccR']

/-- ★ The total width of `composeCounts ccL ccR` is the total width of `ccL` (each source strand contributes to
exactly one block sum), when the blocks partition `ccL` (`ccL.length = listSum ccR`).  Structural recursion on
`ccR` via `listSum_consAppend` + the take/drop split. -/
theorem listSum_composeCounts : ∀ (ccL ccR : List Nat), ccL.length = listSum ccR →
    listSum (composeCounts ccL ccR) = listSum ccL
  | ccL, [], hlen => by
      cases ccL with
      | nil => rfl
      | cons _ _ => exact Nat.noConfusion hlen
  | ccL, r :: ccR', hlen => by
      show listSum (consTake r ccL) + listSum (composeCounts (consDrop r ccL) ccR') = listSum ccL
      have hdroplen : (consDrop r ccL).length = listSum ccR' := by
        rw [consDrop_length, hlen]
        show r + listSum ccR' - r = listSum ccR'
        exact natAddSubCancelLeft r (listSum ccR')
      rw [listSum_composeCounts (consDrop r ccL) ccR' hdroplen,
          ← listSum_consAppend (consTake r ccL) (consDrop r ccL),
          consAppend_consTake_consDrop r ccL]

/-! ## The vertical word multiplicativity -/

/-- The middle-boundary cast that lets `word ccL` and `word ccR` compose vertically: `countsDomainPath ccR =
monadTPower ccL.length` (the codomain of `word ccL` is `t^ccL.length`, matched to the domain of `word ccR`). -/
theorem wordMul_vcomp_hmid (ccL ccR : List Nat) (hlen : ccL.length = listSum ccR) :
    countsDomainPath ccR = monadTPower ccL.length :=
  (countsDomainPath_eq_monadTPower_listSum ccR).trans (congrArg monadTPower hlen.symm)

/-- The target domain cast: `countsDomainPath (composeCounts ccL ccR) = countsDomainPath ccL` (the composite word
lands at `word ccL`'s domain, both `t^(listSum ccL)`). -/
theorem wordMul_vcomp_hdom (ccL ccR : List Nat) (hlen : ccL.length = listSum ccR) :
    countsDomainPath (composeCounts ccL ccR) = countsDomainPath ccL :=
  (countsDomainPath_eq_monadTPower_listSum (composeCounts ccL ccR)).trans
    ((congrArg monadTPower (listSum_composeCounts ccL ccR hlen)).trans
      (countsDomainPath_eq_monadTPower_listSum ccL).symm)

/-! ## Honesty markers -/

/-- **ESTABLISHED — the word-gadget collapse and the block-sum composition are shipped, zero-axiom.**  Toward the
sole open `normalizeCell` case `vcomp` (the vertical word multiplicativity `wordMul_vcomp`), this lane lands:

  * ★ **`wordGadgetCollapse`** — `vcomp (word cc) (gadget cc.length) ≈ cast (gadget (listSum cc))`: a whole canonical
    word absorbed into a single merge gadget, folding `gadgetRightMerge` (the associativity crossing) over the head
    gadget at each cons step, threading the induction hypothesis under the `t`-whisker, and reconciling the
    `countsDomainPath`/`monadTPower` boundary casts through the merge/extrusion cast kit.  This is the per-block
    collapse the vcomp assembly fires on each of the `ccR.length` blocks — the monad-law-bearing sub-brick.
  * **`composeCounts`** (+ `composeCounts_length`, `listSum_composeCounts`) — the run-grouped block sums, the data
    shadow of the vertical composite's canonical word.
  * the take/drop split kit (`consTake` / `consDrop` / `consAppend_consTake_consDrop` / `consTake_consAppend` /
    `consDrop_consAppend` / `listSum_consAppend`) and the domain-path bridge
    (`countsDomainPath_eq_monadTPower_listSum`), plus the two boundary-cast statements the vcomp step needs
    (`wordMul_vcomp_hmid`, `wordMul_vcomp_hdom`).

`= true`. -/
def fxMonad_hasWordGadgetCollapseAndComposeCounts : Bool := true

/-- **Honesty marker — the vertical word multiplicativity `wordMul_vcomp` is the NAMED residual.**  With
`wordGadgetCollapse`, `composeCounts`, `wordMul_hcomp` (the horizontal split), the free interchange
(`TwoCellStep.interchange`), and the boundary-cast statements all shipped, the SOLE remaining piece is the assembly
`wordMul_vcomp : vcomp (word ccL) (cast (word ccR)) ≈ cast (word (composeCounts ccL ccR))` (structural induction on
`ccR`; the base and the `subst`-clean setup of the step are shipped in the working notes).

The residual is EXACTLY the multi-cast interchange assembly of the `r :: ccR'` step: after splitting `word ccL` via
`wordMul_hcomp` into `hcomp (word take) (word drop)` (whose codomain is `composePath (t^take.length) (t^drop.length)`)
and recognizing `word (r :: ccR') = hcomp (gadget r) (word ccR')` (whose domain is `composePath (t^r)
(countsDomainPath ccR')`), the two horizontal composites do NOT share a definitional middle boundary — reconciling
`take.length = r`, `drop.length = listSum ccR'`, and `countsDomainPath ccR' = t^(listSum ccR')` requires threading a
`monadTPower_add` middle cast so the cast-free `TwoCellStep.interchange` fires, then extruding one outer cast
(`vcomp_castBoundaryLeft`), redistributing the right cast onto `word ccR'` (`hcomp_castBoundaryRight`), collapsing the
front factor (`wordGadgetCollapse take`) and threading the IH through the back factor, and reassembling the two
per-factor casts (needs a `hcomp_castBoundaryLeft` + a saturated `hcompCongrLeft`, both still to build) into the
target via `hccEq` + `castBoundary_wordCongr`.  Until `wordMul_vcomp` lands, the `vcomp` `normalizeCell` case is not
inhabited, so `normalize : MonadNormalizesToCanon` is not inhabited and `fxMonad_hasWordMulVcomp` /
`fxMonad_hasConvOfMapEqNormalization` / `fxMonad_hasMonotoneMapDecisionAssembled` /
`fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= false`. -/
def fxMonad_hasVcompWordMultiplicativity : Bool := false

end FX1Poly.Polygraph
