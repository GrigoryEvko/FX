import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCell

/-! # WalkingMonad — the CELL-level normalization cases: base + whisker (toward `normalize`)

`WalkingMonad/MonadNormalizeCell` machine-checked-reduced the completeness leg `convOfMapEq` to ONE inhabitant,
`normalize : MonadNormalizesToCanon` — every parallel free 2-cell is `MonadSaturatedTwoCellConv`-convertible to
the canonical Eilenberg–Zilber word of its own fold (`cell ≈ canon cell`).  This file lands the cases of that
`normalizeCell` induction that do NOT need the vertical word multiplicativity `wordMul_vcomp` (the re-sort).

## The base cases (no monad law, purely free-2-category structural)

Both walking-monad GENERATORS normalize to their canonical word by stripping the horizontal-composite identity
wrappers `wordFromCounts` produces, using ONLY the completed free-strict-2-category laws (`whiskerLeftId`,
`whiskerRightUnit`, `vcompIdLeft`, `vcompIdRight`) — never a monad law:

  * `gen eta` : fold `[]`, canon count `[0]`, `canon = hcomp eta (id t^0)` — strip the trailing left-whisker
    identity and the right-whisker-unit on `eta`.
  * `gen mu`  : fold `[0,0]`, canon count `[2]`, `canon = hcomp (mu-tree 2) (id t^0)` — strip the trailing
    identity, the right-whisker-unit, then collapse `monadGadget 2 = vcomp (t ◁ id_t) mu` to `mu` by
    `whiskerLeftId` + `vcompIdLeft`.

`composePath monadT (monadTPower 0)` reduces to `monadT` DEFINITIONALLY (`composePath` recurses on its first
argument, and `composePath nil nil = nil`), and `RawTwoCellExpr.castBoundary` along a definitionally-reflexive
boundary equality is defeq to the uncast cell (proof-irrelevance of `Eq` collapses the `Eq.rec`), so `canon (gen g)`
is defeq to the explicit horizontal composite — the `show` re-presents it with no cast in sight.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL. -/

namespace FX1Poly.Polygraph

/-! ## Base case: the UNIT generator `eta` normalizes to its canonical word -/

/-- ★ **Base case — the unit `eta`.**  `gen eta ≈ canon (gen eta)`.  Its fold is `[]`, so the canonical count list
is `[0]` and `canon (gen eta)` is DEFINITIONALLY `wordFromCounts [0] = hcomp (monadGadget 0) (id t^0) = vcomp
(whiskerRight t^0 eta) (whiskerLeft t (id t^0))` (the boundary cast is definitionally the identity — both boundaries
are `nil` / `monadT` on the nose).  Strip the trailing left-whisker identity by `whiskerLeftId` + `vcompIdRight`,
then the right-whisker-unit on `eta` by `whiskerRightUnit`, using ONLY the free-2-category structural laws. -/
theorem monadNormalize_genEta :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.gen MonadTwoCell.eta)
      (canon (RawTwoCellExpr.gen MonadTwoCell.eta)) := by
  refine MonadSaturatedTwoCellConv.symm ?_
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))))
      (RawTwoCellExpr.gen MonadTwoCell.eta)
  have hRight : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower 0))) :=
    MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower 0)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell) hRight) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell)))) ?_
  exact MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerRightUnit monadUnitTwoCell)

/-! ## Base case: the MULTIPLICATION generator `mu` normalizes to its canonical word -/

/-- ★ **Base case — the multiplication `mu`.**  `gen mu ≈ canon (gen mu)`.  Its fold is `[0,0]`, so the canonical
count list is `[2]` and `canon (gen mu)` is DEFINITIONALLY `wordFromCounts [2] = hcomp (monadGadget 2) (id t^0) =
vcomp (whiskerRight t^0 (monadGadget 2)) (whiskerLeft t (id t^0))`.  Strip the trailing left-whisker identity
(`whiskerLeftId` + `vcompIdRight`) and the right-whisker-unit (`whiskerRightUnit`) to reach `monadGadget 2`, then
collapse `monadGadget 2 = vcomp (whiskerLeft t (id t)) mu` to `mu`: the inner `whiskerLeft t (id t)` is the identity
on `t·t` (`whiskerLeftId`), dropped by `vcompIdLeft`.  Purely free-2-category structural — no monad law. -/
theorem monadNormalize_genMu :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.gen MonadTwoCell.mu)
      (canon (RawTwoCellExpr.gen MonadTwoCell.mu)) := by
  refine MonadSaturatedTwoCellConv.symm ?_
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))))
      (RawTwoCellExpr.gen MonadTwoCell.mu)
  -- Strip the trailing left-whisker identity.
  have hRight : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower 0))) :=
    MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower 0)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2)) hRight) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2))))) ?_
  -- Strip the right-whisker-unit: whiskerRight (t^0) (monadGadget 2) ≈ monadGadget 2.
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerRightUnit (monadGadget 2))) ?_
  -- Collapse monadGadget 2 = vcomp (whiskerLeft t (id t)) mu to mu.
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        monadMulTwoCell)
      (RawTwoCellExpr.gen MonadTwoCell.mu)
  have hInner : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT monadT)) :=
    MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell hInner) ?_
  exact MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft monadMulTwoCell))

/-! ## The `id`-cell case: the canonical word of an identity is the all-ones word, which collapses to `id`

`monadMonotoneMapOf (id path) = idMap path.length`, so `canon (id path)` is the boundary-transported per-target
word of the ALL-ONES multiplicity list (each target hit exactly once — no merge, no insertion).  That word is a
horizontal composite of `count` copies of the trivial gadget `monadGadget 1 = id_t`, and it collapses to the
identity 2-cell by the free-strict-2-category laws (`whiskerRightId` / `vcompIdLeft` / `whiskerLeftId`) — no monad
law.  The only genuine friction is the BOUNDARY TRANSPORT: the word lives at `(countsDomainPath ones, t^(ones.length))`
which is only PROVABLY-not-definitionally the cell's own `(path, path)`; the collapse is threaded through
`castBoundary` (proof-irrelevant, so the specific transport proofs never matter). -/

/-- The all-ones multiplicity list of length `count` — the Eilenberg–Zilber data of the identity map (each of the
`count` targets is hit exactly once).  Cons-only via the shipped propext-free `consReplicate` (never `List.replicate`,
which pulls `propext`). -/
def monadOnes (count : Nat) : List Nat := consReplicate 1 count []

/-- The ones list has length `count`. -/
theorem length_monadOnes (count : Nat) : (monadOnes count).length = count := by
  show (consReplicate 1 count []).length = count
  rw [consReplicate_length]
  exact Nat.zero_add count

/-- ★ The domain 1-cell of the ones word is the `t`-power `t^count` — each `1` gadget (`= id_t`) contributes one
`t`.  Structural induction on `count`; the head `1` prepends `monadTPower 1 = monadT` DEFINITIONALLY, so each step
is a `composePath monadT` congruence. -/
theorem countsDomainPath_monadOnes : ∀ (count : Nat),
    countsDomainPath (monadOnes count) = monadTPower count
  | 0 => rfl
  | count + 1 => by
      show composePath monadT (countsDomainPath (monadOnes count)) = composePath monadT (monadTPower count)
      exact congrArg (composePath monadT) (countsDomainPath_monadOnes count)

/-! ## The `countsOf (idMap) = ones` computation (run-peeling the strictly-ascending identity map) -/

/-- Past its first entry an ascending block never repeats the earlier base: the run of `base` in
`ascendingFrom (base + 1) n` is empty. -/
theorem runLengthAt_ascendingFrom_succ (base n : Nat) :
    runLengthAt base (ascendingFrom (base + 1) n) = 0 := by
  cases n with
  | zero => rfl
  | succ predN =>
      show runLengthAt base ((base + 1) :: ascendingFrom (base + 1 + 1) predN) = 0
      exact runLengthAt_cons_neg (Nat.succ_ne_self base)

/-- Dropping the (empty) `base`-run from `ascendingFrom (base + 1) n` leaves it unchanged. -/
theorem dropRunAt_ascendingFrom_succ (base n : Nat) :
    dropRunAt base (ascendingFrom (base + 1) n) = ascendingFrom (base + 1) n := by
  cases n with
  | zero => rfl
  | succ predN =>
      show dropRunAt base ((base + 1) :: ascendingFrom (base + 1 + 1) predN)
        = (base + 1) :: ascendingFrom (base + 1 + 1) predN
      exact dropRunAt_cons_neg (Nat.succ_ne_self base)

/-- ★ Reading the per-target multiplicity list off the strictly-ascending block `[base, base+1, …, base+n-1]`
gives the all-ones list: each target is hit exactly once.  Structural recursion on `n` (peel the singleton `base`
run, recurse at `base + 1`). -/
theorem countsOf_ascendingFrom_ones : ∀ (n base : Nat),
    countsOf n base (ascendingFrom base n) = monadOnes n
  | 0, _ => rfl
  | n + 1, base => by
      show runLengthAt base (base :: ascendingFrom (base + 1) n)
          :: countsOf n (base + 1) (dropRunAt base (base :: ascendingFrom (base + 1) n))
        = monadOnes (n + 1)
      rw [runLengthAt_cons_pos (rfl : base = base), runLengthAt_ascendingFrom_succ base n,
          dropRunAt_cons_pos (rfl : base = base), dropRunAt_ascendingFrom_succ base n,
          countsOf_ascendingFrom_ones n (base + 1)]
      rfl

/-! ## Boundary-cast helpers on the saturated relation (monad-specific, propext-free `cases` on the equalities) -/

/-- The saturated relation transports along a boundary cast on BOTH sides (the monad analog of
`TwoCellConvFull.castBoundaryCongr`). -/
theorem MonadSaturatedTwoCellConv.castBoundaryCongr
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellAlpha cellBeta) :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- LEFT whiskering by `t` commutes with a boundary cast (the monad instance of the shipped generic
`whiskerLeft_castBoundary`; re-proved locally to keep the walking-monad lane self-contained). -/
theorem monadWhiskerLeft_castBoundary
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (congrArg (composePath monadT) hsource)
          (congrArg (composePath monadT) htarget)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT cell) := by
  cases hsource; cases htarget; rfl

/-- Two successive boundary casts FUSE into one along the composite equalities (the monad instance of the shipped
generic `castBoundary_castBoundary`; re-proved locally to keep the lane self-contained). -/
theorem monadCastBoundary_castBoundary
    {pathOne pathTwo pathThree targetOne targetTwo targetThree :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsourceFirst : pathOne = pathTwo) (htargetFirst : targetOne = targetTwo)
    (hsourceSecond : pathTwo = pathThree) (htargetSecond : targetTwo = targetThree)
    (cell : RawTwoCellExpr monadModeSignature pathOne targetOne) :
    RawTwoCellExpr.castBoundary hsourceSecond htargetSecond
        (RawTwoCellExpr.castBoundary hsourceFirst htargetFirst cell)
      = RawTwoCellExpr.castBoundary (hsourceFirst.trans hsourceSecond)
          (htargetFirst.trans htargetSecond) cell := by
  cases hsourceFirst; cases htargetFirst; cases hsourceSecond; cases htargetSecond; rfl

/-- Casting an identity 2-cell along a boundary equality yields the identity at the new boundary (two proofs of the
same equality by proof irrelevance). -/
theorem monadCastBoundary_id {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource htarget : sourcePath = targetPath) :
    RawTwoCellExpr.castBoundary (signature := monadModeSignature) hsource htarget
        (RawTwoCellExpr.id (signature := monadModeSignature) sourcePath)
      = RawTwoCellExpr.id (signature := monadModeSignature) targetPath := by
  subst hsource; rfl

/-! ## The ones-word collapse -/

/-- The `count + 1` ones word peels its leading `id_t` gadget: `wordFromCounts (ones (count+1))` — a horizontal
composite `hcomp id_t (wordFromCounts (ones count))` — reduces to `t ◁ wordFromCounts (ones count)` by dropping the
right-whisker identity (`whiskerRightId`) and the left identity factor (`vcompIdLeft`).  Pure free-2-category, no
monad law. -/
theorem wordFromCounts_monadOnes_succ_conv (count : Nat) :
    MonadSaturatedTwoCellConv (wordFromCounts (monadOnes (count + 1)))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts (monadOnes count))) := by
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (countsDomainPath (monadOnes count))
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts (monadOnes count))))
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (wordFromCounts (monadOnes count)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft _
      (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT (countsDomainPath (monadOnes count)))))) ?_
  exact MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
    (TwoCellStep.vcompIdLeft (signature := monadModeSignature) _))

/-- ★ **The ones word collapses to the identity 2-cell** (transported to the word's native boundary).  Induction on
`count`: the base is the empty identity; the step peels the leading `id_t` gadget (`wordFromCounts_monadOnes_succ_conv`),
applies the induction hypothesis under a left whisker (`whiskerLeftCongr`), pulls the cast out of the whisker
(`monadWhiskerLeft_castBoundary`), and collapses `t ◁ id` to `id` (`whiskerLeftId`).  Uses ONLY free-2-category
laws — no monad law. -/
theorem wordFromCounts_monadOnes_conv : ∀ (count : Nat),
    MonadSaturatedTwoCellConv (wordFromCounts (monadOnes count))
      (RawTwoCellExpr.castBoundary (countsDomainPath_monadOnes count).symm
        (congrArg monadTPower (length_monadOnes count).symm)
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower count)))
  | 0 => MonadSaturatedTwoCellConv.refl _
  | count + 1 => by
      refine MonadSaturatedTwoCellConv.trans (wordFromCounts_monadOnes_succ_conv count) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.whiskerLeftCongr monadT (wordFromCounts_monadOnes_conv count)) ?_
      -- Pull the boundary cast out of the left whisker (a genuine propositional equality — `▸`, not `rw`, to dodge
      -- the dependent-index motive), then collapse `t ◁ id` to `id` under the same cast.
      have hpull := monadWhiskerLeft_castBoundary (countsDomainPath_monadOnes count).symm
        (congrArg monadTPower (length_monadOnes count).symm)
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower count))
      have hconv := MonadSaturatedTwoCellConv.castBoundaryCongr
        (congrArg (composePath monadT) (countsDomainPath_monadOnes count).symm)
        (congrArg (composePath monadT) (congrArg monadTPower (length_monadOnes count).symm))
        (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
          (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower count))))
      exact hpull.symm ▸ hconv

/-! ## The `id`-cell normalization case -/

/-- ★ **Case `id path` of `normalize`.**  Every identity 2-cell is saturated-convertible to the canonical word of
its own fold: `id path ≈ canon (id path)`.  `canonCounts (id path) = countsOf path.length 0 (idMap path.length) =
monadOnes path.length` (`countsOf_ascendingFrom_ones`), so `canon (id path)` is the boundary-transported ones word;
that word collapses to the identity (`wordFromCounts_monadOnes_conv`), and the nested boundary casts fuse
(`castBoundary_castBoundary`) and cancel on the identity (`monadCastBoundary_id`).  Purely free-2-category — no monad
law. -/
theorem monadNormalize_id (path : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.id (signature := monadModeSignature) path)
      (canon (RawTwoCellExpr.id (signature := monadModeSignature) path)) := by
  have hcountsEq : canonCounts (RawTwoCellExpr.id (signature := monadModeSignature) path)
      = monadOnes path.length := by
    show countsOf path.length 0 (ascendingFrom 0 path.length) = monadOnes path.length
    exact countsOf_ascendingFrom_ones path.length 0
  have hdomRight : countsDomainPath (monadOnes path.length) = path :=
    (countsDomainPath_monadOnes path.length).trans (monadPath_normalForm path).symm
  have hcodRight : monadTPower (monadOnes path.length).length = path :=
    (congrArg monadTPower (length_monadOnes path.length)).trans (monadPath_normalForm path).symm
  have hcanon : canon (RawTwoCellExpr.id (signature := monadModeSignature) path)
      = RawTwoCellExpr.castBoundary hdomRight hcodRight (wordFromCounts (monadOnes path.length)) :=
    RawTwoCellExpr.castBoundary_wordCongr
      (canonDomain_eq (RawTwoCellExpr.id (signature := monadModeSignature) path))
      (canonCodomain_eq (RawTwoCellExpr.id (signature := monadModeSignature) path))
      hdomRight hcodRight hcountsEq
  have collapse : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.castBoundary hdomRight hcodRight (wordFromCounts (monadOnes path.length)))
      (RawTwoCellExpr.id (signature := monadModeSignature) path) := by
    have hstep := MonadSaturatedTwoCellConv.castBoundaryCongr hdomRight hcodRight
      (wordFromCounts_monadOnes_conv path.length)
    rw [monadCastBoundary_castBoundary, monadCastBoundary_id] at hstep
    exact hstep
  rw [hcanon]
  exact MonadSaturatedTwoCellConv.symm collapse

/-! ## Honesty markers -/

/-- **ESTABLISHED — the two GENERATOR base cases of `normalize` are CLOSED, zero-axiom.**  Both walking-monad
generators are `MonadSaturatedTwoCellConv`-convertible to the canonical Eilenberg–Zilber word of their own fold:
`gen eta ≈ canon (gen eta)` (`monadNormalize_genEta`) and `gen mu ≈ canon (gen mu)` (`monadNormalize_genMu`),
using ONLY the completed free-strict-2-category laws (`whiskerLeftId`, `whiskerRightUnit`, `vcompIdLeft`,
`vcompIdRight`) — no monad law.  These are the `gen` leaf of the five-case `normalizeCell` induction on the cell
constructor.  `= true`. -/
def fxMonad_hasNormalizeGeneratorBaseCases : Bool := true

/-- **ESTABLISHED — the `id`-cell case of `normalize` is CLOSED, zero-axiom.**  Every identity 2-cell is
`MonadSaturatedTwoCellConv`-convertible to the canonical word of its own fold: `id path ≈ canon (id path)`
(`monadNormalize_id`).  The fold of `id path` is `idMap path.length`, whose Eilenberg–Zilber data is the all-ones
list (`countsOf_ascendingFrom_ones : countsOf n 0 (idMap n) = monadOnes n`); the ones word is a horizontal
composite of trivial gadgets `monadGadget 1 = id_t` that collapses to the identity 2-cell
(`wordFromCounts_monadOnes_conv`) by ONLY the free-strict-2-category laws (`whiskerRightId` / `vcompIdLeft` /
`whiskerLeftId`) — no monad law; the boundary transport (`countsDomainPath (ones) = t^count`,
`monadPath_normalForm`) is threaded through proof-irrelevant `castBoundary` (`monadCastBoundary_castBoundary` +
`monadCastBoundary_id`).  This is the third of the five `normalizeCell` cases (after the two `gen` leaves).
`= true`. -/
def fxMonad_hasNormalizeIdCase : Bool := true

/-- **Honesty marker — FOUR of the five `normalize` cases are landed; the SOLE remaining case is `vcomp`.**
`normalize : MonadNormalizesToCanon` inducts on the cell's five constructors.  CLOSED zero-axiom: the two `gen`
leaves (`fxMonad_hasNormalizeGeneratorBaseCases`), the `id` case (`fxMonad_hasNormalizeIdCase`,
`monadNormalize_id`), AND the two WHISKER cases (`monadNormalize_whiskerLeft` / `monadNormalize_whiskerRight`,
`WalkingMonad/MonadWhiskerNormalizeCases`, `fxMonad_hasWhiskerNormalizeCases`) — the whisker cases assembled from
the whisker word multiplicativities (`wordMul_whiskerLeft/Right`), the boundary transport, and the counts-alignment
(`canonCounts_whiskerLeft/Right`), no monad law.

What remains (the SOLE case using the monad LAWS):

  * **`vcomp cellL cellR`** — the congruences + IH reduce it to `vcomp (canon cellL) (canon cellR) ≈ canon (vcomp
    cellL cellR)`.  Its 2-cell half — the VERTICAL word multiplicativity `wordMul_vcomp : vcomp (word ccL)
    (word ccR) ≈ cast (word (composeCounts ccL ccR))` — is now CLOSED zero-axiom
    (`WalkingMonad/MonadWordVcomp`, `fxMonad_hasVcompWordMultiplicativity`), via the `wordMul_hcomp` block split at
    `take/drop ccL`, the free interchange, the `wordGadgetCollapse` per-block merge (the three monad laws through
    `gadgetAbsorb`), and the proof-irrelevant boundary-cast fusion.  What is NOT yet landed is the DATA half — the
    bridge `canonCounts (vcomp cellL cellR) = composeCounts (canonCounts cellL) (canonCounts cellR)`, i.e. the pure
    `List Nat` identity `countsOf targetLen 0 (composeMap mapL mapR) = composeCounts (countsOf midLen 0 mapL)
    (countsOf targetLen 0 mapR)` (the degeneracies-then-faces re-sort; convergent by Guiraud–Malbos–Mimram
    Example 2.6, Weibel Lemma 8.1.2), the analog of the shipped whisker bridges `canonCounts_whiskerLeft/Right`.
    Its base-shifted induction (head = leading composite-run length, tail = mid-suffix shift into the next base) is
    the named residual.

Until the DATA bridge lands and the `vcomp` case is assembled, `normalize` is not inhabited, so
`MonadSaturatedCanonicalization.convOfMapEq` (`monadConvOfMapEq_ofNormalize`) is not inhabited and
`fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasConvOfMapEqNormalization` /
`fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= false`. -/
def fxMonad_hasNormalizeIdWhiskerVcompCases : Bool := false

end FX1Poly.Polygraph
