import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedCanonReps

/-! # WalkingMonad/MonadNormalizeCasesReps — the bespoke-free CASES helpers leaf (conv-decoupled)

MONAD-R7 r5 deep leaf: the conv-FREE helpers of `WalkingMonad/MonadNormalizeCases` relocated VERBATIM so the
survivor lane (and the idempotent-saturated bricks) can reach them WITHOUT importing the conv-bearing rest.  Nine
pure `List Nat`/`Nat`/path/`RawTwoCellExpr`-equality helpers, none of which mention `MonadSaturatedTwoCellConv`:

  * the all-ones multiplicity data (`monadOnes` / `length_monadOnes` / `countsDomainPath_monadOnes`);
  * the run-peeling of the strictly-ascending identity map (`runLengthAt_ascendingFrom_succ` /
    `dropRunAt_ascendingFrom_succ` / `countsOf_ascendingFrom_ones`);
  * the monad-specific boundary-cast algebra (`monadWhiskerLeft_castBoundary` / `monadCastBoundary_castBoundary` /
    `monadCastBoundary_id`).

Imports ONLY `MonadSaturatedCanonReps` (deep layer 2), which transitively supplies every substrate these helpers
need (`countsDomainPath`/`countsOf`/`ascendingFrom`/`runLengthAt`/`dropRunAt`/`monadTPower`/`consReplicate` and the
`RawTwoCellExpr`/`monadModeSignature`/`monadGraph`/`MonadMode` polygraph substrate) — in particular NOT `canon` /
`canonCounts` nor `MonadSaturatedTwoCellConv`.

The conv-bearing rest of `MonadNormalizeCases` (the two generator base cases, `castBoundaryCongr`, the ones-word
collapse, and the `id`-cell normalization) imports this leaf and stays put.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL. -/

namespace FX1Poly.Polygraph

/-! ## The all-ones multiplicity data of the identity map -/

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

/-! ## Boundary-cast helpers on raw cells (monad-specific, propext-free `cases` on the equalities) -/

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

end FX1Poly.Polygraph
