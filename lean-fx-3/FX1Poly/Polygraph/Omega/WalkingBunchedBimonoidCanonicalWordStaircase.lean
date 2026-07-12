import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermMatrixExtractorKit

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordStaircase — the canonical reduced-word engine: the
Coxeter–Moser comb, the recursive staircase, and the pure permutation round-trip (WP-PROP r14, #2033)

★ **THE r14 CANONICAL WORD — the Omega mirror of the Brauer `recComb` staircase, the pure `List Nat` layer of
`CoxeterWordUnique`.**  r13 shipped the perm-middle matrix→`List Nat` reduction
(`evalCell (permWord w1) = evalCell (permWord w2) -> permOfWord w1 = permOfWord w2`, the extractor composed with
`permMatrixInjective`).  The next node of the goal chain is `permOfWord w1 = permOfWord w2 -> recComb (W-1) w1 =
recComb (W-1) w2` — the canonicity of the recursive-comb staircase.  This file ships that staircase's DATA engine
and the pure soundness leg it rests on: the Coxeter–Moser four-case comb-insertion (`combInsertData`), the
one-level normal form (`combNormalizeForm`), the recursive staircase (`recComb`, the Regev–Roichman / Lehmer
reduced word — a UNIQUE reduced word per permutation), and the KEYSTONE

  `combInsertData_realizesSwap` — each comb-insert step applies exactly ONE adjacent swap to the running
  through-strand permutation (four branches COMMUTE / EXTEND / CANCEL / CARRY)

folded to `combNormalizeForm_preservesPerm` — one comb level preserves the permutation.  All PURE `List Nat`
over the shipped Omega symmetric-group engine (`bunchedBimonoidApplyAdjacentSwap` / `bunchedBimonoidPermOfWord`,
byte-identical to the Brauer canonicity lane, re-derived in-namespace — never imported).  ZERO CONV: the cell /
`SaturatedConvOverWithId` layer is untouched here (the `recCombConv` CONV-fold mirror and its `permWord_append`
spelling bridge are the r15 residual, named at the foot of this file).

## What this round is NOT (the honest scope)

This is the pure-permutation soundness leg, NOT the CONV-fold.  The `combInsertStepConv` single-letter CONV
insertion (firing the r9 `bunchedBimonoid{YangBaxter,Involution,DistantSwap}AtPosition` moves through a
`permWord`/`sigmaAt` chain) needs the vcomp-vs-list-append spelling bridge (the fixed base legs
`bunchedBimonoidSigmaInvolutionLeftLeg = vcomp addSigmaGen addSigmaGen` are NOT the `sigmaAt`-chain
`vcomp (sigmaAt w k) (sigmaAt w k)` definitionally — only up to `whiskerLeft/RightFunctorial`); that bridge is the
r15 headline.  The star does NOT flip: no hypothesis-free inhabitant of
`bunchedBimonoidStarStatementAdditiveWellTyped` is produced, and every star / residual marker stays byte-intact
`= false`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  Mirror of the Brauer canonicity lane (`WiringDescStaircaseCanonical`);
never imported from it. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The width-4/5 permutation round-trip `rfl` pins exceed the default heartbeat budget; the raise is a compute
allowance only, the proof terms stay `Eq.refl` / structural, axiom-free (uniform with the r6-r13 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # C0 — THE CANONICAL-WORD DATA ENGINE (the Coxeter–Moser comb + the recursive staircase)
    # =========================================================================================

★ Verbatim ports (renamed into the Omega namespace) of the Brauer `descendingPositions` / `mentionsOnlyBelow` /
`combInsertData` / `combNormalizeForm` / `recComb`, over the SHIPPED Omega symmetric-group engine
`bunchedBimonoidApplyAdjacentSwap` / `bunchedBimonoidPermOfWord`. -/

/-- ★ **A descending run of positions** — `descendingPositions top count = [top, top-1, …, top-count+1]`, the
`count` topmost generator indices at-or-below `top`.  Structural on `count`; the run of the Coxeter–Moser coset is
`descendingPositions (width - 2) count` (anchored at the top generator `s_{width-2}`). -/
def bunchedBimonoidDescendingPositions (top : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => top :: bunchedBimonoidDescendingPositions (top - 1) count

/-- ★ **The `mentionsOnlyBelow` certificate** — every position of the word is strictly below `bound`.  A full-enum
`Bool` all-scan (`Nat.blt`), propext-clean (matching the Kit's `bunchedBimonoidPositionsValid` house style).  For
the comb the prefix carries `mentionsOnlyBelow (width - 2) prefix = true` — the Björner–Brenti right-descent
transversal condition. -/
def bunchedBimonoidMentionsOnlyBelow (bound : Nat) : List Nat → Bool
  | [] => true
  | position :: rest => Nat.blt position bound && bunchedBimonoidMentionsOnlyBelow bound rest

/-- ★ **One data-only comb-insertion step** — the four Coxeter–Moser side conditions on `letter + run` versus
`generatorCount`: COMMUTE (snoc the letter, keep the run), EXTEND (grow the run), CANCEL (shrink the run), CARRY
(snoc `letter - 1`, keep the run).  The pure four-case dispatch the staircase folds. -/
def bunchedBimonoidCombInsertData (generatorCount : Nat) (state : List Nat × Nat) (letter : Nat) :
    List Nat × Nat :=
  if letter + state.2 + 2 ≤ generatorCount then (state.1 ++ [letter], state.2)
  else if letter + state.2 + 1 = generatorCount then (state.1, state.2 + 1)
  else if letter + state.2 = generatorCount then (state.1, state.2 - 1)
  else (state.1 ++ [letter - 1], state.2)

/-- ★ **The one-level comb normal form** — fold the data step from the empty state, then read off
`combPrefix ++ descendingRun`.  The DATA mirror of the single-level `combNormalizeForm_conv`. -/
def bunchedBimonoidCombNormalizeForm (generatorCount : Nat) (input : List Nat) : List Nat :=
  let result := input.foldl (bunchedBimonoidCombInsertData generatorCount) ([], 0)
  result.1 ++ bunchedBimonoidDescendingPositions (generatorCount - 1) result.2

/-- ★★ **The recursive comb staircase** — at level `generatorCount + 1` run the DATA comb fold, then recurse on the
still-uncanonical prefix at level `generatorCount`.  Structural recursion on the generator count (the second
argument is free), so it computes and needs no fuel.  The image is the Regev–Roichman canonical presentation
`w_1 ⋯ w_{width-1}` — a UNIQUE reduced word per permutation. -/
def bunchedBimonoidRecComb : Nat → List Nat → List Nat
  | 0, _ => []
  | generatorCount + 1, input =>
      bunchedBimonoidRecComb generatorCount
          (input.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).1
        ++ bunchedBimonoidDescendingPositions generatorCount
            (input.foldl (bunchedBimonoidCombInsertData (generatorCount + 1)) ([], 0)).2

/-! # =========================================================================================
    # C0 — TRUTH-PROBES (the canonical-word engine computes; run standalone BEFORE any proof)
    # =========================================================================================

★ The 6 width-3 permutations' realizing words fold to their canonical staircases, and every canonical word
round-trips its permutation (`permOfWord (recComb w) = permOfWord w`). -/

#eval bunchedBimonoidRecComb 2 []          -- perm [0,1,2] -> []
#eval bunchedBimonoidRecComb 2 [1]         -- perm [0,2,1] -> [1]
#eval bunchedBimonoidRecComb 2 [0]         -- perm [1,0,2] -> [0]
#eval bunchedBimonoidRecComb 2 [0, 1]      -- perm [1,2,0] -> [0,1]
#eval bunchedBimonoidRecComb 2 [1, 0]      -- perm [2,0,1] -> [1,0]
#eval bunchedBimonoidRecComb 2 [0, 1, 0]   -- perm [2,1,0] -> [0,1,0]
#eval bunchedBimonoidRecComb 2 [1, 0, 1]   -- perm [2,1,0] -> [0,1,0]  (the braid pair UNIFIES)
#eval bunchedBimonoidRecComb 3 [2, 0, 1, 2]      -- perm [1,3,2,0] -> [0,1,2,1]
#eval bunchedBimonoidPermOfWord (bunchedBimonoidRecComb 3 [2, 0, 1, 2]) 4
#eval bunchedBimonoidPermOfWord [2, 0, 1, 2] 4

/-! # =========================================================================================
    # C0 — THE `rfl` PINS (widths <= 4/5; the engine reaches the recon table on the nose)
    # =========================================================================================
-/

/-- ★ **The r9 jam word `[2, 0, 1, 2]` reaches the staircase `[0, 1, 2, 1]`** (`rfl`) — the exact canonical word the
Brauer insertion residual could not reach, computed by the recursive comb at generator count 3. -/
theorem bunchedBimonoidRecComb_r9_stuck_word : bunchedBimonoidRecComb 3 [2, 0, 1, 2] = [0, 1, 2, 1] := rfl

/-- ★★ **The r11 residual pair `[1,2,0,1,2]` / `[0,1,2,0,1]` UNIFY under the recursive comb** — both reach the
common staircase `[0, 1, 0, 2, 1]` (`rfl`), while the ONE-level comb keeps them distinct
(`combNormalizeForm 4 [1,2,0,1,2] = [1,2,0,1,2]` below).  This is exactly why the recursion is load-bearing for the
equal-permutation flip. -/
theorem bunchedBimonoidRecComb_r11_left : bunchedBimonoidRecComb 4 [1, 2, 0, 1, 2] = [0, 1, 0, 2, 1] := rfl

/-- The right member of the r11 pair reaches the SAME staircase (`rfl`). -/
theorem bunchedBimonoidRecComb_r11_right : bunchedBimonoidRecComb 4 [0, 1, 2, 0, 1] = [0, 1, 0, 2, 1] := rfl

/-- ★ **The one-level comb does NOT unify the r11 pair** — it fixes `[1,2,0,1,2]` (`rfl`); only the recursion
collapses it to `[0,1,0,2,1]`.  The recon's load-bearing witness for the recursion. -/
theorem bunchedBimonoidCombNormalizeForm_r11_left_fixed :
    bunchedBimonoidCombNormalizeForm 4 [1, 2, 0, 1, 2] = [1, 2, 0, 1, 2] := rfl

/-- The r9 braid pair `[0,1,0]` / `[1,0,1]` (both realizing the width-3 reversal `[2,1,0]`) UNIFY to `[0,1,0]`
under the recursive comb at generator count 2 (`rfl`). -/
theorem bunchedBimonoidRecComb_braidPairUnifies :
    bunchedBimonoidRecComb 2 [0, 1, 0] = bunchedBimonoidRecComb 2 [1, 0, 1] := rfl

/-- ★★ **The recursive comb ROUND-TRIPS its permutation** — the staircase of `[2,0,1,2]` realizes the same
through-strand permutation as `[2,0,1,2]` itself (`rfl`, width 4).  The pure soundness the general
`combNormalizeForm_preservesPerm` (r15) generalises. -/
theorem bunchedBimonoidRecComb_r9_roundTrip :
    bunchedBimonoidPermOfWord (bunchedBimonoidRecComb 3 [2, 0, 1, 2]) 4
      = bunchedBimonoidPermOfWord [2, 0, 1, 2] 4 := rfl

/-- The r9 braid pair shares its through-strand permutation `[2,1,0]` (`rfl`) — the pure `List Nat` read-off the
staircase then unifies. -/
theorem bunchedBimonoidBraidPairPermShared :
    bunchedBimonoidPermOfWord [0, 1, 0] 3 = bunchedBimonoidPermOfWord [1, 0, 1] 3 := rfl

/-! ## The C0 honesty marker -/

/-- ★★★ **ESTABLISHED (C0) — the canonical-word DATA engine is SHIPPED and truth-probed.**  `= true` records the
Coxeter–Moser comb (`bunchedBimonoidCombInsertData`, four cases), the one-level normal form
(`bunchedBimonoidCombNormalizeForm`), the recursive staircase (`bunchedBimonoidRecComb`, the Regev–Roichman /
Lehmer reduced word), and the descending run (`bunchedBimonoidDescendingPositions`) + the `mentionsOnlyBelow`
certificate, all over the SHIPPED Omega symmetric-group engine (`bunchedBimonoidApplyAdjacentSwap` /
`bunchedBimonoidPermOfWord`, byte-identical to the Brauer canonicity lane).  Truth-probed + pinned by `rfl`: the r9
jam word `[2,0,1,2]` reaches `[0,1,2,1]`, the r11 pair `[1,2,0,1,2]` / `[0,1,2,0,1]` UNIFY to `[0,1,0,2,1]` (the
one-level comb keeping them distinct), the r9 braid pair `[0,1,0]` / `[1,0,1]` unify to `[0,1,0]`, and the
staircase ROUND-TRIPS its permutation (`recComb_r9_roundTrip`).  The Omega mirror of the Brauer `recComb`
staircase.  Zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_canonicalWordStaircaseEngineShipped : Bool := true

end FX1Poly.Polygraph.Omega
