import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingMonad/MonadSaturatedCanonReps — the bespoke-free CANONICAL-WORD representatives bridge (deep layer 2)

MONAD-R7 r4 second deep leaf: the conv-FREE Eilenberg–Zilber canonical-word skeleton relocated from the pure-bespoke
Δ chain, so the SURVIVOR lane (the idempotent reps, the Gen twins) can build / reconstruct the canonical words
WITHOUT importing the bespoke `MonadSaturatedTwoCellConv` inductive.  Imports the deep bridge
`MonadSaturatedDeltaReps` (the law-composite cells, the monotone-map fold engine, the whisker embedding) it builds
on; carries NO conv file in its closure.

## What this file ships (relocated VERBATIM, names / namespace / meaning preserved)

  * from `MonadCanonicalWord`: the eta/mu canonical-WORD builder (`monadTPower`, `monadGadget`, `wordFromCounts`,
    `reconstructFrom`, `countsDomainPath`, `consReplicate`, …) — the Δ Eilenberg–Zilber canonical words.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The canonical `t`-power boundary path -/

/-- The canonical `t`-power 1-cell `t^count : point ⟶ point`, LEFT-nested (`t · (t · … )`) so it lines up
definitionally with `composePath monadT (monadTPower count)` — the domain a left-whisker by `t` produces. -/
def monadTPower : Nat → ModalityPath monadGraph MonadMode.point MonadMode.point
  | 0 => ModalityPath.nil (graph := monadGraph) MonadMode.point
  | count + 1 => composePath monadT (monadTPower count)

/-- Smoke: `t^0` is the identity 1-cell (length `0`). -/
theorem monadTPower_zero_length : (monadTPower 0).length = 0 := rfl

/-- Smoke: `t^count` has length `count`. -/
theorem monadTPower_length : ∀ count : Nat, (monadTPower count).length = count
  | 0 => rfl
  | count + 1 => by
      show (composePath monadT (monadTPower count)).length = count + 1
      rw [ModalityPath.length_composePath monadT (monadTPower count), monadTPower_length count]
      exact Nat.add_comm monadT.length count

/-- Smoke: `t^1` is `monadT` (definitional — `composePath monadT nil` reduces to `monadT`). -/
theorem monadTPower_one : monadTPower 1 = monadT := rfl

/-- Smoke: `t^2` is `monadTThenT` (definitional). -/
theorem monadTPower_two : monadTPower 2 = monadTThenT := rfl

/-! ## The gadget: a merge-count becomes a free 2-cell `t^count ⇒ t` -/

/-- ★ The **merge gadget** `t^count ⇒ t`: `eta` (a face, insert a strand) at `count = 0`, `id_t` at `count = 1`,
and `mu ∘ (t ◁ gadget(count+1))` — a right-leaning `mu`-tree merging `count+2` strands into one — otherwise.
Structural recursion on `count`, so it COMPUTES. -/
def monadGadget : (count : Nat) → RawTwoCellExpr monadModeSignature (monadTPower count) monadT
  | 0 => monadUnitTwoCell
  | 1 => RawTwoCellExpr.id (signature := monadModeSignature) monadT
  | count + 2 =>
      RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (count + 1)))
        monadMulTwoCell

/-! ## `List Nat` merge computations backing the gadget fold -/

/-- `embedLocalMap 1 1 0 xs` prepends `0` and shifts `xs` up by one (`t`-whisker ordinal sum). -/
theorem embedLocalMap_oneOneZero (values : List Nat) :
    embedLocalMap 1 1 0 values = 0 :: shiftPrepend 1 values [] := rfl

/-- Shifting a constant-`0` block up by one gives the constant-`1` block. -/
theorem shiftPrepend_one_replicateZero : ∀ count : Nat,
    shiftPrepend 1 (List.replicate count 0) [] = List.replicate count 1
  | 0 => rfl
  | count + 1 => by
      show (1 + 0) :: shiftPrepend 1 (List.replicate count 0) [] = 1 :: List.replicate count 1
      rw [shiftPrepend_one_replicateZero count]

/-- Post-composing a constant-`1` block with the merge map `[0, 0]` yields the constant-`0` block. -/
theorem composeMap_replicateOne_merge : ∀ count : Nat,
    composeMap (List.replicate count 1) [0, 0] = List.replicate count 0
  | 0 => rfl
  | count + 1 => by
      show monotoneMapGet [0, 0] 1 :: composeMap (List.replicate count 1) [0, 0] = 0 :: List.replicate count 0
      show (0 : Nat) :: composeMap (List.replicate count 1) [0, 0] = 0 :: List.replicate count 0
      rw [composeMap_replicateOne_merge count]

/-- ★ The gadget-step merge: embedding the `count+1` merge one strand deeper and post-composing with `mu`'s map
`[0, 0]` collapses to the `count+2` merge — `composeMap (0 :: replicate (count+1) 1) [0,0] = replicate (count+2) 0`. -/
theorem composeMap_embed_merge (count : Nat) :
    composeMap (embedLocalMap 1 1 0 (List.replicate (count + 1) 0)) [0, 0]
      = List.replicate (count + 2) 0 := by
  rw [embedLocalMap_oneOneZero, shiftPrepend_one_replicateZero]
  show monotoneMapGet [0, 0] 0 :: composeMap (List.replicate (count + 1) 1) [0, 0]
    = List.replicate (count + 2) 0
  show (0 : Nat) :: composeMap (List.replicate (count + 1) 1) [0, 0] = List.replicate (count + 2) 0
  rw [composeMap_replicateOne_merge (count + 1)]
  rfl

/-! ## The gadget fold -/

/-- ★★ **The gadget folds to the constant merge map.**  `monadMonotoneMapOf (monadGadget count) =
replicate count 0` — all `count` source strands hit the single output `0`.  Structural induction on `count`: the
`eta` folds to `[]`, `id_t` to `[0]`, and the `mu`-tree step uses the `vcomp` + `whiskerLeft` homomorphisms and the
merge computation `composeMap_embed_merge`.  The genuine content that the builder realizes the right map. -/
theorem monadGadget_map : ∀ count : Nat,
    monadMonotoneMapOf (monadGadget count) = List.replicate count 0
  | 0 => rfl
  | 1 => rfl
  | count + 2 => by
      show monadMonotoneMapOf (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (count + 1)))
          monadMulTwoCell)
        = List.replicate (count + 2) 0
      rw [monadMonotoneMapOf_vcomp,
          monadMonotoneMapOf_whiskerLeft monadT (monadGadget (count + 1)),
          monadGadget_map (count + 1)]
      show composeMap (embedLocalMap 1 1 0 (List.replicate (count + 1) 0)) [0, 0]
        = List.replicate (count + 2) 0
      exact composeMap_embed_merge count

/-! ## Smokes -/

/-- Smoke: `monadGadget 0` folds to the empty map (it IS `eta`). -/
theorem monadGadget_zero_map : monadMonotoneMapOf (monadGadget 0) = [] := rfl

/-- Smoke: `monadGadget 1` folds to `[0]` (it IS `id_t`). -/
theorem monadGadget_one_map : monadMonotoneMapOf (monadGadget 1) = [0] := rfl

/-- Smoke: `monadGadget 2` folds to `[0, 0]` — the bare `mu` merge (width `2`). -/
theorem monadGadget_two_map : monadMonotoneMapOf (monadGadget 2) = [0, 0] := monadGadget_map 2

/-- Smoke: `monadGadget 3` folds to `[0, 0, 0]` — three strands merged to one (positive width, genuine). -/
theorem monadGadget_three_map : monadMonotoneMapOf (monadGadget 3) = [0, 0, 0] := monadGadget_map 3

/-! ## The word: horizontal composite of per-target gadgets

Given the per-target multiplicity list `counts = [c_0, …, c_{m-1}]`, the canonical word is the horizontal
composite `gadget(c_0) ⊠ gadget(c_1) ⊠ … ⊠ gadget(c_{m-1})` — a free 2-cell `t^(sum counts) ⇒ t^m`.  Its
DOMAIN 1-cell is the right-nested `composePath` of the gadget domains (`countsDomainPath`); no boundary cast is
needed because that domain is DEFINITIONALLY what `hcomp` produces, and the codomain `composePath t (t^k)`
reduces to `t^(k+1)` on the nose. -/

/-- The domain 1-cell of the per-target word: the right-nested `composePath` of the gadget domains `t^(c_j)`.
Definitionally what `hcomp (monadGadget c) (word rest)` produces, so the word needs no boundary cast. -/
def countsDomainPath : List Nat → ModalityPath monadGraph MonadMode.point MonadMode.point
  | [] => monadTPower 0
  | count :: rest => composePath (monadTPower count) (countsDomainPath rest)

/-- ★ The **per-target canonical word** `t^(sum counts) ⇒ t^(counts.length)`: the horizontal composite of the
per-target gadgets.  The empty word is the identity on `t^0`; consing prepends `gadget(count)` by `hcomp`.
Structural recursion on `counts`, so it COMPUTES; no cast (the boundaries line up definitionally). -/
def wordFromCounts : (counts : List Nat) →
    RawTwoCellExpr monadModeSignature (countsDomainPath counts) (monadTPower counts.length)
  | [] => RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)
  | count :: rest => RawTwoCellExpr.hcomp (monadGadget count) (wordFromCounts rest)

/-! ## The reconstructed map + its indexing law -/

/-- Cons-only replication into a difference list: `consReplicate value count tail` prepends `count` copies of
`value` onto `tail`.  Used instead of `List.replicate _ _ ++ tail` so length/indexing stay propext-free (the
library `List.length_append` / `List.length_replicate` / `List.map_append` / `List.map_replicate` all pull
`propext` per the cons-only-difference-list recipe). -/
def consReplicate : Nat → Nat → List Nat → List Nat
  | _,     0,         tail => tail
  | value, count + 1, tail => value :: consReplicate value count tail

/-- Length of a `consReplicate` block: `tail.length + count`.  Cons-only structural recursion on `count`. -/
theorem consReplicate_length : ∀ (value count : Nat) (tail : List Nat),
    (consReplicate value count tail).length = tail.length + count
  | _, 0, _ => rfl
  | value, count + 1, tail => by
      show (consReplicate value count tail).length + 1 = tail.length + (count + 1)
      rw [consReplicate_length value count tail, Nat.add_assoc]

/-- Inside the replicated prefix the value is the constant.  Cons-only structural recursion. -/
theorem monotoneMapGet_consReplicate_lt : ∀ (value count position : Nat) (tail : List Nat),
    position < count → monotoneMapGet (consReplicate value count tail) position = value
  | _, 0, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | _, _ + 1, 0, _, _ => rfl
  | value, count + 1, position + 1, tail, hlt =>
      monotoneMapGet_consReplicate_lt value count position tail (Nat.lt_of_succ_lt_succ hlt)

/-- Past the replicated prefix, `consReplicate` reads the tail.  Cons-only structural recursion. -/
theorem monotoneMapGet_consReplicate_ge : ∀ (value count offset : Nat) (tail : List Nat),
    monotoneMapGet (consReplicate value count tail) (count + offset) = monotoneMapGet tail offset
  | _, 0, offset, tail => by
      show monotoneMapGet tail (0 + offset) = monotoneMapGet tail offset
      rw [Nat.zero_add]
  | value, count + 1, offset, tail => by
      rw [show count + 1 + offset = (count + offset) + 1 from Nat.succ_add count offset]
      show monotoneMapGet (consReplicate value count tail) (count + offset) = monotoneMapGet tail offset
      exact monotoneMapGet_consReplicate_ge value count offset tail

/-- Cons-only length of `List.replicate` (the library `List.length_replicate` pulls `propext`). -/
theorem replicate_length : ∀ (count value : Nat),
    (List.replicate count value).length = count
  | 0, _ => rfl
  | count + 1, value => by
      show (List.replicate count value).length + 1 = count + 1
      rw [replicate_length count value]

/-- The monotone map reconstructed from a multiplicity list starting at target `base`: `c_0` copies of `base`,
`c_1` copies of `base+1`, ….  `reconstructFrom 0 counts` is the sorted map with the given per-target
multiplicities.  Built with `consReplicate` (a difference list) so its length/indexing laws are propext-free. -/
def reconstructFrom : Nat → List Nat → List Nat
  | _, [] => []
  | base, count :: rest => consReplicate base count (reconstructFrom (base + 1) rest)

/-- `reconstructFrom` has length the sum of the multiplicities.  Cons-only via `consReplicate_length`. -/
theorem reconstructFrom_length : ∀ (base : Nat) (counts : List Nat),
    (reconstructFrom base counts).length = (countsDomainPath counts).length
  | _, [] => rfl
  | base, count :: rest => by
      show (consReplicate base count (reconstructFrom (base + 1) rest)).length
        = (composePath (monadTPower count) (countsDomainPath rest)).length
      rw [consReplicate_length, reconstructFrom_length (base + 1) rest,
          ModalityPath.length_composePath, monadTPower_length]
      exact Nat.add_comm (countsDomainPath rest).length count

/-! ## Indexing helpers for the reconstructed map -/

/-- Inside a constant block the value is the constant. -/
theorem monotoneMapGet_replicate : ∀ (count base position : Nat), position < count →
    monotoneMapGet (List.replicate count base) position = base
  | 0, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | count + 1, base, position + 1, hlt => by
      show monotoneMapGet (List.replicate count base) position = base
      exact monotoneMapGet_replicate count base position (Nat.lt_of_succ_lt_succ hlt)

/-- Indexing the shifted reconstruction: `reconstructFrom (base+1)` at an in-range position is the base
reconstruction raised by one.  Direct structural induction on `counts` (peeling `consReplicate` blocks) — no
`List.map`, so propext-free. -/
theorem reconstructFrom_get_succ : ∀ (base : Nat) (counts : List Nat) (position : Nat),
    position < (reconstructFrom base counts).length →
    monotoneMapGet (reconstructFrom (base + 1) counts) position
      = monotoneMapGet (reconstructFrom base counts) position + 1
  | _, [], position, hpos => absurd hpos (Nat.not_lt_zero _)
  | base, count :: rest, position, hpos => by
      -- `reconstructFrom base (count::rest) = consReplicate base count (reconstructFrom (base+1) rest)`;
      -- shift by one is `consReplicate (base+1) count (reconstructFrom (base+2) rest)`.
      have hlen : (reconstructFrom base (count :: rest)).length
          = (reconstructFrom (base + 1) rest).length + count :=
        consReplicate_length base count (reconstructFrom (base + 1) rest)
      rw [hlen] at hpos
      rcases Nat.lt_or_ge position count with hlt | hge
      · -- within the replicated block: both sides read the constant `base+1` / `base`
        show monotoneMapGet (consReplicate (base + 1) count (reconstructFrom (base + 1 + 1) rest)) position
          = monotoneMapGet (consReplicate base count (reconstructFrom (base + 1) rest)) position + 1
        rw [monotoneMapGet_consReplicate_lt (base + 1) count position (reconstructFrom (base + 1 + 1) rest) hlt,
            monotoneMapGet_consReplicate_lt base count position (reconstructFrom (base + 1) rest) hlt]
      · -- past the block: peel to the tail and recurse
        rcases Nat.le.dest hge with ⟨offset, hoffEq⟩
        have hoff : offset < (reconstructFrom (base + 1) rest).length := by
          have hpos' : count + offset < (reconstructFrom (base + 1) rest).length + count := by
            rw [hoffEq]; exact hpos
          rw [Nat.add_comm count offset] at hpos'
          exact Nat.lt_of_add_lt_add_right hpos'
        rw [← hoffEq]
        show monotoneMapGet (consReplicate (base + 1) count (reconstructFrom (base + 1 + 1) rest))
            (count + offset)
          = monotoneMapGet (consReplicate base count (reconstructFrom (base + 1) rest)) (count + offset) + 1
        rw [monotoneMapGet_consReplicate_ge (base + 1) count offset (reconstructFrom (base + 1 + 1) rest),
            monotoneMapGet_consReplicate_ge base count offset (reconstructFrom (base + 1) rest)]
        exact reconstructFrom_get_succ (base + 1) rest offset hoff

/-! ## ★★ The section: the per-target word folds back to its map -/

/-- ★★ **The word-builder round-trips through the fold.**  `monadMonotoneMapOf (wordFromCounts counts) =
reconstructFrom 0 counts` — the fold of the per-target hcomp of gadgets is EXACTLY the reconstructed monotone map
(`c_0` zeros, `c_1` ones, …).  This validates the Eilenberg–Zilber word-builder: it is NON-VACUOUS and produces a
cell whose monotone map is the intended one.  Structural induction on `counts`: the empty word folds to `[]`; the
`hcomp` step uses the shipped `monadMonotoneMapOf_hcomp` + `monadGadget_map`, then pointwise (`listExtById`) the
two ordinal-sum embeddings compose to the reconstruction (the gadget block emits `0`s, the recursive block shifts
up by one). -/
theorem monadMonotoneMapOf_wordFromCounts : ∀ counts : List Nat,
    monadMonotoneMapOf (wordFromCounts counts) = reconstructFrom 0 counts
  | [] => rfl
  | count :: rest => by
      show monadMonotoneMapOf (RawTwoCellExpr.hcomp (monadGadget count) (wordFromCounts rest))
        = reconstructFrom 0 (count :: rest)
      rw [monadMonotoneMapOf_hcomp (monadGadget count) (wordFromCounts rest),
          monadGadget_map count, monadMonotoneMapOf_wordFromCounts rest, monadTPower_length rest.length]
      have hrec0 : (reconstructFrom 0 rest).length = (countsDomainPath rest).length :=
        reconstructFrom_length 0 rest
      apply listExtById
      · rw [composeMap_length, embedLocalMap_length, replicate_length]
        show 0 + count + (countsDomainPath rest).length = (reconstructFrom 0 (count :: rest)).length
        rw [show (reconstructFrom 0 (count :: rest)).length
              = (reconstructFrom (0 + 1) rest).length + count from
              consReplicate_length 0 count (reconstructFrom (0 + 1) rest),
            reconstructFrom_length (0 + 1) rest, Nat.zero_add]
        exact Nat.add_comm count (countsDomainPath rest).length
      · intro position hposComposeMap
        have hposA : position
            < (embedLocalMap 0 monadT.length (countsDomainPath rest).length (List.replicate count 0)).length := by
          rw [composeMap_length] at hposComposeMap; exact hposComposeMap
        have hposNum : position < 0 + count + (countsDomainPath rest).length := by
          rw [embedLocalMap_length, replicate_length] at hposA; exact hposA
        rw [composeMap_get _ _ position hposA]
        show monotoneMapGet
            (embedLocalMap monadT.length rest.length 0 (reconstructFrom 0 rest))
            (monotoneMapGet (embedLocalMap 0 monadT.length (countsDomainPath rest).length (List.replicate count 0))
              position)
          = monotoneMapGet (reconstructFrom 0 (count :: rest)) position
        rcases embedRegionSplit 0 count (countsDomainPath rest).length position hposNum with
            hleft | ⟨offset, hoff, rfl⟩ | ⟨offset, hoff, rfl⟩
        · exact absurd hleft (Nat.not_lt_zero position)
        · -- middle region: position = 0 + offset, offset < count (gadget block)
          have hA : monotoneMapGet
              (embedLocalMap 0 monadT.length (countsDomainPath rest).length (List.replicate count 0)) (0 + offset)
              = 0 := by
            rw [embedLocalMap_get_mid 0 monadT.length (countsDomainPath rest).length (List.replicate count 0)
                  offset (by rw [replicate_length]; exact hoff),
                monotoneMapGet_replicate count 0 offset hoff]
          rw [hA, embedLocalMap_get_left monadT.length rest.length 0 (reconstructFrom 0 rest) 0
                (Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_refl _))]
          -- RHS: reconstructFrom 0 (count :: rest) = consReplicate 0 count (reconstructFrom (0+1) rest); offset<count
          show (0 : Nat)
            = monotoneMapGet (consReplicate 0 count (reconstructFrom 1 rest)) (0 + offset)
          rw [Nat.zero_add,
              monotoneMapGet_consReplicate_lt 0 count offset (reconstructFrom 1 rest) hoff]
        · -- right region: position = 0 + count + offset, offset < dr (recursive block)
          have hA : monotoneMapGet
              (embedLocalMap 0 monadT.length (countsDomainPath rest).length (List.replicate count 0))
              (0 + count + offset) = 0 + monadT.length + offset := by
            have h := embedLocalMap_get_right 0 monadT.length (countsDomainPath rest).length
              (List.replicate count 0) offset hoff
            rw [replicate_length] at h; exact h
          rw [hA]
          have hBoff : offset < (reconstructFrom 0 rest).length := by rw [hrec0]; exact hoff
          rw [Nat.zero_add,
              embedLocalMap_get_mid monadT.length rest.length 0 (reconstructFrom 0 rest) offset hBoff]
          show monadT.length + monotoneMapGet (reconstructFrom 0 rest) offset
            = monotoneMapGet (consReplicate 0 count (reconstructFrom 1 rest)) (0 + count + offset)
          rw [Nat.zero_add, monotoneMapGet_consReplicate_ge 0 count offset (reconstructFrom 1 rest)]
          show monadT.length + monotoneMapGet (reconstructFrom 0 rest) offset
            = monotoneMapGet (reconstructFrom (0 + 1) rest) offset
          rw [reconstructFrom_get_succ 0 rest offset hBoff]
          exact Nat.add_comm monadT.length (monotoneMapGet (reconstructFrom 0 rest) offset)

/-! ## Non-vacuity smokes: the builder computes genuine maps

The multiplicity list IS the Eilenberg–Zilber data — `c_j` counts how many source strands merge onto target `j`
(the `mu`/degeneracy content), and a `c_j = 0` inserts a strand (the `eta`/face content).  Each smoke exhibits the
word for a genuine map, folding back to it. -/

/-- Smoke: the word for counts `[1, 1]` (each target hit once) is a 2-cell `t^2 ⇒ t^2` folding to the IDENTITY
map `[0, 1]` — no merge, no insertion. -/
theorem wordFromCounts_id_two : monadMonotoneMapOf (wordFromCounts [1, 1]) = [0, 1] :=
  monadMonotoneMapOf_wordFromCounts [1, 1]

/-- Smoke: the word for counts `[2, 1]` is a 2-cell `t^3 ⇒ t^2` folding to `[0, 0, 1]` — the first two strands
MERGE (a `mu`), the third passes through. -/
theorem wordFromCounts_merge_first : monadMonotoneMapOf (wordFromCounts [2, 1]) = [0, 0, 1] :=
  monadMonotoneMapOf_wordFromCounts [2, 1]

/-- Smoke: the word for counts `[0, 1]` is a 2-cell `t^1 ⇒ t^2` folding to `[1]` — target `0` is MISSED (an
`eta`/face inserts it), the single strand lands on target `1`.  The genuine face (insertion) case. -/
theorem wordFromCounts_insert_first : monadMonotoneMapOf (wordFromCounts [0, 1]) = [1] :=
  monadMonotoneMapOf_wordFromCounts [0, 1]

/-- Smoke: the word for counts `[3]` is a 2-cell `t^3 ⇒ t^1` folding to `[0, 0, 0]` — all three strands merge to
one (a `mu`-tree).  Exhibits the positive-width degeneracy content. -/
theorem wordFromCounts_merge_all : monadMonotoneMapOf (wordFromCounts [3]) = [0, 0, 0] :=
  monadMonotoneMapOf_wordFromCounts [3]

/-- Smoke: the two words `[1, 1]` and `[2]` fold to DISTINCT maps `[0, 1]` and `[0, 0]` — the builder SEPARATES
the identity on `t^2` from the merge `mu`, matching the separation witness the decision relies on. -/
theorem wordFromCounts_separates :
    monadMonotoneMapOf (wordFromCounts [1, 1]) ≠ monadMonotoneMapOf (wordFromCounts [2]) := by
  rw [monadMonotoneMapOf_wordFromCounts [1, 1], monadMonotoneMapOf_wordFromCounts [2]]
  show ([0, 1] : List Nat) ≠ [0, 0]
  intro hcontra
  injection hcontra with _ htail
  injection htail with hhead _
  exact Nat.noConfusion hhead

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The Eilenberg–Zilber WORD-BUILDER is shipped: `wordFromCounts` turns the per-target
multiplicity list (the EZ degeneracy/face data of a monotone map) into an actual free 2-cell of the walking monad
(`RawTwoCellExpr`), as the horizontal composite of the per-target merge gadgets (`monadGadget` — `eta` for a
missed target, `id_t` for a single hit, a `mu`-tree for a merge).  ★★ The **section** `monadMonotoneMapOf
(wordFromCounts counts) = reconstructFrom 0 counts` (`monadMonotoneMapOf_wordFromCounts`) proves the builder
round-trips through the fold — it is NON-VACUOUS and realizes the intended monotone map (smokes: identity,
merge, insertion, full merge, separation).  This is the recon-named missing piece — "no function turns a `List
Nat` into a `RawTwoCellExpr`" — now shipped, zero-axiom.  `= true`. -/
def fxMonad_hasEilenbergZilberWordBuilder : Bool := true

/-- **ESTABLISHED — the COMPLETENESS field `convOfMapEq` is now INHABITED, zero-axiom.**  The NORMALIZATION
direction — every cell is `MonadSaturatedTwoCellConv`-convertible to the canonical word of its own fold,
`cell ≈ canon cell` — is CLOSED for all five `normalizeCell` cases: the two `gen` leaves, `id`, both whiskers, and
the `vcomp` case.  The `vcomp` case (`monadNormalize_vcomp`, `WalkingMonad/MonadNormalizeVcomp`) combines the 2-cell
half `wordMul_vcomp : vcomp (word ccL) (word ccR) ≈ cast (word (composeCounts ccL ccR))`
(`fxMonad_hasVcompWordMultiplicativity`) with the now-shipped DATA bridge `canonCounts_vcomp : canonCounts (vcomp
cellL cellR) = composeCounts (canonCounts cellL) (canonCounts cellR)` — the pure `List Nat` functoriality
`countsOf ∘ composeMap = composeCounts ∘ countsOf` (`countsOf_composeMap`, base-shifted structural induction:
leading-run head, mid-suffix-shift tail).  Hence `monadNormalize : MonadNormalizesToCanon` is inhabited and
`monadConvOfMapEq_ofNormalize monadNormalize` inhabits `convOfMapEq` — the canonicalization
(`monadSaturatedCanonicalization`) and the unconditional decision (`monadSaturatedTwoCellDecision`) are real
(`fxMonad_hasSaturatedWordProblemClosed`).  `= true`. -/
def fxMonad_hasConvOfMapEqNormalization : Bool := true

end FX1Poly.Polygraph
