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

/-! ## The fibre-COUNTS round-trip stratum, relocated from `MonadCountsRoundTrip` -/


/-! ## The fold monotonicity invariant: the covariant fold lands in a WEAKLY-INCREASING value-list -/

/-- The monotonicity invariant at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free.  Both `eta` (a face) and `mu` (a degeneracy) post-compose a weakly-increasing generator onto the
running map, which stays weakly increasing by `composeMap_isWeaklyIncreasing` (whose in-range side condition is the
running `mapsInto` invariant). -/
theorem monadRunMonoCell_isWeaklyIncreasing_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length)
    (hmap : mapsInto map width) (hmono : isWeaklyIncreasing map) :
    isWeaklyIncreasing (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2 := by
  cases generator with
  | eta =>
      show isWeaklyIncreasing (composeMap map (faceMap leftAcc.length width))
      exact composeMap_isWeaklyIncreasing map (faceMap leftAcc.length width) hmono
        (faceMap_isWeaklyIncreasing leftAcc.length width)
        (by rw [faceMap_length]; exact hmap)
  | mu =>
      show isWeaklyIncreasing (composeMap map (degenMap leftAcc.length (width - 1)))
      have hsucc : width - 1 + 1 = width := by
        have hwidthPred : width - 1 = leftAcc.length + 1 + rightAcc.length := by
          rw [hwidth]; exact monadMuWidthShift leftAcc.length rightAcc.length
        rw [hwidthPred, hwidth]
        show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
        rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
            Nat.add_right_comm leftAcc.length 1 rightAcc.length]
      exact composeMap_isWeaklyIncreasing map (degenMap leftAcc.length (width - 1)) hmono
        (degenMap_isWeaklyIncreasing leftAcc.length (width - 1))
        (by rw [degenMap_length, hsucc]; exact hmap)

/-- ★ **The covariant fold lands every free 2-cell in a WEAKLY-INCREASING value-list.**  Structural recursion
mirroring `monadRunMonoCell_mapsInto`: a generator via the gen lemma, a vertical composite through both factors
(intermediate width / in-range from `monadRunMonoCell_width` / `_mapsInto`), the whiskerings under shifted
accumulators.  Together with `monadRunMonoCell_mapsInto` this says the fold output is a genuine monotone Δ₊
morphism. -/
theorem monadRunMonoCell_isWeaklyIncreasing {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto map width → isWeaklyIncreasing map →
    isWeaklyIncreasing (monadRunMonoCell (width, map) leftAcc rightAcc cell).2
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth, hmap, hmono =>
      monadRunMonoCell_isWeaklyIncreasing_gen generator width map leftAcc rightAcc hwidth hmap hmono
  | _, _, _, _, .id _, _, _, _, _, _, _, hmono => hmono
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth, hmap, hmono => by
      rw [monadRunMonoCell_vcomp]
      exact monadRunMonoCell_isWeaklyIncreasing cellRight _ _ leftAcc rightAcc
        (monadRunMonoCell_width cellLeft width map leftAcc rightAcc hwidth)
        (monadRunMonoCell_mapsInto cellLeft width map leftAcc rightAcc hwidth hmap)
        (monadRunMonoCell_isWeaklyIncreasing cellLeft width map leftAcc rightAcc hwidth hmap hmono)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap, hmono => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_isWeaklyIncreasing body width map (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap hmono
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap, hmono => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_isWeaklyIncreasing body width map leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap hmono

/-- ★ **The whole-cell monotone map is WEAKLY INCREASING** — instantiate the run-level invariant at the identity
state (the identity map is weakly increasing and maps into its own ordinal). -/
theorem monadMonotoneMapOf_isWeaklyIncreasing {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    isWeaklyIncreasing (monadMonotoneMapOf cell) := by
  rw [monadMonotoneMapOf_eq_runMonoCell]
  exact monadRunMonoCell_isWeaklyIncreasing cell sourcePath.length (idMap sourcePath.length)
    (identityPath (graph := monadModeSignature.graph) sourceMode)
    (identityPath (graph := monadModeSignature.graph) targetMode)
    (by show sourcePath.length = 0 + sourcePath.length + 0; rw [Nat.add_zero, Nat.zero_add])
    (idMap_mapsInto sourcePath.length) (idMap_isWeaklyIncreasing sourcePath.length)

/-! ## The run-peel: read the per-target multiplicity list off a sorted value-list -/

/-- The length of the leading run of entries equal to `base` in a value-list.  Structural on the list; the
`head = base` test splits on `Nat.decEq` via `ite` (propext-free through `if_pos` / `if_neg`). -/
def runLengthAt (base : Nat) : List Nat → Nat
  | [] => 0
  | head :: rest => if head = base then runLengthAt base rest + 1 else 0

/-- Drop the leading run of entries equal to `base` from a value-list.  Structural on the list. -/
def dropRunAt (base : Nat) : List Nat → List Nat
  | [] => []
  | head :: rest => if head = base then dropRunAt base rest else head :: rest

/-- `runLengthAt` unfolds on a cons whose head IS the base. -/
theorem runLengthAt_cons_pos {base head : Nat} {rest : List Nat} (h : head = base) :
    runLengthAt base (head :: rest) = runLengthAt base rest + 1 := if_pos h

/-- `runLengthAt` unfolds on a cons whose head is NOT the base (the run is empty). -/
theorem runLengthAt_cons_neg {base head : Nat} {rest : List Nat} (h : ¬ head = base) :
    runLengthAt base (head :: rest) = 0 := if_neg h

/-- `dropRunAt` unfolds on a cons whose head IS the base (drop it and continue). -/
theorem dropRunAt_cons_pos {base head : Nat} {rest : List Nat} (h : head = base) :
    dropRunAt base (head :: rest) = dropRunAt base rest := if_pos h

/-- `dropRunAt` unfolds on a cons whose head is NOT the base (the run is empty; keep the whole list). -/
theorem dropRunAt_cons_neg {base head : Nat} {rest : List Nat} (h : ¬ head = base) :
    dropRunAt base (head :: rest) = head :: rest := if_neg h

/-- The per-target multiplicity list of a sorted value-list into `[base, base + targetLen)`: the count of the
`base`-run, then recurse at `base + 1` on the dropped tail.  Structural on `targetLen`, so it produces exactly
`targetLen` counts. -/
def countsOf : Nat → Nat → List Nat → List Nat
  | 0, _, _ => []
  | targetLen + 1, base, values =>
      runLengthAt base values :: countsOf targetLen (base + 1) (dropRunAt base values)

/-! ## Tail lemmas for the invariants threaded through the peel -/

/-- The tail of a weakly-increasing list is weakly increasing. -/
theorem isWeaklyIncreasing_tail {head : Nat} {rest : List Nat}
    (hmono : isWeaklyIncreasing (head :: rest)) : isWeaklyIncreasing rest := by
  intro lowerPos upperPos hle hupper
  exact hmono (lowerPos + 1) (upperPos + 1) (Nat.succ_le_succ hle) (Nat.succ_lt_succ hupper)

/-- The tail of a list mapping into `[cap]` maps into `[cap]`. -/
theorem mapsInto_tail {head : Nat} {rest : List Nat} {cap : Nat}
    (hinto : mapsInto (head :: rest) cap) : mapsInto rest cap := by
  intro position hposition
  exact hinto (position + 1) (Nat.succ_lt_succ hposition)

/-- The tail of a list bounded below by `base` is bounded below by `base`. -/
theorem lowerBound_tail {base head : Nat} {rest : List Nat}
    (hlow : ∀ position, position < (head :: rest).length → base ≤ monotoneMapGet (head :: rest) position) :
    ∀ position, position < rest.length → base ≤ monotoneMapGet rest position := by
  intro position hposition
  exact hlow (position + 1) (Nat.succ_lt_succ hposition)

/-! ## `dropRunAt` preserves the three invariants (weakly increasing, lower bound rises, upper bound) -/

/-- Dropping the base-run preserves weak monotonicity (the remainder is a suffix). -/
theorem dropRunAt_isWeaklyIncreasing : ∀ (base : Nat) (values : List Nat),
    isWeaklyIncreasing values → isWeaklyIncreasing (dropRunAt base values)
  | _, [], _ => by intro _ _ _ hupper; exact absurd hupper (Nat.not_lt_zero _)
  | base, head :: rest, hmono => by
      rcases Nat.decEq head base with h | h
      · rw [dropRunAt_cons_neg h]; exact hmono
      · rw [dropRunAt_cons_pos h]
        exact dropRunAt_isWeaklyIncreasing base rest (isWeaklyIncreasing_tail hmono)

/-- ★ Dropping the base-run RAISES the lower bound to `base + 1`: every remaining entry exceeds `base` (the run of
`base`s is exactly what was removed; monotonicity makes the remainder start strictly above `base`). -/
theorem dropRunAt_lowerBound : ∀ (base : Nat) (values : List Nat),
    isWeaklyIncreasing values →
    (∀ position, position < values.length → base ≤ monotoneMapGet values position) →
    (∀ position, position < (dropRunAt base values).length →
      base + 1 ≤ monotoneMapGet (dropRunAt base values) position)
  | _, [], _, _ => by intro position hposition; exact absurd hposition (Nat.not_lt_zero _)
  | base, head :: rest, hmono, hlow => by
      rcases Nat.decEq head base with h | h
      · rw [dropRunAt_cons_neg h]
        intro position hposition
        have hbh : base ≤ head := hlow 0 (Nat.succ_pos _)
        have hbhlt : base + 1 ≤ head := Nat.lt_of_le_of_ne hbh (fun heq => h heq.symm)
        cases position with
        | zero => exact hbhlt
        | succ predPos =>
            have hpred : predPos < rest.length := Nat.lt_of_succ_lt_succ hposition
            have hle : head ≤ monotoneMapGet rest predPos :=
              hmono 0 (predPos + 1) (Nat.zero_le _) (Nat.succ_lt_succ hpred)
            exact Nat.le_trans hbhlt hle
      · rw [dropRunAt_cons_pos h]
        exact dropRunAt_lowerBound base rest (isWeaklyIncreasing_tail hmono) (lowerBound_tail hlow)

/-- Dropping the base-run preserves the upper bound (the remainder is a suffix). -/
theorem dropRunAt_mapsInto : ∀ (base : Nat) (values : List Nat) (cap : Nat),
    mapsInto values cap → mapsInto (dropRunAt base values) cap
  | _, [], _, _ => by intro position hposition; exact absurd hposition (Nat.not_lt_zero _)
  | base, head :: rest, cap, hinto => by
      rcases Nat.decEq head base with h | h
      · rw [dropRunAt_cons_neg h]; exact hinto
      · rw [dropRunAt_cons_pos h]; exact dropRunAt_mapsInto base rest cap (mapsInto_tail hinto)

/-! ## The KEY reconstruction step: peel-then-prepend is the identity (UNCONDITIONAL) -/

/-- ★★ **Peel the base-run, prepend it back = identity.**  `consReplicate base (runLengthAt base values)
(dropRunAt base values) = values` for ANY `values` — the run-peel and the run-rebuild are inverse.  Structural on
the value-list; the `head = base` branch prepends `base` (which equals `head`) and recurses, the `head ≠ base`
branch is the empty run (`consReplicate base 0 _` is the tail, unchanged). -/
theorem consReplicate_runLengthAt_dropRunAt : ∀ (base : Nat) (values : List Nat),
    consReplicate base (runLengthAt base values) (dropRunAt base values) = values
  | _, [] => rfl
  | base, head :: rest => by
      rcases Nat.decEq head base with h | h
      · rw [runLengthAt_cons_neg h, dropRunAt_cons_neg h]; rfl
      · rw [runLengthAt_cons_pos h, dropRunAt_cons_pos h]
        show base :: consReplicate base (runLengthAt base rest) (dropRunAt base rest) = head :: rest
        rw [consReplicate_runLengthAt_dropRunAt base rest, h]

/-! ## ★★ The counts round-trip -/

/-- ★★ **The counts ROUND-TRIP.**  For a weakly-increasing `values` mapping into `[base, base + targetLen)`,
reconstructing from its per-target multiplicity list returns `values`: `reconstructFrom base (countsOf targetLen
base values) = values`.  Structural on `targetLen`; the successor step peels the `base`-run
(`consReplicate_runLengthAt_dropRunAt`) and recurses on the dropped tail (weakly increasing, lower bound risen to
`base + 1`, still bounded above, by the `dropRunAt_*` invariants).  The `targetLen = 0` base forces `values = []`
(no entry can be both `≥ base` and `< base`). -/
theorem reconstructFrom_countsOf : ∀ (targetLen base : Nat) (values : List Nat),
    isWeaklyIncreasing values →
    (∀ position, position < values.length → base ≤ monotoneMapGet values position) →
    mapsInto values (base + targetLen) →
    reconstructFrom base (countsOf targetLen base values) = values
  | 0, base, values, _, hlow, hinto => by
      cases values with
      | nil => rfl
      | cons head rest =>
          exact absurd (hinto 0 (Nat.succ_pos _)) (Nat.not_lt.mpr (hlow 0 (Nat.succ_pos _)))
  | targetLen + 1, base, values, hmono, hlow, hinto => by
      show consReplicate base (runLengthAt base values)
             (reconstructFrom (base + 1) (countsOf targetLen (base + 1) (dropRunAt base values))) = values
      have hupperShift : mapsInto (dropRunAt base values) (base + 1 + targetLen) := by
        have hupper : mapsInto (dropRunAt base values) (base + (targetLen + 1)) :=
          dropRunAt_mapsInto base values (base + (targetLen + 1)) hinto
        have heq : base + (targetLen + 1) = base + 1 + targetLen := by
          rw [← Nat.add_assoc]; exact (Nat.add_right_comm base 1 targetLen).symm
        rw [heq] at hupper; exact hupper
      rw [reconstructFrom_countsOf targetLen (base + 1) (dropRunAt base values)
            (dropRunAt_isWeaklyIncreasing base values hmono)
            (dropRunAt_lowerBound base values hmono hlow)
            hupperShift]
      exact consReplicate_runLengthAt_dropRunAt base values

/-- ★★ **The whole-cell counts round-trip.**  The fold output rebuilds from its own per-target multiplicity list:
`reconstructFrom 0 (countsOf targetPath.length 0 (monadMonotoneMapOf cell)) = monadMonotoneMapOf cell`.  Base `0`
makes the lower bound trivial; the upper bound is `monadMonotoneMapOf_mapsInto`; monotonicity is
`monadMonotoneMapOf_isWeaklyIncreasing`.  This is the map→counts inversion residual the `convOfMapEq` honesty
markers named, now discharged zero-axiom. -/
theorem monadMonotoneMapOf_reconstructRoundTrip {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    reconstructFrom 0 (countsOf targetPath.length 0 (monadMonotoneMapOf cell)) = monadMonotoneMapOf cell := by
  refine reconstructFrom_countsOf targetPath.length 0 (monadMonotoneMapOf cell)
    (monadMonotoneMapOf_isWeaklyIncreasing cell)
    (fun position _ => Nat.zero_le _)
    ?_
  show mapsInto (monadMonotoneMapOf cell) (0 + targetPath.length)
  rw [Nat.zero_add]
  exact monadMonotoneMapOf_mapsInto cell

/-! ## Non-vacuity smokes: the round-trip on concrete fold outputs -/

/-- Smoke: `countsOf` reads the identity map `[0, 1]` (a 2-cell `t^2 ⇒ t^2`) as counts `[1, 1]`. -/
theorem countsOf_id_two : countsOf 2 0 [0, 1] = [1, 1] := rfl

/-- Smoke: `countsOf` reads the merge map `[0, 0]` (the bare `mu`) as counts `[2]` — width-2 codomain-1. -/
theorem countsOf_merge : countsOf 1 0 [0, 0] = [2] := rfl

/-- Smoke: `countsOf` reads `[0, 0, 1]` as `[2, 1]` — the first two strands merge, the third passes. -/
theorem countsOf_merge_first : countsOf 2 0 [0, 0, 1] = [2, 1] := rfl

/-- Smoke: `countsOf` reads `[1]` (target `0` missed) as `[0, 1]` — the insertion / face content. -/
theorem countsOf_insert_first : countsOf 2 0 [1] = [0, 1] := rfl

/-- Smoke: the round-trip COMPUTES on a merge map — `reconstructFrom 0 (countsOf 2 0 [0, 0, 1]) = [0, 0, 1]`. -/
theorem reconstructFrom_countsOf_smoke : reconstructFrom 0 (countsOf 2 0 [0, 0, 1]) = [0, 0, 1] := rfl

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The map→counts inversion is shipped, zero-axiom: the covariant fold lands every free 2-cell
in a WEAKLY-INCREASING value-list (`monadMonotoneMapOf_isWeaklyIncreasing`), and reconstructing from the per-target
multiplicity list read off by the run-peel (`countsOf`) returns the map (`reconstructFrom_countsOf` /
`monadMonotoneMapOf_reconstructRoundTrip`).  Combined with the shipped section
(`monadMonotoneMapOf_wordFromCounts`) this closes BOTH directions of the map ↔ counts correspondence.

**Residual toward `convOfMapEq` (the FLIP): the cell-level insertion-sort `normalizeCell`.**  What remains is the
NORMALIZATION `cell ≈ wordFromCounts (countsOf (monadMonotoneMapOf cell))` under `MonadSaturatedTwoCellConv`.  Its
crux is the vcomp / hcomp WORD-MULTIPLICATIVITY `wordMul_vcomp` / `wordMul_hcomp` — concatenate two canonical
EZ words and re-normalize (degeneracies-then-faces, index-sorted) to one, as a chain of adjacent-swap seed-law Conv
steps (the simplicial identities `σσ` commute, `σδ = id` cancel), terminating by an inversion-count structural
measure (Guiraud–Malbos–Mimram, Example 2.6; Weibel Lemma 8.1.2 uniqueness).  That sort — the faithfulness-weight
brick, the adjunction lane's flag-B analog — is NOT yet landed; the boundary transport
`monadPath_normalForm : P = monadTPower P.length` is a secondary residual.  Until `wordMul_*` + `normalizeCell`
land, `MonadSaturatedCanonicalization.convOfMapEq` is NOT inhabited and
`fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasConvOfMapEqNormalization` /
`fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= true` (this file's own contribution: the inversion). -/
def fxMonad_hasCountsRoundTripInversion : Bool := true


end FX1Poly.Polygraph
