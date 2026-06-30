import FX1Poly.Tier0.Mode.FreeTwoCellSaturatedDecision

/-! # mode-9 keystone — the Schanuel–Street monotone-map model + the simplicial-identity triangle collapse

`FreeTwoCellSaturatedDecision` reduced the SATURATED walking-adjunction 2-cell decision to a single residual: the
**Schanuel–Street monotone-map canonicalization** (`AdjunctionSaturatedCanonicalization`).  By Schanuel–Street
("The free adjunction"), the saturated hom-categories of the walking adjunction are the augmented simplex category
Δ₊: a 2-cell is a MONOTONE MAP between finite ordinals, the unit/counit ARE the degeneracy/face generators, and —
the headline — the TRIANGLE IDENTITY IS the simplicial identity `σ_i ∘ δ_i = id`, so the snake collapse is FREE
in the monotone-map model.

## What this file ships (each piece zero-axiom)

  * **`MonotoneMap` algebra** — monotone maps between finite ordinals encoded as the weakly-increasing value
    `List Nat`: `composeMap` (g∘f by value lookup), `idMap` (`ascendingFrom 0`), the FACE generators `faceMap`
    (δ, the order-preserving injection skipping a value) and the DEGENERACY generators `degenMap` (σ, the
    order-preserving surjection repeating a value).  Equality is `List Nat`'s zero-axiom `DecidableEq`, which
    COMPUTES.
  * ★ **the SIMPLICIAL IDENTITY `composeMap (faceMap i n) (degenMap i n) = idMap n`** — `σ_i ∘ δ_i = id`, proved
    pointwise by the value characterizations of σ and δ (the headline: the triangle's snake collapse is exactly
    this identity, holding for EVERY position `i`, hence under any whisker context).
  * the composition laws `composeMap_idMap_right` / `composeMap` associativity scaffold the vcomp homomorphism.

The harder downstream content — the structural fold `monotoneMapOf`, the soundness `mapEqOfConv`, and the
faithfulness `convOfMapEq` — builds on this self-contained algebra.

Raw Lean 4 + Init; every declaration here is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-
free (the model is plain `List Nat`; the lemmas are structural `Nat`/`List` inductions with hand arithmetic).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The monotone-map value model on `List Nat` -/

/-- Read the value of a monotone map (its value-list) at a position, defaulting to `0` past the end (every
position used in a well-formed composite is in range; the default keeps the function total). -/
def monotoneMapGet : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: rest, position + 1 => monotoneMapGet rest position

/-- The ascending block `[base, base+1, …, base+count-1]` — the building block of identity maps and the
boundary segments of faces / degeneracies. -/
def ascendingFrom : Nat → Nat → List Nat
  | _, 0 => []
  | base, count + 1 => base :: ascendingFrom (base + 1) count

/-- Compose two monotone maps given as value-lists: `(composeMap first second)` applies `second` after `first`,
i.e. its value at `i` is `second (first i)` — looked up by `monotoneMapGet`. -/
def composeMap : List Nat → List Nat → List Nat
  | [], _ => []
  | head :: rest, second => monotoneMapGet second head :: composeMap rest second

/-- The identity monotone map on the ordinal `[n]` — the ascending block `[0, 1, …, n-1]`. -/
def idMap (n : Nat) : List Nat := ascendingFrom 0 n

/-! ## Length + indexing lemmas (structural, propext-free) -/

/-- The ascending block has exactly `count` entries. -/
theorem ascendingFrom_length : ∀ (base count : Nat), (ascendingFrom base count).length = count
  | _, 0 => rfl
  | base, count + 1 => by
      show (ascendingFrom (base + 1) count).length + 1 = count + 1
      rw [ascendingFrom_length (base + 1) count]

/-- The ascending block's value at an in-range position is `base + position`. -/
theorem ascendingFrom_get : ∀ (base count position : Nat), position < count →
    monotoneMapGet (ascendingFrom base count) position = base + position
  | _, 0, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | base, _ + 1, 0, _ => rfl
  | base, count + 1, position + 1, hlt => by
      have hlt' : position < count := Nat.lt_of_succ_lt_succ hlt
      show monotoneMapGet (ascendingFrom (base + 1) count) position = base + (position + 1)
      rw [ascendingFrom_get (base + 1) count position hlt', Nat.add_assoc, Nat.add_comm 1 position]

/-- Composition preserves length (the value-list of `composeMap f g` has `f`'s length). -/
theorem composeMap_length : ∀ (first second : List Nat),
    (composeMap first second).length = first.length
  | [], _ => rfl
  | head :: rest, second => by
      show (composeMap rest second).length + 1 = rest.length + 1
      rw [composeMap_length rest second]

/-- The defining indexing law of composition: `(g∘f)(position) = g (f position)` at every in-range position. -/
theorem composeMap_get : ∀ (first second : List Nat) (position : Nat), position < first.length →
    monotoneMapGet (composeMap first second) position
      = monotoneMapGet second (monotoneMapGet first position)
  | [], _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | head :: rest, second, position + 1, hlt => by
      have hlt' : position < rest.length := Nat.lt_of_succ_lt_succ hlt
      show monotoneMapGet (composeMap rest second) position
        = monotoneMapGet second (monotoneMapGet rest position)
      exact composeMap_get rest second position hlt'

/-- **Extensionality by indexing**: two equal-length value-lists with equal entries at every in-range position
are equal.  The bridge that lets the simplicial identity be proved pointwise. -/
theorem listExtById : ∀ (xs ys : List Nat), xs.length = ys.length →
    (∀ position, position < xs.length → monotoneMapGet xs position = monotoneMapGet ys position) → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _ => Nat.noConfusion hlen
  | headX :: tailX, headY :: tailY, hlen, hget => by
      have hhead : headX = headY := hget 0 (Nat.succ_pos _)
      have hlentail : tailX.length = tailY.length := Nat.succ.inj hlen
      have hgettail : ∀ position, position < tailX.length →
          monotoneMapGet tailX position = monotoneMapGet tailY position := by
        intro position hposition
        exact hget (position + 1) (Nat.succ_lt_succ hposition)
      rw [hhead, listExtById tailX tailY hlentail hgettail]

/-- Right identity for composition: `f ∘ id = f` when `f`'s values are in range `[0, length second)`. The
generic right-unit needs the codomain; the form actually consumed by the vcomp homomorphism is the in-range
version proved at the use site. -/
theorem composeMap_idMap_left : ∀ (second : List Nat) (position : Nat), position < second.length →
    monotoneMapGet (composeMap (idMap second.length) second) position = monotoneMapGet second position := by
  intro second position hposition
  rw [composeMap_get (idMap second.length) second position
        (by rw [show (idMap second.length).length = second.length from ascendingFrom_length 0 second.length];
            exact hposition)]
  show monotoneMapGet second (monotoneMapGet (ascendingFrom 0 second.length) position) = _
  rw [ascendingFrom_get 0 second.length position hposition, Nat.zero_add]

/-! ## The face (δ) and degeneracy (σ) generators -/

/-- The **face** value-list `δ_i : [n] → [n+1]` shifted by `base`: the order-preserving injection that SKIPS the
value `base + i`.  Its value at position `position` is `base + (if position < i then position else position+1)`.
Built by base-shifting recursion so the simplicial identity is a clean structural induction (no `List.map`). -/
def faceFrom : Nat → Nat → Nat → List Nat
  | base, 0,     n     => ascendingFrom (base + 1) n
  | _,    _ + 1, 0     => []
  | base, i + 1, n + 1 => base :: faceFrom (base + 1) i n

/-- The **degeneracy** value-list `σ_i : [n+1] → [n]` shifted by `base`: the order-preserving surjection that
REPEATS the value `base + i`.  Its value at position `position` is `base + (if position ≤ i then position else
position-1)`.  Base-shifting recursion, no `List.map`. -/
def degenFrom : Nat → Nat → Nat → List Nat
  | base, 0,     n     => base :: ascendingFrom base n
  | base, _ + 1, 0     => [base]
  | base, i + 1, n + 1 => base :: degenFrom (base + 1) i n

/-- The face generator `δ_i : [n] → [n+1]` as a value-list (base `0`). -/
def faceMap (i n : Nat) : List Nat := faceFrom 0 i n

/-- The degeneracy generator `σ_i : [n+1] → [n]` as a value-list (base `0`). -/
def degenMap (i n : Nat) : List Nat := degenFrom 0 i n

/-! ## Length + value characterizations of the face / degeneracy generators -/

/-- The face `δ_i` value-list has `n` entries (it is a map out of `[n]`). -/
theorem faceFrom_length : ∀ (base i n : Nat), (faceFrom base i n).length = n
  | base, 0, n => by show (ascendingFrom (base + 1) n).length = n; exact ascendingFrom_length _ _
  | _, _ + 1, 0 => rfl
  | base, i + 1, n + 1 => by
      show (faceFrom (base + 1) i n).length + 1 = n + 1; rw [faceFrom_length (base + 1) i n]

/-- The degeneracy `σ_i` value-list has `n+1` entries (it is a map out of `[n+1]`). -/
theorem degenFrom_length : ∀ (base i n : Nat), (degenFrom base i n).length = n + 1
  | base, 0, n => by show (ascendingFrom base n).length + 1 = n + 1; rw [ascendingFrom_length]
  | _, _ + 1, 0 => rfl
  | base, i + 1, n + 1 => by
      show (degenFrom (base + 1) i n).length + 1 = (n + 1) + 1; rw [degenFrom_length (base + 1) i n]

/-- Below the skipped value, `δ_i` is the identity: value at `position < i` is `base + position`. -/
theorem faceFrom_get_lt : ∀ (base i n position : Nat), position < i → position < n →
    monotoneMapGet (faceFrom base i n) position = base + position
  | _, 0, _, _, hlt, _ => absurd hlt (Nat.not_lt_zero _)
  | _, _ + 1, 0, _, _, hltn => absurd hltn (Nat.not_lt_zero _)
  | _, _ + 1, _ + 1, 0, _, _ => rfl
  | base, i + 1, n + 1, position + 1, hlt, hltn => by
      have hlt' : position < i := Nat.lt_of_succ_lt_succ hlt
      have hltn' : position < n := Nat.lt_of_succ_lt_succ hltn
      show monotoneMapGet (faceFrom (base + 1) i n) position = base + (position + 1)
      rw [faceFrom_get_lt (base + 1) i n position hlt' hltn', Nat.add_assoc, Nat.add_comm 1 position]

/-- At or above the skipped value, `δ_i` shifts up by one: value at `i ≤ position` is `base + (position+1)`. -/
theorem faceFrom_get_ge : ∀ (base i n position : Nat), i ≤ position → position < n →
    monotoneMapGet (faceFrom base i n) position = base + (position + 1)
  | base, 0, n, position, _, hltn => by
      show monotoneMapGet (ascendingFrom (base + 1) n) position = base + (position + 1)
      rw [ascendingFrom_get (base + 1) n position hltn, Nat.add_assoc, Nat.add_comm 1 position]
  | _, _ + 1, 0, _, _, hltn => absurd hltn (Nat.not_lt_zero _)
  | _, i + 1, _ + 1, 0, hik, _ => absurd hik (Nat.not_succ_le_zero i)
  | base, i + 1, n + 1, position + 1, hik, hltn => by
      have hik' : i ≤ position := Nat.le_of_succ_le_succ hik
      have hltn' : position < n := Nat.lt_of_succ_lt_succ hltn
      show monotoneMapGet (faceFrom (base + 1) i n) position = base + ((position + 1) + 1)
      rw [faceFrom_get_ge (base + 1) i n position hik' hltn', Nat.add_assoc, Nat.add_comm 1 (position + 1)]

/-- At or below the repeated value, `σ_i` is the identity: value at `position ≤ i` is `base + position`. -/
theorem degenFrom_get_le : ∀ (base i n position : Nat), position ≤ i → position < n + 1 →
    monotoneMapGet (degenFrom base i n) position = base + position
  | _, 0, _, 0, _, _ => rfl
  | _, 0, _, _ + 1, hle, _ => absurd hle (Nat.not_succ_le_zero _)
  | _, _ + 1, 0, 0, _, _ => rfl
  | _, _ + 1, 0, position + 1, _, hltn => absurd (Nat.lt_of_succ_lt_succ hltn) (Nat.not_lt_zero _)
  | _, _ + 1, _ + 1, 0, _, _ => rfl
  | base, i + 1, n + 1, position + 1, hle, hltn => by
      have hle' : position ≤ i := Nat.le_of_succ_le_succ hle
      have hltn' : position < n + 1 := Nat.lt_of_succ_lt_succ hltn
      show monotoneMapGet (degenFrom (base + 1) i n) position = base + (position + 1)
      rw [degenFrom_get_le (base + 1) i n position hle' hltn', Nat.add_assoc, Nat.add_comm 1 position]

/-- Above the repeated value, `σ_i` shifts down: value at the SUCCESSOR position `position+1` with
`i ≤ position` is `base + position`.  (The subtraction-free form actually used by the simplicial identity.) -/
theorem degenFrom_get_succ : ∀ (base i n position : Nat), i ≤ position → position < n →
    monotoneMapGet (degenFrom base i n) (position + 1) = base + position
  | base, 0, n, position, _, hltn => by
      show monotoneMapGet (ascendingFrom base n) position = base + position
      rw [ascendingFrom_get base n position hltn]
  | _, _ + 1, 0, _, _, hltn => absurd hltn (Nat.not_lt_zero _)
  | _, i + 1, _ + 1, 0, hik, _ => absurd hik (Nat.not_succ_le_zero i)
  | base, i + 1, n + 1, position + 1, hik, hltn => by
      have hik' : i ≤ position := Nat.le_of_succ_le_succ hik
      have hltn' : position < n := Nat.lt_of_succ_lt_succ hltn
      show monotoneMapGet (degenFrom (base + 1) i n) (position + 1) = base + (position + 1)
      rw [degenFrom_get_succ (base + 1) i n position hik' hltn', Nat.add_assoc, Nat.add_comm 1 position]

/-! ## ★ The simplicial identity `σ_i ∘ δ_i = id` — the triangle's snake collapse, FREE -/

/-- Pointwise heart of the simplicial identity: applying `σ_i` after `δ_i` returns the input position.  Split on
`position < i` (δ is the identity there, σ keeps it) versus `i ≤ position` (δ shifts up to `position+1`, σ shifts
it back down).  Each half is one face-value lemma followed by one degeneracy-value lemma — no rewriting beyond the
two characterizations.  This is exactly the simplicial relation `σ_i δ_i = id` read off the value functions. -/
theorem degenFrom_faceFrom_pointwise (i n position : Nat) (hposn : position < n) :
    monotoneMapGet (degenFrom 0 i n) (monotoneMapGet (faceFrom 0 i n) position) = position := by
  rcases Nat.lt_or_ge position i with hlt | hge
  · rw [faceFrom_get_lt 0 i n position hlt hposn, Nat.zero_add,
        degenFrom_get_le 0 i n position (Nat.le_of_lt hlt) (Nat.lt_succ_of_lt hposn), Nat.zero_add]
  · rw [faceFrom_get_ge 0 i n position hge hposn, Nat.zero_add,
        degenFrom_get_succ 0 i n position hge hposn, Nat.zero_add]

/-- ★ **THE SIMPLICIAL IDENTITY `σ_i ∘ δ_i = id`.**  In the monotone-map model, composing the degeneracy `σ_i`
after the face `δ_i` is the identity map on `[n]` — for EVERY position `i`.  This is the Schanuel–Street headline:
the walking adjunction's TRIANGLE IDENTITY *is* this simplicial relation, so the snake's collapse to the identity
is FREE in the monotone-map model (it holds for every `i`, hence under any whisker context — the whiskered
triangle reuses this very identity at the shifted position).  Proved by `listExtById`: equal length `n`, equal
entries by the pointwise heart. -/
theorem composeMap_faceMap_degenMap (i n : Nat) :
    composeMap (faceMap i n) (degenMap i n) = idMap n := by
  apply listExtById
  · rw [composeMap_length]
    show (faceFrom 0 i n).length = (idMap n).length
    rw [faceFrom_length 0 i n, show (idMap n).length = n from ascendingFrom_length 0 n]
  · intro position hpos
    have hlen : (composeMap (faceMap i n) (degenMap i n)).length = n := by
      rw [composeMap_length]; exact faceFrom_length 0 i n
    have hposn : position < n := by rw [hlen] at hpos; exact hpos
    rw [composeMap_get (faceMap i n) (degenMap i n) position
          (by rw [show (faceMap i n).length = n from faceFrom_length 0 i n]; exact hposn)]
    show monotoneMapGet (degenFrom 0 i n) (monotoneMapGet (faceFrom 0 i n) position)
      = monotoneMapGet (idMap n) position
    rw [degenFrom_faceFrom_pointwise i n position hposn]
    show position = monotoneMapGet (ascendingFrom 0 n) position
    rw [ascendingFrom_get 0 n position hposn, Nat.zero_add]

/-- Smoke: the simplicial identity COMPUTES on a concrete instance — `σ_0 ∘ δ_0 = id` on `[1]` is `[0]`. -/
theorem composeMap_faceMap_degenMap_smoke : composeMap (faceMap 0 1) (degenMap 0 1) = idMap 1 := rfl

/-- Pointwise heart of the SECOND simplicial identity `σ_i ∘ δ_{i+1} = id`: the OTHER adjacent face–degeneracy
cancellation (the face one above the repeated value).  Split on `position < i+1` (δ_{i+1} keeps it, σ_i keeps it)
versus `i+1 ≤ position` (δ_{i+1} shifts up, σ_i shifts back). -/
theorem degenFrom_faceFrom_succ_pointwise (i n position : Nat) (hposn : position < n) :
    monotoneMapGet (degenFrom 0 i n) (monotoneMapGet (faceFrom 0 (i + 1) n) position) = position := by
  rcases Nat.lt_or_ge position (i + 1) with hlt | hge
  · rw [faceFrom_get_lt 0 (i + 1) n position hlt hposn, Nat.zero_add,
        degenFrom_get_le 0 i n position (Nat.le_of_lt_succ hlt) (Nat.lt_succ_of_lt hposn), Nat.zero_add]
  · rw [faceFrom_get_ge 0 (i + 1) n position hge hposn, Nat.zero_add,
        degenFrom_get_succ 0 i n position (Nat.le_of_succ_le hge) hposn, Nat.zero_add]

/-- ★ **THE SECOND SIMPLICIAL IDENTITY `σ_i ∘ δ_{i+1} = id`.**  Composing the degeneracy `σ_i` after the face
`δ_{i+1}` (the face just above the repeated value) is also the identity on `[n]`.  Together with
`composeMap_faceMap_degenMap` these are BOTH simplicial relations between an adjacent face and degeneracy, so the
snake of EITHER triangle orientation (left or right) collapses for free in the model. -/
theorem composeMap_faceMap_succ_degenMap (i n : Nat) :
    composeMap (faceMap (i + 1) n) (degenMap i n) = idMap n := by
  apply listExtById
  · rw [composeMap_length]
    show (faceFrom 0 (i + 1) n).length = (idMap n).length
    rw [faceFrom_length 0 (i + 1) n, show (idMap n).length = n from ascendingFrom_length 0 n]
  · intro position hpos
    have hlen : (composeMap (faceMap (i + 1) n) (degenMap i n)).length = n := by
      rw [composeMap_length]; exact faceFrom_length 0 (i + 1) n
    have hposn : position < n := by rw [hlen] at hpos; exact hpos
    rw [composeMap_get (faceMap (i + 1) n) (degenMap i n) position
          (by rw [show (faceMap (i + 1) n).length = n from faceFrom_length 0 (i + 1) n]; exact hposn)]
    show monotoneMapGet (degenFrom 0 i n) (monotoneMapGet (faceFrom 0 (i + 1) n) position)
      = monotoneMapGet (idMap n) position
    rw [degenFrom_faceFrom_succ_pointwise i n position hposn]
    show position = monotoneMapGet (ascendingFrom 0 n) position
    rw [ascendingFrom_get 0 n position hposn, Nat.zero_add]

/-! ## Length restatements at the `faceMap` / `degenMap` / `idMap` level -/

/-- The identity map on `[n]` has `n` entries. -/
theorem idMap_length (n : Nat) : (idMap n).length = n := ascendingFrom_length 0 n

/-- The face generator's value-list has `n` entries (`faceMap`-level restatement). -/
theorem faceMap_length (i n : Nat) : (faceMap i n).length = n := faceFrom_length 0 i n

/-- The degeneracy generator's value-list has `n+1` entries (`degenMap`-level restatement). -/
theorem degenMap_length (i n : Nat) : (degenMap i n).length = n + 1 := degenFrom_length 0 i n

/-! ## ★ The COMMUTING simplicial identities `δδ` / `σσ` / `σδ` — the Godement-independence algebra

The two identities above are the `σδ = id` cancellations (the triangle's snake collapse).  The OTHER simplicial
relations are the COMMUTATIONS: two faces, two degeneracies, or a separated face/degeneracy at distinct positions
COMMUTE (with an index shift).  These are exactly the algebra that a Godement / interchange transposition of two
horizontally-independent atoms must reduce to — when the two atoms live in disjoint blocks their monotone-map
positions differ and the post-compositions commute by precisely these laws.  Each is proved pointwise on the
value characterizations, the same way as the `σδ = id` cancellation. -/

/-- Pointwise heart of the cosimplicial identity `δ_j δ_i = δ_i δ_{j-1}` (faces commute), in the shift-free form
`δ_{j+1} ∘ δ_i = δ_i ∘ δ_j` for `i ≤ j`: applying `δ_i` then `δ_{j+1}` equals applying `δ_j` then `δ_i`.  Split on
`position < i` / `i ≤ position < j` / `j ≤ position`; each region is two face-value lemmas. -/
theorem faceFrom_faceFrom_commute_pointwise (i j n position : Nat) (hij : i ≤ j) (hposn : position < n) :
    monotoneMapGet (faceFrom 0 (j + 1) (n + 1)) (monotoneMapGet (faceFrom 0 i n) position)
      = monotoneMapGet (faceFrom 0 i (n + 1)) (monotoneMapGet (faceFrom 0 j n) position) := by
  rcases Nat.lt_or_ge position i with hposi | hposi
  · have hposj : position < j := Nat.lt_of_lt_of_le hposi hij
    rw [faceFrom_get_lt 0 i n position hposi hposn, Nat.zero_add,
        faceFrom_get_lt 0 (j + 1) (n + 1) position (Nat.lt_succ_of_lt hposj) (Nat.lt_succ_of_lt hposn), Nat.zero_add,
        faceFrom_get_lt 0 j n position hposj hposn, Nat.zero_add,
        faceFrom_get_lt 0 i (n + 1) position hposi (Nat.lt_succ_of_lt hposn), Nat.zero_add]
  · rcases Nat.lt_or_ge position j with hposj | hposj
    · rw [faceFrom_get_ge 0 i n position hposi hposn, Nat.zero_add,
          faceFrom_get_lt 0 (j + 1) (n + 1) (position + 1) (Nat.succ_lt_succ hposj) (Nat.succ_lt_succ hposn), Nat.zero_add,
          faceFrom_get_lt 0 j n position hposj hposn, Nat.zero_add,
          faceFrom_get_ge 0 i (n + 1) position hposi (Nat.lt_succ_of_lt hposn), Nat.zero_add]
    · rw [faceFrom_get_ge 0 i n position hposi hposn, Nat.zero_add,
          faceFrom_get_ge 0 (j + 1) (n + 1) (position + 1) (Nat.succ_le_succ hposj) (Nat.succ_lt_succ hposn), Nat.zero_add,
          faceFrom_get_ge 0 j n position hposj hposn, Nat.zero_add,
          faceFrom_get_ge 0 i (n + 1) (position + 1) (Nat.le_succ_of_le hposi) (Nat.succ_lt_succ hposn), Nat.zero_add]

/-- ★ **The cosimplicial (face-face) commutation `δ_{j+1} ∘ δ_i = δ_i ∘ δ_j` for `i ≤ j`.**  Two faces at distinct
positions commute with the standard index shift — the monotone-map shadow of two horizontally-independent CUP
atoms transposing.  Proved by `listExtById` from the pointwise heart. -/
theorem composeMap_faceMap_faceMap_commute (i j n : Nat) (hij : i ≤ j) :
    composeMap (faceMap i n) (faceMap (j + 1) (n + 1))
      = composeMap (faceMap j n) (faceMap i (n + 1)) := by
  apply listExtById
  · rw [composeMap_length, composeMap_length, faceMap_length, faceMap_length]
  · intro position hpos
    rw [composeMap_length, faceMap_length] at hpos
    rw [composeMap_get (faceMap i n) (faceMap (j + 1) (n + 1)) position
          (by rw [faceMap_length]; exact hpos),
        composeMap_get (faceMap j n) (faceMap i (n + 1)) position
          (by rw [faceMap_length]; exact hpos)]
    exact faceFrom_faceFrom_commute_pointwise i j n position hij hpos

/-- Pointwise heart of the codegeneracy identity `σ_j σ_i = σ_i σ_{j+1}` (degeneracies commute), shift-free as
`σ_j ∘ σ_i = σ_i ∘ σ_{j+1}` for `i ≤ j`, `j < n`.  Split on `position ≤ i` / `i < position ≤ j+1` / `j+1 <
position`, each region's repeated value handled by the `≤`-value or successor-value degeneracy lemma. -/
theorem degenFrom_degenFrom_commute_pointwise (i j n position : Nat)
    (hij : i ≤ j) (hjn : j < n) (hposn : position < n + 2) :
    monotoneMapGet (degenFrom 0 j n) (monotoneMapGet (degenFrom 0 i (n + 1)) position)
      = monotoneMapGet (degenFrom 0 i n) (monotoneMapGet (degenFrom 0 (j + 1) (n + 1)) position) := by
  rcases Nat.lt_or_ge position (i + 1) with hposi | hposi
  · have hposle : position ≤ i := Nat.le_of_lt_succ hposi
    have hposn1 : position < n + 1 := Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hposle hij) hjn)
    rw [degenFrom_get_le 0 i (n + 1) position hposle hposn, Nat.zero_add,
        degenFrom_get_le 0 j n position (Nat.le_trans hposle hij) hposn1, Nat.zero_add,
        degenFrom_get_le 0 (j + 1) (n + 1) position (Nat.le_trans hposle (Nat.le_succ_of_le hij)) hposn, Nat.zero_add,
        degenFrom_get_le 0 i n position hposle hposn1, Nat.zero_add]
  · obtain ⟨predPos, rfl⟩ : ∃ earlierPos, position = earlierPos + 1 :=
      ⟨position - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos i) hposi)).symm⟩
    have hipred : i ≤ predPos := Nat.le_of_succ_le_succ hposi
    have hpredn1 : predPos < n + 1 := Nat.lt_of_succ_lt_succ hposn
    rcases Nat.lt_or_ge predPos (j + 1) with hpredj | hpredj
    · have hpredjle : predPos ≤ j := Nat.le_of_lt_succ hpredj
      have hpredn : predPos < n := Nat.lt_of_le_of_lt hpredjle hjn
      rw [degenFrom_get_succ 0 i (n + 1) predPos hipred hpredn1, Nat.zero_add,
          degenFrom_get_le 0 j n predPos hpredjle (Nat.lt_succ_of_lt hpredn), Nat.zero_add,
          degenFrom_get_le 0 (j + 1) (n + 1) (predPos + 1) (Nat.succ_le_succ hpredjle) hposn, Nat.zero_add,
          degenFrom_get_succ 0 i n predPos hipred hpredn, Nat.zero_add]
    · obtain ⟨predPred, rfl⟩ : ∃ earlierPos, predPos = earlierPos + 1 :=
        ⟨predPos - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos j) hpredj)).symm⟩
      have hjpred : j ≤ predPred := Nat.le_of_succ_le_succ hpredj
      have hpredn : predPred < n := Nat.lt_of_succ_lt_succ hpredn1
      rw [degenFrom_get_succ 0 i (n + 1) (predPred + 1) (Nat.le_succ_of_le (Nat.le_trans hij hjpred)) hpredn1, Nat.zero_add,
          degenFrom_get_succ 0 j n predPred hjpred hpredn, Nat.zero_add,
          degenFrom_get_succ 0 (j + 1) (n + 1) (predPred + 1) (Nat.succ_le_succ hjpred) hpredn1, Nat.zero_add,
          degenFrom_get_succ 0 i n predPred (Nat.le_trans hij hjpred) hpredn, Nat.zero_add]

/-- ★ **The codegeneracy (degeneracy-degeneracy) commutation `σ_j ∘ σ_i = σ_i ∘ σ_{j+1}` for `i ≤ j`, `j < n`.**
Two degeneracies at distinct positions commute — the shadow of two horizontally-independent CAP atoms transposing.
Proved by `listExtById` from the pointwise heart. -/
theorem composeMap_degenMap_degenMap_commute (i j n : Nat) (hij : i ≤ j) (hjn : j < n) :
    composeMap (degenMap i (n + 1)) (degenMap j n)
      = composeMap (degenMap (j + 1) (n + 1)) (degenMap i n) := by
  apply listExtById
  · rw [composeMap_length, composeMap_length, degenMap_length, degenMap_length]
  · intro position hpos
    rw [composeMap_length, degenMap_length] at hpos
    rw [composeMap_get (degenMap i (n + 1)) (degenMap j n) position
          (by rw [degenMap_length]; exact hpos),
        composeMap_get (degenMap (j + 1) (n + 1)) (degenMap i n) position
          (by rw [degenMap_length]; exact hpos)]
    exact degenFrom_degenFrom_commute_pointwise i j n position hij hjn hpos

/-- Pointwise heart of the mixed identity `σ_j δ_i = δ_i σ_{j-1}` (separated face below the repeated value),
shift-free as `σ_{j+1} ∘ δ_i = δ_i ∘ σ_j` for `i ≤ j`, `j < n`.  The boundary `position = j` is its own sub-case
(the face lands exactly on the repeated value's lower copy). -/
theorem degenFrom_faceFrom_lowerCommute_pointwise (i j n position : Nat)
    (hij : i ≤ j) (hjn : j < n) (hposn : position < n + 1) :
    monotoneMapGet (degenFrom 0 (j + 1) (n + 1)) (monotoneMapGet (faceFrom 0 i (n + 1)) position)
      = monotoneMapGet (faceFrom 0 i n) (monotoneMapGet (degenFrom 0 j n) position) := by
  rcases Nat.lt_or_ge position i with hposi | hposi
  · have hposj : position < j := Nat.lt_of_lt_of_le hposi hij
    have hposn' : position < n := Nat.lt_trans hposj hjn
    rw [faceFrom_get_lt 0 i (n + 1) position hposi hposn, Nat.zero_add,
        degenFrom_get_le 0 (j + 1) (n + 1) position (Nat.le_of_lt (Nat.lt_succ_of_lt hposj)) (Nat.lt_succ_of_lt hposn), Nat.zero_add,
        degenFrom_get_le 0 j n position (Nat.le_of_lt hposj) hposn, Nat.zero_add,
        faceFrom_get_lt 0 i n position hposi hposn', Nat.zero_add]
  · rcases Nat.lt_or_ge position j with hposj | hposj
    · have hposn' : position < n := Nat.lt_trans hposj hjn
      rw [faceFrom_get_ge 0 i (n + 1) position hposi hposn, Nat.zero_add,
          degenFrom_get_le 0 (j + 1) (n + 1) (position + 1) (Nat.succ_le_succ (Nat.le_of_lt hposj)) (Nat.succ_lt_succ hposn), Nat.zero_add,
          degenFrom_get_le 0 j n position (Nat.le_of_lt hposj) hposn, Nat.zero_add,
          faceFrom_get_ge 0 i n position hposi hposn', Nat.zero_add]
    · rcases Nat.eq_or_lt_of_le hposj with hposeqj | hposgtj
      · subst hposeqj
        rw [faceFrom_get_ge 0 i (n + 1) j hposi hposn, Nat.zero_add,
            degenFrom_get_le 0 (j + 1) (n + 1) (j + 1) (Nat.le_refl _) (Nat.succ_lt_succ hposn), Nat.zero_add,
            degenFrom_get_le 0 j n j (Nat.le_refl _) hposn, Nat.zero_add,
            faceFrom_get_ge 0 i n j hposi hjn, Nat.zero_add]
      · obtain ⟨predPos, rfl⟩ : ∃ earlierPos, position = earlierPos + 1 :=
          ⟨position - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos j) hposgtj)).symm⟩
        have hjpred : j ≤ predPos := Nat.le_of_succ_le_succ hposgtj
        have hpredn : predPos < n := Nat.lt_of_succ_lt_succ hposn
        rw [faceFrom_get_ge 0 i (n + 1) (predPos + 1) (Nat.le_succ_of_le (Nat.le_trans hij hjpred)) hposn, Nat.zero_add,
            degenFrom_get_succ 0 (j + 1) (n + 1) (predPos + 1) (Nat.succ_le_succ hjpred) hposn, Nat.zero_add,
            degenFrom_get_succ 0 j n predPos hjpred hpredn, Nat.zero_add,
            faceFrom_get_ge 0 i n predPos (Nat.le_trans hij hjpred) hpredn, Nat.zero_add]

/-- ★ **The mixed (face-degeneracy) commutation `σ_{j+1} ∘ δ_i = δ_i ∘ σ_j` for `i ≤ j`, `j < n`.**  A face and a
separated degeneracy commute — the shadow of a CUP and a CAP in disjoint blocks transposing (the genuine
content of a Godement step on a cup/cap pair, as opposed to the adjacent `σδ = id` snake collapse).  Proved by
`listExtById` from the pointwise heart. -/
theorem composeMap_faceMap_degenMap_lowerCommute (i j n : Nat) (hij : i ≤ j) (hjn : j < n) :
    composeMap (faceMap i (n + 1)) (degenMap (j + 1) (n + 1))
      = composeMap (degenMap j n) (faceMap i n) := by
  apply listExtById
  · rw [composeMap_length, composeMap_length, faceMap_length, degenMap_length]
  · intro position hpos
    rw [composeMap_length, faceMap_length] at hpos
    rw [composeMap_get (faceMap i (n + 1)) (degenMap (j + 1) (n + 1)) position
          (by rw [faceMap_length]; exact hpos),
        composeMap_get (degenMap j n) (faceMap i n) position
          (by rw [degenMap_length]; exact hpos)]
    exact degenFrom_faceFrom_lowerCommute_pointwise i j n position hij hjn hpos

/-! ## Composition identities scaffolding the vcomp homomorphism + the snake collapse -/

/-- Left identity of composition `id ∘ f = f` when `id` is sized to `f`'s domain — proved by indexing
extensionality (the identity map's value at an in-range position is the position itself). -/
theorem composeMap_idMap_eq (first : List Nat) : composeMap (idMap first.length) first = first := by
  apply listExtById
  · rw [composeMap_length, idMap_length]
  · intro position hpos
    rw [composeMap_length, idMap_length] at hpos
    exact composeMap_idMap_left first position hpos

/-- ★ **The snake collapse at any width, via the simplicial identity.**  A cup (a face `δ_p`) immediately
followed by a cap (a degeneracy `σ_p`) at the SAME position, composed onto any width-`w` identity, collapses back
to the identity `[w]`.  This is the monotone-map shadow of the walking adjunction's TRIANGLE IDENTITY, and it is
discharged by exactly the simplicial identity `composeMap_faceMap_degenMap` — the headline that the snake's
collapse is FREE in the monotone-map model, holding at EVERY position `p` and width `w` (so the whiskered
triangle, which shifts `p` and `w` by the whisker context, reuses this very lemma). -/
theorem snakeCollapseAtWidth (position width : Nat) :
    composeMap (composeMap (idMap width) (faceMap position width)) (degenMap position width) = idMap width := by
  have step : composeMap (idMap width) (faceMap position width) = faceMap position width := by
    have collapse := composeMap_idMap_eq (faceMap position width)
    rw [faceMap_length position width] at collapse
    exact collapse
  rw [step, composeMap_faceMap_degenMap]

/-! ## ★ The monotone-map model is a CATEGORY of genuinely-monotone maps — the Δ₊ structure

The file calls these value-lists "monotone maps"; this section PROVES it.  With the codomain tracked
(`mapsInto`), `composeMap` is associative (`composeMap_assoc`) and unital on the right (`composeMap_idMap_right`,
complementing the unconditional left unit `composeMap_idMap_eq`), so the value-lists form a CATEGORY.  And every
generator is genuinely WEAKLY INCREASING (`idMap` / `faceMap` / `degenMap`), a property closed under composition
(`composeMap_isWeaklyIncreasing`) — so the model is the category of MONOTONE maps between finite ordinals, i.e.
the augmented simplex category Δ₊ exactly as Schanuel–Street require.  Tracking the codomain (`mapsInto`) is the
variance-aware refinement a bare `List Nat` lacks: it is what makes associativity hold (an out-of-range value
would break it). -/

/-- A value-list maps INTO the ordinal `[codomain]`: every in-range value is `< codomain`.  This is the codomain
half of a TYPED Δ₊ morphism — the data a bare value-list omits and the reason composition needs it. -/
def mapsInto (values : List Nat) (codomain : Nat) : Prop :=
  ∀ position, position < values.length → monotoneMapGet values position < codomain

/-- A value-list is WEAKLY INCREASING — a genuine monotone map: its value at a lower position never exceeds its
value at a higher one. -/
def isWeaklyIncreasing (values : List Nat) : Prop :=
  ∀ lowerPos upperPos, lowerPos ≤ upperPos → upperPos < values.length →
    monotoneMapGet values lowerPos ≤ monotoneMapGet values upperPos

/-- ★ **Associativity of `composeMap`** when the first map lands in the second's domain (`mapsInto`).  The
category-composition law of Δ₊ in the model; the in-range side-condition is exactly why the codomain must be
tracked (out of range, the deep lookup would default to `0` and break associativity). -/
theorem composeMap_assoc (first second third : List Nat)
    (hrange : mapsInto first second.length) :
    composeMap (composeMap first second) third = composeMap first (composeMap second third) := by
  apply listExtById
  · rw [composeMap_length, composeMap_length, composeMap_length]
  · intro position hpos
    rw [composeMap_length, composeMap_length] at hpos
    rw [composeMap_get (composeMap first second) third position (by rw [composeMap_length]; exact hpos),
        composeMap_get first second position hpos,
        composeMap_get first (composeMap second third) position hpos,
        composeMap_get second third (monotoneMapGet first position) (hrange position hpos)]

/-- `idMap codomain` returns an in-range position to itself. -/
theorem monotoneMapGet_idMap (codomain position : Nat) (hpos : position < codomain) :
    monotoneMapGet (idMap codomain) position = position := by
  show monotoneMapGet (ascendingFrom 0 codomain) position = position
  rw [ascendingFrom_get 0 codomain position hpos, Nat.zero_add]

/-- ★ **Right identity of `composeMap`** when the map lands in `[codomain]`: `f ∘ id_{codomain} = f`.  Together
with the unconditional left unit `composeMap_idMap_eq`, the unit laws of the Δ₊ category. -/
theorem composeMap_idMap_right (values : List Nat) (codomain : Nat)
    (hrange : mapsInto values codomain) :
    composeMap values (idMap codomain) = values := by
  apply listExtById
  · rw [composeMap_length]
  · intro position hpos
    rw [composeMap_length] at hpos
    rw [composeMap_get values (idMap codomain) position hpos]
    exact monotoneMapGet_idMap codomain (monotoneMapGet values position) (hrange position hpos)

/-- The identity map is weakly increasing. -/
theorem idMap_isWeaklyIncreasing (codomain : Nat) : isWeaklyIncreasing (idMap codomain) := by
  intro lowerPos upperPos hle hupper
  rw [idMap_length] at hupper
  rw [monotoneMapGet_idMap codomain lowerPos (Nat.lt_of_le_of_lt hle hupper),
      monotoneMapGet_idMap codomain upperPos hupper]
  exact hle

/-- ★ The FACE generator `δ_i` is weakly increasing (an order-preserving injection). -/
theorem faceMap_isWeaklyIncreasing (i n : Nat) : isWeaklyIncreasing (faceMap i n) := by
  intro lowerPos upperPos hle hupper
  rw [faceMap_length] at hupper
  have hlower : lowerPos < n := Nat.lt_of_le_of_lt hle hupper
  show monotoneMapGet (faceFrom 0 i n) lowerPos ≤ monotoneMapGet (faceFrom 0 i n) upperPos
  rcases Nat.lt_or_ge lowerPos i with hli | hli
  · rcases Nat.lt_or_ge upperPos i with hui | hui
    · rw [faceFrom_get_lt 0 i n lowerPos hli hlower, faceFrom_get_lt 0 i n upperPos hui hupper]
      exact Nat.add_le_add_left hle 0
    · rw [faceFrom_get_lt 0 i n lowerPos hli hlower, faceFrom_get_ge 0 i n upperPos hui hupper]
      exact Nat.add_le_add_left (Nat.le_trans hle (Nat.le_succ upperPos)) 0
  · have hui : i ≤ upperPos := Nat.le_trans hli hle
    rw [faceFrom_get_ge 0 i n lowerPos hli hlower, faceFrom_get_ge 0 i n upperPos hui hupper]
    exact Nat.add_le_add_left (Nat.add_le_add_right hle 1) 0

/-- ★ The DEGENERACY generator `σ_i` is weakly increasing (an order-preserving surjection). -/
theorem degenMap_isWeaklyIncreasing (i n : Nat) : isWeaklyIncreasing (degenMap i n) := by
  intro lowerPos upperPos hle hupper
  rw [degenMap_length] at hupper
  show monotoneMapGet (degenFrom 0 i n) lowerPos ≤ monotoneMapGet (degenFrom 0 i n) upperPos
  rcases Nat.lt_or_ge lowerPos (i + 1) with hli | hli
  · have hlle : lowerPos ≤ i := Nat.le_of_lt_succ hli
    rw [degenFrom_get_le 0 i n lowerPos hlle (Nat.lt_of_le_of_lt hle hupper), Nat.zero_add]
    rcases Nat.lt_or_ge upperPos (i + 1) with hui | hui
    · rw [degenFrom_get_le 0 i n upperPos (Nat.le_of_lt_succ hui) hupper, Nat.zero_add]; exact hle
    · obtain ⟨upperPred, rfl⟩ : ∃ earlierPos, upperPos = earlierPos + 1 :=
        ⟨upperPos - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos i) hui)).symm⟩
      have hiup : i ≤ upperPred := Nat.le_of_succ_le_succ hui
      rw [degenFrom_get_succ 0 i n upperPred hiup (Nat.lt_of_succ_lt_succ hupper), Nat.zero_add]
      exact Nat.le_trans hlle hiup
  · obtain ⟨lowerPred, rfl⟩ : ∃ earlierPos, lowerPos = earlierPos + 1 :=
      ⟨lowerPos - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos i) hli)).symm⟩
    have hilo : i ≤ lowerPred := Nat.le_of_succ_le_succ hli
    have huppos : 0 < upperPos := Nat.lt_of_lt_of_le (Nat.succ_pos lowerPred) hle
    obtain ⟨upperPred, rfl⟩ : ∃ earlierPos, upperPos = earlierPos + 1 :=
      ⟨upperPos - 1, (Nat.succ_pred_eq_of_pos huppos).symm⟩
    have hlepred : lowerPred ≤ upperPred := Nat.le_of_succ_le_succ hle
    have hiup : i ≤ upperPred := Nat.le_trans hilo hlepred
    rw [degenFrom_get_succ 0 i n lowerPred hilo (Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hle hupper)), Nat.zero_add,
        degenFrom_get_succ 0 i n upperPred hiup (Nat.lt_of_succ_lt_succ hupper), Nat.zero_add]
    exact hlepred

/-- ★ **Composition of weakly-increasing maps is weakly increasing** (the first landing in the second's domain) —
composites of monotone maps are monotone, the closure that makes the model a category OF monotone maps. -/
theorem composeMap_isWeaklyIncreasing (first second : List Nat)
    (hfirst : isWeaklyIncreasing first) (hsecond : isWeaklyIncreasing second)
    (hrange : mapsInto first second.length) : isWeaklyIncreasing (composeMap first second) := by
  intro lowerPos upperPos hle hupper
  rw [composeMap_length] at hupper
  have hlower : lowerPos < first.length := Nat.lt_of_le_of_lt hle hupper
  rw [composeMap_get first second lowerPos hlower, composeMap_get first second upperPos hupper]
  exact hsecond (monotoneMapGet first lowerPos) (monotoneMapGet first upperPos)
    (hfirst lowerPos upperPos hle hupper) (hrange upperPos hupper)

/-! ## ★ The codomain-tracked, variance-aware `MonotoneMap` morphism type — junk made UNREPRESENTABLE

A bare `List Nat` is an UNTRACKED-CODOMAIN encoding: nothing pins the ordinal a value-list maps INTO, so a junk
list like `[5]` claiming to map into `[0]` typechecks, and that is exactly what refutes the Godement-soundness
residual (`monoGodementMapCommute_refuted`'s `state = (0, [5])`) and what escapes the counit's codomain
(`counitMonotoneMap_notMapsInto`).  `MonotoneMap domainWidth codomainWidth` bundles the three invariants a genuine
Δ₊ morphism `[domainWidth] → [codomainWidth]` carries: `hasLength` pins the domain ordinal, `mapsIntoCodomain`
pins the codomain (so an out-of-range entry is a TYPE ERROR), and `isMonotone` makes it weakly increasing.  Then
`(0, [5])` is unrepresentable (`MonotoneMap 1 0` is uninhabited — no entry is `< 0`), the augmentation is free
(`MonotoneMap (d+1) 0` is uninhabited; `MonotoneMap 0 c` forces `values = []`), and `composeMap`'s in-range side
condition holds BY CONSTRUCTION.

### ★ The VARIANCE decision (read the cell definitions: `Mode.lean` `AdjunctionTwoCell`)

The walking-adjunction hom-categories are NOT variance-uniform, so `MonotoneMap` is the COVARIANT Δ₊ morphism and
the variance flip is exposed as a TYPE-LEVEL side condition rather than absorbed silently:

  * `unit : id_base ⟹ L·R` lives at hom `base ⟶ base` — a CUP that GROWS the ordinal; covariantly it is the FACE
    `MonotoneMap.face` (`[n] → [n+1]`).  `counit : R·L ⟹ id_tip` lives at hom `tip ⟶ tip`.
  * At mode `base` (`Adj(+,+) ≅ Δ₊`, covariant) a (whiskered) counit caps an INTERNAL `R·L` seam of `(L·R)^w`,
    block position `i < w`, so it is a GENUINE degeneracy `σ_i : [w] → [w-1]` (`MonotoneMap.degeneracy`, gated on
    `i < n`), and in-range is preserved.
  * At mode `tip` (`Adj(−,−) ≅ Δ₊^op`) the bare counit caps the LAST (only) `R·L` block — block position `i = w-1`
    — where the covariant fold mislabels it as `degenMap (w-1) (w-1) = idMap w` (`degenMap_self_eq_idMapSucc`): a
    no-op claiming a width drop, escaping its claimed codomain.  `MonotoneMap.degeneracy` REFUSES this case (it
    requires `i < n`), so the variance flip is a representability obstruction, not a silent junk list.  The honest
    op-variant treatment (reading the tip map backwards, Δ₊^op) is the faithfulness residual; the soundness leg
    only needs that the boundary case is excluded from the covariant degeneracy, which the gate `i < n` enforces. -/

/-- The identity value-list maps into its own ordinal `[n]` (every in-range position returns itself, `< n`). -/
theorem idMap_mapsInto (n : Nat) : mapsInto (idMap n) n := by
  intro position hpos
  rw [idMap_length] at hpos
  rw [monotoneMapGet_idMap n position hpos]
  exact hpos

/-- The FACE `δ_i : [n] → [n+1]` lands in `[n+1]`: below the skipped value it returns `position < n < n+1`, at or
above it returns `position + 1 ≤ n < n+1`. -/
theorem faceMap_mapsInto (i n : Nat) : mapsInto (faceMap i n) (n + 1) := by
  intro position hpos
  rw [faceMap_length] at hpos
  show monotoneMapGet (faceFrom 0 i n) position < n + 1
  rcases Nat.lt_or_ge position i with hlt | hge
  · rw [faceFrom_get_lt 0 i n position hlt hpos, Nat.zero_add]
    exact Nat.lt_succ_of_lt hpos
  · rw [faceFrom_get_ge 0 i n position hge hpos, Nat.zero_add]
    exact Nat.succ_lt_succ hpos

/-- The DEGENERACY `σ_i : [n+1] → [n]` lands in `[n]` PROVIDED `i < n` (a genuine internal merge).  At the boundary
`i = n` this FAILS — `degenMap n n = idMap (n+1)` hits `n ∉ [n]` — which is exactly the Δ₊^op variance flip the
tracked type refuses to label as a degeneracy. -/
theorem degenMap_mapsInto (i n : Nat) (hi : i < n) : mapsInto (degenMap i n) n := by
  intro position hpos
  rw [degenMap_length] at hpos
  show monotoneMapGet (degenFrom 0 i n) position < n
  rcases Nat.lt_or_ge position (i + 1) with hle | hge
  · rw [degenFrom_get_le 0 i n position (Nat.le_of_lt_succ hle) hpos, Nat.zero_add]
    exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hle) hi
  · obtain ⟨predPos, rfl⟩ : ∃ earlierPos, position = earlierPos + 1 :=
      ⟨position - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos i) hge)).symm⟩
    have hip : i ≤ predPos := Nat.le_of_succ_le_succ hge
    have hpn : predPos < n := Nat.lt_of_succ_lt_succ hpos
    rw [degenFrom_get_succ 0 i n predPos hip hpn, Nat.zero_add]
    exact hpn

/-- ★ A **codomain-tracked monotone map** `[domainWidth] → [codomainWidth]` — a genuine morphism of the augmented
simplex category Δ₊.  The three bundled invariants make every off-path value-list UNREPRESENTABLE: `hasLength`
pins the domain ordinal, `mapsIntoCodomain` pins the codomain (an out-of-range entry cannot be constructed), and
`isMonotone` makes it weakly increasing.  Equality reduces to value-list equality by proof irrelevance
(`MonotoneMap.ext`). -/
structure MonotoneMap (domainWidth codomainWidth : Nat) where
  /-- The value-list — the map's values at `0, 1, …, domainWidth-1`. -/
  values : List Nat
  /-- The map is out of the ordinal `[domainWidth]` (its value-list has exactly that length). -/
  hasLength : values.length = domainWidth
  /-- The map lands in the ordinal `[codomainWidth]` (every value is `< codomainWidth`). -/
  mapsIntoCodomain : mapsInto values codomainWidth
  /-- The map is genuinely monotone (weakly increasing). -/
  isMonotone : isWeaklyIncreasing values

/-- ★ **Extensionality**: two tracked maps with equal value-lists are equal — the three invariant fields are
`Prop`s, so Lean's definitional proof irrelevance collapses them once the values match.  Lets the category laws be
proved by transporting the bare-`List` identities. -/
theorem MonotoneMap.ext {domainWidth codomainWidth : Nat}
    {first second : MonotoneMap domainWidth codomainWidth}
    (valuesEqual : first.values = second.values) : first = second := by
  cases first; cases second; cases valuesEqual; rfl

/-- The identity morphism `[n] → [n]` of the tracked category. -/
def MonotoneMap.identity (n : Nat) : MonotoneMap n n :=
  ⟨idMap n, idMap_length n, idMap_mapsInto n, idMap_isWeaklyIncreasing n⟩

/-- The FACE generator `δ_i : [n] → [n+1]` as a tracked morphism. -/
def MonotoneMap.face (i n : Nat) : MonotoneMap n (n + 1) :=
  ⟨faceMap i n, faceMap_length i n, faceMap_mapsInto i n, faceMap_isWeaklyIncreasing i n⟩

/-- The DEGENERACY generator `σ_i : [n+1] → [n]` as a tracked morphism — gated on `i < n` (an internal merge); the
boundary `i = n` is the Δ₊^op variance case and is NOT a tracked degeneracy. -/
def MonotoneMap.degeneracy (i n : Nat) (hlt : i < n) : MonotoneMap (n + 1) n :=
  ⟨degenMap i n, degenMap_length i n, degenMap_mapsInto i n hlt, degenMap_isWeaklyIncreasing i n⟩

/-- The middle map of a composite lands in the second factor's domain ordinal — the in-range side condition
`composeMap` needs, now holding BY CONSTRUCTION from the tracked codomain. -/
theorem MonotoneMap.mapsIntoMiddle {domainWidth middleWidth codomainWidth : Nat}
    (first : MonotoneMap domainWidth middleWidth) (second : MonotoneMap middleWidth codomainWidth) :
    mapsInto first.values second.values.length := by
  intro position hpos
  rw [second.hasLength]
  exact first.mapsIntoCodomain position hpos

/-- ★ **Composition** of tracked morphisms `[a] → [b] → [c]`, landing `[a] → [c]`.  Totality is the headline: the
in-range invariants (`first.mapsIntoCodomain` plus `second.hasLength`) discharge `composeMap`'s side condition by
construction, so no junk arises. -/
def MonotoneMap.comp {domainWidth middleWidth codomainWidth : Nat}
    (first : MonotoneMap domainWidth middleWidth) (second : MonotoneMap middleWidth codomainWidth) :
    MonotoneMap domainWidth codomainWidth where
  values := composeMap first.values second.values
  hasLength := by rw [composeMap_length, first.hasLength]
  mapsIntoCodomain := by
    intro position hpos
    rw [composeMap_length] at hpos
    rw [composeMap_get first.values second.values position hpos]
    exact second.mapsIntoCodomain (monotoneMapGet first.values position)
      (MonotoneMap.mapsIntoMiddle first second position hpos)
  isMonotone :=
    composeMap_isWeaklyIncreasing first.values second.values first.isMonotone second.isMonotone
      (MonotoneMap.mapsIntoMiddle first second)

/-- ★ **Associativity** of tracked composition — the category-composition law, now UNCONDITIONAL (the in-range
side condition `composeMap_assoc` once needed is supplied by the tracked codomain). -/
theorem MonotoneMap.comp_assoc {domainWidth middleOneWidth middleTwoWidth codomainWidth : Nat}
    (first : MonotoneMap domainWidth middleOneWidth) (second : MonotoneMap middleOneWidth middleTwoWidth)
    (third : MonotoneMap middleTwoWidth codomainWidth) :
    (first.comp second).comp third = first.comp (second.comp third) :=
  MonotoneMap.ext (composeMap_assoc first.values second.values third.values
    (MonotoneMap.mapsIntoMiddle first second))

/-- ★ **Left unit** `id ∘ f = f` of tracked composition (unconditional). -/
theorem MonotoneMap.identity_comp {domainWidth codomainWidth : Nat}
    (first : MonotoneMap domainWidth codomainWidth) :
    (MonotoneMap.identity domainWidth).comp first = first :=
  MonotoneMap.ext (by
    have hcollapse := composeMap_idMap_eq first.values
    rw [first.hasLength] at hcollapse
    exact hcollapse)

/-- ★ **Right unit** `f ∘ id = f` of tracked composition — its in-range side condition is exactly
`first.mapsIntoCodomain`. -/
theorem MonotoneMap.comp_identity {domainWidth codomainWidth : Nat}
    (first : MonotoneMap domainWidth codomainWidth) :
    first.comp (MonotoneMap.identity codomainWidth) = first :=
  MonotoneMap.ext (composeMap_idMap_right first.values codomainWidth first.mapsIntoCodomain)

/-- The augmentation, FREE from tracking: a tracked map out of a positive ordinal cannot land in the empty ordinal
`[0]` — `MonotoneMap (domainWidth+1) 0` is uninhabited (its first value would be `< 0`).  This is Δ₊'s "no map
`[m] → [0]` for `m > 0`", and it is exactly why the bare counit's `[0] ↛ [0]` is a representability error, not a
valid morphism. -/
theorem MonotoneMap.no_map_into_zero (domainWidth : Nat) (map : MonotoneMap (domainWidth + 1) 0) : False :=
  Nat.not_lt_zero _ (map.mapsIntoCodomain 0 (by rw [map.hasLength]; exact Nat.succ_pos _))

/-! ## ★ The generators are genuine EPIS and MONOS — the Eilenberg–Zilber building blocks

The Eilenberg–Zilber factorization presents every Δ₊ morphism as a surjection (composite of degeneracies σ)
followed by an injection (composite of faces δ).  Its building blocks are that the FACES are genuine order-
preserving INJECTIONS and the DEGENERACIES genuine order-preserving SURJECTIONS — proved here.  Faces are
STRICTLY increasing (hence injective on the finite domain), strictness closed under composition (injections
compose); degeneracies are SURJECTIVE onto their codomain ordinal.  These are exactly the epi/mono halves the EZ
factorization of an arbitrary monotone map decomposes into. -/

/-- STRICTLY increasing: a lower position has a strictly smaller value (an order-preserving injection). -/
def isStrictlyIncreasing (values : List Nat) : Prop :=
  ∀ lowerPos upperPos, lowerPos < upperPos → upperPos < values.length →
    monotoneMapGet values lowerPos < monotoneMapGet values upperPos

/-- INJECTIVE on the finite domain: equal values force equal in-range positions. -/
def isInjectiveOnDomain (values : List Nat) : Prop :=
  ∀ lowerPos upperPos, lowerPos < values.length → upperPos < values.length →
    monotoneMapGet values lowerPos = monotoneMapGet values upperPos → lowerPos = upperPos

/-- SURJECTIVE onto `[codomain]`: every target value is hit by some in-range position. -/
def isSurjectiveOnto (values : List Nat) (codomain : Nat) : Prop :=
  ∀ targetValue, targetValue < codomain →
    ∃ position, position < values.length ∧ monotoneMapGet values position = targetValue

/-- Strict monotonicity entails injectivity on the finite domain — by trichotomy on the two positions. -/
theorem isStrictlyIncreasing_isInjectiveOnDomain (values : List Nat)
    (hstrict : isStrictlyIncreasing values) : isInjectiveOnDomain values := by
  intro lowerPos upperPos hlower hupper hvalEq
  rcases Nat.lt_trichotomy lowerPos upperPos with hlt | heq | hgt
  · exact absurd hvalEq (Nat.ne_of_lt (hstrict lowerPos upperPos hlt hupper))
  · exact heq
  · exact absurd hvalEq.symm (Nat.ne_of_lt (hstrict upperPos lowerPos hgt hlower))

/-- The identity map is strictly increasing. -/
theorem idMap_isStrictlyIncreasing (codomain : Nat) : isStrictlyIncreasing (idMap codomain) := by
  intro lowerPos upperPos hlt hupper
  rw [idMap_length] at hupper
  rw [monotoneMapGet_idMap codomain lowerPos (Nat.lt_trans hlt hupper),
      monotoneMapGet_idMap codomain upperPos hupper]
  exact hlt

/-- ★ **The FACE generator `δ_i` is strictly increasing** — a genuine order-preserving injection. -/
theorem faceMap_isStrictlyIncreasing (i n : Nat) : isStrictlyIncreasing (faceMap i n) := by
  intro lowerPos upperPos hlt hupper
  rw [faceMap_length] at hupper
  have hlower : lowerPos < n := Nat.lt_trans hlt hupper
  show monotoneMapGet (faceFrom 0 i n) lowerPos < monotoneMapGet (faceFrom 0 i n) upperPos
  rcases Nat.lt_or_ge lowerPos i with hli | hli
  · rcases Nat.lt_or_ge upperPos i with hui | hui
    · rw [faceFrom_get_lt 0 i n lowerPos hli hlower, faceFrom_get_lt 0 i n upperPos hui hupper]
      exact Nat.add_lt_add_left hlt 0
    · rw [faceFrom_get_lt 0 i n lowerPos hli hlower, faceFrom_get_ge 0 i n upperPos hui hupper]
      exact Nat.add_lt_add_left (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hli hui)) 0
  · have hui : i ≤ upperPos := Nat.le_of_lt (Nat.lt_of_le_of_lt hli hlt)
    rw [faceFrom_get_ge 0 i n lowerPos hli hlower, faceFrom_get_ge 0 i n upperPos hui hupper]
    exact Nat.add_lt_add_left (Nat.succ_lt_succ hlt) 0

/-- ★ **The FACE generator `δ_i` is injective** on its finite domain — its monotone-map shadow is a mono. -/
theorem faceMap_isInjectiveOnDomain (i n : Nat) : isInjectiveOnDomain (faceMap i n) :=
  isStrictlyIncreasing_isInjectiveOnDomain (faceMap i n) (faceMap_isStrictlyIncreasing i n)

/-- ★ **Composition of strictly-increasing maps is strictly increasing** (the first landing in the second's
domain) — order-preserving injections compose, so the EZ mono part (a composite of faces) is a genuine mono. -/
theorem composeMap_isStrictlyIncreasing (first second : List Nat)
    (hfirst : isStrictlyIncreasing first) (hsecond : isStrictlyIncreasing second)
    (hrange : mapsInto first second.length) : isStrictlyIncreasing (composeMap first second) := by
  intro lowerPos upperPos hlt hupper
  rw [composeMap_length] at hupper
  have hlower : lowerPos < first.length := Nat.lt_trans hlt hupper
  rw [composeMap_get first second lowerPos hlower, composeMap_get first second upperPos hupper]
  exact hsecond (monotoneMapGet first lowerPos) (monotoneMapGet first upperPos)
    (hfirst lowerPos upperPos hlt hupper) (hrange upperPos hupper)

/-- ★ **The DEGENERACY generator `σ_i` is surjective** onto `[n]` — a genuine order-preserving surjection (epi):
the target `v` is hit at position `v` when `v ≤ i`, else at position `v+1`. -/
theorem degenMap_isSurjectiveOnto (i n : Nat) : isSurjectiveOnto (degenMap i n) n := by
  intro targetValue htarget
  rcases Nat.lt_or_ge targetValue (i + 1) with hti | hti
  · refine ⟨targetValue, ?_, ?_⟩
    · rw [degenMap_length]; exact Nat.lt_succ_of_lt htarget
    · show monotoneMapGet (degenFrom 0 i n) targetValue = targetValue
      rw [degenFrom_get_le 0 i n targetValue (Nat.le_of_lt_succ hti) (Nat.lt_succ_of_lt htarget), Nat.zero_add]
  · refine ⟨targetValue + 1, ?_, ?_⟩
    · rw [degenMap_length]; exact Nat.succ_lt_succ htarget
    · show monotoneMapGet (degenFrom 0 i n) (targetValue + 1) = targetValue
      rw [degenFrom_get_succ 0 i n targetValue (Nat.le_of_succ_le hti) htarget, Nat.zero_add]

/-! ## ★ The Eilenberg–Zilber epi-mono factorization — every monotone map is `image ∘ rank`

The Eilenberg–Zilber lemma factors every Δ₊ morphism as a SURJECTION (composite of degeneracies) followed by an
INJECTION (composite of faces).  In the value-list model the two parts are read off directly: the INJECTION (mono)
is `imageList` — the strictly-increasing list of DISTINCT values (the image); the SURJECTION (epi) is `rankList` —
each element's index into that image (its rank).  The headline `composeMap_rankList_imageList` proves the
FACTORIZATION: `composeMap (rankList values) (imageList values) = values`, i.e. `values` IS its rank composed with
its image (apply the surjection then the injection — the EZ orientation).  It is a STRUCTURAL inverse identity (it
holds for every value-list, no sortedness needed), and `propext`-free: the dedup/rank recursions branch on `dite`
over `Nat.decEq`, closed by `dif_pos`/`dif_neg`.  For a SORTED (monotone) input the image is genuinely strictly
increasing and the rank genuinely surjective (the smokes exhibit `[2,2,5,5,5,7] = [0,0,1,1,1,2] then [2,5,7]`);
the general proof of those epi/mono properties for arbitrary sorted input — and EZ uniqueness — is the residual
(the generators are already proved epi/mono above). -/

/-- The distinct values strictly after an already-emitted `lastValue` (the INJECTION / image tail).  Sorted-list
dedup: a `head` equal to the previous value is dropped; a new `head` is emitted. -/
def imageTailFrom : Nat → List Nat → List Nat
  | _, [] => []
  | lastValue, head :: rest =>
      if head = lastValue then imageTailFrom head rest else head :: imageTailFrom head rest

/-- The rank of each remaining element (the SURJECTION / epi tail): the rank stays on a repeated value and
increments on a new value. -/
def rankTailFrom : Nat → Nat → List Nat → List Nat
  | _, _, [] => []
  | currentRank, lastValue, head :: rest =>
      if head = lastValue then currentRank :: rankTailFrom currentRank lastValue rest
      else (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest

/-- The IMAGE (mono / injection) part of a value-list: its distinct values in order. -/
def imageList : List Nat → List Nat
  | [] => []
  | head :: rest => head :: imageTailFrom head rest

/-- The RANK (epi / surjection) part of a value-list: each element's index into `imageList`. -/
def rankList : List Nat → List Nat
  | [] => []
  | head :: rest => 0 :: rankTailFrom 0 head rest

/-- The factorization invariant over the tails: the ranks index into a shared `fullMono` whose `currentRank`-th
entry is `lastValue` and whose suffix matches `imageTailFrom lastValue rest`.  No sortedness — a structural inverse
identity, by induction on `rest` with the `dite` branch closed by `if_pos` / `if_neg`. -/
theorem composeMap_rankTailFrom (fullMono : List Nat) :
    ∀ (currentRank lastValue : Nat) (rest : List Nat),
      monotoneMapGet fullMono currentRank = lastValue →
      (∀ offset, monotoneMapGet fullMono (currentRank + 1 + offset)
        = monotoneMapGet (imageTailFrom lastValue rest) offset) →
      composeMap (rankTailFrom currentRank lastValue rest) fullMono = rest
  | _, _, [], _, _ => rfl
  | currentRank, lastValue, head :: rest, hcurrent, hsuffix => by
      by_cases hcase : head = lastValue
      · have hrank : rankTailFrom currentRank lastValue (head :: rest)
              = currentRank :: rankTailFrom currentRank lastValue rest := by
          show (if head = lastValue then currentRank :: rankTailFrom currentRank lastValue rest
            else (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest)
              = currentRank :: rankTailFrom currentRank lastValue rest
          rw [if_pos hcase]
        have himage : imageTailFrom lastValue (head :: rest) = imageTailFrom lastValue rest := by
          show (if head = lastValue then imageTailFrom head rest else head :: imageTailFrom head rest)
              = imageTailFrom lastValue rest
          rw [if_pos hcase, hcase]
        have hsuffix' : ∀ offset, monotoneMapGet fullMono (currentRank + 1 + offset)
            = monotoneMapGet (imageTailFrom lastValue rest) offset := by
          intro offset; rw [hsuffix offset, himage]
        show composeMap (rankTailFrom currentRank lastValue (head :: rest)) fullMono = head :: rest
        rw [hrank]
        show monotoneMapGet fullMono currentRank
          :: composeMap (rankTailFrom currentRank lastValue rest) fullMono = head :: rest
        rw [composeMap_rankTailFrom fullMono currentRank lastValue rest hcurrent hsuffix', hcurrent, hcase]
      · have hrank : rankTailFrom currentRank lastValue (head :: rest)
              = (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest := by
          show (if head = lastValue then currentRank :: rankTailFrom currentRank lastValue rest
            else (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest)
              = (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest
          rw [if_neg hcase]
        have himage : imageTailFrom lastValue (head :: rest) = head :: imageTailFrom head rest := by
          show (if head = lastValue then imageTailFrom head rest else head :: imageTailFrom head rest)
              = head :: imageTailFrom head rest
          rw [if_neg hcase]
        have hhead : monotoneMapGet fullMono (currentRank + 1) = head := by
          have hs := hsuffix 0
          rw [Nat.add_zero, himage] at hs
          exact hs
        have hsuffix' : ∀ offset, monotoneMapGet fullMono (currentRank + 1 + 1 + offset)
            = monotoneMapGet (imageTailFrom head rest) offset := by
          intro offset
          have hs := hsuffix (offset + 1)
          rw [show currentRank + 1 + (offset + 1) = currentRank + 1 + 1 + offset from by
                rw [Nat.add_assoc (currentRank + 1) 1 offset, Nat.add_comm 1 offset], himage] at hs
          exact hs
        show composeMap (rankTailFrom currentRank lastValue (head :: rest)) fullMono = head :: rest
        rw [hrank]
        show monotoneMapGet fullMono (currentRank + 1)
          :: composeMap (rankTailFrom (currentRank + 1) head rest) fullMono = head :: rest
        rw [composeMap_rankTailFrom fullMono (currentRank + 1) head rest hhead hsuffix', hhead]

/-- ★ **THE EILENBERG–ZILBER FACTORIZATION (existence).**  Every value-list is its RANK (epi/surjection) composed
with its IMAGE (mono/injection): `composeMap (rankList values) (imageList values) = values` — apply the surjection
then the injection, the EZ orientation.  Proved from the tail invariant; zero-axiom. -/
theorem composeMap_rankList_imageList (values : List Nat) :
    composeMap (rankList values) (imageList values) = values := by
  cases values with
  | nil => rfl
  | cons head rest =>
      have key : composeMap (rankTailFrom 0 head rest) (head :: imageTailFrom head rest) = rest :=
        composeMap_rankTailFrom (head :: imageTailFrom head rest) 0 head rest rfl
          (fun offset => by rw [Nat.zero_add, Nat.add_comm 1 offset]; rfl)
      show monotoneMapGet (head :: imageTailFrom head rest) 0
        :: composeMap (rankTailFrom 0 head rest) (head :: imageTailFrom head rest) = head :: rest
      exact congrArg (fun remainingTail => head :: remainingTail) key

/-- The rank tail has one entry per remaining element. -/
theorem rankTailFrom_length : ∀ (currentRank lastValue : Nat) (rest : List Nat),
    (rankTailFrom currentRank lastValue rest).length = rest.length
  | _, _, [] => rfl
  | currentRank, lastValue, head :: rest => by
      by_cases hcase : head = lastValue
      · have hr : rankTailFrom currentRank lastValue (head :: rest)
            = currentRank :: rankTailFrom currentRank lastValue rest := by
          show (if head = lastValue then currentRank :: rankTailFrom currentRank lastValue rest
            else (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest)
              = currentRank :: rankTailFrom currentRank lastValue rest
          rw [if_pos hcase]
        rw [hr]
        show (rankTailFrom currentRank lastValue rest).length + 1 = rest.length + 1
        rw [rankTailFrom_length currentRank lastValue rest]
      · have hr : rankTailFrom currentRank lastValue (head :: rest)
            = (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest := by
          show (if head = lastValue then currentRank :: rankTailFrom currentRank lastValue rest
            else (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest)
              = (currentRank + 1) :: rankTailFrom (currentRank + 1) head rest
          rw [if_neg hcase]
        rw [hr]
        show (rankTailFrom (currentRank + 1) head rest).length + 1 = rest.length + 1
        rw [rankTailFrom_length (currentRank + 1) head rest]

/-- ★ The RANK (epi) part is a map out of the SAME finite domain as the input: `|rankList values| = |values|` —
the surjection has the right source ordinal. -/
theorem rankList_length (values : List Nat) : (rankList values).length = values.length := by
  cases values with
  | nil => rfl
  | cons head rest =>
      show (rankTailFrom 0 head rest).length + 1 = rest.length + 1
      rw [rankTailFrom_length 0 head rest]

/-- Smoke: on a sorted input the factorization COMPUTES with the genuine epi/mono shape — image is the strictly
increasing distinct values, rank is the surjective rank. -/
theorem composeMap_rankList_imageList_smoke :
    composeMap (rankList [2, 2, 5, 5, 5, 7]) (imageList [2, 2, 5, 5, 5, 7]) = [2, 2, 5, 5, 5, 7] := rfl

/-- Smoke: the image (mono) part of `[2,2,5,5,5,7]` is the strictly-increasing distinct values `[2,5,7]`. -/
theorem imageList_smoke : imageList [2, 2, 5, 5, 5, 7] = [2, 5, 7] := rfl

/-- Smoke: the rank (epi) part of `[2,2,5,5,5,7]` is the surjective rank `[0,0,1,1,1,2]`. -/
theorem rankList_smoke : rankList [2, 2, 5, 5, 5, 7] = [0, 0, 1, 1, 1, 2] := rfl

/-! ## The structural fold `monotoneMapOf` over the spine

A free 2-cell is read into its monotone map by folding its SPINE (the flat whiskered-atom list,
`FreeTwoCellSpine`) bottom-to-top: each CUP atom (the unit, a `0 ⇒ 2` generator) post-composes a FACE `δ` at its
whisker-context block position, growing the width by one; each CAP atom (the counit, a `2 ⇒ 0` generator)
post-composes a DEGENERACY `σ`, shrinking the width.  The running map is `[sourceWidth] → [currentWidth]`; the
final map (at `targetWidth`) is the 2-cell's monotone-map normal form.  Structural / fold recursion, so it
COMPUTES (the smokes are `rfl`). -/

/-- The block width of a 1-cell word of the walking adjunction — the number of complete `LR` / `RL` blocks, i.e.
half the path length.  Structural (decrement by two) so it reduces by `rfl` (unlike `Nat./`, which is
well-founded and does not compute in the kernel). -/
def blockOf : Nat → Nat
  | 0 => 0
  | 1 => 0
  | length + 2 => blockOf length + 1

/-- One fold step: a CUP (`0 ⇒ 2`, the unit) post-composes a face `δ_p` and grows the width; a CAP (`2 ⇒ 0`, the
counit) post-composes a degeneracy `σ_p` and shrinks the width.  The position `p` is the block width to the left
of the generator (its whisker context).  Any other arity is an opaque box that leaves the map unchanged (never
occurs at the cup/cap walking-adjunction seed). -/
def monoStepAtom {sourceMode targetMode : AdjunctionMode}
    (state : Nat × List Nat) (atom : SpineAtom adjunctionModeSignature sourceMode targetMode) :
    Nat × List Nat :=
  let position := blockOf atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 2 => (state.1 + 1, composeMap state.2 (faceMap position state.1))
  | 2, 0 => (state.1 - 1, composeMap state.2 (degenMap position (state.1 - 1)))
  | _, _ => state

/-- ★ The **Schanuel–Street monotone-map normal form** of a free 2-cell of the walking adjunction: fold the cup /
cap spine into the composite face / degeneracy map, starting from the identity on the source block width.  This
is the candidate `monotoneMapOf` for `AdjunctionSaturatedCanonicalization`.  Structural fold — it COMPUTES. -/
def monotoneMapOf {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) : List Nat :=
  (cell.spine.foldl monoStepAtom (blockOf sourcePath.length, idMap (blockOf sourcePath.length))).2

/-! ## Smoke: the fold COMPUTES the generators and the snake -/

/-- Smoke: the bare unit (a cup at the empty source, width `0`) folds to the empty face `[]`. -/
theorem monotoneMapOf_unit : monotoneMapOf adjunctionUnitTwoCell = [] := rfl

/-- Smoke: the bare counit (a cap, source `RL` of block width `1`) folds to the degeneracy `[0]`. -/
theorem monotoneMapOf_counit : monotoneMapOf adjunctionCounitTwoCell = [0] := rfl

/-! ## ★ The triangle identity in the monotone-map model — the snake collapses, via the simplicial identity

The SEED snake's boundary `L ⇒ L` has block width `0`, so both the snake and the identity fold to the empty map
`[]` — the triangle holds.  But the genuine content (that the snake collapse IS the simplicial identity, not a
width-`0` accident) is exposed by a WHISKERED snake at positive width, where the fold genuinely composes a face
`δ_p` after the running identity and then a degeneracy `σ_p`, and the collapse is `snakeCollapseAtWidth` — i.e.
exactly `composeMap_faceMap_degenMap` (`σ_p ∘ δ_p = id`) at the shifted position. -/

/-- ★ **The LEFT triangle identity in the monotone-map model** — `monotoneMapOf adjunctionSeedLeftSnake =
monotoneMapOf id_L`.  The map `mapEqOfConv` must send `SaturatedTwoCellConv.triangleLeft` to.  At the seed both
fold to `[]` (width `0`). -/
theorem monotoneMapOf_leftSnake_eq_id :
    monotoneMapOf adjunctionSeedLeftSnake
      = monotoneMapOf (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) := rfl

/-- ★ **The RIGHT triangle identity in the monotone-map model** — `monotoneMapOf adjunctionSeedRightSnake =
monotoneMapOf id_R`. -/
theorem monotoneMapOf_rightSnake_eq_id :
    monotoneMapOf adjunctionSeedRightSnake
      = monotoneMapOf (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)) := rfl

/-- ★★ **The WHISKERED left snake collapses to the identity GENUINELY via the simplicial identity.**  Whiskering
the left snake by `L·R` lifts its boundary to block width `1`; the fold then computes
`composeMap (composeMap (idMap 1) (faceMap 1 1)) (degenMap 1 1)` — a face `δ_1` then a degeneracy `σ_1` at the
shifted position `1` — and this equals `idMap 1` by `snakeCollapseAtWidth 1 1`, i.e. by the simplicial identity
`σ_1 ∘ δ_1 = id` at the NON-trivial position `1`.  This is the honest witness that the triangle's collapse is the
simplicial identity, not a width-`0` accident: the `show` exposes the fold's composite, and the proof IS the
simplicial-identity lemma. -/
theorem monotoneMapOf_whiskeredLeftSnake_via_simplicialIdentity :
    monotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        adjunctionLeftThenRight adjunctionSeedLeftSnake) = idMap 1 := by
  show composeMap (composeMap (idMap 1) (faceMap 1 1)) (degenMap 1 1) = idMap 1
  exact snakeCollapseAtWidth 1 1

/-- The whiskered identity on `L` (at the same `L·R` context) also folds to `idMap 1` — so the WHISKERED triangle
`whiskerLeft (L·R) snake ≈ whiskerLeft (L·R) id_L` holds in the model at the non-trivial width `1`, matching
`SaturatedTwoCellConv.whiskerLeftCongr _ SaturatedTwoCellConv.triangleLeft`. -/
theorem monotoneMapOf_whiskeredLeftId_eq :
    monotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        adjunctionLeftThenRight (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))) = idMap 1 := rfl

/-- ★ **The whiskered LEFT triangle holds in the monotone-map model at positive width** — the genuine, non-vacuous
manifestation of the triangle-collapse-is-free crux. -/
theorem monotoneMapOf_whiskeredLeftTriangle :
    monotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        adjunctionLeftThenRight adjunctionSeedLeftSnake)
      = monotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          adjunctionLeftThenRight (RawTwoCellExpr.id (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left))) :=
  monotoneMapOf_whiskeredLeftSnake_via_simplicialIdentity.trans monotoneMapOf_whiskeredLeftId_eq.symm

/-! ## Soundness leg: `monotoneMapOf` is invariant under the interchange-free structural fragment

`monotoneMapOf` reads ONLY the spine and the source-word length (fixed by the boundary), so it is invariant under
any rewrite preserving the spine.  The eleven interchange-free structural strict-2-category laws do exactly that
(`TwoCellStepInterchangeFree.spine_eq`, congruences included), so `monotoneMapOf` is invariant under the whole
structural fragment of `TwoCellConvFull` — the same clean soundness leg the matching invariant has.  (The
interchange/Godement step preserves the spine only up to TRACE equivalence; that invariance, and the saturated
congruences threading the whisker-shifted positions, are the residual — see the honesty markers.) -/

/-- `monotoneMapOf` depends on the cell only through its spine (the boundary, hence the source length, is fixed):
equal spines give equal monotone maps. -/
theorem monotoneMapOf_congr_of_spine_eq {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellOne cellTwo : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (spineEqual : cellOne.spine = cellTwo.spine) : monotoneMapOf cellOne = monotoneMapOf cellTwo := by
  show (cellOne.spine.foldl monoStepAtom (blockOf sourcePath.length, idMap (blockOf sourcePath.length))).2
    = (cellTwo.spine.foldl monoStepAtom (blockOf sourcePath.length, idMap (blockOf sourcePath.length))).2
  rw [spineEqual]

/-- ★ **Soundness of `monotoneMapOf` under the interchange-free structural fragment**: every one of the eleven
structural strict-2-category laws (identity removal, re-association, whisker distribution / unit — congruences
included) preserves the monotone map, because each preserves the spine on the nose
(`TwoCellStepInterchangeFree.spine_eq`).  This is the structural-fragment leg of `mapEqOfConv`. -/
theorem monotoneMapOf_eq_of_interchangeFreeStep {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellOne cellTwo : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree adjunctionModeSignature cellOne cellTwo) :
    monotoneMapOf cellOne = monotoneMapOf cellTwo :=
  monotoneMapOf_congr_of_spine_eq step.spine_eq

/-! ## ★ Decidable normal-form equality = decidable monotone-map equality (propext-free)

The augmented-simplex decision compares two 2-cells by their monotone-map normal forms.  The normal form is the
value-`List Nat`; two of them denote the SAME monotone map `Fin m → Fin n` exactly when they agree extensionally
on their common finite domain, and — by `listExtById` — that is exactly structural list equality.  So deciding
monotone-map equality is deciding `List Nat` equality, which COMPUTES and is `propext`-free: the decider is a
`dite` over the structural `List.decEq`, never the `propext`-routed `decidable_of_iff`. -/

/-- Extensional equality of two monotone-map normal forms as maps `Fin (length) → Nat`: equal domain length and
equal value at every in-range position.  The `Fin`-indexed reading of "the same Δ₊ morphism". -/
def monotoneMapExtEq (firstMap secondMap : List Nat) : Prop :=
  firstMap.length = secondMap.length ∧
    ∀ position, position < firstMap.length →
      monotoneMapGet firstMap position = monotoneMapGet secondMap position

/-- ★ **Extensional equality of monotone maps is exactly structural value-list equality.**  Forward by
`listExtById` (equal length + equal entries ⟹ equal list); backward by `congrArg`.  This is the bridge that lets
the decision compare the underlying `Fin m → Fin n` maps by comparing their canonical value-lists. -/
theorem monotoneMapExtEq_iff_eq (firstMap secondMap : List Nat) :
    monotoneMapExtEq firstMap secondMap ↔ firstMap = secondMap :=
  ⟨fun ⟨equalLength, equalEntries⟩ => listExtById firstMap secondMap equalLength equalEntries,
   fun mapsEqual =>
     ⟨congrArg List.length mapsEqual, fun position _ => congrArg (monotoneMapGet · position) mapsEqual⟩⟩

/-- ★ **Decide monotone-map (normal-form) equality, `propext`-free.**  Branch on the structural `List Nat`
equality `List.decEq`: equal lists give the extensional equality (backward bridge), unequal lists refute it
(forward bridge).  A `dite` over a structural `Decidable`, so the procedure COMPUTES and carries no `propext`
(unlike `decidable_of_iff`, which routes through it). -/
def decideMonotoneMapExtEq (firstMap secondMap : List Nat) : Decidable (monotoneMapExtEq firstMap secondMap) :=
  if mapsEqual : firstMap = secondMap then
    isTrue ((monotoneMapExtEq_iff_eq firstMap secondMap).mpr mapsEqual)
  else
    isFalse (fun extensionallyEqual => mapsEqual ((monotoneMapExtEq_iff_eq firstMap secondMap).mp extensionallyEqual))

/-- Smoke: extensional equality of the bare-counit normal form `[0]` with itself decides `isTrue`, computing. -/
theorem decideMonotoneMapExtEq_refl_smoke :
    monotoneMapExtEq (monotoneMapOf adjunctionCounitTwoCell) (monotoneMapOf adjunctionCounitTwoCell) :=
  (monotoneMapExtEq_iff_eq _ _).mpr rfl

/-! ## ★ The Godement-soundness reduction — `monotoneMapOf` invariance under interchange, reduced to the
two-block simplicial commutation

`monotoneMapOf` reads a cell through its SPINE (the flat cup/cap atom list).  Its invariance under the eleven
interchange-free structural laws is the shipped `monotoneMapOf_eq_of_interchangeFreeStep`.  The remaining
GODEMENT / interchange law transposes two horizontally-independent blocks with a whisker-context shift; this
section reduces `monotoneMapOf`'s invariance under that step to a SINGLE residual — the two-block commutation
core `MonoGodementCommute` — discharging everything else zero-axiom:

  * `monoProcessSpine` / `runMonoCell` / `monoProcessSpine_spineDiff` — the **fold-decomposition engine**:
    folding `monoStepAtom` over a cell's cons-only `spineDiff` difference-list equals running the cell alone
    (`runMonoCell`) then the tail.  Mirrors the arc route's `processArcSpine_spineDiff`; structural recursion.
  * `runMonoCell_rightContext_irrelevant` — `monoStepAtom` reads only the LEFT whisker context (the block
    position) and the generator arity, never the right context; so `runMonoCell` is invariant under the right
    accumulator.  This drops HALF the Godement context shift (`cellAlphaUpper`'s `gLow → gMid`) for free.
  * `runMonoCell_width` — the **block-width invariant**: the running width tracks `blockOf` of the current
    1-cell length, threading `blockOf(leftAcc + dom + rightAcc) → blockOf(leftAcc + cod + rightAcc)` through
    every fold step.  This DISCHARGES the width component of the commutation (the analog of the arc route's
    cup/cap COUNT discharge) and rules out the truncated-subtraction underflow that makes the unconditional
    (`∀ state`) commutation false.
  * `runMonoCell_interchangeRedex` / `runMonoCell_interchangeReduct` — the four-block decompositions of the
    interchange redex / reduct, read off `RawTwoCellExpr.interchangeRedex/ReductSpineDiff` and peeled.
  * `MonoGodementCommute` — the **two-block commutation core** (the residual): transposing `cellAlphaUpper`
    (an f-side block, low positions) and `cellBeta` (a g-side block, high positions) at their well-formed
    widths preserves the running monotone map — exactly the disjoint-position simplicial `δδ` / `σσ` / `σδ`
    commutation (`composeMap_faceMap_faceMap_commute` et al.) at BLOCK scale.
  * `monotoneMapOf_interchange_eq_of_commute` — the **reduction**: `monotoneMapOf` is invariant under the
    cell-level interchange step GIVEN `MonoGodementCommute`.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

/-- Fold the monotone-map step `monoStepAtom` over a spine atom list — the spine-list-level engine underlying
`monotoneMapOf` (`monotoneMapOf cell = (monoProcessSpine initialState cell.spine).2`). -/
def monoProcessSpine {sourceMode targetMode : AdjunctionMode}
    (state : Nat × List Nat)
    (atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) : Nat × List Nat :=
  atoms.foldl monoStepAtom state

/-- Run the monotone-map fold over ONE cell's spine from a given state (the cell's contribution alone, empty
tail) — the per-block fold unit the Godement decomposition peels. -/
def runMonoCell {overallSource overallTarget localSource localTarget : AdjunctionMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath adjunctionModeSignature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath adjunctionModeSignature.graph localSource localTarget}
    (cell : RawTwoCellExpr adjunctionModeSignature localDom localCod) : Nat × List Nat :=
  monoProcessSpine state (cell.spineDiff leftAcc rightAcc [])

/-- ★ **The fold-decomposition of the monotone-map fold over a `spineDiff` difference-list.**  Folding
`monoStepAtom` over `cell.spineDiff leftAcc rightAcc rest` equals folding over the cell alone (`runMonoCell`)
then over `rest`.  Structural recursion on the cell (generator / identity definitional; vcomp peels each factor;
the whiskerings recurse under shifted accumulators).  Mirrors `processArcSpine_spineDiff`; propext-free. -/
theorem monoProcessSpine_spineDiff {overallSource overallTarget : AdjunctionMode} :
    {localSource localTarget : AdjunctionMode} →
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath adjunctionModeSignature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath adjunctionModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr adjunctionModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    monoProcessSpine state (cell.spineDiff leftAcc rightAcc rest)
      = monoProcessSpine (runMonoCell state leftAcc rightAcc cell) rest
  | _, _, _, _, _, _, .gen _, _, _ => rfl
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, state, rest => by
      show monoProcessSpine state
          (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc rest))
        = monoProcessSpine (runMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)) rest
      rw [monoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc rest),
        monoProcessSpine_spineDiff leftAcc rightAcc cellRight (runMonoCell state leftAcc rightAcc cellLeft) rest]
      congr 1
      show runMonoCell (runMonoCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight
        = monoProcessSpine state (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc []))
      rw [monoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])]
      rfl
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, state, rest =>
      monoProcessSpine_spineDiff (composePath leftAcc oneCell) rightAcc body state rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, state, rest =>
      monoProcessSpine_spineDiff leftAcc (composePath oneCell rightAcc) body state rest

/-- Running a vertical composite is running the first factor then the second (the fold-decomposition at a
`vcomp`). -/
theorem runMonoCell_vcomp {overallSource overallTarget localSource localTarget : AdjunctionMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath adjunctionModeSignature.graph localTarget overallTarget)
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionModeSignature.graph localSource localTarget}
    (cellLeft : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
    (cellRight : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
    runMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)
      = runMonoCell (runMonoCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight :=
  monoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])

/-- Running a left-whiskered cell shifts the left accumulator by the whisker (definitional). -/
theorem runMonoCell_whiskerLeft {overallSource overallTarget localSource localMiddle localTarget : AdjunctionMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath adjunctionModeSignature.graph localTarget overallTarget)
    (oneCell : ModalityPath adjunctionModeSignature.graph localSource localMiddle)
    {oneCellG oneCellH : ModalityPath adjunctionModeSignature.graph localMiddle localTarget}
    (body : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
    runMonoCell state leftAcc rightAcc (RawTwoCellExpr.whiskerLeft oneCell body)
      = runMonoCell state (composePath leftAcc oneCell) rightAcc body := rfl

/-- Running a right-whiskered cell shifts the right accumulator by the whisker (definitional). -/
theorem runMonoCell_whiskerRight {overallSource overallTarget localSource localMiddle localTarget : AdjunctionMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath adjunctionModeSignature.graph localTarget overallTarget)
    {oneCellF oneCellG : ModalityPath adjunctionModeSignature.graph localSource localMiddle}
    (oneCell : ModalityPath adjunctionModeSignature.graph localMiddle localTarget)
    (body : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG) :
    runMonoCell state leftAcc rightAcc (RawTwoCellExpr.whiskerRight oneCell body)
      = runMonoCell state leftAcc (composePath oneCell rightAcc) body := rfl

/-- ★ **Right-context irrelevance.**  `monoStepAtom` reads only the LEFT whisker context (its block position)
and the generator arity, never the right context; so `runMonoCell` gives the same result under any right
accumulator.  This is what lets the Godement step's `cellAlphaUpper` right-context shift `gLow → gMid` be
ignored entirely (a simplification the arc route cannot make). -/
theorem runMonoCell_rightContext_irrelevant {overallSource overallTarget : AdjunctionMode} :
    {localSource localTarget : AdjunctionMode} →
    {localDom localCod : ModalityPath adjunctionModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr adjunctionModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource) →
    (rA1 rA2 : ModalityPath adjunctionModeSignature.graph localTarget overallTarget) →
    runMonoCell state leftAcc rA1 cell = runMonoCell state leftAcc rA2 cell
  | _, _, _, _, .gen _, _, _, _, _ => rfl
  | _, _, _, _, .id _, _, _, _, _ => rfl
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rA1, rA2 => by
      rw [runMonoCell_vcomp, runMonoCell_vcomp,
          runMonoCell_rightContext_irrelevant cellLeft state leftAcc rA1 rA2]
      exact runMonoCell_rightContext_irrelevant cellRight _ leftAcc rA1 rA2
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rA1, rA2 => by
      rw [runMonoCell_whiskerLeft, runMonoCell_whiskerLeft]
      exact runMonoCell_rightContext_irrelevant body state (composePath leftAcc oneCell) rA1 rA2
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rA1, rA2 => by
      rw [runMonoCell_whiskerRight, runMonoCell_whiskerRight]
      exact runMonoCell_rightContext_irrelevant body state leftAcc (composePath oneCell rA1) (composePath oneCell rA2)

/-- `blockOf (value + 2) = blockOf value + 1` — adding a complete `LR` / `RL` block to a 1-cell adds one block
width (definitional). -/
theorem blockOf_add_two (value : Nat) : blockOf (value + 2) = blockOf value + 1 := rfl

/-- The width effect of a CUP (unit, `0 ⇒ 2`): `blockOf(low + 0 + high) + 1 = blockOf(low + 2 + high)`. -/
theorem blockOf_unitShift (lowLen highLen : Nat) :
    blockOf (lowLen + 0 + highLen) + 1 = blockOf (lowLen + 2 + highLen) := by
  show blockOf (lowLen + highLen) + 1 = blockOf (lowLen + 2 + highLen)
  rw [Nat.add_right_comm lowLen 2 highLen, blockOf_add_two]

/-- `(value + 1) - 1 = value` (definitional; the truncation never bites because the predecessor of a successor
is exact). -/
theorem succPredCancel (value : Nat) : value + 1 - 1 = value := rfl

/-- The width effect of a CAP (counit, `2 ⇒ 0`): `blockOf(low + 2 + high) - 1 = blockOf(low + 0 + high)`. -/
theorem blockOf_counitShift (lowLen highLen : Nat) :
    blockOf (lowLen + 2 + highLen) - 1 = blockOf (lowLen + 0 + highLen) := by
  show blockOf (lowLen + 2 + highLen) - 1 = blockOf (lowLen + highLen)
  rw [Nat.add_right_comm lowLen 2 highLen, blockOf_add_two]
  exact succPredCancel _

/-- The block-width invariant at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free (the indexed-partial-match trap bites only when the boundary paths are recursion indices). -/
theorem runMonoCell_width_gen {overallSource overallTarget sourceMode targetMode : AdjunctionMode}
    {generatorDom generatorCod : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (generator : AdjunctionTwoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (hwidth : width = blockOf (leftAcc.length + generatorDom.length + rightAcc.length)) :
    (runMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).1
      = blockOf (leftAcc.length + generatorCod.length + rightAcc.length) := by
  cases generator with
  | unit =>
      show width + 1 = blockOf (leftAcc.length + 2 + rightAcc.length)
      rw [hwidth]; exact blockOf_unitShift leftAcc.length rightAcc.length
  | counit =>
      show width - 1 = blockOf (leftAcc.length + 0 + rightAcc.length)
      rw [hwidth]; exact blockOf_counitShift leftAcc.length rightAcc.length

/-- ★ **The block-width invariant.**  Given the running width equals `blockOf` of the current 1-cell length
(`leftAcc · localDom · rightAcc`), running the cell lands the width at `blockOf` of the codomain 1-cell length
(`leftAcc · localCod · rightAcc`).  Structural recursion on the cell: a generator steps the width by the unit /
counit `±2` length change (`runMonoCell_width_gen`); a vertical composite threads the invariant; the whiskerings
shift the length additively (`length_composePath`).  This DISCHARGES the width half of `MonoGodementCommute`,
and (anchoring the width to the genuine `blockOf`) rules out the truncated-subtraction underflow that makes the
unconditional commutation false. -/
theorem runMonoCell_width {overallSource overallTarget : AdjunctionMode} :
    {localSource localTarget : AdjunctionMode} →
    {localDom localCod : ModalityPath adjunctionModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr adjunctionModeSignature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath adjunctionModeSignature.graph localTarget overallTarget) →
    width = blockOf (leftAcc.length + localDom.length + rightAcc.length) →
    (runMonoCell (width, map) leftAcc rightAcc cell).1
      = blockOf (leftAcc.length + localCod.length + rightAcc.length)
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth =>
      runMonoCell_width_gen generator width map leftAcc rightAcc hwidth
  | _, _, _, _, .id _, _, _, _, _, hwidth => hwidth
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth => by
      rw [runMonoCell_vcomp]
      exact runMonoCell_width cellRight _ _ leftAcc rightAcc
        (runMonoCell_width cellLeft width map leftAcc rightAcc hwidth)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth => by
      rename_i bodyDom bodyCod
      rw [runMonoCell_whiskerLeft,
          runMonoCell_width body width map (composePath leftAcc oneCell) rightAcc (by
            rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
                ModalityPath.length_composePath leftAcc oneCell,
                Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]),
          ModalityPath.length_composePath leftAcc oneCell,
          ModalityPath.length_composePath oneCell bodyCod,
          Nat.add_assoc leftAcc.length oneCell.length bodyCod.length]
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth => by
      rename_i bodyDom bodyCod
      rw [runMonoCell_whiskerRight,
          runMonoCell_width body width map leftAcc (composePath oneCell rightAcc) (by
            rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
                ModalityPath.length_composePath oneCell rightAcc,
                ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
                Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]),
          ModalityPath.length_composePath oneCell rightAcc,
          ModalityPath.length_composePath bodyCod oneCell,
          ← Nat.add_assoc leftAcc.length bodyCod.length oneCell.length,
          Nat.add_assoc (leftAcc.length + bodyCod.length) oneCell.length rightAcc.length]

/-- `monotoneMapOf` IS the `.2` of `runMonoCell` from the source-block-width identity state at empty
accumulators (definitional bridge). -/
theorem monotoneMapOf_eq_runMonoCell {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    monotoneMapOf cell
      = (runMonoCell (blockOf sourcePath.length, idMap (blockOf sourcePath.length))
          (identityPath sourceMode) (identityPath targetMode) cell).2 := rfl

/-- ★ The interchange REDEX folds as four blocks in order `cellAlpha`, `cellAlphaUpper`, `cellBeta`,
`cellBetaUpper` — read off `RawTwoCellExpr.interchangeRedexSpineDiff` and peeled by the fold-decomposition. -/
theorem runMonoCell_interchangeRedex
    {overallSource overallTarget sourceMode middleMode targetMode : AdjunctionMode}
    {fLow fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr adjunctionModeSignature gMid gHigh)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (state : Nat × List Nat) :
    runMonoCell state leftAcc rightAcc
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
          (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
      = runMonoCell (runMonoCell (runMonoCell
            (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper := by
  show monoProcessSpine state
      ((RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
          (RawTwoCellExpr.vcomp cellBeta cellBetaUpper)).spineDiff leftAcc rightAcc []) = _
  rw [RawTwoCellExpr.interchangeRedexSpineDiff,
      monoProcessSpine_spineDiff, monoProcessSpine_spineDiff,
      monoProcessSpine_spineDiff, monoProcessSpine_spineDiff]
  rfl

/-- ★ The interchange REDUCT folds as four blocks in order `cellAlpha`, `cellBeta`, `cellAlphaUpper`,
`cellBetaUpper` — the two MIDDLE blocks transposed and context-shifted (`cellBeta`'s left `fHigh → fMid`,
`cellAlphaUpper`'s right `gLow → gMid`), from `RawTwoCellExpr.interchangeReductSpineDiff`. -/
theorem runMonoCell_interchangeReduct
    {overallSource overallTarget sourceMode middleMode targetMode : AdjunctionMode}
    {fLow fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr adjunctionModeSignature gMid gHigh)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (state : Nat × List Nat) :
    runMonoCell state leftAcc rightAcc
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper))
      = runMonoCell (runMonoCell (runMonoCell
            (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper := by
  show monoProcessSpine state
      ((RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)).spineDiff leftAcc rightAcc []) = _
  rw [RawTwoCellExpr.interchangeReductSpineDiff,
      monoProcessSpine_spineDiff, monoProcessSpine_spineDiff,
      monoProcessSpine_spineDiff, monoProcessSpine_spineDiff]
  rfl

/-- ★ **The block-width (FIRST projection) half of the Godement commutation, discharged unconditionally.**  The
running WIDTH of the interchange redex's two-middle-block run equals that of the reduct's: both land at
`blockOf(leftAcc · fHigh · gMid · rightAcc)`.  Each nested run's width is pinned to the genuine `blockOf` of its
current 1-cell length by the block-width invariant `runMonoCell_width`, so transposing `cellAlphaUpper` and
`cellBeta` leaves the width invariant.  This DISCHARGES the width component of `MonoGodementCommute`, leaving only
the value-list (second projection) as the residual. -/
theorem runMonoCell_godementWidthCommute
    {overallSource overallTarget sourceMode middleMode targetMode : AdjunctionMode}
    {fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (state : Nat × List Nat)
    (hstate : state.1 = blockOf (leftAcc.length + fMid.length + (composePath gLow rightAcc).length)) :
    (runMonoCell (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta).1
      = (runMonoCell (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper).1 := by
  have lhsInnerWidth :
      (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper).1
        = blockOf (leftAcc.length + fHigh.length + (composePath gLow rightAcc).length) :=
    runMonoCell_width cellAlphaUpper state.1 state.2 leftAcc (composePath gLow rightAcc) hstate
  have lhsOuterWidth :
      (runMonoCell (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta).1
        = blockOf ((composePath leftAcc fHigh).length + gMid.length + rightAcc.length) :=
    runMonoCell_width cellBeta _ _ (composePath leftAcc fHigh) rightAcc (by
      show (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper).1
          = blockOf ((composePath leftAcc fHigh).length + gLow.length + rightAcc.length)
      rw [lhsInnerWidth, ModalityPath.length_composePath gLow rightAcc,
          ModalityPath.length_composePath leftAcc fHigh,
          Nat.add_assoc (leftAcc.length + fHigh.length) gLow.length rightAcc.length])
  have rhsInnerWidth :
      (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta).1
        = blockOf ((composePath leftAcc fMid).length + gMid.length + rightAcc.length) :=
    runMonoCell_width cellBeta state.1 state.2 (composePath leftAcc fMid) rightAcc (by
      rw [hstate, ModalityPath.length_composePath gLow rightAcc,
          ModalityPath.length_composePath leftAcc fMid,
          Nat.add_assoc (leftAcc.length + fMid.length) gLow.length rightAcc.length])
  have rhsOuterWidth :
      (runMonoCell (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper).1
        = blockOf (leftAcc.length + fHigh.length + (composePath gMid rightAcc).length) :=
    runMonoCell_width cellAlphaUpper _ _ leftAcc (composePath gMid rightAcc) (by
      show (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta).1
          = blockOf (leftAcc.length + fMid.length + (composePath gMid rightAcc).length)
      rw [rhsInnerWidth, ModalityPath.length_composePath leftAcc fMid,
          ModalityPath.length_composePath gMid rightAcc,
          Nat.add_assoc (leftAcc.length + fMid.length) gMid.length rightAcc.length])
  rw [lhsOuterWidth, rhsOuterWidth, ModalityPath.length_composePath leftAcc fHigh,
      ModalityPath.length_composePath gMid rightAcc,
      Nat.add_assoc (leftAcc.length + fHigh.length) gMid.length rightAcc.length]

/-- ★ **The two-block commutation core** — the SHARPENED Godement-soundness residual.  Transposing the two
horizontally-independent middle blocks `cellAlphaUpper` (f-side, low block positions, right context the
g-prefix) and `cellBeta` (g-side, high block positions, left context the f-prefix), at a WELL-FORMED incoming
width (`state.1 = blockOf` of the post-`cellAlpha` 1-cell), preserves the running monotone map.  This is exactly
the disjoint-position simplicial `δδ` / `σσ` / `σδ` commutation at BLOCK scale — its single-generator instances
are the shipped `composeMap_faceMap_faceMap_commute` / `composeMap_degenMap_degenMap_commute` /
`composeMap_faceMap_degenMap_lowerCommute`.  The fold-threading, the right-context shift, and the WIDTH
component are all discharged (see the section lemmas); only this block-scale map commutation remains. -/
def MonoGodementCommute : Prop :=
  ∀ {overallSource overallTarget : AdjunctionMode}
    {sourceMode middleMode targetMode : AdjunctionMode}
    {fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (state : Nat × List Nat),
    state.1 = blockOf (leftAcc.length + fMid.length + (composePath gLow rightAcc).length) →
    runMonoCell (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta
      = runMonoCell (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper

/-- ★ **The SHARPENED two-block commutation residual — the VALUE-LIST (second projection) only.**  Identical to
`MonoGodementCommute` except it asserts equality of the running value-list `.2` alone; the WIDTH `.1` half is
discharged unconditionally by `runMonoCell_godementWidthCommute`.  This is the strictly-smaller residual the
Godement soundness now reduces to: the bare block-scale simplicial commutation of the two intrinsic monotone maps,
with the map-threading width bookkeeping already removed. -/
def MonoGodementMapCommute : Prop :=
  ∀ {overallSource overallTarget : AdjunctionMode}
    {sourceMode middleMode targetMode : AdjunctionMode}
    {fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (state : Nat × List Nat),
    state.1 = blockOf (leftAcc.length + fMid.length + (composePath gLow rightAcc).length) →
    (runMonoCell (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta).2
      = (runMonoCell (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper).2

/-- Component-wise extensionality for a width/value-list state pair, propext-free (`Prod.casesOn` + `rw`): two
states are equal when their width and value-list projections agree. -/
theorem prodEqOfComponentsEq {firstPair secondPair : Nat × List Nat}
    (widthEq : firstPair.1 = secondPair.1) (mapEq : firstPair.2 = secondPair.2) :
    firstPair = secondPair := by
  show (firstPair.1, firstPair.2) = secondPair
  rw [widthEq, mapEq]

/-- ★ **The value-list residual implies the full two-block commutation core.**  `MonoGodementCommute` is the pair
equality; its WIDTH half is `runMonoCell_godementWidthCommute` (unconditional given the well-formed incoming
width) and its VALUE-LIST half is `MonoGodementMapCommute`, assembled by component-wise extensionality.  So the
Godement soundness now reduces to `MonoGodementMapCommute` alone. -/
theorem MonoGodementCommute_of_mapCommute (mapCommute : MonoGodementMapCommute) : MonoGodementCommute := by
  intro overallSource overallTarget sourceMode middleMode targetMode fMid fHigh gLow gMid
    cellAlphaUpper cellBeta leftAcc rightAcc state hstate
  exact prodEqOfComponentsEq
    (runMonoCell_godementWidthCommute cellAlphaUpper cellBeta leftAcc rightAcc state hstate)
    (mapCommute cellAlphaUpper cellBeta leftAcc rightAcc state hstate)

/-- ★ **The Godement-soundness reduction.**  `monotoneMapOf` is invariant under the cell-level INTERCHANGE step
(`hcomp (α ⊟ αUpper) (β ⊟ βUpper) ≈ (α ⊟ β) ⊞ (αUpper ⊟ βUpper)`) GIVEN the two-block commutation core
`MonoGodementCommute`.  The shared `cellAlpha` prefix folds identically; `runMonoCell_width` supplies the core's
well-formedness precondition (the post-`cellAlpha` width is the genuine `blockOf`); the inner two-block IS the
core; the shared `cellBetaUpper` suffix is applied to the now-equal states by `congrArg`.  This is the
necessary-direction soundness leg of the augmented-simplex route: convertible-by-interchange cells have equal
monotone maps — combined with `decideMonotoneMapExtEq`, distinct maps SOUNDLY refute interchange-convertibility. -/
theorem monotoneMapOf_interchange_eq_of_commute (commute : MonoGodementCommute)
    {sourceMode middleMode targetMode : AdjunctionMode}
    {fLow fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr adjunctionModeSignature gMid gHigh) :
    monotoneMapOf (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
      = monotoneMapOf (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)) := by
  have hinit : blockOf (composePath fLow gLow).length
      = blockOf ((identityPath (graph := adjunctionModeSignature.graph) sourceMode).length + fLow.length
          + (composePath gLow (identityPath (graph := adjunctionModeSignature.graph) targetMode)).length) := by
    rw [ModalityPath.length_composePath fLow gLow,
        ModalityPath.length_composePath gLow (identityPath (graph := adjunctionModeSignature.graph) targetMode)]
    show blockOf (fLow.length + gLow.length) = blockOf (0 + fLow.length + (gLow.length + 0))
    rw [Nat.zero_add, Nat.add_zero]
  have hwf := runMonoCell_width cellAlpha (blockOf (composePath fLow gLow).length)
    (idMap (blockOf (composePath fLow gLow).length))
    (identityPath (graph := adjunctionModeSignature.graph) sourceMode)
    (composePath gLow (identityPath (graph := adjunctionModeSignature.graph) targetMode)) hinit
  rw [monotoneMapOf_eq_runMonoCell, monotoneMapOf_eq_runMonoCell,
      runMonoCell_interchangeRedex, runMonoCell_interchangeReduct]
  exact congrArg
    (fun st => (runMonoCell st (composePath (identityPath sourceMode) fHigh)
        (identityPath targetMode) cellBetaUpper).2)
    (commute cellAlphaUpper cellBeta (identityPath (graph := adjunctionModeSignature.graph) sourceMode)
      (identityPath (graph := adjunctionModeSignature.graph) targetMode) _ hwf)

/-! ## ★ The Godement-soundness residual is FALSE as stated — the over-quantification + degenerate-cap
obstructions, machine-checked

The prior pass reduced `monotoneMapOf`'s interchange-invariance to `MonoGodementMapCommute` and described what
remained as a "structural double induction" lifting the single-generator simplicial commutations to whole blocks.
This pass establishes, zero-axiom, that the residual is not merely UNPROVEN but FALSE as stated, and that the
natural in-range repair is undischargeable under the present encoding — so the soundness leg is blocked BELOW the
residual (in the encoding), not by a missing induction.  The three concrete obstructions:

  * `monoGodementMapCommute_refuted` — `MonoGodementMapCommute` quantifies over EVERY `state : Nat × List Nat`
    with only the width `state.1` pinned, leaving the value-list `state.2` unconstrained; a `state.2` with an
    out-of-range entry breaks the commutation already in the all-CUP case.
  * `degenMap_self_eq_idMapSucc` — the boundary degeneracy `σ_n : [n+1] → [n]` at the last position is `idMap
    (n+1)` (a no-op on the map), so the in-range invariant `mapsInto map width` is NOT preserved across a cap.
  * `counitMonotoneMap_notMapsInto` — the bare counit's intrinsic map is `[0] ∉ [0]`, so the in-range hypothesis
    the corrected residual would need is itself false for cells reaching width 0 through a cap. -/

/-- ★ **The residual `MonoGodementMapCommute` is FALSE as stated** (zero-axiom, machine-checked).  It quantifies
over EVERY `state : Nat × List Nat` with only the WIDTH `state.1` pinned to `blockOf`, leaving the value-list
`state.2` arbitrary.  A garbage `state.2` whose entries exceed the width breaks the commutation already in the
all-CUP case: with `cellAlphaUpper = cellBeta = adjunctionUnitTwoCell` (two cups), empty accumulators, and
`state = (0, [5])`, the LEFT run folds to value-list `[0]` while the RIGHT run folds to `[1]` — the out-of-range
entry `5` defaults to `0` after the first cup (`composeMap [5] [] = [0]`), then the two transposed faces at the
shifted positions `1` (β-high) versus `0` (α) disagree (`faceMap 1 1 = [0]` vs `faceMap 0 1 = [1]`).  So NO proof
term for `MonoGodementMapCommute` exists; the residual is missing the in-range hypothesis `mapsInto state.2
state.1`, without which the augmented-simplex commutation does not even hold pointwise. -/
theorem monoGodementMapCommute_refuted : ¬ MonoGodementMapCommute := by
  intro hcommute
  have hbad : ([0] : List Nat) = [1] :=
    hcommute adjunctionUnitTwoCell adjunctionUnitTwoCell
      (identityPath (graph := adjunctionModeSignature.graph) AdjunctionMode.base)
      (identityPath (graph := adjunctionModeSignature.graph) AdjunctionMode.base)
      ((0 : Nat), ([5] : List Nat)) rfl
  exact Nat.noConfusion (List.cons.inj hbad).1

/-- ★ **The pair-level core `MonoGodementCommute` is FALSE too** — its second projection IS
`MonoGodementMapCommute` (refuted above), so the full pair commutation cannot hold either.  Recorded so the dead
end is explicit: `monotoneMapOf_interchange_eq_of_commute`'s hypothesis `MonoGodementCommute` can never be
discharged as stated. -/
theorem monoGodementCommute_refuted : ¬ MonoGodementCommute := by
  intro hpair
  apply monoGodementMapCommute_refuted
  intro overallSource overallTarget sourceMode middleMode targetMode fMid fHigh gLow gMid
    cellAlphaUpper cellBeta leftAcc rightAcc state hstate
  exact congrArg Prod.snd (hpair cellAlphaUpper cellBeta leftAcc rightAcc state hstate)

/-- **The boundary-cap collapse** (obstruction 1): the degeneracy `σ_n : [n+1] → [n]` at the LAST position `n` is
the IDENTITY value-list `idMap (n+1)`.  `degenMap n n` repeats the maximal value, so by the `≤`-value
characterization it sends every position to itself rather than merging two — a no-op on any post-composed map,
yet it still drops the running width.  Hence at a cap whose block position equals `width - 1` the in-range
invariant `mapsInto map width` is NOT preserved: the map is unchanged but the width shrinks, and the map may
still hit `width - 1`.  (This is the `degenMap (w-1) (w-1) = idMap w` boundary the prior note flagged.) -/
theorem degenMap_self_eq_idMapSucc (n : Nat) : degenMap n n = idMap (n + 1) := by
  apply listExtById
  · rw [degenMap_length, idMap_length]
  · intro position hpos
    rw [degenMap_length] at hpos
    show monotoneMapGet (degenFrom 0 n n) position = monotoneMapGet (idMap (n + 1)) position
    rw [degenFrom_get_le 0 n n position (Nat.le_of_lt_succ hpos) hpos, Nat.zero_add,
        monotoneMapGet_idMap (n + 1) position hpos]

/-- ★ **Obstruction (2), sharpened: the in-range REPAIR is itself undischargeable.**  The bare counit's intrinsic
monotone map is `monotoneMapOf adjunctionCounitTwoCell = [0]` (a claimed map `[1] → [0]`), and `[0]` does NOT map
into its codomain ordinal `[0] = ∅` — its sole entry `0` is not `< 0`.  So `mapsInto (monotoneMapOf cellAlpha)
width`, the in-range hypothesis a corrected `MonoGodementMapCommute` would require at the real call site
`monotoneMapOf_interchange_eq_of_commute`, is itself FALSE for any cell reaching width 0 through a cap.  Thus
even adding `mapsInto state.2 state.1` does not close the leg: the monotone-map encoding produces out-of-range
value-lists at the degenerate `L·R` / `R·L` boundary clicks (the non-uniform-variance / non-additive-block-width
gap the faithfulness marker flags), so the encoding itself must be refined (codomain-tracked, variance-aware Δ₊
morphisms) before this leg can close. -/
theorem counitMonotoneMap_notMapsInto :
    ¬ mapsInto (monotoneMapOf adjunctionCounitTwoCell) 0 := by
  rw [monotoneMapOf_counit]
  intro hmaps
  exact absurd (hmaps 0 (Nat.succ_pos 0)) (Nat.not_lt_zero 0)

/-! ## ★ The codomain-tracked in-range REPAIR is NECESSARY but NOT SUFFICIENT — the tip op-variance refutes the
restated residual even from the IDENTITY state, machine-checked

The prior pass refuted `MonoGodementMapCommute` with a JUNK out-of-range state (`(0, [5])`) and concluded the
residual is "missing the in-range hypothesis `mapsInto state.2 state.1`".  The codomain-tracked `MonotoneMap` makes
that junk UNREPRESENTABLE — so the natural next move is to RESTATE the residual with the in-range (and even
weakly-increasing) hypothesis and hope it now holds.  This section establishes, zero-axiom and machine-checked,
that the in-range repair is **necessary but NOT sufficient**: the restated `MonoGodementMapCommuteInRange` is
STILL FALSE, refuted from the canonical IDENTITY state `(2, idMap 2)` by a single op-variant cup at mode `tip`.

The mechanism is the NON-UNIFORM VARIANCE, localized precisely:

  * **In-range is preserved by every CUP and every INTERNAL cap** (`cupPreservesMapsInto`,
    `internalCapPreservesMapsInto`): the covariant fold is well-behaved on the `base ⟶ base` (`Adj(+,+) ≅ Δ₊`)
    fragment, where every cap sits at an internal `R·L` seam (`position < width - 1`).
  * **In-range is BROKEN by a BOUNDARY cap** (`degenMap_self_eq_idMapSucc`: `degenMap (w-1) (w-1) = idMap w`, a
    no-op on the map that still drops the width) — the `Adj(−,−) ≅ Δ₊^op` mode-`tip` case, where the bare counit
    caps the LAST block (`position = width - 1`).
  * Consequently a mode-`tip` CUP (`opVariantTipCup` = `(R ◁ η) ▷ L : R·L ⟹ (R·L)²`, which the COVARIANT fold
    mislabels as a face growing the ordinal, when in `Δ₊^op` it is a degeneracy) reads the post-boundary-cap
    out-of-range value through the WRONG (dropped) width, and the Godement transposition disagrees:
    `monoGodementMapCommuteInRange_refuted`.

So the soundness leg is blocked not at the STATE encoding (which the tracked type fixes) but at the FOLD itself:
`monoStepAtom` treats every cup as a covariant face and every cap as a covariant degeneracy, ignoring the
per-mode variance.  Closing the leg requires a VARIANCE-AWARE fold (op-reading at `tip`), strictly more than the
codomain-tracking — which this section pins down, machine-checked. -/

/-- A composite lands in the outer codomain when the first map lands in the second's domain and the second lands
in the codomain — the in-range transfer law for `composeMap`. -/
theorem composeMap_mapsInto (first second : List Nat) (codomain : Nat)
    (hfirst : mapsInto first second.length) (hsecond : mapsInto second codomain) :
    mapsInto (composeMap first second) codomain := by
  intro position hpos
  rw [composeMap_length] at hpos
  rw [composeMap_get first second position hpos]
  exact hsecond (monotoneMapGet first position) (hfirst position hpos)

/-- ★ **A CUP preserves the in-range invariant, unconditionally** (covariantly): post-composing the face
`δ_position : [width] → [width+1]` onto an in-range map keeps it in range into the grown ordinal `[width+1]`.  The
covariant fold is well-behaved on cups. -/
theorem cupPreservesMapsInto (position width : Nat) (map : List Nat) (hmap : mapsInto map width) :
    mapsInto (composeMap map (faceMap position width)) (width + 1) :=
  composeMap_mapsInto map (faceMap position width) (width + 1)
    (by rw [faceMap_length]; exact hmap) (faceMap_mapsInto position width)

/-- ★ **An INTERNAL cap preserves the in-range invariant**: post-composing a GENUINE degeneracy
`σ_position : [widthPred+1] → [widthPred]` (position `< widthPred`, an internal `R·L` seam) onto an in-range map
keeps it in range into the shrunk ordinal `[widthPred]`.  This is exactly the `base ⟶ base` covariant case —
every cap there is internal. -/
theorem internalCapPreservesMapsInto (position widthPred : Nat) (map : List Nat)
    (hmap : mapsInto map (widthPred + 1)) (hinternal : position < widthPred) :
    mapsInto (composeMap map (degenMap position widthPred)) widthPred :=
  composeMap_mapsInto map (degenMap position widthPred) widthPred
    (by rw [degenMap_length]; exact hmap) (degenMap_mapsInto position widthPred hinternal)

/-- ★ **A BOUNDARY cap does NOT preserve the in-range invariant** — the machine-checked obstruction.  At the last
position `position = widthPred` the "degeneracy" `degenMap widthPred widthPred = idMap (widthPred+1)` is the
IDENTITY (a no-op on the map), so post-composing it onto the identity map `idMap (widthPred+1)` leaves
`idMap (widthPred+1)`, which hits `widthPred ∉ [widthPred]`.  This is the `Δ₊^op` mode-`tip` boundary click that
breaks the covariant fold (the bare counit's `[0] ∉ [0]`, generalized). -/
theorem boundaryCapBreaksMapsInto (widthPred : Nat) :
    ¬ mapsInto (composeMap (idMap (widthPred + 1)) (degenMap widthPred widthPred)) widthPred := by
  rw [degenMap_self_eq_idMapSucc,
      composeMap_idMap_right (idMap (widthPred + 1)) (widthPred + 1) (idMap_mapsInto (widthPred + 1))]
  intro hmaps
  have hhit : monotoneMapGet (idMap (widthPred + 1)) widthPred < widthPred :=
    hmaps widthPred (by rw [idMap_length]; exact Nat.lt_succ_self widthPred)
  rw [monotoneMapGet_idMap (widthPred + 1) widthPred (Nat.lt_succ_self widthPred)] at hhit
  exact Nat.lt_irrefl widthPred hhit

/-- The **op-variant tip CUP** `(R ◁ η) ▷ L : R·L ⟹ (R·L)²` — the unit whiskered into mode `tip`.  The COVARIANT
fold reads it as a FACE growing the ordinal; but at `tip` (`Adj(−,−) ≅ Δ₊^op`) it is the op of a degeneracy, so
the covariant treatment is variance-WRONG.  This is the witness that refutes the in-range restatement below. -/
def opVariantTipCup :
    RawTwoCellExpr adjunctionModeSignature adjunctionRightThenLeft
      (composePath (composePath (singletonModalityPath AdjunctionModality.right) adjunctionLeftThenRight)
        (singletonModalityPath AdjunctionModality.left)) :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.left)
    (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)

/-- ★ **The in-range-REPAIRED Godement residual** — `MonoGodementMapCommute` strengthened with BOTH the in-range
hypothesis `mapsInto state.2 state.1` (excluding the prior junk refutation) AND weak monotonicity
`isWeaklyIncreasing state.2` (so `state.2` is a genuine tracked `MonotoneMap`).  This is the strongest natural
restatement the codomain-tracking suggests; the refutation below shows even this is FALSE. -/
def MonoGodementMapCommuteInRange : Prop :=
  ∀ {overallSource overallTarget : AdjunctionMode}
    {sourceMode middleMode targetMode : AdjunctionMode}
    {fMid fHigh : ModalityPath adjunctionModeSignature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath adjunctionModeSignature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr adjunctionModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr adjunctionModeSignature gLow gMid)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath adjunctionModeSignature.graph targetMode overallTarget)
    (state : Nat × List Nat),
    state.1 = blockOf (leftAcc.length + fMid.length + (composePath gLow rightAcc).length) →
    mapsInto state.2 state.1 →
    isWeaklyIncreasing state.2 →
    (runMonoCell (runMonoCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta).2
      = (runMonoCell (runMonoCell state (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper).2

/-- ★★ **The in-range repair is INSUFFICIENT — `MonoGodementMapCommuteInRange` is FALSE** (zero-axiom,
machine-checked).  Transposing the op-variant tip cup `opVariantTipCup` (f-side) past the bare counit (g-side) at
the canonical IDENTITY state `(2, idMap 2 = [0,1])` — which is in-range AND weakly increasing — disagrees: the
LEFT run (cup at width 2 BEFORE the cap, face `δ_0 : [2]→[3] = [1,2]`) folds the value-list to `[1,2]`, while the
RIGHT run (cap FIRST drops the width to 1 via the boundary degeneracy `σ_1 = idMap 2`, leaving `[0,1]` out of
range, so the subsequent cup's face `δ_0 : [1]→[2] = [1]` reads the now-out-of-range entry `1` as the default `0`)
folds to `[1,0]`.  `[1,2] ≠ [1,0]`, so NO proof of `MonoGodementMapCommuteInRange` exists.

This SHARPENS the prior junk refutation decisively: the obstruction is NOT the state encoding (the tracked type
makes junk unrepresentable) but the FOLD's variance-blindness — `monoStepAtom` treats the mode-`tip` cup as a
covariant face when `Δ₊^op` demands a degeneracy.  Closing the Godement-soundness leg therefore requires a
VARIANCE-AWARE fold (op-reading at `tip`), strictly more than codomain-tracking. -/
theorem monoGodementMapCommuteInRange_refuted : ¬ MonoGodementMapCommuteInRange := by
  intro hcommute
  have hbad : ([1, 2] : List Nat) = [1, 0] :=
    hcommute opVariantTipCup adjunctionCounitTwoCell
      (identityPath (graph := adjunctionModeSignature.graph) AdjunctionMode.tip)
      (identityPath (graph := adjunctionModeSignature.graph) AdjunctionMode.tip)
      (2, idMap 2) rfl (idMap_mapsInto 2) (idMap_isWeaklyIncreasing 2)
  injection hbad with _headEqual tailEqual
  injection tailEqual with secondEqual _
  exact Nat.noConfusion secondEqual

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The Schanuel–Street monotone-map model is shipped: the `MonotoneMap` algebra on `List Nat`
(`composeMap` / `idMap` / face `faceMap` / degeneracy `degenMap`), the structural fold `monotoneMapOf` over the
cup/cap spine (it COMPUTES), and the structural-fragment soundness leg
(`monotoneMapOf_eq_of_interchangeFreeStep`).  `= true`. -/
def fxMode_hasSaturatedMonotoneMapFold : Bool := true

/-- **★ ESTABLISHED — the headline.**  The TRIANGLE IDENTITY is FREE in the monotone-map model: it is exactly the
SIMPLICIAL IDENTITY `σ_i ∘ δ_i = id` (`composeMap_faceMap_degenMap`), proved zero-axiom for EVERY position `i`,
hence under any whisker context.  The snake collapse `snakeCollapseAtWidth` discharges by it at every width, and
the WHISKERED left snake collapses to the identity at the non-trivial width `1` GENUINELY via the simplicial
identity (`monotoneMapOf_whiskeredLeftSnake_via_simplicialIdentity` — the proof is the simplicial-identity lemma,
not a width-`0` accident).  `= true`. -/
def fxMode_hasSaturatedMonotoneMapTriangleFree : Bool := true

/-- **★ ESTABLISHED — the full commuting simplicial identity set.**  Beyond the two `σδ = id` cancellations, the
monotone-map model now carries ALL THREE Godement-independence COMMUTATIONS, each zero-axiom: the cosimplicial
face-face `δ_{j+1} ∘ δ_i = δ_i ∘ δ_j` (`composeMap_faceMap_faceMap_commute`), the codegeneracy degeneracy-degeneracy
`σ_j ∘ σ_i = σ_i ∘ σ_{j+1}` (`composeMap_degenMap_degenMap_commute`), and the mixed separated face-degeneracy
`σ_{j+1} ∘ δ_i = δ_i ∘ σ_j` (`composeMap_faceMap_degenMap_lowerCommute`).  This is the complete algebra a Godement
transposition of two horizontally-independent atoms must reduce to — the disjoint-position commutations.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapSimplicialIdentitySet : Bool := true

/-- **★ ESTABLISHED — the decision procedure on normal forms.**  Monotone-map (normal-form) equality is decidable
`propext`-free: extensional `Fin m → Fin n` equality is exactly structural value-list equality
(`monotoneMapExtEq_iff_eq`, via `listExtById`), decided by a `dite` over `List.decEq` (`decideMonotoneMapExtEq`) —
which COMPUTES and carries no `propext`.  So the augmented-simplex side of the cross-check supplies a genuine,
independent, zero-axiom decision of monotone-map equality on the canonical forms.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapDecidableNormalForm : Bool := true

/-- **★ ESTABLISHED — the model is the category Δ₊ of genuinely-monotone maps.**  With the codomain tracked
(`mapsInto`), `composeMap` is associative (`composeMap_assoc`) and right-unital (`composeMap_idMap_right`, plus the
unconditional left unit `composeMap_idMap_eq`): the value-lists form a CATEGORY.  Every generator is genuinely
weakly increasing (`idMap_isWeaklyIncreasing` / `faceMap_isWeaklyIncreasing` / `degenMap_isWeaklyIncreasing`),
closed under composition (`composeMap_isWeaklyIncreasing`) — so "monotone map" is PROVED, not merely asserted, and
the model realizes the augmented simplex category Δ₊.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapCategory : Bool := true

/-- **★ ESTABLISHED — the generators are genuine epis and monos (the Eilenberg–Zilber building blocks).**  The
FACE generators are strictly increasing (`faceMap_isStrictlyIncreasing`) hence injective
(`faceMap_isInjectiveOnDomain`), strictness closed under composition (`composeMap_isStrictlyIncreasing`); the
DEGENERACY generators are surjective onto their codomain (`degenMap_isSurjectiveOnto`).  These are exactly the
epi/mono halves an EZ factorization (surjection-then-injection) of an arbitrary monotone map decomposes into — the
building blocks proved, the full factorization of an arbitrary map left as the named residual below.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapGeneratorEpiMono : Bool := true

/-- **★ ESTABLISHED — the Eilenberg–Zilber factorization (existence).**  Every value-list is its RANK (epi) composed
with its IMAGE (mono): `composeMap_rankList_imageList` proves `composeMap (rankList values) (imageList values) =
values` zero-axiom — the EZ decomposition map (surjection-then-injection) exists for every monotone map, with
`rankList_length` giving the surjection the right source ordinal.  The construction is `propext`-free (`dite` over
`Nat.decEq`), and the smokes exhibit the genuine epi/mono shape on a sorted input
(`[2,2,5,5,5,7] = [0,0,1,1,1,2] then [2,5,7]`).  What REMAINS toward full EZ is the proof that for an ARBITRARY
sorted input the image is strictly increasing and the rank surjective (the generators are already proved epi/mono),
plus EZ UNIQUENESS — see the faithfulness residual.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapEZFactorization : Bool := true

/-- **★ ESTABLISHED — `monotoneMapOf` Godement-invariance REDUCED to the two-block commutation core.**  The
interchange (Godement) soundness of `monotoneMapOf` is reduced, zero-axiom, to the single residual
`MonoGodementCommute` by `monotoneMapOf_interchange_eq_of_commute`, discharging everything else:
  * the **fold-decomposition** `monoProcessSpine_spineDiff` peels the four whiskered blocks of an interchange
    redex / reduct (`runMonoCell_interchangeRedex` / `…Reduct`);
  * **right-context irrelevance** `runMonoCell_rightContext_irrelevant` drops the `cellAlphaUpper` shift
    `gLow → gMid` for free (`monoStepAtom` never reads the right whisker);
  * the **block-width invariant** `runMonoCell_width` DISCHARGES the non-additive block-width bookkeeping the
    prior residual flagged — the running width is pinned to the genuine `blockOf` of the current 1-cell length,
    so the width component of the commutation holds and the truncated-subtraction underflow is ruled out.
This mirrors the arc route's reduction (`arcGodementInvariant_of_commute`) but lands strictly sharper: the
right-context and the WIDTH are both discharged here.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapGodementReduction : Bool := true

/-- **Honesty marker — the interchange/Godement soundness residual is FALSE AS STATED (sharpened, machine-checked;
not merely unproven).**  The prior pass reduced `monotoneMapOf`'s invariance under the INTERCHANGE law to the
value-list residual `MonoGodementMapCommute` (via `monotoneMapOf_interchange_eq_of_commute` /
`MonoGodementCommute_of_mapCommute`, the WIDTH half discharged unconditionally by
`runMonoCell_godementWidthCommute`) and anticipated a "structural double induction" lifting the single-generator
`δδ` / `σσ` / `σδ` commutations to whole blocks.  This pass establishes, zero-axiom, that the residual cannot be
closed as stated and the leg is blocked BELOW it — in the encoding, not in a missing induction:

  * `monoGodementMapCommute_refuted : ¬ MonoGodementMapCommute` — the residual quantifies over EVERY `state` with
    only the width `state.1` pinned, so a value-list `state.2` with an out-of-range entry breaks it already in
    the all-CUP case (`cellAlphaUpper = cellBeta = unit`, empty accumulators, `state = (0, [5])`: left run `[0]`,
    right run `[1]`).  It is missing the in-range hypothesis `mapsInto state.2 state.1`, without which the
    block-scale simplicial commutation does not hold even pointwise.
  * `monoGodementCommute_refuted : ¬ MonoGodementCommute` — the pair-level core (the second projection of which
    IS `MonoGodementMapCommute`) is false for the same reason, so the hypothesis of
    `monotoneMapOf_interchange_eq_of_commute` can never be discharged as stated.
  * `counitMonotoneMap_notMapsInto : ¬ mapsInto (monotoneMapOf adjunctionCounitTwoCell) 0` — and the in-range
    RESTATEMENT is itself undischargeable: the real intrinsic maps escape their codomain at width-0 caps (the
    counit's map is `[0] ∉ [0]`), so `monotoneMapOf_interchange_eq_of_commute` could not supply
    `mapsInto state.2 state.1` even if it were added to the residual.
  * `degenMap_self_eq_idMapSucc : degenMap n n = idMap (n+1)` — the boundary-cap collapse (obstruction 1) that
    additionally breaks preservation of any in-range invariant across a `vcomp` (a no-op on the map that still
    drops the width).

★ **SHARPENED this pass: the in-range REPAIR is NECESSARY but NOT SUFFICIENT (machine-checked).**  The
codomain-tracked `MonotoneMap` type (this file) makes the prior junk state `(0, [5])` UNREPRESENTABLE, so the
natural next move — RESTATE the residual with the in-range (and weakly-increasing) hypothesis — is now available
as `MonoGodementMapCommuteInRange`.  But `monoGodementMapCommuteInRange_refuted : ¬ MonoGodementMapCommuteInRange`
refutes EVEN THAT, zero-axiom, from the canonical IDENTITY state `(2, idMap 2)`: transposing the op-variant tip
cup `opVariantTipCup` past the counit gives `[1,2]` vs `[1,0]`.  The obstruction is therefore NOT the state
encoding but the FOLD's VARIANCE-BLINDNESS: in-range is preserved by every cup and every internal cap
(`cupPreservesMapsInto` / `internalCapPreservesMapsInto`) but BROKEN by a `tip` boundary cap
(`boundaryCapBreaksMapsInto`), and `monoStepAtom` reads the mode-`tip` cup as a covariant FACE when `Δ₊^op`
demands a DEGENERACY.  So closing the Godement soundness leg requires a genuinely VARIANCE-AWARE fold (op-reading
at `tip`), strictly MORE than the codomain-tracking — the codomain-tracking is a necessary first half, now
shipped, and the precise remaining obstruction is machine-checked here.  `= false`. -/
def fxMode_hasSaturatedMonotoneMapGodementSoundness : Bool := false

/-- **Honesty marker — the faithfulness residual (SHARPENED).**  `convOfMapEq` (equal monotone maps ⟹
saturated-convertible) is the genuine hard Schanuel–Street direction: build the canonical cell per monotone map
(its EILENBERG–ZILBER factorization into a composite of degeneracies-then-faces) and show every cell with that map
converts to it.  The generator-level EZ building blocks are now SHIPPED
(`fxMode_hasSaturatedMonotoneMapGeneratorEpiMono`: faces injective, degeneracies surjective), and the model is a
category with the full simplicial presentation; what REMAINS is (1) the EZ FACTORIZATION of an ARBITRARY monotone
map into those generators (the epi-mono `image`/`rank` split — a dedup/rank construction over the value-list), and
(2) the CELL-LEVEL reconstruction past the `spine` quotient (lives in the arc-route files).  Both are gated by the
non-uniform variance (`Adj(+,+) ≅ Δ₊` vs `Adj(−,−) ≅ Δ₊^op`) and the non-additive block-width at the `L·R` / `R·L`
boundary clicks, which a bare `List Nat` carrier cannot witness.  `= false`. -/
def fxMode_hasSaturatedMonotoneMapFaithfulness : Bool := false

end FX1Poly.Tier0
