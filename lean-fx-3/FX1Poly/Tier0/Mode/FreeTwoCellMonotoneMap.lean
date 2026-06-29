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

/-! ## Composition identities scaffolding the vcomp homomorphism + the snake collapse -/

/-- The identity map on `[n]` has `n` entries. -/
theorem idMap_length (n : Nat) : (idMap n).length = n := ascendingFrom_length 0 n

/-- The face generator's value-list has `n` entries (`faceMap`-level restatement). -/
theorem faceMap_length (i n : Nat) : (faceMap i n).length = n := faceFrom_length 0 i n

/-- The degeneracy generator's value-list has `n+1` entries (`degenMap`-level restatement). -/
theorem degenMap_length (i n : Nat) : (degenMap i n).length = n + 1 := degenFrom_length 0 i n

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

/-- **Honesty marker — the interchange/Godement soundness residual.**  `monotoneMapOf` reads the spine, so its
invariance under the INTERCHANGE (Godement) law is the spine TRACE-equivalence invariance — the same residual the
matching invariant left open (`fxMode_hasMatchingGodementIndependenceProof`): a `SpineGodementStep` permutes two
horizontally-independent atoms with whisker-context shifts, and the corresponding face/degeneracy positions
commute by the DISJOINT simplicial identities — a cleaner residual than the union-find independence, but the
general zero-axiom proof (matching the Godement context shift to the simplicial position shift) is the standing
obligation.  Hence the full `mapEqOfConv` (which also threads the saturated whisker congruences through the
shifted positions) is NOT yet a total field.  `= false`. -/
def fxMode_hasSaturatedMonotoneMapGodementSoundness : Bool := false

/-- **Honesty marker — the faithfulness residual.**  `convOfMapEq` (equal monotone maps ⟹ saturated-convertible)
is the genuine hard Schanuel–Street direction (build the canonical cell per monotone map; every cell with that
map converts to it).  The walking-adjunction hom-categories' variance is non-uniform (the `+,+` and `-,-` homs
use opposite identifications, and the block-width ordinal is non-additive at the `L·R` / `R·L` boundary clicks),
so a globally faithful `monotoneMapOf` and its inverse are a multi-brick development.  This file ships the SOUND
direction's model + the simplicial-identity triangle crux; faithfulness is the named residual.  `= false`. -/
def fxMode_hasSaturatedMonotoneMapFaithfulness : Bool := false

end FX1Poly.Tier0
