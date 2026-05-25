import LeanFX2.Foundation._deprecated_polygraph.ParallelPair

/-! # `HorizontalChain` — whiskering / parallel composition of dim-1 cells.

Burroni 1993 §1.1 / §2 free strict ω-category presentation: horizontal
composition `c · c'` of two 1-cells along their shared dim-0 vertex
requires `t_0(c) = s_0(c')` (target vertex of `c` equals source vertex
of `c'`).

While vertical composition (`VerticalChain`) sequences `(n+2)`-cells
along their `(n+1)`-boundary, horizontal composition sequences dim-1
arrows along their dim-0 boundary.  The two operations are dual within
a strict ω-category: vertical is `∗_n` along the codim-1 boundary;
horizontal is `·` along the codim-2 boundary.

## Construction

`HorizontalChain sourceVtx targetVtx`:

* `identity anchorVtx` — the empty / identity chain at vertex
  `anchorVtx` (a degenerate dim-1 path).
* `cons stepArrow tailChain` — extend a chain starting at `midVtx`
  to one starting at `sourceVtx` by prepending a dim-1 arrow
  `stepArrow : PolyCell 1 sourceVtx midVtx`.

The matching condition `t_0(stepArrow) = s_0(tailChain)` is enforced
by the shared `midVtx` index across the cons argument types — no
separate hypothesis needed.

## Operations shipped here (K11.5 minimal scope, globular reading)

* `HorizontalChain.length` — number of arrows composed.
* `HorizontalChain.append` — concatenation of two chains sharing a
  midpoint vertex.
* `HorizontalChain.length_identity_eq_zero` / `_cons_eq_succ_length_tail`
  — length on the constructors.
* `HorizontalChain.length_append_eq_sum_of_lengths` — append
  distributes length.
* `HorizontalChain.append_identity_left/right` — identity unit laws.
* `HorizontalChain.composeTwoArrows` — pair-wise horizontal composition.

## Multi-port (operadic Squier reading) deferral

The PolyCell substrate shipped at K11.1 is globular — every cell has a
single source and single target.  Squier 1987 / Métayer 2008 give an
operadic reading where cells take a finite *list* of source ports and
a finite *list* of target ports, generalizing whiskering to a tensorial
horizontal composition over multi-input/multi-output rewriting rules.

That operadic generalization requires a NEW polygraph encoding indexed
by port arity, not merely operations over the existing `PolyCell`.
It is deferred to a follow-up K11.5b ticket; the globular horizontal
composition shipped here is what every downstream FX construct
(`Step.toDim1Cell`, free n-category, strategy 3-cells) actually
consumes, because FX's reduction relation is single-source-single-
target at every cell.

Verified zero-axiom via `#print axioms` per declaration. -/

namespace LeanFX2.Foundation._deprecated_polygraph

/-- A free horizontal chain of dim-1 arrows composing end-to-end from
`sourceVtx` to `targetVtx`. -/
inductive HorizontalChain :
    (sourceVtx targetVtx : Nat) → Type
  | identity (anchorVtx : Nat) :
      HorizontalChain anchorVtx anchorVtx
  | cons {sourceVtx midVtx targetVtx : Nat}
         (stepArrow : PolyCell 1 sourceVtx midVtx)
         (tailChain : HorizontalChain midVtx targetVtx) :
      HorizontalChain sourceVtx targetVtx

namespace HorizontalChain

/-- Number of arrows composed in a chain.  Identity has length 0;
each `cons` adds one. -/
def length {sourceVtx targetVtx : Nat}
    (chain : HorizontalChain sourceVtx targetVtx) : Nat :=
  match chain with
  | identity _ => 0
  | cons _ tailChain => tailChain.length + 1

@[simp] theorem length_identity_eq_zero (anchorVtx : Nat) :
    (identity anchorVtx).length = 0 := rfl

@[simp] theorem length_cons_eq_succ_length_tail
    {sourceVtx midVtx targetVtx : Nat}
    (stepArrow : PolyCell 1 sourceVtx midVtx)
    (tailChain : HorizontalChain midVtx targetVtx) :
    (cons stepArrow tailChain).length = tailChain.length + 1 := rfl

/-- Concatenation of two horizontal chains sharing a midpoint vertex. -/
def append {sourceVtx midVtx targetVtx : Nat}
    (firstChain : HorizontalChain sourceVtx midVtx)
    (secondChain : HorizontalChain midVtx targetVtx) :
    HorizontalChain sourceVtx targetVtx :=
  match firstChain with
  | identity _ => secondChain
  | cons stepArrow restChain =>
    cons stepArrow (append restChain secondChain)

@[simp] theorem append_identity_left {sourceVtx targetVtx : Nat}
    (chain : HorizontalChain sourceVtx targetVtx) :
    append (identity sourceVtx) chain = chain := rfl

theorem append_cons_unfold
    {sourceVtx midVtxInner midVtx targetVtx : Nat}
    (stepArrow : PolyCell 1 sourceVtx midVtxInner)
    (restChain : HorizontalChain midVtxInner midVtx)
    (secondChain : HorizontalChain midVtx targetVtx) :
    append (cons stepArrow restChain) secondChain =
    cons stepArrow (append restChain secondChain) := rfl

theorem append_identity_right {sourceVtx targetVtx : Nat}
    (chain : HorizontalChain sourceVtx targetVtx) :
    append chain (identity targetVtx) = chain := by
  induction chain with
  | identity _ => rfl
  | cons stepArrow restChain ih =>
    rw [append_cons_unfold, ih]

theorem length_append_eq_sum_of_lengths {sourceVtx midVtx targetVtx : Nat}
    (firstChain : HorizontalChain sourceVtx midVtx)
    (secondChain : HorizontalChain midVtx targetVtx) :
    (firstChain.append secondChain).length =
      firstChain.length + secondChain.length := by
  induction firstChain with
  | identity _ =>
    rw [append_identity_left, length_identity_eq_zero, Nat.zero_add]
  | cons stepArrow restChain ih =>
    rw [append_cons_unfold,
        length_cons_eq_succ_length_tail,
        length_cons_eq_succ_length_tail,
        ih,
        Nat.add_right_comm]

/-- Horizontal composition of two arrows sharing a dim-0 vertex.
Returns a length-2 chain. -/
def composeTwoArrows {sourceVtx midVtx targetVtx : Nat}
    (firstArrow : PolyCell 1 sourceVtx midVtx)
    (secondArrow : PolyCell 1 midVtx targetVtx) :
    HorizontalChain sourceVtx targetVtx :=
  cons firstArrow (cons secondArrow (identity targetVtx))

theorem composeTwoArrows_length_eq_two {sourceVtx midVtx targetVtx : Nat}
    (firstArrow : PolyCell 1 sourceVtx midVtx)
    (secondArrow : PolyCell 1 midVtx targetVtx) :
    (composeTwoArrows firstArrow secondArrow).length = 2 := by
  show (cons firstArrow (cons secondArrow (identity targetVtx))).length = 2
  rw [length_cons_eq_succ_length_tail,
      length_cons_eq_succ_length_tail,
      length_identity_eq_zero]

end HorizontalChain

end LeanFX2.Foundation._deprecated_polygraph
