import FX1Poly.Polygraph.TwoCategory.WalkingTraced.TracedDiagramSeed

/-! # WalkingTraced/TracedDiagramBoxCount — the genuine-generator (box) count invariant + SOUNDNESS

The soundness half of the walking traced PROP: the genuine-generator map `boxCount : TracedDiagram → Nat` counting
the `box` occurrences (`box ↦ 1`; `empty` / `idWire` / `swap` ↦ 0; `seq` / `tensor` ↦ sum; and — trace-transparent
— `traceN k f ↦ boxCount f`, ignoring the fed-back wire-count `k`), and the SOUNDNESS theorem
`boxCount_congr_of_conv` — trace-convertible diagrams have EQUAL genuine-generator count.  This is the trace-axiom
soundness invariant: distinct `boxCount` ⟹ not convertible.

## The invariant — a genuine `Nat` structural fold, ZERO subtraction

Because the carrier `TracedDiagram` is UN-INDEXED over objects (see `TracedDiagramSeed`), `boxCount` is an honest
structural recursion whose defining equations reduce by `rfl`, and its preservation under the three trace axioms is
pure additive `Nat` arithmetic with NO subtraction — the faithful `arityOf` analog:

* vanishing-I `Tr^I(f) ↦ f` — `boxCount (traceN 0 f) = boxCount f` DEFINITIONALLY (`traceN` is transparent);
* yanking `Tr^W(σ) ↦ id_W` — `boxCount (traceN 1 swap) = 0 = boxCount idWire`, `rfl`;
* left tightening `Tr^W((g ⊗ id_W) ∘ f) ↦ g ∘ Tr^W(f)` — both sides reduce to `boxCount g + boxCount f`, the
  `boxCount idWire = 0` folding away since `x + 0 ≡ x` definitionally (the same fact the operad right-unit arm uses).

Keeping `boxCount` (not a wire-count) as the primary invariant sidesteps `Nat` subtraction entirely — the
propext-leak risk that `Nat.sub_sub` / vanishing-⊗ would introduce is avoided by construction, staying maximally
template-faithful to `arityOf`.

## ★ Honesty boundary — SOUNDNESS ONLY, and a witnessed INCOMPLETENESS (see the markers)

Brick 1 ships the SOUNDNESS direction (`boxCount_congr_of_conv`) plus non-vacuity (an axiom fires; non-convertible
pairs separate by `boxCount`).  The full DECISION (completeness / a word-problem decider) is deferred to the later
Int-construction brick.

`boxCount` is a genuine INVARIANT, manifestly INCOMPLETE — like the braid's `S_3` map, NOT the operad's secretly
complete arity: `swap` and `tensor idWire idWire` both have `boxCount = 0` (`boxCount_swap_eq_tensorIdWireIdWire`,
by `rfl`), yet the symmetry `σ` is NOT the identity `id_{W⊗W}` — they are not convertible, and separating them is
exactly the Int-construction normal-form content of the later brick.  So this rung reads like the braid (genuine
invariant, manifestly incomplete), the more honest of the two stories.

## Propext-cleanliness

`boxCount` is DATA-valued (`Nat`) and folds by `casesOn` on the tree constructor (no index refinement, the trace
payload `k` matched by `_`) — clean.  All matches are full-enumeration; the soundness induction uses only `rfl` /
`rw` (all additive `Nat`, no subtraction, no `omega` / `simp` / `decide`); the negatives route through soundness +
`Nat.noConfusion`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The genuine-generator (box) count invariant -/

/-- ★ The **genuine-generator count** of the walking traced PROP: fold a diagram into its number of `box`
occurrences — `box ↦ 1`; `empty` / `idWire` / `swap` ↦ 0; `seq` / `tensor` sum the children's counts; and a trace
`traceN k f ↦ boxCount f` is TRANSPARENT (ignores the fed-back wire-count `k`).  Additive, ZERO subtraction,
full-enumeration (seven arms, no wildcard over the carrier), DATA-valued → propext-clean.  DATA-valued structural
recursion on the un-indexed `TracedDiagram`, so the defining equations reduce DEFINITIONALLY.  The trace-axiom
soundness invariant (the `arityOf` analog). -/
def boxCount : TracedDiagram → Nat
  | .empty => 0
  | .idWire => 0
  | .box => 1
  | .swap => 0
  | .seq left right => boxCount left + boxCount right
  | .tensor left right => boxCount left + boxCount right
  | .traceN _ inner => boxCount inner

/-- The defining equation on `empty` — the empty diagram has no generators. -/
theorem boxCount_empty : boxCount TracedDiagram.empty = 0 := rfl

/-- The defining equation on `idWire` — an identity wire has no generators. -/
theorem boxCount_idWire : boxCount TracedDiagram.idWire = 0 := rfl

/-- The defining equation on `box` — the genuine generator counts once. -/
theorem boxCount_box : boxCount TracedDiagram.box = 1 := rfl

/-- The defining equation on `swap` — the symmetry is structure, no generators. -/
theorem boxCount_swap : boxCount TracedDiagram.swap = 0 := rfl

/-- The defining equation on `seq` — sequential composition sums the children's counts.  Holds DEFINITIONALLY. -/
theorem boxCount_seq (left right : TracedDiagram) :
    boxCount (TracedDiagram.seq left right) = boxCount left + boxCount right := rfl

/-- The defining equation on `tensor` — parallel composition sums the children's counts.  Holds
DEFINITIONALLY. -/
theorem boxCount_tensor (left right : TracedDiagram) :
    boxCount (TracedDiagram.tensor left right) = boxCount left + boxCount right := rfl

/-- The defining equation on `traceN` — the trace is TRANSPARENT to the generator count (ignores the fed-back
wire-count `traceCount`).  Holds DEFINITIONALLY. -/
theorem boxCount_traceN (traceCount : Nat) (inner : TracedDiagram) :
    boxCount (TracedDiagram.traceN traceCount inner) = boxCount inner := rfl

/-- Smoke: the yanking law's left diagram `Tr^W(σ)` has generator count 0 — the SAME as `id_W` (both structure). -/
theorem boxCount_yankingLeft : boxCount tracedYankingLeft = 0 := rfl

/-- Smoke: the vanishing-I law's left diagram `Tr^I(box)` has generator count 1 — the SAME as `box` (the trace is
transparent). -/
theorem boxCount_vanishingBoxLeft : boxCount tracedVanishingBoxLeft = 1 := rfl

/-- Smoke: the left-tightening law's left diagram `Tr^W((box ⊗ id_W) ∘ box)` has generator count 2 — the bystander
`box` (count 1) plus the inner `box` (count 1); `id_W` and the trace contribute 0. -/
theorem boxCount_tighteningLeft : boxCount tracedTighteningLeft = 2 := rfl

/-- Smoke: the left-tightening law's right diagram `box ∘ Tr^W(box)` also has generator count 2 — the bystander
`box` plus the traced `box`, the SAME total as the left diagram (left tightening preserves the count, the axiom
merely slides the bystander out of the trace). -/
theorem boxCount_tighteningRight : boxCount tracedTighteningRight = 2 := rfl

/-! ## SOUNDNESS: convertible diagrams have equal genuine-generator count -/

/-- ★ **Soundness of the boxCount invariant**: trace-convertible diagrams have EQUAL genuine-generator count.  By
induction on the convertibility: vanishing-I is `rfl` (`boxCount (traceN 0 f) = boxCount f` definitionally),
yanking is `rfl` (`0 = 0`), left tightening is `rfl` (both sides reduce to `boxCount bystander + boxCount inner`,
the `boxCount idWire = 0` folding away via `x + 0 ≡ x`), the three congruences rewrite/relay their IHs, and
`refl` / `symm` / `trans` are the equivalence closure.  This is the NO-direction of the (undecided-here) word
problem: distinct `boxCount` ⟹ not convertible.  Mirrors `arityOf_congr_of_conv` /
`braidThreePermutationOf_congr_of_conv`. -/
theorem boxCount_congr_of_conv
    {diagram1 diagram2 : TracedDiagram} (conv : TracedDiagramConv diagram1 diagram2) :
    boxCount diagram1 = boxCount diagram2 := by
  induction conv with
  | vanishingUnit _ => rfl
  | yanking => rfl
  | leftTightening _ _ => rfl
  | seqCongr _ _ ihLeft ihRight =>
      rw [boxCount_seq, boxCount_seq, ihLeft, ihRight]
  | tensorCongr _ _ ihLeft ihRight =>
      rw [boxCount_tensor, boxCount_tensor, ihLeft, ihRight]
  | traceCongr _ _ ih => exact ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Non-vacuity — the invariant genuinely discriminates -/

/-- Positive witness: `Tr^W(σ) ≈ id_W` (the yanking move is a convertible pair). -/
theorem tracedConv_yanking_idWire :
    TracedDiagramConv tracedYankingLeft TracedDiagram.idWire :=
  tracedYankingHolds

/-- Positive witness: soundness applied to the vanishing-I law — `boxCount (Tr^I(box)) = boxCount box` — via
`boxCount_congr_of_conv tracedVanishingUnitHolds` (the invariant IS preserved by a genuine axiom firing, not
merely by `rfl` on an atom). -/
theorem boxCount_vanishingBoxLeft_eq_box_via_soundness :
    boxCount tracedVanishingBoxLeft = boxCount TracedDiagram.box :=
  boxCount_congr_of_conv tracedVanishingUnitHolds

/-- Positive witness: soundness applied to the left-tightening law — the two sides of
`Tr^W((box ⊗ id_W) ∘ box) ≈ box ∘ Tr^W(box)` have equal generator count via
`boxCount_congr_of_conv tracedLeftTighteningHolds`. -/
theorem boxCount_tightening_eq_via_soundness :
    boxCount tracedTighteningLeft = boxCount tracedTighteningRight :=
  boxCount_congr_of_conv tracedLeftTighteningHolds

/-- Negative witness: `box` (generator count 1) is NOT convertible to `idWire` (generator count 0) — via
soundness, since `1 = 0` is impossible (`Nat.noConfusion`).  The genuine generator is not the identity wire. -/
theorem tracedNotConv_box_idWire :
    ¬ TracedDiagramConv TracedDiagram.box TracedDiagram.idWire := by
  intro conv
  have countsEqual : boxCount TracedDiagram.box = boxCount TracedDiagram.idWire :=
    boxCount_congr_of_conv conv
  have oneEqualsZero : (1 : Nat) = 0 := countsEqual
  exact Nat.noConfusion oneEqualsZero

/-- Negative witness: `box ⊗ box` (generator count 2) is NOT convertible to `box` (generator count 1) — via
soundness, since `2 = 1` is impossible (`Nat.noConfusion`).  A parallel pair of generators is a genuinely
different morphism from a single generator. -/
theorem tracedNotConv_tensorBoxBox_box :
    ¬ TracedDiagramConv (TracedDiagram.tensor TracedDiagram.box TracedDiagram.box) TracedDiagram.box := by
  intro conv
  have countsEqual :
      boxCount (TracedDiagram.tensor TracedDiagram.box TracedDiagram.box) = boxCount TracedDiagram.box :=
    boxCount_congr_of_conv conv
  have twoEqualsOne : (2 : Nat) = 1 := countsEqual
  exact Nat.noConfusion twoEqualsOne (fun oneEqualsZero => Nat.noConfusion oneEqualsZero)

/-! ## The honesty boundary, witnessed: the invariant is NOT complete -/

/-- ★ The **incompleteness witness** pinning the soundness-only boundary: `boxCount swap = 0 =
boxCount (id_W ⊗ id_W)` (both structure, no generators), even though the symmetry `σ` is NOT the identity
`id_{W ⊗ W}` — `swap` is not `TracedDiagramConv`-convertible to `tensor idWire idWire`.  So `boxCount` is a genuine
INVARIANT, not a decision procedure — separating the symmetry from the identity is exactly the Int-construction
normal-form content of the later brick.  Like the braid's `permutationOf(σ1σ1) = permutationOf(nil)` collision:
the collision is PROVED (`rfl`), the non-convertibility is the later-brick content.  This is the braid story
(manifestly incomplete), not the operad story (secretly complete). -/
theorem boxCount_swap_eq_tensorIdWireIdWire :
    boxCount TracedDiagram.swap
      = boxCount (TracedDiagram.tensor TracedDiagram.idWire TracedDiagram.idWire) := rfl

/-! ## Markers -/

/-- **ESTABLISHED.**  The walking traced PROP (single object `W`, one genuine generator `box : W ⟶ W` beside the
identities / symmetry / `seq` / `tensor` / `traceN` structure, relations = the decidable-safe trace-axiom subset
vanishing-I + yanking + left tightening) has its SIGNATURE and a genuine-generator (`boxCount`) invariant with
SOUNDNESS (`boxCount_congr_of_conv`: convertible diagrams have equal `boxCount`), zero-axiom and non-vacuously
(positives `tracedYankingHolds` / `tracedVanishingUnitHolds` / `tracedLeftTighteningHolds`; negatives
`tracedNotConv_box_idWire`, `tracedNotConv_tensorBoxBox_box`).  `= true`. -/
def fxTraced_hasSignatureAndTraceInvariant : Bool := true

/-- Alias of `fxTraced_hasSignatureAndTraceInvariant` naming the soundness content: brick 1 ships the traced-PROP
signature (fixed single-object `W` + the `box` generator + the three trace-axiom conv generators), the
genuine-generator `boxCount` map, and the soundness theorem.  `= true`. -/
def fxTraced_hasSignatureAndBoxCountSoundness : Bool := true

/-- **NOT ESTABLISHED (brick boundary).**  The traced WORD PROBLEM is NOT decided here: `boxCount` is sound but NOT
complete (`boxCount_swap_eq_tensorIdWireIdWire` collides the symmetry with the identity), so it is an invariant
only.  A total decider needs the Int-construction `Int(C)` embedding into a compact-closed category and its
completeness — the later brick.  This rung therefore does NOT enter the `WordProblem*` "decided" enumeration; it
belongs to the Int-construction-walled bucket.  `= false`. -/
def fxTraced_hasWordProblemDecided : Bool := false

end FX1Poly.Polygraph
