import FX1Poly.Polygraph.TwoCategory.WalkingTraced.TracedDiagramBoxCount

/-! # WalkingTraced/TracedDiagramDecision — the smart-constructor normal form: the 3-axiom traced fragment word problem, DECIDED

Brick 2 of WP-TRACED.  Brick 1 (`TracedDiagramSeed` / `TracedDiagramBoxCount`) ships the SIGNATURE, the
genuine-generator map `boxCount : TracedDiagram → Nat`, SOUNDNESS (`boxCount_congr_of_conv`), and a WITNESSED
incompleteness (`boxCount_swap_eq_tensorIdWireIdWire`: the symmetry collides with `id_W ⊗ id_W` on `boxCount`).
Here the missing COMPLETE invariant and hence the TOTAL word-problem DECISION for the shipped 3-axiom fragment
land, mirroring `OperadTreeDecision` exactly.

## ★ Why this fragment is decidable WITHOUT the Int-construction — the stale-prose correction

Brick 1's marker prose claims "a total decider needs the Int-construction `Int(C)` embedding".  That claim is
TRUE for the FULL Joyal–Street–Verity axiom set (sliding / dinaturality is size-PRESERVING and non-orthogonal —
that is the rule that genuinely forces `Int(C)`), but STALE for `TracedDiagramConv` AS SHIPPED: oriented
left-to-right, the three rules

  * vanishing-I    `traceN 0 f            ↝ f`                       (node count −1)
  * yanking        `traceN 1 swap         ↝ idWire`                  (node count −1)
  * left tightening `traceN 1 ((g ⊗ id) ∘ f) ↝ g ∘ traceN 1 f`       (node count −2)

form an ORTHOGONAL, strictly size-reducing rewriting system: left-linear (each of `bystander` / `innerDiagram`
occurs once per LHS), ZERO critical pairs (all three LHS roots are `traceN`-headed and pairwise non-unifiable —
payload `0` vs `1` separates vanishing-I from the other two, inner head `swap` vs `seq` separates yanking from
tightening — and no LHS has a `traceN`-headed PROPER subterm, so no nested overlap).  No abstract confluence
theorem is imported: the decision is self-contained via reconstruction + soundness, the operad brick-2 shape.
The seed's `fxTraced_hasWordProblemDecided := false` flag stays byte-intact (frozen-owner convention); the wall
MOVES to the honest boundary — see `fxTraced_hasFullJsvTraceAxiomsDecided` below.

## ★ The naive-fold trap and the smart-constructor repair

A one-shot bottom-up fold that fires each rule once at each node is INCOMPLETE: left tightening's RHS
`seq g (traceN 1 f)` RE-EMBEDS a `traceN 1 f` node that can itself be a yanking or tightening redex.  Concrete
counterexample: `traceN 1 (seq (tensor box idWire) swap)` — the children are already normal, the root tightening
fires, and the naive result `seq box (traceN 1 swap)` still contains the yanking redex (it is conv-equal to
`seq box idWire`).  The repair is the smart constructor `contractTraceOne`, taking an ALREADY-NORMAL argument
and computing the normal form of its 1-trace: `swap ↦ idWire` (yanking); the tightening shape recurses on the
seq-RIGHT child (a proper subterm, so plain structural recursion — NO `WellFounded.fix`); every other shape is a
verified irredex and keeps its `traceN 1`.  The normalizer `tracedNF` is then a single bottom-up structural
fold whose `traceN` arm dispatches the normalized child through the payload helper `dispatchTrace`
(`0 ↦` child, `1 ↦ contractTraceOne`, `k+2 ↦ traceN (k+2)` — no rule has payload ≥ 2).

## The two directions

  * **SOUNDNESS (NO-direction)** `tracedNF_congr_of_conv`: induction on the convertibility; all THREE axiom
    arms close by `rfl` — the smart-constructor factoring makes each axiom arm DEFINITIONAL (the tightening
    arm's match scrutinizes only literal constructors even with opaque normalized children inside, so iota
    fires).  `tracedNF` is thereby the COMPLETE invariant brick 1 lacked: preserved by all three axioms + the
    full congruence, and separating `swap` from `tensor idWire idWire` where `boxCount` could not.
  * **COMPLETENESS (YES-direction)** `conv_toTracedNF`: every diagram is convertible to its normal form, built
    from `conv_toContractTraceOne` (`traceN 1 f ≈ contractTraceOne f`, structural induction on `f`: the swap
    arm is yanking, the tightening arm chains `leftTightening` with the IH under `seqCongr`, every other arm is
    `refl`) and the payload split `conv_toDispatchTrace` (`0` = vanishing-I, `1` = the contract lemma, `k+2` =
    `refl`).

## Payoff corollaries

  * The seed's honesty witness UPGRADED from prose to theorem: `tracedNotConv_swap_tensorIdWireIdWire` — the
    symmetry is genuinely not the identity in this fragment.
  * The seed's soundness-trap note machine-confirmed: `tracedNotConv_loopScalar_idWire` /
    `tracedNotConv_boxScalar_box` — the loop scalar `Tr^W(id_W)` and the fully-traced generator `Tr^W(box)` are
    genuinely NEW morphisms (both are `tracedNF`-fixed).
  * Trace-free collapse FOR FREE: every trace-free diagram is `tracedNF`-fixed (all three LHS are
    `traceN`-headed), so convertibility between trace-free endpoints collapses to syntactic equality
    (`tracedConv_collapses_on_traceFree`) — the trace-free-subfragment decision is a corollary, not a route.

Raw Lean 4 + Init; all recursions STRUCTURAL (never `WellFounded.fix`), all matches full-enumeration (no
wildcard rows), the decider compares normal forms via a hand-rolled `DecidableEq` (Squiggle recipe — the carrier
is un-indexed, so no indexed-`DecidableEq` propext leak).  Per-declaration `#assert_no_axioms` gated in the
audit twin, with an independent `#print axioms` cross-check.  Free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`, `simp`, `decide`-the-tactic. -/

namespace FX1Poly.Polygraph

/-! ## The smart constructor: the normal form of a 1-trace over a normal argument -/

/-- ★ The **1-trace smart constructor**: given an ALREADY-NORMAL diagram, compute the normal form of its
1-wire trace `Tr^W(·)`.  `swap ↦ idWire` fires yanking; the tightening shape
`seq (tensor bystander idWire) rest ↦ seq bystander (contractTraceOne rest)` fires left tightening and RECURSES
on the re-embedded 1-trace (the seq-RIGHT child — a proper subterm, so plain STRUCTURAL recursion, no
`WellFounded.fix`); every other shape is a verified irredex (payload 1 ≠ 0, head not `swap`, not the tightening
shape) and keeps its `traceN 1`.  Full-enumeration — 19 arms, no wildcard row (the seq arm sub-enumerates its
left child's 7 shapes; the tensor-left sub-arm sub-enumerates its right child's 7 shapes) — so the compiled
match is propext-clean and every arm reduces DEFINITIONALLY on constructor-headed input. -/
def contractTraceOne : TracedDiagram → TracedDiagram
  | .empty => .traceN 1 .empty
  | .idWire => .traceN 1 .idWire
  | .box => .traceN 1 .box
  | .swap => .idWire
  | .seq .empty second => .traceN 1 (.seq .empty second)
  | .seq .idWire second => .traceN 1 (.seq .idWire second)
  | .seq .box second => .traceN 1 (.seq .box second)
  | .seq .swap second => .traceN 1 (.seq .swap second)
  | .seq (.seq nestedFirst nestedSecond) second =>
      .traceN 1 (.seq (.seq nestedFirst nestedSecond) second)
  | .seq (.tensor bystander .empty) second =>
      .traceN 1 (.seq (.tensor bystander .empty) second)
  | .seq (.tensor bystander .idWire) second =>
      .seq bystander (contractTraceOne second)
  | .seq (.tensor bystander .box) second =>
      .traceN 1 (.seq (.tensor bystander .box) second)
  | .seq (.tensor bystander .swap) second =>
      .traceN 1 (.seq (.tensor bystander .swap) second)
  | .seq (.tensor bystander (.seq nestedFirst nestedSecond)) second =>
      .traceN 1 (.seq (.tensor bystander (.seq nestedFirst nestedSecond)) second)
  | .seq (.tensor bystander (.tensor nestedFirst nestedSecond)) second =>
      .traceN 1 (.seq (.tensor bystander (.tensor nestedFirst nestedSecond)) second)
  | .seq (.tensor bystander (.traceN nestedCount nestedInner)) second =>
      .traceN 1 (.seq (.tensor bystander (.traceN nestedCount nestedInner)) second)
  | .seq (.traceN nestedCount nestedInner) second =>
      .traceN 1 (.seq (.traceN nestedCount nestedInner) second)
  | .tensor first second => .traceN 1 (.tensor first second)
  | .traceN traceCount inner => .traceN 1 (.traceN traceCount inner)

/-- The yanking arm — the 1-trace of the symmetry contracts to the identity wire.  Holds DEFINITIONALLY. -/
theorem contractTraceOne_swap : contractTraceOne TracedDiagram.swap = TracedDiagram.idWire := rfl

/-- ★ The tightening arm with OPAQUE children — the load-bearing definitional equation: the match scrutinizes
only literal constructors (`seq`, `tensor`, `idWire`), so iota fires even with variables at the leaves.  This
is exactly why the smart-constructor factoring makes the soundness axiom arms close by `rfl`. -/
theorem contractTraceOne_tightening (bystander second : TracedDiagram) :
    contractTraceOne (TracedDiagram.seq (TracedDiagram.tensor bystander TracedDiagram.idWire) second)
      = TracedDiagram.seq bystander (contractTraceOne second) := rfl

/-- Irredex smoke: the 1-trace of the generator stays — `Tr^W(box)` is a genuinely new scalar (see the
seed's soundness-trap note: `traceN 1 (tensor f idWire) ≈ f` would be UNSOUND, and its degenerate instance
`traceN 1 box ≈ box`-style collapses are equally absent). -/
theorem contractTraceOne_box : contractTraceOne TracedDiagram.box = TracedDiagram.traceN 1 TracedDiagram.box := rfl

/-- Irredex smoke: a 1-trace over a parallel composite stays (only the SEQ-with-bystander shape tightens). -/
theorem contractTraceOne_tensor (first second : TracedDiagram) :
    contractTraceOne (TracedDiagram.tensor first second)
      = TracedDiagram.traceN 1 (TracedDiagram.tensor first second) := rfl

/-- Irredex smoke: a seq whose LEFT child is not a tensor does not tighten. -/
theorem contractTraceOne_seqSwapLeft (second : TracedDiagram) :
    contractTraceOne (TracedDiagram.seq TracedDiagram.swap second)
      = TracedDiagram.traceN 1 (TracedDiagram.seq TracedDiagram.swap second) := rfl

/-- Irredex smoke: a seq whose left tensor does NOT carry a literal `idWire` on the traced wire does not
tighten (the axiom demands the traced wire enter as a LITERAL identity). -/
theorem contractTraceOne_seqTensorBoxRight (bystander second : TracedDiagram) :
    contractTraceOne (TracedDiagram.seq (TracedDiagram.tensor bystander TracedDiagram.box) second)
      = TracedDiagram.traceN 1 (TracedDiagram.seq (TracedDiagram.tensor bystander TracedDiagram.box) second) := rfl

/-- Irredex smoke: a 1-trace over a nested trace stays (no rule has a `traceN`-headed LHS argument). -/
theorem contractTraceOne_traceN (traceCount : Nat) (inner : TracedDiagram) :
    contractTraceOne (TracedDiagram.traceN traceCount inner)
      = TracedDiagram.traceN 1 (TracedDiagram.traceN traceCount inner) := rfl

/-! ## The payload dispatch: which trace rule a wire-count can fire -/

/-- ★ The **trace payload dispatch**: route an already-normal diagram under a `traceN traceCount` to its
normal form by the fed-back wire-count — `0 ↦` the diagram itself (vanishing-I), `1 ↦ contractTraceOne`
(yanking / tightening / verified irredex), `traceCount + 2 ↦` keep the trace (NO shipped rule has payload
≥ 2).  Full `Nat` enumeration `0 / 1 / succ (succ _)`, no wildcard row, non-recursive — hoisted to a
top-level helper so the soundness `traceCongr` arm is a single `congrArg`, never a `Nat` case split. -/
def dispatchTrace : Nat → TracedDiagram → TracedDiagram
  | 0, normalInner => normalInner
  | 1, normalInner => contractTraceOne normalInner
  | traceCount + 2, normalInner => .traceN (traceCount + 2) normalInner

/-- The payload-0 arm — vanishing-I erases the trace.  Holds DEFINITIONALLY. -/
theorem dispatchTrace_zero (normalInner : TracedDiagram) :
    dispatchTrace 0 normalInner = normalInner := rfl

/-- The payload-1 arm — route through the smart constructor.  Holds DEFINITIONALLY. -/
theorem dispatchTrace_one (normalInner : TracedDiagram) :
    dispatchTrace 1 normalInner = contractTraceOne normalInner := rfl

/-- The payload-(k+2) arm — traces of two or more wires are untouched by the shipped fragment.  Holds
DEFINITIONALLY. -/
theorem dispatchTrace_twoPlus (traceCount : Nat) (normalInner : TracedDiagram) :
    dispatchTrace (traceCount + 2) normalInner
      = TracedDiagram.traceN (traceCount + 2) normalInner := rfl

/-! ## The normalizer: one bottom-up structural fold -/

/-- ★ The **traced-fragment normalizer**: a single bottom-up STRUCTURAL fold — atoms are fixed, `seq` /
`tensor` map over their children, and `traceN traceCount inner` dispatches the normalized child through
`dispatchTrace`.  No `WellFounded.fix` anywhere (the smart constructor's recursion is structural on the
seq-right child; this fold is structural on the diagram).  `tracedNF` is the COMPLETE invariant of the shipped
3-axiom fragment: preserved by all three trace axioms + the full congruence (`tracedNF_congr_of_conv`) and
reconstructible (`conv_toTracedNF`), so equal normal forms characterize convertibility exactly. -/
def tracedNF : TracedDiagram → TracedDiagram
  | .empty => .empty
  | .idWire => .idWire
  | .box => .box
  | .swap => .swap
  | .seq first second => .seq (tracedNF first) (tracedNF second)
  | .tensor first second => .tensor (tracedNF first) (tracedNF second)
  | .traceN traceCount inner => dispatchTrace traceCount (tracedNF inner)

/-- The defining equation on `empty`. -/
theorem tracedNF_empty : tracedNF TracedDiagram.empty = TracedDiagram.empty := rfl

/-- The defining equation on `idWire`. -/
theorem tracedNF_idWire : tracedNF TracedDiagram.idWire = TracedDiagram.idWire := rfl

/-- The defining equation on `box`. -/
theorem tracedNF_box : tracedNF TracedDiagram.box = TracedDiagram.box := rfl

/-- The defining equation on `swap` — the symmetry is its own normal form (yanking fires only UNDER a
1-trace). -/
theorem tracedNF_swap : tracedNF TracedDiagram.swap = TracedDiagram.swap := rfl

/-- The defining equation on `seq` — normalize both children.  Holds DEFINITIONALLY. -/
theorem tracedNF_seq (first second : TracedDiagram) :
    tracedNF (TracedDiagram.seq first second)
      = TracedDiagram.seq (tracedNF first) (tracedNF second) := rfl

/-- The defining equation on `tensor` — normalize both children.  Holds DEFINITIONALLY. -/
theorem tracedNF_tensor (first second : TracedDiagram) :
    tracedNF (TracedDiagram.tensor first second)
      = TracedDiagram.tensor (tracedNF first) (tracedNF second) := rfl

/-- The defining equation on `traceN` — normalize the child, then dispatch on the payload.  Holds
DEFINITIONALLY. -/
theorem tracedNF_traceN (traceCount : Nat) (inner : TracedDiagram) :
    tracedNF (TracedDiagram.traceN traceCount inner)
      = dispatchTrace traceCount (tracedNF inner) := rfl

/-! ## COMPLETENESS (YES-direction) — the reconstruction -/

/-- ★ **The contract lemma**: a 1-trace is convertible to its smart-constructor contraction —
`traceN 1 f ≈ contractTraceOne f` for EVERY `f` (normality of `f` is not needed for this direction).
Structural induction on `f`, mirroring the smart constructor's 19 arms move-for-move: the swap arm is
yanking; the tightening arm chains `leftTightening` with the IH on the re-embedded 1-trace under
`seqCongr` (the exact spot where the naive one-shot fold loses completeness); every other arm is a
verified irredex, closed by `refl` (the smart constructor keeps the `traceN 1` definitionally). -/
theorem conv_toContractTraceOne : (diagram : TracedDiagram) →
    TracedDiagramConv (TracedDiagram.traceN 1 diagram) (contractTraceOne diagram)
  | .empty => .refl (.traceN 1 .empty)
  | .idWire => .refl (.traceN 1 .idWire)
  | .box => .refl (.traceN 1 .box)
  | .swap => .yanking
  | .seq .empty second => .refl (.traceN 1 (.seq .empty second))
  | .seq .idWire second => .refl (.traceN 1 (.seq .idWire second))
  | .seq .box second => .refl (.traceN 1 (.seq .box second))
  | .seq .swap second => .refl (.traceN 1 (.seq .swap second))
  | .seq (.seq nestedFirst nestedSecond) second =>
      .refl (.traceN 1 (.seq (.seq nestedFirst nestedSecond) second))
  | .seq (.tensor bystander .empty) second =>
      .refl (.traceN 1 (.seq (.tensor bystander .empty) second))
  | .seq (.tensor bystander .idWire) second =>
      .trans (.leftTightening bystander second)
        (.seqCongr (.refl bystander) (conv_toContractTraceOne second))
  | .seq (.tensor bystander .box) second =>
      .refl (.traceN 1 (.seq (.tensor bystander .box) second))
  | .seq (.tensor bystander .swap) second =>
      .refl (.traceN 1 (.seq (.tensor bystander .swap) second))
  | .seq (.tensor bystander (.seq nestedFirst nestedSecond)) second =>
      .refl (.traceN 1 (.seq (.tensor bystander (.seq nestedFirst nestedSecond)) second))
  | .seq (.tensor bystander (.tensor nestedFirst nestedSecond)) second =>
      .refl (.traceN 1 (.seq (.tensor bystander (.tensor nestedFirst nestedSecond)) second))
  | .seq (.tensor bystander (.traceN nestedCount nestedInner)) second =>
      .refl (.traceN 1 (.seq (.tensor bystander (.traceN nestedCount nestedInner)) second))
  | .seq (.traceN nestedCount nestedInner) second =>
      .refl (.traceN 1 (.seq (.traceN nestedCount nestedInner) second))
  | .tensor first second => .refl (.traceN 1 (.tensor first second))
  | .traceN traceCount inner => .refl (.traceN 1 (.traceN traceCount inner))

/-- **The payload split**: a trace is convertible to its payload dispatch — `traceN k x ≈ dispatchTrace k x`.
Full `Nat` enumeration: `0` fires vanishing-I, `1` is the contract lemma, `k+2` is `refl` (the dispatch keeps
the trace definitionally). -/
theorem conv_toDispatchTrace : (traceCount : Nat) → (normalInner : TracedDiagram) →
    TracedDiagramConv (TracedDiagram.traceN traceCount normalInner) (dispatchTrace traceCount normalInner)
  | 0, normalInner => .vanishingUnit normalInner
  | 1, normalInner => conv_toContractTraceOne normalInner
  | traceCount + 2, normalInner => .refl (.traceN (traceCount + 2) normalInner)

/-- ★ **The reconstruction**: every diagram is convertible to its normal form — `d ≈ tracedNF d`.  A direct
STRUCTURAL induction on the un-indexed carrier (no index refinement, no length generalization): atoms by
`refl`; `seq` / `tensor` rewrite both children by their IHs under the congruences; `traceN` rewrites the child
under `traceCongr`, then splits on the payload via `conv_toDispatchTrace`. -/
theorem conv_toTracedNF : (diagram : TracedDiagram) → TracedDiagramConv diagram (tracedNF diagram)
  | .empty => .refl .empty
  | .idWire => .refl .idWire
  | .box => .refl .box
  | .swap => .refl .swap
  | .seq first second => .seqCongr (conv_toTracedNF first) (conv_toTracedNF second)
  | .tensor first second => .tensorCongr (conv_toTracedNF first) (conv_toTracedNF second)
  | .traceN traceCount inner =>
      .trans (.traceCongr traceCount (conv_toTracedNF inner))
        (conv_toDispatchTrace traceCount (tracedNF inner))

/-! ## SOUNDNESS (NO-direction) — the normal form is preserved by the whole congruence -/

/-- ★ **Soundness of the normal form**: trace-convertible diagrams have EQUAL normal form.  Induction on the
convertibility; the smart-constructor factoring makes all THREE axiom arms DEFINITIONAL:

  * vanishing-I — `tracedNF (traceN 0 f) ≡ dispatchTrace 0 (tracedNF f) ≡ tracedNF f`, `rfl`;
  * yanking — `tracedNF (traceN 1 swap) ≡ contractTraceOne swap ≡ idWire ≡ tracedNF idWire`, `rfl`;
  * left tightening — BOTH sides reduce to
    `seq (tracedNF bystander) (contractTraceOne (tracedNF inner))` (the tightening match scrutinizes only
    literal constructors, so iota fires past the opaque normalized children), `rfl`;

the three congruences rewrite by their IHs (the `traceCongr` arm is a pure rewrite through the hoisted
`dispatchTrace` — no `Nat` case split), and `refl` / `symm` / `trans` are the equivalence closure.  This is
the COMPLETE-invariant preservation check the task demanded, discharged for every axiom and every congruence
generator: `tracedNF` separates `swap` from `tensor idWire idWire` where `boxCount` could not. -/
theorem tracedNF_congr_of_conv
    {diagram1 diagram2 : TracedDiagram} (conv : TracedDiagramConv diagram1 diagram2) :
    tracedNF diagram1 = tracedNF diagram2 := by
  induction conv with
  | vanishingUnit _ => rfl
  | yanking => rfl
  | leftTightening _ _ => rfl
  | seqCongr _ _ ihLeft ihRight =>
      rw [tracedNF_seq, tracedNF_seq, ihLeft, ihRight]
  | tensorCongr _ _ ihLeft ihRight =>
      rw [tracedNF_tensor, tracedNF_tensor, ihLeft, ihRight]
  | traceCongr traceCount _ ih =>
      rw [tracedNF_traceN, tracedNF_traceN, ih]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## COMPLETENESS in normal-form shape + the characterization -/

/-- ★ **Completeness via the common normal form**: diagrams with EQUAL normal form are convertible.  Route
both through the shared normal form: `d1 ≈ tracedNF d1 = tracedNF d2 ≈ d2` (the middle `=` is the
hypothesis; the outer legs are the reconstruction, the right one reversed). -/
theorem conv_of_tracedNF_eq
    {diagram1 diagram2 : TracedDiagram} (normalFormsEqual : tracedNF diagram1 = tracedNF diagram2) :
    TracedDiagramConv diagram1 diagram2 := by
  have reductionOne : TracedDiagramConv diagram1 (tracedNF diagram2) := by
    rw [← normalFormsEqual]
    exact conv_toTracedNF diagram1
  exact TracedDiagramConv.trans reductionOne (TracedDiagramConv.symm (conv_toTracedNF diagram2))

/-- ★ **The word problem as a normal-form equality**: two diagrams are convertible iff they share a normal
form — `tracedNF_congr_of_conv` (⟹) paired with `conv_of_tracedNF_eq` (⟸).  The complete characterization of
the shipped 3-axiom traced fragment's word problem. -/
theorem tracedConv_iff_nf_eq (diagram1 diagram2 : TracedDiagram) :
    TracedDiagramConv diagram1 diagram2 ↔ tracedNF diagram1 = tracedNF diagram2 :=
  ⟨tracedNF_congr_of_conv, conv_of_tracedNF_eq⟩

/-! ## Hand-rolled decidable equality on the carrier

The Squiggle recipe: the carrier is UN-INDEXED, so structural `DecidableEq` is propext-clean — cascade
`Nat.decEq` on the trace payload, recursion on children, `noConfusion` on every mismatch.  Full 7 × 7
enumeration (49 arms), NO `deriving`, no wildcard rows. -/

/-- ★ Decidable equality on `TracedDiagram`, hand-rolled: 49 full-enumeration arms — 42 cross-constructor
`isFalse (noConfusion)` one-liners, 4 atomic diagonal `isTrue rfl`, and 3 recursive diagonal arms (`seq` /
`tensor` cascade on both children; `traceN` cascades `Nat.decEq` on the payload then recurses on the child),
rebuilding equality proofs by `congr`/`congrArg` and refuting by `noConfusion` field projection.  Plain
structural recursion on the first argument. -/
def tracedDiagramDecEq : (diagram1 diagram2 : TracedDiagram) → Decidable (diagram1 = diagram2)
  | .empty, .empty => isTrue rfl
  | .empty, .idWire => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .empty, .box => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .empty, .swap => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .empty, .seq _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .empty, .tensor _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .empty, .traceN _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .idWire, .empty => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .idWire, .idWire => isTrue rfl
  | .idWire, .box => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .idWire, .swap => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .idWire, .seq _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .idWire, .tensor _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .idWire, .traceN _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .box, .empty => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .box, .idWire => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .box, .box => isTrue rfl
  | .box, .swap => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .box, .seq _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .box, .tensor _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .box, .traceN _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .swap, .empty => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .swap, .idWire => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .swap, .box => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .swap, .swap => isTrue rfl
  | .swap, .seq _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .swap, .tensor _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .swap, .traceN _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .seq _ _, .empty => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .seq _ _, .idWire => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .seq _ _, .box => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .seq _ _, .swap => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .seq firstLeft firstRight, .seq secondLeft secondRight =>
      match tracedDiagramDecEq firstLeft secondLeft with
      | isFalse leftsDiffer =>
          isFalse (fun equal =>
            TracedDiagram.noConfusion equal (fun leftsEqual _ => leftsDiffer leftsEqual))
      | isTrue leftsEqual =>
          match tracedDiagramDecEq firstRight secondRight with
          | isFalse rightsDiffer =>
              isFalse (fun equal =>
                TracedDiagram.noConfusion equal (fun _ rightsEqual => rightsDiffer rightsEqual))
          | isTrue rightsEqual =>
              isTrue (congr (congrArg TracedDiagram.seq leftsEqual) rightsEqual)
  | .seq _ _, .tensor _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .seq _ _, .traceN _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .tensor _ _, .empty => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .tensor _ _, .idWire => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .tensor _ _, .box => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .tensor _ _, .swap => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .tensor _ _, .seq _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .tensor firstLeft firstRight, .tensor secondLeft secondRight =>
      match tracedDiagramDecEq firstLeft secondLeft with
      | isFalse leftsDiffer =>
          isFalse (fun equal =>
            TracedDiagram.noConfusion equal (fun leftsEqual _ => leftsDiffer leftsEqual))
      | isTrue leftsEqual =>
          match tracedDiagramDecEq firstRight secondRight with
          | isFalse rightsDiffer =>
              isFalse (fun equal =>
                TracedDiagram.noConfusion equal (fun _ rightsEqual => rightsDiffer rightsEqual))
          | isTrue rightsEqual =>
              isTrue (congr (congrArg TracedDiagram.tensor leftsEqual) rightsEqual)
  | .tensor _ _, .traceN _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN _ _, .empty => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN _ _, .idWire => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN _ _, .box => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN _ _, .swap => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN _ _, .seq _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN _ _, .tensor _ _ => isFalse (fun equal => TracedDiagram.noConfusion equal)
  | .traceN firstCount firstInner, .traceN secondCount secondInner =>
      match Nat.decEq firstCount secondCount with
      | isFalse countsDiffer =>
          isFalse (fun equal =>
            TracedDiagram.noConfusion equal (fun countsEqual _ => countsDiffer countsEqual))
      | isTrue countsEqual =>
          match tracedDiagramDecEq firstInner secondInner with
          | isFalse innersDiffer =>
              isFalse (fun equal =>
                TracedDiagram.noConfusion equal (fun _ innersEqual => innersDiffer innersEqual))
          | isTrue innersEqual =>
              isTrue (congr (congrArg TracedDiagram.traceN countsEqual) innersEqual)

/-- `TracedDiagram` equality as a `DecidableEq` instance (the decision procedure on normal forms feeds on
it). -/
instance instDecidableEqTracedDiagram : DecidableEq TracedDiagram := tracedDiagramDecEq

/-! ## The TOTAL decision -/

/-- ★ **Decide traced-fragment convertibility** — TOTAL.  Compare the two diagrams' normal forms with the
hand-rolled `tracedDiagramDecEq`: equal normal forms ⟹ `isTrue` (completeness `conv_of_tracedNF_eq`);
distinct normal forms ⟹ `isFalse` (soundness `tracedNF_congr_of_conv` would force them equal).  Both branches
discharged — the shipped 3-axiom traced fragment's word problem is genuinely decided, no Int-construction
needed. -/
def decideTracedDiagramConv (diagram1 diagram2 : TracedDiagram) :
    Decidable (TracedDiagramConv diagram1 diagram2) :=
  match tracedDiagramDecEq (tracedNF diagram1) (tracedNF diagram2) with
  | isTrue normalFormsEqual => isTrue (conv_of_tracedNF_eq normalFormsEqual)
  | isFalse normalFormsDiffer =>
      isFalse (fun conv => normalFormsDiffer (tracedNF_congr_of_conv conv))

/-- The traced-fragment convertibility as a `Decidable` instance (so `decide` fires on it). -/
instance instDecidableTracedDiagramConv (diagram1 diagram2 : TracedDiagram) :
    Decidable (TracedDiagramConv diagram1 diagram2) :=
  decideTracedDiagramConv diagram1 diagram2

/-! ## Concrete sample diagrams for the pins -/

/-- The completeness-crux pair, LEFT: `Tr^W((box ⊗ id_W) ∘ σ)` — the exact shape the naive one-shot fold
mishandles (tightening fires at the root, RE-EMBEDDING the yanking redex `Tr^W(σ)`). -/
def tracedTwoAxiomChainLeft : TracedDiagram :=
  TracedDiagram.traceN 1
    (TracedDiagram.seq (TracedDiagram.tensor TracedDiagram.box TracedDiagram.idWire) TracedDiagram.swap)

/-- The completeness-crux pair, RIGHT: `box ∘ id_W` — reached only by the TWO-axiom chain (tightening, then
yanking under `seqCongr`). -/
def tracedTwoAxiomChainRight : TracedDiagram :=
  TracedDiagram.seq TracedDiagram.box TracedDiagram.idWire

/-- The **loop scalar** `Tr^W(id_W)` — the dimension of `W`, a genuinely new `0 → 0` morphism of the traced
PROP (NOT the identity wire, NOT the empty diagram); its non-collapse is the seed's soundness-trap note, here
machine-confirmed. -/
def tracedLoopScalar : TracedDiagram := TracedDiagram.traceN 1 TracedDiagram.idWire

/-- The **box scalar** `Tr^W(box)` — the trace of the generator, a genuinely new `0 → 0` morphism (the
categorical trace of `box`), distinct from `box` itself. -/
def tracedBoxScalar : TracedDiagram := TracedDiagram.traceN 1 TracedDiagram.box

/-- The double-tightening tower, LEFT: `Tr^W((box ⊗ id_W) ∘ ((box ⊗ id_W) ∘ σ))` — TWO nested tightening
firings then a yanking, exercising the smart constructor's structural recursion depth. -/
def tracedDoubleTighteningLeft : TracedDiagram :=
  TracedDiagram.traceN 1
    (TracedDiagram.seq (TracedDiagram.tensor TracedDiagram.box TracedDiagram.idWire)
      (TracedDiagram.seq (TracedDiagram.tensor TracedDiagram.box TracedDiagram.idWire)
        TracedDiagram.swap))

/-- The double-tightening tower, RIGHT: `box ∘ (box ∘ id_W)` — both bystanders pulled out, the yanking
absorbed. -/
def tracedDoubleTighteningRight : TracedDiagram :=
  TracedDiagram.seq TracedDiagram.box (TracedDiagram.seq TracedDiagram.box TracedDiagram.idWire)

/-! ## Non-vacuity — positive witnesses (completeness genuinely fires) -/

/-- ★ Positive witness (completeness-only): the two-axiom chain
`Tr^W((box ⊗ id_W) ∘ σ) ≈ box ∘ id_W` — the exact pair the naive one-shot fold assigns DIFFERENT "normal
forms"; convertible only through the smart constructor's re-contraction.  Via `conv_of_tracedNF_eq rfl` (both
normal forms compute to `seq box idWire`). -/
theorem tracedConv_twoAxiomChain :
    TracedDiagramConv tracedTwoAxiomChainLeft tracedTwoAxiomChainRight :=
  conv_of_tracedNF_eq rfl

/-- ★ Non-vacuity by the DECIDER (positive, yanking): `decide` on `Tr^W(σ) ≈ id_W` returns `true`. -/
theorem tracedDecide_true_on_yanking :
    decide (TracedDiagramConv tracedYankingLeft TracedDiagram.idWire) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, vanishing-I): `decide` on `Tr^I(box) ≈ box` returns `true`. -/
theorem tracedDecide_true_on_vanishingUnit :
    decide (TracedDiagramConv tracedVanishingBoxLeft TracedDiagram.box) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, tightening): `decide` on
`Tr^W((box ⊗ id_W) ∘ box) ≈ box ∘ Tr^W(box)` returns `true`. -/
theorem tracedDecide_true_on_tightening :
    decide (TracedDiagramConv tracedTighteningLeft tracedTighteningRight) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, the completeness-only two-axiom chain): `decide` on
`Tr^W((box ⊗ id_W) ∘ σ) ≈ box ∘ id_W` returns `true` — witnessing the re-contraction genuinely, not a `rfl`
coincidence on already-normal endpoints. -/
theorem tracedDecide_true_on_twoAxiomChain :
    decide (TracedDiagramConv tracedTwoAxiomChainLeft tracedTwoAxiomChainRight) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, nested vanishing-then-yanking): `decide` on
`Tr^W(Tr^I(σ)) ≈ id_W` returns `true` — the inner vanishing-I must fire before the outer yanking can see the
symmetry. -/
theorem tracedDecide_true_on_nestedVanishingYanking :
    decide (TracedDiagramConv
      (TracedDiagram.traceN 1 (TracedDiagram.traceN 0 TracedDiagram.swap))
      TracedDiagram.idWire) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, double tightening): `decide` on the two-level tightening tower
`Tr^W((box ⊗ id_W) ∘ ((box ⊗ id_W) ∘ σ)) ≈ box ∘ (box ∘ id_W)` returns `true` — exercising the smart
constructor's recursion two levels deep. -/
theorem tracedDecide_true_on_doubleTightening :
    decide (TracedDiagramConv tracedDoubleTighteningLeft tracedDoubleTighteningRight) = true := rfl

/-! ## The seed's honesty witness DISCHARGED + the soundness-trap notes machine-confirmed -/

/-- ★ **The seed's incompleteness witness UPGRADED from prose to theorem**: the symmetry `σ` is NOT
convertible to `id_W ⊗ id_W`.  Brick 1 proved the `boxCount` COLLISION (`boxCount_swap_eq_tensorIdWireIdWire`)
and left the separation as prose; here the complete invariant separates them — both are their own normal
forms, distinct constructors (`swap` vs `tensor`), so soundness + `noConfusion` refute.  What brick 1 deferred
to "the Int-construction brick" for THIS fragment needed only the smart-constructor fold. -/
theorem tracedNotConv_swap_tensorIdWireIdWire :
    ¬ TracedDiagramConv TracedDiagram.swap
        (TracedDiagram.tensor TracedDiagram.idWire TracedDiagram.idWire) :=
  fun conv => TracedDiagram.noConfusion (tracedNF_congr_of_conv conv)

/-- ★ The seed's soundness-trap note machine-confirmed, half 1: the loop scalar `Tr^W(id_W)` is NOT the
identity wire — it is a genuinely new morphism of the traced PROP (the dimension of `W`).  Both sides are
`tracedNF`-fixed (`traceN 1 idWire` is a verified irredex), distinct constructors refute. -/
theorem tracedNotConv_loopScalar_idWire :
    ¬ TracedDiagramConv tracedLoopScalar TracedDiagram.idWire :=
  fun conv => TracedDiagram.noConfusion (tracedNF_congr_of_conv conv)

/-- ★ The seed's soundness-trap note machine-confirmed, half 2: the box scalar `Tr^W(box)` is NOT the
generator `box` — tracing the generator's only wire produces a new `0 → 0` scalar, not the generator back.
(The tempting rule that would collapse these is exactly the seed's flagged-UNSOUND `traceN 1 (tensor f idWire)
≈ f` in spirit; the fragment correctly keeps them apart.) -/
theorem tracedNotConv_boxScalar_box :
    ¬ TracedDiagramConv tracedBoxScalar TracedDiagram.box :=
  fun conv => TracedDiagram.noConfusion (tracedNF_congr_of_conv conv)

/-- ★ Non-vacuity by the DECIDER (negative, the headline separation): `decide` on
`σ ≟ id_W ⊗ id_W` returns `false` — the pair `boxCount` could not separate. -/
theorem tracedDecide_false_on_swap_tensorIdWires :
    decide (TracedDiagramConv TracedDiagram.swap
      (TracedDiagram.tensor TracedDiagram.idWire TracedDiagram.idWire)) = false := rfl

/-- ★ Non-vacuity by the DECIDER (negative, loop scalar): `decide` on `Tr^W(id_W) ≟ id_W` returns
`false`. -/
theorem tracedDecide_false_on_loopScalar_idWire :
    decide (TracedDiagramConv tracedLoopScalar TracedDiagram.idWire) = false := rfl

/-- ★ Non-vacuity by the DECIDER (negative, box scalar): `decide` on `Tr^W(box) ≟ box` returns `false`. -/
theorem tracedDecide_false_on_boxScalar_box :
    decide (TracedDiagramConv tracedBoxScalar TracedDiagram.box) = false := rfl

/-! ## The trace-free collapse — the subfragment decision as a COROLLARY -/

/-- Does a diagram contain NO trace node?  A `Bool` structural fold: atoms are trace-free, `seq` / `tensor`
conjoin their children, any `traceN` is not.  Full enumeration, DATA-valued, propext-clean. -/
def isTraceFree : TracedDiagram → Bool
  | .empty => true
  | .idWire => true
  | .box => true
  | .swap => true
  | .seq first second => isTraceFree first && isTraceFree second
  | .tensor first second => isTraceFree first && isTraceFree second
  | .traceN _ _ => false

/-- The defining equation on `seq`. -/
theorem isTraceFree_seq (first second : TracedDiagram) :
    isTraceFree (TracedDiagram.seq first second) = (isTraceFree first && isTraceFree second) := rfl

/-- The defining equation on `tensor`. -/
theorem isTraceFree_tensor (first second : TracedDiagram) :
    isTraceFree (TracedDiagram.tensor first second) = (isTraceFree first && isTraceFree second) := rfl

/-- ★ **Trace-free diagrams are already normal**: every rewrite rule's LHS is `traceN`-headed, so a diagram
with no trace node is `tracedNF`-fixed.  Structural induction; the `seq` / `tensor` arms split the boolean
conjunction by cases on each child's `isTraceFree` value (no `simp`, no iff lemmas — `Bool.noConfusion` kills
the false branches definitionally). -/
theorem tracedNF_fixed_of_traceFree : (diagram : TracedDiagram) →
    isTraceFree diagram = true → tracedNF diagram = diagram
  | .empty, _ => rfl
  | .idWire, _ => rfl
  | .box, _ => rfl
  | .swap, _ => rfl
  | .seq first second, freeEvidence => by
      cases firstFreeEq : isTraceFree first with
      | false =>
          rw [isTraceFree_seq, firstFreeEq] at freeEvidence
          exact Bool.noConfusion freeEvidence
      | true =>
          cases secondFreeEq : isTraceFree second with
          | false =>
              rw [isTraceFree_seq, firstFreeEq, secondFreeEq] at freeEvidence
              exact Bool.noConfusion freeEvidence
          | true =>
              rw [tracedNF_seq, tracedNF_fixed_of_traceFree first firstFreeEq,
                tracedNF_fixed_of_traceFree second secondFreeEq]
  | .tensor first second, freeEvidence => by
      cases firstFreeEq : isTraceFree first with
      | false =>
          rw [isTraceFree_tensor, firstFreeEq] at freeEvidence
          exact Bool.noConfusion freeEvidence
      | true =>
          cases secondFreeEq : isTraceFree second with
          | false =>
              rw [isTraceFree_tensor, firstFreeEq, secondFreeEq] at freeEvidence
              exact Bool.noConfusion freeEvidence
          | true =>
              rw [tracedNF_tensor, tracedNF_fixed_of_traceFree first firstFreeEq,
                tracedNF_fixed_of_traceFree second secondFreeEq]
  | .traceN _ _, freeEvidence => Bool.noConfusion freeEvidence

/-- ★ **The trace-free collapse**: convertibility between trace-free endpoints IS syntactic equality — the
subfragment decision the scoping fallback route would have shipped standalone, here a two-line corollary of
the full decision (soundness + fixedness).  Note the derivation between them may still wander through traced
diagrams (`symm` of vanishing-I introduces `traceN 0` freely mid-derivation) — the collapse is about the
ENDPOINTS, which is exactly why the standalone route would have needed the whole-carrier invariant anyway. -/
theorem tracedConv_collapses_on_traceFree
    {diagram1 diagram2 : TracedDiagram}
    (free1 : isTraceFree diagram1 = true) (free2 : isTraceFree diagram2 = true)
    (conv : TracedDiagramConv diagram1 diagram2) : diagram1 = diagram2 := by
  have normalFormsEqual : tracedNF diagram1 = tracedNF diagram2 := tracedNF_congr_of_conv conv
  rw [tracedNF_fixed_of_traceFree diagram1 free1,
    tracedNF_fixed_of_traceFree diagram2 free2] at normalFormsEqual
  exact normalFormsEqual

/-! ## Honesty markers — the decision recorded, the wall MOVED (not erased) -/

/-- **ESTABLISHED.**  The walking traced PROP's 3-axiom fragment word problem (`TracedDiagramConv` AS SHIPPED:
vanishing-I + yanking + left tightening + full diagram congruence) is DECIDED via the smart-constructor normal
form, zero-axiom and non-vacuously.  The normalizer `tracedNF` (bottom-up fold; `traceN` payload dispatched
through `dispatchTrace` / `contractTraceOne`, all recursion STRUCTURAL) is SOUND (`tracedNF_congr_of_conv` —
all three axiom arms definitional) and COMPLETE (`conv_of_tracedNF_eq` via the reconstruction
`conv_toTracedNF` / `conv_toContractTraceOne`), giving the characterization `tracedConv_iff_nf_eq` and the
total decider `decideTracedDiagramConv` over the hand-rolled `tracedDiagramDecEq`.  Non-vacuity: positives
`tracedDecide_true_on_yanking` / `_vanishingUnit` / `_tightening` / the completeness-only
`_twoAxiomChain` (the exact pair a naive one-shot fold mishandles) / `_nestedVanishingYanking` /
`_doubleTightening`; negatives `tracedDecide_false_on_swap_tensorIdWires` (the seed's honesty witness
UPGRADED to theorem `tracedNotConv_swap_tensorIdWireIdWire`), `_loopScalar_idWire`, `_boxScalar_box`;
plus the trace-free collapse `tracedConv_collapses_on_traceFree`.  This SUPERSEDES the seed's
`fxTraced_hasWordProblemDecided := false` marker prose ("a total decider needs the Int-construction") FOR THE
SHIPPED FRAGMENT: oriented, the three rules form an orthogonal strictly size-reducing system with zero
critical pairs, so the decision is a self-contained fold — the Int-construction claim was stale for this
relation (three-strata-drift pattern).  The seed's flag stays byte-intact false per the frozen-owner
convention; THIS marker is the superseding content marker.  `= true`. -/
def fxTraced_hasFragmentDecision : Bool := true

/-- **NOT ESTABLISHED (the wall, MOVED to the honest boundary).**  The FULL Joyal–Street–Verity traced word
problem is NOT decided here: the deferred rows — vanishing-⊗, RIGHT tightening, SLIDING / dinaturality,
superposing — are not in the shipped relation.  Sliding is the genuine wall: it is size-PRESERVING and
non-orthogonal (its two sides overlap the other rules' `traceN`-headed LHSs), which breaks the
strictly-size-reducing orthogonal-system argument this brick rides — THAT is the rule whose decision
genuinely motivates the Int-construction `Int(C)` compact-closed embedding and its completeness (a later
brick, if taken).  Adding any of the four rows invalidates `tracedNF` as shipped; this marker names the
boundary so the decision above is never over-read.  `= false`. -/
def fxTraced_hasFullJsvTraceAxiomsDecided : Bool := false

end FX1Poly.Polygraph
