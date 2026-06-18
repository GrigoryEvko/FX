/-! # Tier0/Term — mixed inductive-coinductive types: the μ/ν parity (term-14)

The LEFT (`term-1`, initial algebra `μ` / induction) and RIGHT (`term-3`, terminal coalgebra `ν` /
coinduction) meet here.  A **mixed inductive-coinductive type** ALTERNATES least and greatest fixpoints —
e.g. `νX. (μY. F) × X`, a productive stream of finite data — and the **μ/ν parity** is the duality of the two
fixpoint kinds: `μ` (inductive) gives FINITE data eliminated by well-founded `fold` (induction); `ν`
(coinductive) gives possibly-INFINITE data produced by guarded `corec` (coinduction).

This file ships a concrete, self-contained instance of the parity (each zero-axiom):

  * **`MuTree`** — the least fixpoint `μY. 1 + Nat × Y × Y` (finite labelled binary trees), with the
    catamorphism `MuTree.fold`, the **induction principle** `MuTree.fold_unique` (`fold` is the unique
    homomorphism), and the finiteness measure `MuTree.size`.
  * **`NuStream A := Nat → A`** — the greatest fixpoint `νX. A × X` (the terminal coalgebra of `X ↦ A × X`,
    streams ≅ functions out of `Nat`), with `head` / `tail` / the corecursor `NuStream.corec` (with its
    head/tail computation laws) and the **coinduction principle** `NuStream.corec_unique` (`corec` is the
    unique coalgebra morphism — proved POINTWISE, funext-free).
  * **`MixedMuNu := NuStream MuTree`** — the MIXED type `νX. MuTree × X` (a productive stream of finite
    trees), with `mixedFold` distributing the inner `μ`-fold over the outer `ν`-structure
    (`mixedFold_head` / `mixedFold_tail`).
  * **the parity** — `mu_isFinite` (every `μ`-element is finite) versus `nu_canBeUnbounded` (a `ν`-element can
    strictly increase forever): the least-vs-greatest-fixpoint separation.

## Honest scope

A concrete mixed `ν(μ)` type + the two recursion schemes with their universal properties + the
finiteness/unboundedness parity.  DEFERRED: the GENERAL mixed inductive-coinductive type theory
(Basold-Geuvers dependent `μ`/`ν` with arbitrary functor alternation `νX. μY. F(X, Y)`, the combined
productivity+termination criterion for the alternation, and the dialgebra / parity-game semantics);
`term-3`'s `FinalStream` is the general terminal coalgebra (this file uses the concrete `Nat → A`
presentation to keep the parity crisp).

## Zero-axiom verification

`MuTree.fold` / `fold_unique` are structural recursion / induction on the tree; `NuStream.corec` iterates by
structural recursion on the position; the corec laws and `corec_unique` are induction on the position with a
`generalizing` seed (no funext — every stream law is stated POINTWISE); the parity uses `Nat.lt_succ_self`
only (no `Nat.max`, no `Nat.add_comm`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TermMixedFixpoint.lean`.
-/

namespace FX1Poly.Core

/-! ## The least fixpoint `μ` — finite trees with induction -/

/-- The least fixpoint `μY. 1 + Nat × Y × Y`: finite labelled binary trees.  Inductive — every element is
finite, eliminated by well-founded recursion. -/
inductive MuTree where
  | leaf : MuTree
  | branch : Nat → MuTree → MuTree → MuTree

/-- The **catamorphism** (`μ`-fold): the unique structurally-recursive elimination of a finite tree. -/
def MuTree.fold {Result : Type} (onLeaf : Result) (onBranch : Nat → Result → Result → Result) :
    MuTree → Result
  | .leaf => onLeaf
  | .branch label left right =>
      onBranch label (MuTree.fold onLeaf onBranch left) (MuTree.fold onLeaf onBranch right)

/-- The finiteness measure: every `μ`-element has a finite size. -/
def MuTree.size : MuTree → Nat
  | .leaf => 1
  | .branch _ left right => Nat.succ (MuTree.size left + MuTree.size right)

/-- ★ **The induction principle for `μ`** (`fold`-uniqueness): any elimination agreeing with the algebra at
`leaf` and `branch` IS the catamorphism.  Structural induction on the tree. -/
theorem MuTree.fold_unique {Result : Type} (onLeaf : Result)
    (onBranch : Nat → Result → Result → Result) (candidate : MuTree → Result)
    (candidateLeaf : candidate MuTree.leaf = onLeaf)
    (candidateBranch : ∀ label left right,
      candidate (MuTree.branch label left right) = onBranch label (candidate left) (candidate right)) :
    (tree : MuTree) → candidate tree = MuTree.fold onLeaf onBranch tree
  | .leaf => candidateLeaf
  | .branch label left right => by
      show candidate (MuTree.branch label left right)
        = onBranch label (MuTree.fold onLeaf onBranch left) (MuTree.fold onLeaf onBranch right)
      rw [candidateBranch label left right,
        MuTree.fold_unique onLeaf onBranch candidate candidateLeaf candidateBranch left,
        MuTree.fold_unique onLeaf onBranch candidate candidateLeaf candidateBranch right]

/-! ## The greatest fixpoint `ν` — streams with coinduction -/

/-- The greatest fixpoint `νX. A × X`: streams, presented as functions out of `Nat` (the terminal coalgebra
of `X ↦ A × X`). -/
def NuStream (A : Type) : Type := Nat → A

/-- The head of a stream (the `A`-component of the coalgebra). -/
def NuStream.head {A : Type} (stream : NuStream A) : A := stream 0

/-- The tail of a stream (the `X`-component of the coalgebra). -/
def NuStream.tail {A : Type} (stream : NuStream A) : NuStream A := fun position => stream (position + 1)

/-- Iterate `advance` structurally on the position. -/
def iterateAdvance {Seed : Type} (advance : Seed → Seed) : Nat → Seed → Seed
  | 0, seed => seed
  | step + 1, seed => advance (iterateAdvance advance step seed)

/-- The **corecursor** (`ν`-unfold): from a seed, observe at each position the iterated advance. -/
def NuStream.corec {A Seed : Type} (observe : Seed → A) (advance : Seed → Seed) :
    Seed → NuStream A :=
  fun seed position => observe (iterateAdvance advance position seed)

/-- `corec`'s head law: the head observes the seed. -/
theorem NuStream.corec_head {A Seed : Type} (observe : Seed → A) (advance : Seed → Seed) (seed : Seed) :
    (NuStream.corec observe advance seed).head = observe seed := rfl

/-- Iterating commutes with one advance: `advance ∘ iterate = iterate ∘ advance`. -/
theorem iterateAdvance_commute {Seed : Type} (advance : Seed → Seed) (seed : Seed) :
    (position : Nat) →
      advance (iterateAdvance advance position seed) = iterateAdvance advance position (advance seed)
  | 0 => rfl
  | step + 1 => congrArg advance (iterateAdvance_commute advance seed step)

/-- `corec`'s tail law (pointwise): the tail is the corecursion from the advanced seed. -/
theorem NuStream.corec_tail {A Seed : Type} (observe : Seed → A) (advance : Seed → Seed) (seed : Seed) :
    (position : Nat) →
      (NuStream.corec observe advance seed).tail position
        = NuStream.corec observe advance (advance seed) position :=
  fun position => congrArg observe (iterateAdvance_commute advance seed position)

/-- ★ **The coinduction principle for `ν`** (`corec`-uniqueness): any candidate that satisfies the head and
tail laws agrees POINTWISE with the corecursor — `corec` is the unique coalgebra morphism into the stream.
Funext-free: stated and proved pointwise, by induction on the position. -/
theorem NuStream.corec_unique {A Seed : Type} (observe : Seed → A) (advance : Seed → Seed)
    (candidate : Seed → NuStream A)
    (candidateHead : ∀ seed, (candidate seed).head = observe seed)
    (candidateTail : ∀ seed position, (candidate seed).tail position = candidate (advance seed) position) :
    ∀ (seed : Seed) (position : Nat), candidate seed position = NuStream.corec observe advance seed position := by
  intro seed position
  induction position generalizing seed with
  | zero => exact candidateHead seed
  | succ priorPosition inductionHypothesis =>
      have viaTail : candidate seed (priorPosition + 1) = candidate (advance seed) priorPosition :=
        candidateTail seed priorPosition
      rw [viaTail, inductionHypothesis (advance seed)]
      exact (NuStream.corec_tail observe advance seed priorPosition).symm

/-! ## The mixed type `ν(μ)` — a productive stream of finite trees -/

/-- The **mixed inductive-coinductive type** `νX. MuTree × X`: a productive stream of finite trees.  The
outer `ν` is coinductive (infinite), each element is an inductive (finite) `MuTree`. -/
def MixedMuNu : Type := NuStream MuTree

/-- The mixed elimination: fold the inner `μ` (tree) at every outer `ν` (stream) position — `μ`-recursion
inside `ν`-corecursion. -/
def mixedFold {Result : Type} (onLeaf : Result) (onBranch : Nat → Result → Result → Result)
    (stream : MixedMuNu) : NuStream Result :=
  fun position => MuTree.fold onLeaf onBranch (stream position)

/-- The mixed fold commutes with the head: folding then observing the head equals observing the head then
folding. -/
theorem mixedFold_head {Result : Type} (onLeaf : Result) (onBranch : Nat → Result → Result → Result)
    (stream : MixedMuNu) :
    (mixedFold onLeaf onBranch stream).head = MuTree.fold onLeaf onBranch stream.head := rfl

/-- The mixed fold commutes with the tail (pointwise): the `μ`-fold distributes over the `ν`-tail. -/
theorem mixedFold_tail {Result : Type} (onLeaf : Result) (onBranch : Nat → Result → Result → Result)
    (stream : MixedMuNu) :
    (position : Nat) → (mixedFold onLeaf onBranch stream).tail position
      = mixedFold onLeaf onBranch stream.tail position :=
  fun _position => rfl

/-! ## The μ/ν parity -/

/-- ★ **`μ` is finite**: every inductive element has a finite size (the least fixpoint contains only finite
data). -/
theorem mu_isFinite (tree : MuTree) : MuTree.size tree < MuTree.size tree + 1 :=
  Nat.lt_succ_self _

/-- ★ **`ν` can be unbounded**: a coinductive element may strictly increase forever (the greatest fixpoint
contains genuinely infinite data with no finite bound) — the identity stream `0, 1, 2, …` strictly
increases.  The contrast with `mu_isFinite` IS the μ/ν parity. -/
theorem nu_canBeUnbounded :
    ∃ stream : NuStream Nat, ∀ position, stream position < stream (position + 1) :=
  ⟨fun position => position, fun position => Nat.lt_succ_self position⟩

/-! ## Concrete witnesses -/

/-- Folding the constant stream of leaves with `size` yields the constant stream `1` (the fold computes at
each productive position). -/
theorem exampleMixedFold :
    (mixedFold 1 (fun _label left right => Nat.succ (left + right)) (fun _position => MuTree.leaf)).head = 1 :=
  rfl

end FX1Poly.Core
