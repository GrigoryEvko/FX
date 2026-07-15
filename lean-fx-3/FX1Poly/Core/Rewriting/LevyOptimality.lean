/-! # Axis/Term — Lévy optimality: redex families + the no-duplication bound (term-9)

Lévy's theory of OPTIMAL REDUCTION groups redexes into FAMILIES — a redex and all its copies (residuals
created by duplicating a common ancestor) share a Lévy LABEL, and are the "same redex" to be contracted
together.  An OPTIMAL reduction contracts a whole family in one shared step, so no family is ever contracted
twice: it never duplicates work.  Sharing-graph implementations (Lamping; Gonthier-Abadi-Lévy) realize this
concretely on a DAG where shared subterms appear once.

This file ships the genuine, abstract CORE: redex families as Lévy-label classes, and the QUANTITATIVE
optimality bound — the shared reduction (one step per family) never exceeds, and STRICTLY beats, the naive
reduction (one step per redex) exactly when some family has multiple members (genuine sharing).

## What this file ships (each zero-axiom)

  * **`CoFamilial`** — the family relation: two redexes are co-familial iff they carry the same Lévy label.
    An EQUIVALENCE (`CoFamilial.refl` / `.symm` / `.trans`) — families partition the redexes.
  * **`familyTotalRedexes`** — the NAIVE redex count: the sum of the family sizes (every redex contracted
    separately, duplicating shared work).
  * **`optimalReduction_le_unshared`** — the OPTIMALITY bound: the shared reduction length (one step per
    family = the number of families = `List.length`) never exceeds the naive count.
  * **`optimalReduction_lt_unshared_of_sharing`** — ★ when some family has ≥ 2 members (genuine sharing),
    the shared reduction is STRICTLY shorter: optimal reduction provably saves work.
  * concrete witnesses (`familyTotalRedexes [2, 3] = 5` vs length `2` — sharing saves 3 steps).

## Honest scope

The family framework + the quantitative no-duplication bound.  DEFERRED (the capstone): Lévy's full
OPTIMALITY THEOREM (a family-complete derivation is optimal among ALL strategies to normal form), the
labeled λ-calculus residual / zig-zag family theory over actual terms, and the Lamping / Gonthier-Abadi-Lévy
SHARING GRAPHS (interaction nets, fans/brackets, read-back) — together with the Asperti-Mairson caveat that
the sharing-graph bookkeeping itself need not be cost-elementary.

## Zero-axiom verification

`CoFamilial` is `Eq`-on-label (equivalence by `Eq`); the bounds are structural list recursion with the
standard `Nat` order lemmas (`Nat.add_le_add`, `Nat.add_lt_add_*`, `Nat.lt_of_le_of_lt`), no `Nat.add_comm`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated
in `FX1PolyAudit/Core/Rewriting/LevyOptimality.lean`.
-/

namespace FX1Poly.Core

/-- Two redexes are **co-familial** when they carry the same Lévy label — i.e. one is a copy/residual of the
other, so they form one redex family.  The family relation is `Eq` on the label, hence an equivalence. -/
def CoFamilial {Redex : Type} (familyLabel : Redex → Nat) (left right : Redex) : Prop :=
  familyLabel left = familyLabel right

/-- Family membership is reflexive. -/
theorem CoFamilial.refl {Redex : Type} (familyLabel : Redex → Nat) (redex : Redex) :
    CoFamilial familyLabel redex redex := rfl

/-- Family membership is symmetric. -/
theorem CoFamilial.symm {Redex : Type} {familyLabel : Redex → Nat} {left right : Redex}
    (related : CoFamilial familyLabel left right) : CoFamilial familyLabel right left :=
  Eq.symm related

/-- Family membership is transitive. -/
theorem CoFamilial.trans {Redex : Type} {familyLabel : Redex → Nat} {left middle right : Redex}
    (firstRelated : CoFamilial familyLabel left middle)
    (secondRelated : CoFamilial familyLabel middle right) : CoFamilial familyLabel left right :=
  Eq.trans firstRelated secondRelated

/-- The **naive (unshared) redex count**: given the size of each family (how many copies it has), the total
number of redexes a non-sharing reduction contracts — every copy separately.  (The shared/optimal reduction
contracts one step per family, i.e. `familySizes.length`.) -/
def familyTotalRedexes : List Nat → Nat
  | [] => 0
  | headSize :: restSizes => familyTotalRedexes restSizes + headSize

/-- ★ **The optimality bound.**  The shared reduction (one step per family, `familySizes.length`) never
exceeds the naive reduction (one step per redex, `familyTotalRedexes`) — given every family is non-empty.
Optimal sharing never costs more than naive reduction. -/
theorem optimalReduction_le_unshared :
    (familySizes : List Nat) → (∀ size ∈ familySizes, 1 ≤ size) →
      familySizes.length ≤ familyTotalRedexes familySizes
  | [], _ => Nat.le_refl 0
  | headSize :: restSizes, allPositive =>
      Nat.add_le_add
        (optimalReduction_le_unshared restSizes
          (fun size memberOfRest => allPositive size (List.Mem.tail headSize memberOfRest)))
        (allPositive headSize (List.Mem.head restSizes))

/-- ★ **Optimal reduction strictly saves work under genuine sharing.**  If some family has ≥ 2 members (a
redex really was duplicated), the shared reduction is STRICTLY shorter than the naive one — the precise
sense in which Lévy-optimal reduction never re-contracts a shared family. -/
theorem optimalReduction_lt_unshared_of_sharing :
    (familySizes : List Nat) → (∀ size ∈ familySizes, 1 ≤ size) →
      (∃ size ∈ familySizes, 2 ≤ size) →
      familySizes.length < familyTotalRedexes familySizes
  | [], _, hasSharing => by obtain ⟨_, memberOfEmpty, _⟩ := hasSharing; nomatch memberOfEmpty
  | headSize :: restSizes, allPositive, hasSharing => by
      have restPositive : ∀ size ∈ restSizes, 1 ≤ size :=
        fun size memberOfRest => allPositive size (List.Mem.tail headSize memberOfRest)
      have headPositive : 1 ≤ headSize := allPositive headSize (List.Mem.head restSizes)
      obtain ⟨witnessSize, witnessMember, witnessLarge⟩ := hasSharing
      cases witnessMember with
      | head =>
          show restSizes.length + 1 < familyTotalRedexes restSizes + headSize
          exact Nat.lt_of_le_of_lt
            (Nat.succ_le_succ (optimalReduction_le_unshared restSizes restPositive))
            (Nat.add_lt_add_left witnessLarge (familyTotalRedexes restSizes))
      | tail _ witnessInRest =>
          show restSizes.length + 1 < familyTotalRedexes restSizes + headSize
          exact Nat.lt_of_lt_of_le
            (Nat.add_lt_add_right
              (optimalReduction_lt_unshared_of_sharing restSizes restPositive
                ⟨witnessSize, witnessInRest, witnessLarge⟩) 1)
            (Nat.add_le_add_left headPositive (familyTotalRedexes restSizes))

/-! ## Concrete witnesses — sharing genuinely saves steps -/

/-- A two-family example with sizes 2 and 3: the naive reduction contracts `5` redexes. -/
theorem familyTotalRedexes_example : familyTotalRedexes [2, 3] = 5 := rfl

/-- The shared reduction contracts only `2` steps (one per family). -/
theorem optimalReductionLength_example : [2, 3].length = 2 := rfl

/-- ★ The optimality theorem fires on the concrete example: `2 < 5` — sharing saves three steps. -/
theorem levyOptimality_savesWork_witness : [2, 3].length < familyTotalRedexes [2, 3] :=
  optimalReduction_lt_unshared_of_sharing [2, 3]
    (fun size memberOf => by
      cases memberOf with
      | head => exact Nat.le_add_left 1 1
      | tail _ restMember =>
          cases restMember with
          | head => exact Nat.le_add_left 1 2
          | tail _ emptyMember => nomatch emptyMember)
    ⟨2, List.Mem.head _, Nat.le_refl 2⟩

end FX1Poly.Core
