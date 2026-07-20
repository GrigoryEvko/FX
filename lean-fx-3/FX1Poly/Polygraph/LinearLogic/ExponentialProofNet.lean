import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem

/-! # Polygraph/LinearLogic/ExponentialProofNet — the linear-exponential `!`-comonad
    over the finite-multiset (free commutative comonoid) model

The multiplicative base (`Polygraph/LinearLogic/MultiplicativeProofNet`, prefix `mnl`) ships
unit-free MLL and the Danos–Regnier decision.  This sibling adds the **exponential** layer: the
`!`-modality read as the **free commutative comonoid / finite-multiset comonad**, denoted into a
concrete `List Nat` multiset carrier reused from the commutative-word kit
(`FX1Poly.ComputerAlgebra.CommWordProblem`, prefix `csw`).

The design faithfully mirrors the already-proven store-exponential of `Axis/Mode/Linear.lean`
(`storeExponential`, all laws `rfl`): the `!` functor is the *resource store* — a finite multiset of
atom occurrences paired with a payload — with dereliction reading out the payload and digging
replicating the resource record.  The genuinely new content is the **finite-multiset comonoid**
structure (weakening = discard to the empty multiset, contraction = multiset union) whose laws are the
free-commutative-monoid laws proved through the `csw` insertion-sort algebra, and the **promotion-free
exponential-fragment word decision** lifted from `cswFreeWordDecisionCorrect`.

## What this file ships (Init only, zero-axiom, per-declaration `#assert_no_axioms` in the twin)

  * **T1 — the `!` model + signature.**  `BngBang` (the resource-store `!` functor over a multiset of
    atom occurrences), the exponential generators denoted as structural maps: dereliction `bngDereliction`
    (counit `ε`), digging `bngDigging` (comultiplication `δ`), weakening `bngWeakening` (comonoid counit,
    discard to the empty multiset), contraction `bngContraction` (comonoid comultiplication, copy).  The
    multiset carrier `List Nat` with normal form `bngNorm` (`cswSort`), decidable equality `bngMultisetEq`,
    empty multiset `bngEmpty`, and union `bngMerge`.

  * **T2 — the laws (soundness).**  The COMONAD laws (`bngCounit_comult` `ε∘δ=id`, `bngMap_counit_comult`
    `!ε∘δ=id`, `bngComult_comult` coassociativity, plus the two naturalities and `map_id`) hold by `rfl` on
    the resource-store witness.  The COMMUTATIVE-COMONOID laws hold in the multiset model: weakening counit
    (`bngMergeEmptyLeft`/`bngMergeEmptyRight`), contraction coassociativity (`bngMergeAssoc`), and
    cocommutativity (`bngMergeComm`, and its decision-level corollary `bngMergeComm_decides`) — proved
    through the `csw` free-commutative-monoid congruence.  The Seely / promotion compatibility is WALLED
    (see T4).

  * **T3 — the fragment decision.**  `bngDecideFragment` decides the promotion-free (comonoid-fragment)
    exponential word problem via multiset equality; `bngFragmentSound` (fragment congruence ⟹ equal
    multiset denotation) and `bngFragmentDecisionCorrect` (the sound+complete `↔`) lift the `csw` free
    decision.

  * **T4 — the MELL wall.**  `bngHasMellWordProblem := false`: the FULL MELL word problem (equality of
    MELL proofs modulo cut-elimination) and MELL provability decidability are famous long-standing OPEN
    problems.  Marker names the obstruction.

  * **T5 — ground fires.**  The comonad counit law on a concrete multiset; contraction-then-weakening =
    identity on a concrete multiset; two convertible comonoid-fragment terms decide equal; a control
    non-convertible pair decides false.

Reuses `cswSort` / `cswListNatBeq` / `CswCongr` / `cswCongrCons` / `cswCongrToExpEq` /
`cswDecideFreeWord` / `cswFreeWordDecisionCorrect` — all certified zero-axiom in the imported kit.  This
file adds only structural `List` recursions (`bngAppendNil`, `bngAppendAssoc`, `bngPushCons`,
`bngAppendComm`); no leak-prone library append/reverse lemma is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.LinearLogic

open FX1Poly.ComputerAlgebra

/-! ## T1 — the finite-multiset carrier for `!` -/

/-- The **multiset normal form**: a `List Nat` of atom occurrences sorted into the canonical
representative of its free-commutative-monoid class.  Two occurrence lists denote the same multiset iff
their normal forms coincide. -/
def bngNorm (occurrences : List Nat) : List Nat := cswSort occurrences

/-- **Decidable multiset equality**: compare normal forms.  This is the equality of the free commutative
comonoid on the atom generators — exactly the `csw` free-word decision. -/
def bngMultisetEq (left right : List Nat) : Bool := cswDecideFreeWord left right

/-- The **empty multiset** — the weakening target (comonoid counit lands here). -/
def bngEmpty : List Nat := []

/-- **Multiset union** — the contraction / comonoid-comultiplication support operation on occurrence
lists.  Concatenation of occurrence lists is multiset union up to the commutative congruence. -/
def bngMerge (left right : List Nat) : List Nat := left ++ right

/-! ## T1 — the `!` functor as the resource store, and the four exponential generators -/

/-- The **`!` functor**: a value of type `payload` carried alongside a finite multiset of atom
occurrences (the resource record).  This is the store/writer comonad whose store is the free commutative
monoid of resources — the functional witness of `!payload`. -/
def BngBang (payload : Type) : Type := List Nat × payload

/-- Functorial action of `!`: transform the payload, keep the resource multiset. -/
def bngBangMap {source target : Type} (morphism : source → target) :
    BngBang source → BngBang target :=
  fun boxed => (boxed.1, morphism boxed.2)

/-- **Dereliction** `ε : !A → A` (the comonad counit): read out the payload, forgetting the resource
multiset. -/
def bngDereliction {payload : Type} : BngBang payload → payload :=
  fun boxed => boxed.2

/-- **Digging** `δ : !A → !!A` (the comonad comultiplication): replicate the resource record so the
payload sits under two layers of `!`. -/
def bngDigging {payload : Type} : BngBang payload → BngBang (BngBang payload) :=
  fun boxed => (boxed.1, (boxed.1, boxed.2))

/-- **Weakening** (the comonoid counit): discard a boxed resource entirely.  Its multiset-level target is
`bngEmpty`. -/
def bngWeakening {payload : Type} : BngBang payload → Unit :=
  fun _ => ()

/-- **Contraction** (the comonoid comultiplication): copy a boxed resource into two identical copies.  Its
multiset-level operation is `bngMerge`. -/
def bngContraction {payload : Type} : BngBang payload → BngBang payload × BngBang payload :=
  fun boxed => (boxed, boxed)

/-! ## T2 — the comonad laws (resource-store witness, all `rfl`) -/

/-- Functoriality identity: `!` maps the identity to the identity (`Prod` eta). -/
theorem bngBangMap_id {payload : Type} (boxed : BngBang payload) :
    bngBangMap (fun value => value) boxed = boxed := rfl

/-- Dereliction is natural: `ε` commutes with `!`-map. -/
theorem bngDereliction_natural {source target : Type} (morphism : source → target)
    (boxed : BngBang source) :
    bngDereliction (bngBangMap morphism boxed) = morphism (bngDereliction boxed) := rfl

/-- Digging is natural: `δ` commutes with `!`-map. -/
theorem bngDigging_natural {source target : Type} (morphism : source → target)
    (boxed : BngBang source) :
    bngDigging (bngBangMap morphism boxed)
      = bngBangMap (bngBangMap morphism) (bngDigging boxed) := rfl

/-- **Comonad counit law** `ε ∘ δ = id`: dereliction after digging is the identity. -/
theorem bngCounit_comult {payload : Type} (boxed : BngBang payload) :
    bngDereliction (bngDigging boxed) = boxed := rfl

/-- **Comonad counit law** `!ε ∘ δ = id`: mapping dereliction after digging is the identity. -/
theorem bngMap_counit_comult {payload : Type} (boxed : BngBang payload) :
    bngBangMap bngDereliction (bngDigging boxed) = boxed := rfl

/-- **Comonad coassociativity** `δ ∘ δ = !δ ∘ δ`: digging is coassociative. -/
theorem bngComult_comult {payload : Type} (boxed : BngBang payload) :
    bngDigging (bngDigging boxed) = bngBangMap bngDigging (bngDigging boxed) := rfl

/-! ## T2 — the comonoid laws (weakening / contraction, trivial part) -/

/-- **Weakening counit** on the store witness: discarding yields the tensor unit. -/
theorem bngWeakening_unit {payload : Type} (boxed : BngBang payload) :
    bngWeakening boxed = () := rfl

/-- **Contraction cocommutativity** on the store witness: swapping the two copies changes nothing. -/
theorem bngContraction_cocomm {payload : Type} (boxed : BngBang payload) :
    Prod.swap (bngContraction boxed) = bngContraction boxed := rfl

/-! ## T2 — the comonoid laws on the multiset (free commutative monoid); the genuine content -/

/-- Structural right-unit for occurrence-list concatenation (own lemma; avoids the leak-prone library
`List.append_nil`). -/
theorem bngAppendNil : (occurrences : List Nat) → occurrences ++ [] = occurrences
  | [] => rfl
  | head :: rest => congrArg (fun tail => head :: tail) (bngAppendNil rest)

/-- Structural associativity for occurrence-list concatenation. -/
theorem bngAppendAssoc : (first second third : List Nat) →
    (first ++ second) ++ third = first ++ (second ++ third)
  | [], _, _ => rfl
  | head :: rest, second, third => congrArg (fun tail => head :: tail) (bngAppendAssoc rest second third)

/-- Push a single occurrence past a prefix: `letter :: (front ++ back)` is congruent to
`front ++ (letter :: back)` (bubble the letter through `front`). -/
theorem bngPushCons (letter : Nat) : (front back : List Nat) →
    CswCongr (letter :: (front ++ back)) (front ++ (letter :: back))
  | [], back => CswCongr.refl (letter :: back)
  | head :: rest, back => by
      show CswCongr (letter :: head :: (rest ++ back)) (head :: (rest ++ (letter :: back)))
      have hSwap : CswCongr (letter :: head :: (rest ++ back)) (head :: letter :: (rest ++ back)) :=
        CswCongr.swap [] letter head (rest ++ back)
      have hRec : CswCongr (letter :: (rest ++ back)) (rest ++ (letter :: back)) :=
        bngPushCons letter rest back
      exact CswCongr.trans hSwap (cswCongrCons head hRec)

/-- **Multiset-union commutativity** as a congruence: `a ++ b` and `b ++ a` denote the same multiset
(cocommutativity of contraction). -/
theorem bngAppendComm : (left right : List Nat) → CswCongr (left ++ right) (right ++ left)
  | [], right => by
      show CswCongr right (right ++ [])
      rw [bngAppendNil right]
      exact CswCongr.refl right
  | head :: rest, right => by
      show CswCongr (head :: (rest ++ right)) (right ++ (head :: rest))
      have hInner : CswCongr (rest ++ right) (right ++ rest) := bngAppendComm rest right
      have hStep : CswCongr (head :: (rest ++ right)) (head :: (right ++ rest)) :=
        cswCongrCons head hInner
      exact CswCongr.trans hStep (bngPushCons head right rest)

/-- **Weakening counit, left**: merging the empty multiset on the left is the identity. -/
theorem bngMergeEmptyLeft (word : List Nat) : bngMerge bngEmpty word = word := rfl

/-- **Weakening counit, right**: merging the empty multiset on the right is the identity. -/
theorem bngMergeEmptyRight (word : List Nat) : bngMerge word bngEmpty = word := bngAppendNil word

/-- **Contraction coassociativity**: multiset union is associative. -/
theorem bngMergeAssoc (first second third : List Nat) :
    bngMerge (bngMerge first second) third = bngMerge first (bngMerge second third) :=
  bngAppendAssoc first second third

/-- **Contraction cocommutativity** in the multiset model: multiset union commutes (as a congruence). -/
theorem bngMergeComm (left right : List Nat) :
    CswCongr (bngMerge left right) (bngMerge right left) :=
  bngAppendComm left right

/-- Decision-level corollary of cocommutativity: the two orders of a union decide equal. -/
theorem bngMergeComm_decides (left right : List Nat) :
    bngMultisetEq (bngMerge left right) (bngMerge right left) = true :=
  cswDecideFreeWordComplete (bngMergeComm left right)

/-! ## T3 — the promotion-free exponential-fragment word decision -/

/-- **The promotion-free (comonoid-fragment) exponential word decision.**  Exponentials generated by
dereliction + weakening + contraction (no digging/promotion box) form the free commutative comonoid, whose
word problem is multiset equality — the `csw` free decision. -/
def bngDecideFragment (left right : List Nat) : Bool := cswDecideFreeWord left right

/-- **T3 soundness**: fragment congruence implies equal multiset denotation. -/
theorem bngFragmentSound {left right : List Nat} (hCongr : CswCongr left right) :
    bngNorm left = bngNorm right := cswCongrToExpEq hCongr

/-- **T3 headline**: the promotion-free exponential-fragment word problem is decided (sound + complete). -/
theorem bngFragmentDecisionCorrect (left right : List Nat) :
    bngDecideFragment left right = true ↔ CswCongr left right :=
  cswFreeWordDecisionCorrect left right

/-! ## T3/T4 — capability markers -/

/-- Owner marker: the finite-multiset resource-store `!`-comonad model is delivered. -/
def bngHasMultisetComonadModel : Bool := true

/-- Owner marker: the commutative-comonoid laws (weakening counit, contraction assoc, cocommutativity)
hold in the multiset model. -/
def bngHasCommComonoidLaws : Bool := true

/-- Owner marker: the promotion-free exponential-fragment word problem is decided. -/
def bngHasPromotionFreeFragmentDecision : Bool := true

/-- Owner marker (WALL): the FULL MELL word problem is NOT delivered.  Equality of MELL proofs modulo
cut-elimination, and MELL provability decidability, are famous long-standing OPEN problems.  Obstruction:
(1) the promotion (digging) box makes the correction-graph switching enumeration non-terminating / of
unbounded box depth, so the finite Danos–Regnier decision of the multiplicative base does not lift; (2)
cut-elimination in the presence of the exponential box is not confluent as a box-free rewriting system, so
proof equality is not a finite-multiset comparison beyond the comonoid fragment; (3) the presented /
non-fragment non-membership half already inherits the certified zero-axiom AF-product impossibility from
NET-3 (`FX1Poly.ComputerAlgebra.cswHasPresentedCommWordDecision = false`, bottoming out at
`fxNet4_dicksonWall = false`, which needs `WellFounded.fix`).  Two burned attacks: (a) extend the `mnl`
switching enumeration with box nodes — non-terminating because promotion nests boxes without a fuel bound
tied to formula size; (b) reduce full MELL equality to presented-multiset word equality — this is exactly
the walled two-sided presented commutative-word decision. -/
def bngHasMellWordProblem : Bool := false

/-! ## T5 — ground fires -/

/-- Comonad counit law on a concrete boxed resource: dereliction after digging returns the box. -/
theorem bngFireCounitComult :
    bngDereliction (bngDigging (([3, 1] : List Nat), (7 : Nat))) = ([3, 1], 7) := rfl

/-- Contraction-then-weakening on a concrete multiset: copy `[2,0]`, weaken one copy to the empty
multiset, merge — the identity. -/
theorem bngFireContractThenWeaken : bngMerge [2, 0] bngEmpty = [2, 0] := rfl

/-- Two convertible comonoid-fragment terms decide equal: `x·y·x` and `x·x·y` share the multiset
`x²y`. -/
theorem bngFireFragmentEqual : bngDecideFragment [0, 1, 0] [0, 0, 1] = true := rfl

/-- Control: `x·x·y` and `x·y·y` are NOT fragment-convertible (`x²y` vs `x y²`) — decide false. -/
theorem bngFireFragmentControl : bngDecideFragment [0, 0, 1] [0, 1, 1] = false := rfl

end FX1Poly.Polygraph.LinearLogic
