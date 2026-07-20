/-! # Equipment/ProarrowWordProblem — the free proarrow equipment word problem: companion/conjoint of vertical words, the horizontal-monoid normal form, the 1-cell word decision, and the mates transpose involution

A **proarrow equipment** (framed bicategory) has a category of *vertical* arrows, a bicategory of
*proarrows* (horizontal 1-cells), and — the framing datum — for every vertical arrow `f` a **companion**
`f_*` and a **conjoint** `f^*` proarrow.  Companion assignment is a covariant functor
`(g ∘ f)_* ≈ f_* ⊗ g_*`; conjoint assignment is CONTRAVARIANT `(g ∘ f)^* ≈ g^* ⊗ f^*`.  Kelly–Street
*mates* transpose a 2-cell across a companion/conjoint pair, swapping the two framings.

This file presents the **free** equipment on a set of vertical generators and horizontal-proarrow
generators, and DECIDES its 1-cell (proarrow-word) problem zero-axiom:

* a vertical arrow is a `List Nat` (a word of vertical generators, free-category composite = append);
* a proarrow atom is a 3-way tag `ProAtom` — a horizontal generator, a companion of a vertical generator,
  or a conjoint of a vertical generator, each carrying a `Nat` id;
* a proarrow word is a `List ProAtom`; horizontal composite = own cons-only append; identity = `[]`;
* `eqpCompanionOfVertical` is the ORDER-PRESERVING map (covariant functoriality);
* `eqpConjointOfVertical` is the ORDER-REVERSING map (own cons-only reverse — the contravariance);
* `eqpProAtomListBeq` structurally decides proarrow-word equality (soundness `…Eq`);
* `ProExprConv` is the horizontal-monoid congruence on proarrow expressions, DECIDED both ways against the
  flattened normal form (`eqpProarrowConvSound` / `eqpProarrowConvComplete`, plus the refutation half);
* `eqpMatesTranspose` swaps `companion ↔ conjoint` (order-reversed over the word) with
  `eqpMatesTransposeInvol` — the mates involution on representatives.

## ★ Why a NEW subtree — equipment ≠ double category

The adjacent free-double-category work (`Polygraph/TwoCategory/WalkingDouble/`) fixes a single square
signature with no vertical/horizontal-arrow *framing*: no companions, no conjoints, no fibrancy.  Equipment
sits one level richer.  The vertical-word + proarrow-atom-list kit is cloned from the `csw` structural
`List Nat` equality (`ComputerAlgebra/Semigroup/CommWordProblem.lean`) and the cons-only reverse shape of
`reverseOperationWord` (`ComputerAlgebra/LinearAlgebra/SmithNormalForm.lean`); `List.reverse` / `List.append`
stdlib lemmas leak `propext`, so every list operation here is hand-rolled cons-only.

## ★ The walls (see the two `Bool := false` markers at the foot)

The 1-cell (proarrow-word) layer is a FREE monoid and is decided completely.  The 2-cell layer — squares
between proarrows with the double-category interchange law, and the mates as a genuine *bijection on 2-cells*
rather than an involution on representatives — inherits WP-DOUBLE's un-decided grid coherence and the Poly
double-category interchange wall.  Companion/conjoint *existence* for a NON-FREE base is the framing/fibrancy
condition, non-structural in general.  Both are walled honestly. -/

namespace FX1Poly.Polygraph

/-! ## The clean `Nat.beq` / `Bool.and` micro-kit (own, cons-only, propext-free) -/

/-- `Nat.beq` is reflexive. -/
theorem eqpNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => eqpNatBeqRefl predecessor

/-- `Nat.beq` sound: beq-true naturals are propositionally equal. -/
theorem eqpNatBeqEq : (left right : Nat) → Nat.beq left right = true → left = right
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, 0, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      congrArg Nat.succ (eqpNatBeqEq leftPredecessor rightPredecessor hBeq)

/-- Split a true Boolean conjunction into its two true conjuncts (full enumeration, no wildcard). -/
theorem eqpBoolAndElim : (left right : Bool) → (left && right) = true → left = true ∧ right = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hAnd => Bool.noConfusion hAnd
  | false, true, hAnd => Bool.noConfusion hAnd
  | false, false, hAnd => Bool.noConfusion hAnd

/-! ## The proarrow atom and the cons-only word operations -/

/-- A proarrow atom: a horizontal generator, a companion of a vertical generator, or a conjoint of a
vertical generator — the 3-way tag, each carrying a `Nat` id. -/
inductive ProAtom where
  | hgen (identifier : Nat)
  | companion (verticalGeneratorId : Nat)
  | conjoint (verticalGeneratorId : Nat)

/-- Structural Boolean equality on proarrow atoms (full 3×3 enumeration, no wildcard). -/
def eqpProAtomBeq : ProAtom → ProAtom → Bool
  | ProAtom.hgen leftId, ProAtom.hgen rightId => Nat.beq leftId rightId
  | ProAtom.hgen _, ProAtom.companion _ => false
  | ProAtom.hgen _, ProAtom.conjoint _ => false
  | ProAtom.companion _, ProAtom.hgen _ => false
  | ProAtom.companion leftId, ProAtom.companion rightId => Nat.beq leftId rightId
  | ProAtom.companion _, ProAtom.conjoint _ => false
  | ProAtom.conjoint _, ProAtom.hgen _ => false
  | ProAtom.conjoint _, ProAtom.companion _ => false
  | ProAtom.conjoint leftId, ProAtom.conjoint rightId => Nat.beq leftId rightId

/-- `eqpProAtomBeq` is reflexive. -/
theorem eqpProAtomBeqRefl : (atom : ProAtom) → eqpProAtomBeq atom atom = true
  | ProAtom.hgen identifier => eqpNatBeqRefl identifier
  | ProAtom.companion verticalGeneratorId => eqpNatBeqRefl verticalGeneratorId
  | ProAtom.conjoint verticalGeneratorId => eqpNatBeqRefl verticalGeneratorId

/-- `eqpProAtomBeq` sound: beq-true atoms are propositionally equal (full enumeration). -/
theorem eqpProAtomBeqEq : (left right : ProAtom) → eqpProAtomBeq left right = true → left = right
  | ProAtom.hgen leftId, ProAtom.hgen rightId, hBeq =>
      congrArg ProAtom.hgen (eqpNatBeqEq leftId rightId hBeq)
  | ProAtom.hgen _, ProAtom.companion _, hBeq => Bool.noConfusion hBeq
  | ProAtom.hgen _, ProAtom.conjoint _, hBeq => Bool.noConfusion hBeq
  | ProAtom.companion _, ProAtom.hgen _, hBeq => Bool.noConfusion hBeq
  | ProAtom.companion leftId, ProAtom.companion rightId, hBeq =>
      congrArg ProAtom.companion (eqpNatBeqEq leftId rightId hBeq)
  | ProAtom.companion _, ProAtom.conjoint _, hBeq => Bool.noConfusion hBeq
  | ProAtom.conjoint _, ProAtom.hgen _, hBeq => Bool.noConfusion hBeq
  | ProAtom.conjoint _, ProAtom.companion _, hBeq => Bool.noConfusion hBeq
  | ProAtom.conjoint leftId, ProAtom.conjoint rightId, hBeq =>
      congrArg ProAtom.conjoint (eqpNatBeqEq leftId rightId hBeq)

/-- Own cons-only append (polymorphic).  The horizontal composite of proarrow words; the free-category
composite of vertical words.  `List.append` stdlib lemmas leak `propext`; this structural form does not. -/
def eqpAppend {carrier : Type} : List carrier → List carrier → List carrier
  | [], suffix => suffix
  | element :: prefixRest, suffix => element :: eqpAppend prefixRest suffix

/-- Right identity of `eqpAppend`. -/
theorem eqpAppendNil {carrier : Type} : (letters : List carrier) → eqpAppend letters [] = letters
  | [] => rfl
  | element :: rest => by
      show element :: eqpAppend rest [] = element :: rest
      rw [eqpAppendNil rest]

/-- Associativity of `eqpAppend`. -/
theorem eqpAppendAssoc {carrier : Type} : (first second third : List carrier) →
    eqpAppend (eqpAppend first second) third = eqpAppend first (eqpAppend second third)
  | [], _, _ => rfl
  | element :: rest, second, third => by
      show element :: eqpAppend (eqpAppend rest second) third
        = element :: eqpAppend rest (eqpAppend second third)
      rw [eqpAppendAssoc rest second third]

/-- Structural Boolean equality on proarrow words (cons-only, cloned from the `csw` list kit). -/
def eqpProAtomListBeq : List ProAtom → List ProAtom → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      eqpProAtomBeq leftHead rightHead && eqpProAtomListBeq leftRest rightRest

/-- Reflexivity of `eqpProAtomListBeq`. -/
theorem eqpProAtomListBeqRefl : (word : List ProAtom) → eqpProAtomListBeq word word = true
  | [] => rfl
  | head :: rest => by
      show (eqpProAtomBeq head head && eqpProAtomListBeq rest rest) = true
      rw [eqpProAtomBeqRefl head, eqpProAtomListBeqRefl rest]
      rfl

/-- `eqpProAtomListBeq` sound: beq-true proarrow words are propositionally equal. -/
theorem eqpProAtomListBeqEq : (left right : List ProAtom) →
    eqpProAtomListBeq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := eqpBoolAndElim _ _ hBeq
      rw [eqpProAtomBeqEq leftHead rightHead hSplit.left,
        eqpProAtomListBeqEq leftRest rightRest hSplit.right]

/-! ## Companion and conjoint of a vertical word (the framing functors) -/

/-- The companion of a vertical word: ORDER-PRESERVING map to companion atoms.  `(g ∘ f)_* = f_* ⊗ g_*`. -/
def eqpCompanionOfVertical : List Nat → List ProAtom
  | [] => []
  | verticalGenerator :: rest => ProAtom.companion verticalGenerator :: eqpCompanionOfVertical rest

/-- The conjoint of a vertical word: ORDER-REVERSING map to conjoint atoms (own cons-only reverse — the
contravariance `(g ∘ f)^* = g^* ⊗ f^*`).  Same shape as `reverseOperationWord`, no `List.reverse`. -/
def eqpConjointOfVertical : List Nat → List ProAtom
  | [] => []
  | verticalGenerator :: rest =>
      eqpAppend (eqpConjointOfVertical rest) [ProAtom.conjoint verticalGenerator]

/-- Companion of the identity vertical arrow is the identity proarrow. -/
theorem eqpCompanionNil : eqpCompanionOfVertical [] = [] := rfl

/-- Conjoint of the identity vertical arrow is the identity proarrow. -/
theorem eqpConjointNil : eqpConjointOfVertical [] = [] := rfl

/-- **Companion functoriality (covariant).**  `(g ∘ f)_* = f_* ⊗ g_*`. -/
theorem eqpCompanionAppend : (first second : List Nat) →
    eqpCompanionOfVertical (eqpAppend first second)
      = eqpAppend (eqpCompanionOfVertical first) (eqpCompanionOfVertical second)
  | [], _ => rfl
  | verticalGenerator :: rest, second => by
      show ProAtom.companion verticalGenerator :: eqpCompanionOfVertical (eqpAppend rest second)
        = ProAtom.companion verticalGenerator
            :: eqpAppend (eqpCompanionOfVertical rest) (eqpCompanionOfVertical second)
      rw [eqpCompanionAppend rest second]

/-- **Conjoint functoriality (contravariant).**  `(g ∘ f)^* = g^* ⊗ f^*` — the framing REVERSES order. -/
theorem eqpConjointAppend : (first second : List Nat) →
    eqpConjointOfVertical (eqpAppend first second)
      = eqpAppend (eqpConjointOfVertical second) (eqpConjointOfVertical first)
  | [], second => by
      show eqpConjointOfVertical second = eqpAppend (eqpConjointOfVertical second) []
      rw [eqpAppendNil]
  | verticalGenerator :: rest, second => by
      show eqpAppend (eqpConjointOfVertical (eqpAppend rest second))
            [ProAtom.conjoint verticalGenerator]
        = eqpAppend (eqpConjointOfVertical second)
            (eqpAppend (eqpConjointOfVertical rest) [ProAtom.conjoint verticalGenerator])
      rw [eqpConjointAppend rest second, eqpAppendAssoc]

/-! ## The proarrow (with objects) and the 1-cell decision -/

/-- A proarrow: a word of atoms with declared source / target objects (bookkeeping `Nat`s). -/
structure Proarrow where
  sourceObject : Nat
  targetObject : Nat
  atoms : List ProAtom

/-- The identity proarrow on an object: the empty atom word. -/
def eqpIdentityProarrow (object : Nat) : Proarrow :=
  { sourceObject := object, targetObject := object, atoms := [] }

/-- Decide proarrow equality: objects match AND the atom words are structurally equal. -/
def eqpDecideProarrowEq (left right : Proarrow) : Bool :=
  Nat.beq left.sourceObject right.sourceObject
    && Nat.beq left.targetObject right.targetObject
    && eqpProAtomListBeq left.atoms right.atoms

/-- `eqpDecideProarrowEq` sound: a positive decision is a propositional equality. -/
theorem eqpDecideProarrowEqSound : (left right : Proarrow) →
    eqpDecideProarrowEq left right = true → left = right
  | ⟨leftSource, leftTarget, leftAtoms⟩, ⟨rightSource, rightTarget, rightAtoms⟩, hDecision => by
      have hOuter := eqpBoolAndElim _ _ hDecision
      have hObjects := eqpBoolAndElim _ _ hOuter.left
      rw [eqpNatBeqEq leftSource rightSource hObjects.left,
        eqpNatBeqEq leftTarget rightTarget hObjects.right,
        eqpProAtomListBeqEq leftAtoms rightAtoms hOuter.right]

/-! ## Proarrow expressions, the flattening normal form, and the horizontal-monoid congruence -/

/-- A proarrow expression tree: identity, a single atom, or a horizontal composite. -/
inductive ProExpr where
  | idPro
  | atom (representative : ProAtom)
  | hcomp (left right : ProExpr)

/-- Flatten an expression to its proarrow word (the normal form). -/
def normalizeProExpr : ProExpr → List ProAtom
  | ProExpr.idPro => []
  | ProExpr.atom representative => [representative]
  | ProExpr.hcomp left right => eqpAppend (normalizeProExpr left) (normalizeProExpr right)

/-- The horizontal-monoid congruence on proarrow expressions: reflexive/symmetric/transitive,
congruent under horizontal composite, with associativity and left/right identity of `hcomp`. -/
inductive ProExprConv : ProExpr → ProExpr → Prop where
  | reflConv (expression : ProExpr) : ProExprConv expression expression
  | symmConv {left right : ProExpr} : ProExprConv left right → ProExprConv right left
  | transConv {left middle right : ProExpr} :
      ProExprConv left middle → ProExprConv middle right → ProExprConv left right
  | hcompCongr {leftA rightA leftB rightB : ProExpr} :
      ProExprConv leftA rightA → ProExprConv leftB rightB →
      ProExprConv (ProExpr.hcomp leftA leftB) (ProExpr.hcomp rightA rightB)
  | hcompAssoc (first second third : ProExpr) :
      ProExprConv (ProExpr.hcomp (ProExpr.hcomp first second) third)
        (ProExpr.hcomp first (ProExpr.hcomp second third))
  | hcompIdLeft (expression : ProExpr) :
      ProExprConv (ProExpr.hcomp ProExpr.idPro expression) expression
  | hcompIdRight (expression : ProExpr) :
      ProExprConv (ProExpr.hcomp expression ProExpr.idPro) expression

/-- Convertible expressions have equal normal forms. -/
theorem eqpProExprConvNormEq {left right : ProExpr} (hConv : ProExprConv left right) :
    normalizeProExpr left = normalizeProExpr right := by
  induction hConv with
  | reflConv _ => rfl
  | symmConv _ ih => exact ih.symm
  | transConv _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | hcompCongr _ _ ihLeft ihRight =>
      show eqpAppend (normalizeProExpr _) (normalizeProExpr _)
        = eqpAppend (normalizeProExpr _) (normalizeProExpr _)
      rw [ihLeft, ihRight]
  | hcompAssoc first second third =>
      exact eqpAppendAssoc (normalizeProExpr first) (normalizeProExpr second) (normalizeProExpr third)
  | hcompIdLeft _ => rfl
  | hcompIdRight expression => exact eqpAppendNil (normalizeProExpr expression)

/-- **1-cell soundness.**  Convertible expressions decide equal at the word level. -/
theorem eqpProarrowConvSound (left right : ProExpr) (hConv : ProExprConv left right) :
    eqpProAtomListBeq (normalizeProExpr left) (normalizeProExpr right) = true := by
  rw [eqpProExprConvNormEq hConv]
  exact eqpProAtomListBeqRefl (normalizeProExpr right)

/-- Rebuild a right-nested horizontal composite from a proarrow word. -/
def eqpAtomsToExpr : List ProAtom → ProExpr
  | [] => ProExpr.idPro
  | representative :: rest => ProExpr.hcomp (ProExpr.atom representative) (eqpAtomsToExpr rest)

/-- `eqpAtomsToExpr` is a horizontal-monoid homomorphism: it sends `eqpAppend` to `hcomp` up to
convertibility. -/
theorem eqpAtomsToExprAppend : (first second : List ProAtom) →
    ProExprConv (ProExpr.hcomp (eqpAtomsToExpr first) (eqpAtomsToExpr second))
      (eqpAtomsToExpr (eqpAppend first second))
  | [], second => ProExprConv.hcompIdLeft (eqpAtomsToExpr second)
  | representative :: rest, second =>
      ProExprConv.transConv
        (ProExprConv.hcompAssoc (ProExpr.atom representative) (eqpAtomsToExpr rest)
          (eqpAtomsToExpr second))
        (ProExprConv.hcompCongr (ProExprConv.reflConv (ProExpr.atom representative))
          (eqpAtomsToExprAppend rest second))

/-- Every expression is convertible to the canonical rebuild of its normal form. -/
theorem eqpExprConvAtomsToExprOfNorm : (expression : ProExpr) →
    ProExprConv expression (eqpAtomsToExpr (normalizeProExpr expression))
  | ProExpr.idPro => ProExprConv.reflConv ProExpr.idPro
  | ProExpr.atom representative => ProExprConv.symmConv (ProExprConv.hcompIdRight (ProExpr.atom representative))
  | ProExpr.hcomp left right =>
      ProExprConv.transConv
        (ProExprConv.hcompCongr (eqpExprConvAtomsToExprOfNorm left)
          (eqpExprConvAtomsToExprOfNorm right))
        (eqpAtomsToExprAppend (normalizeProExpr left) (normalizeProExpr right))

/-- Equal normal forms give convertible expressions (via the canonical rebuild). -/
theorem eqpProExprCompleteOfNormEq (left right : ProExpr)
    (hNormEq : normalizeProExpr left = normalizeProExpr right) : ProExprConv left right := by
  have hLeft := eqpExprConvAtomsToExprOfNorm left
  have hRight := eqpExprConvAtomsToExprOfNorm right
  rw [hNormEq] at hLeft
  exact ProExprConv.transConv hLeft (ProExprConv.symmConv hRight)

/-- **1-cell completeness.**  A positive word decision yields a convertibility — the free proarrow monoid
has decidable word problem, both directions. -/
theorem eqpProarrowConvComplete (left right : ProExpr)
    (hDecision : eqpProAtomListBeq (normalizeProExpr left) (normalizeProExpr right) = true) :
    ProExprConv left right :=
  eqpProExprCompleteOfNormEq left right (eqpProAtomListBeqEq _ _ hDecision)

/-- **The refutation half.**  A negative word decision refutes convertibility. -/
theorem eqpProarrowConvRefute (left right : ProExpr)
    (hFalse : eqpProAtomListBeq (normalizeProExpr left) (normalizeProExpr right) = false) :
    ProExprConv left right → False := by
  intro hConv
  have hTrue := eqpProarrowConvSound left right hConv
  rw [hFalse] at hTrue
  exact Bool.noConfusion hTrue

/-- **Companion functoriality at the expression level** (derived from the list equality + the homomorphism). -/
theorem eqpCompanionExprFunctorial (first second : List Nat) :
    ProExprConv (eqpAtomsToExpr (eqpCompanionOfVertical (eqpAppend first second)))
      (ProExpr.hcomp (eqpAtomsToExpr (eqpCompanionOfVertical first))
        (eqpAtomsToExpr (eqpCompanionOfVertical second))) := by
  rw [eqpCompanionAppend first second]
  exact ProExprConv.symmConv (eqpAtomsToExprAppend _ _)

/-- **Conjoint functoriality at the expression level** (contravariant — the composite REVERSES). -/
theorem eqpConjointExprFunctorial (first second : List Nat) :
    ProExprConv (eqpAtomsToExpr (eqpConjointOfVertical (eqpAppend first second)))
      (ProExpr.hcomp (eqpAtomsToExpr (eqpConjointOfVertical second))
        (eqpAtomsToExpr (eqpConjointOfVertical first))) := by
  rw [eqpConjointAppend first second]
  exact ProExprConv.symmConv (eqpAtomsToExprAppend _ _)

/-! ## The mates transpose (companion ↔ conjoint) and its involution -/

/-- Swap a companion with a conjoint on an atom, fixing horizontal generators. -/
def eqpMatesTransposeAtom : ProAtom → ProAtom
  | ProAtom.hgen identifier => ProAtom.hgen identifier
  | ProAtom.companion verticalGeneratorId => ProAtom.conjoint verticalGeneratorId
  | ProAtom.conjoint verticalGeneratorId => ProAtom.companion verticalGeneratorId

/-- The atom-level mates swap is self-inverse. -/
theorem eqpMatesTransposeAtomInvol : (atom : ProAtom) →
    eqpMatesTransposeAtom (eqpMatesTransposeAtom atom) = atom
  | ProAtom.hgen _ => rfl
  | ProAtom.companion _ => rfl
  | ProAtom.conjoint _ => rfl

/-- The mates transpose on a proarrow word: order-reversed atom-level swap (respecting the
companion ↔ conjoint duality's contravariance). -/
def eqpMatesTranspose : List ProAtom → List ProAtom
  | [] => []
  | representative :: rest =>
      eqpAppend (eqpMatesTranspose rest) [eqpMatesTransposeAtom representative]

/-- The mates transpose is contravariant over horizontal composite. -/
theorem eqpMatesTransposeAppend : (first second : List ProAtom) →
    eqpMatesTranspose (eqpAppend first second)
      = eqpAppend (eqpMatesTranspose second) (eqpMatesTranspose first)
  | [], second => by
      show eqpMatesTranspose second = eqpAppend (eqpMatesTranspose second) []
      rw [eqpAppendNil]
  | representative :: rest, second => by
      show eqpAppend (eqpMatesTranspose (eqpAppend rest second)) [eqpMatesTransposeAtom representative]
        = eqpAppend (eqpMatesTranspose second)
            (eqpAppend (eqpMatesTranspose rest) [eqpMatesTransposeAtom representative])
      rw [eqpMatesTransposeAppend rest second, eqpAppendAssoc]

/-- **The mates involution.**  Transposing twice returns the original proarrow word. -/
theorem eqpMatesTransposeInvol : (word : List ProAtom) →
    eqpMatesTranspose (eqpMatesTranspose word) = word
  | [] => rfl
  | representative :: rest => by
      show eqpMatesTranspose
            (eqpAppend (eqpMatesTranspose rest) [eqpMatesTransposeAtom representative]) = representative :: rest
      rw [eqpMatesTransposeAppend (eqpMatesTranspose rest) [eqpMatesTransposeAtom representative],
        eqpMatesTransposeInvol rest]
      show eqpAppend [eqpMatesTransposeAtom (eqpMatesTransposeAtom representative)] rest
        = representative :: rest
      rw [eqpMatesTransposeAtomInvol representative]
      rfl

/-! ## Ground fires -/

/-- Companion of a 2-letter vertical word is the 2-atom companion word (covariant functoriality). -/
theorem eqpFireCompanionTwoLetter :
    eqpCompanionOfVertical [3, 5] = [ProAtom.companion 3, ProAtom.companion 5] := rfl

/-- Conjoint of a 2-letter vertical word is the REVERSED 2-atom conjoint word (contravariance —
a genuine separation from the companion). -/
theorem eqpFireConjointTwoLetterReversed :
    eqpConjointOfVertical [3, 5] = [ProAtom.conjoint 5, ProAtom.conjoint 3] := rfl

/-- Two different proarrow words decide NOT equal. -/
theorem eqpFireDistinctWordsNotEqual :
    eqpProAtomListBeq [ProAtom.hgen 1] [ProAtom.companion 1] = false := rfl

/-- The mates transpose is self-inverse on a concrete mixed proarrow. -/
theorem eqpFireMatesInvolConcrete :
    eqpMatesTranspose (eqpMatesTranspose [ProAtom.companion 1, ProAtom.hgen 2, ProAtom.conjoint 3])
      = [ProAtom.companion 1, ProAtom.hgen 2, ProAtom.conjoint 3] :=
  eqpMatesTransposeInvol _

/-- Identity-composing a proarrow word (on the left) decides equal to it. -/
theorem eqpFireIdentityComposeEqual :
    eqpProAtomListBeq (eqpAppend [] [ProAtom.hgen 7]) [ProAtom.hgen 7] = true := rfl

/-- The mates transpose swaps companion to conjoint on a singleton. -/
theorem eqpFireMatesSwapSingleton :
    eqpMatesTranspose [ProAtom.companion 4] = [ProAtom.conjoint 4] := rfl

/-! ## The walls -/

/-- **WALL — full 2-cell coherence / mates as a genuine 2-cell bijection.**

The 1-cell (proarrow-word) layer is DECIDED both ways above.  The 2-cell layer — squares between proarrows,
composed both vertically and horizontally, subject to the double-category **interchange law**
`vcomp (hcomp a b) (hcomp c d) ≈ hcomp (vcomp a c) (vcomp b d)`, and the mates as a *bijection on 2-cell
equivalence classes* rather than the atom-representative involution `eqpMatesTranspose` — is NOT decided here.

Obstruction: the interchange coherence is exactly WP-DOUBLE's un-decided grid coherence.  The shipped
free-double-category work decides its word problem only on the honest UNIT-FREE grid fragment
(`WalkingDouble/DoubleTileGridNF`, `IsUnitFreeGrid`), and `Omega/Optic/FiniteLensWordProblem`
(`lgpHasPolyDoubleCoherence := false`) walls the Poly double-category bifunctoriality/interchange.  The
2-cell mates layer inherits both.

Burned attack 1 — a `(verticalDegree, horizontalDegree)` fold as a complete 2-cell invariant (the
`DoubleTileDimension` shape): fails because the mates bijection is NOT degree-preserving.  Swapping
`companion ↔ conjoint` reverses framing orientation, so a horizontal-degree fold cannot separate a square
from its mate; the fold is complete only on the unit-free grid — precisely WP-DOUBLE's decided boundary,
not the full 2-cell category.

Burned attack 2 — reuse the atom involution `eqpMatesTranspose` as the full 2-cell bijection: fails because
`eqpMatesTranspose` is an involution on atom REPRESENTATIVES, not a bijection on 2-cell convertibility
classes.  Without the interchange law, two convertible-but-syntactically-distinct squares can transpose to
non-convertible representatives, and there is no coherence in scope to reconcile them (the same gap that
keeps `lgpHasPolyDoubleCoherence` false). -/
def eqpHasFull2CellCoherence : Bool := false

/-- **WALL — companion/conjoint existence for a NON-FREE base (fibrancy / framing).**

In the FREE equipment every vertical generator gets a companion and a conjoint by construction — that is
exactly what `eqpCompanionOfVertical` / `eqpConjointOfVertical` produce.  For an arbitrary category of
vertical arrows sitting inside a bicategory, companion/conjoint EXISTENCE is the framing/fibrancy condition:
not every such structure is an equipment.

Obstruction: adjoint (companion/conjoint) existence in a general bicategory is a Σ-over-proarrows existence
statement, not a finite structural fold — the proarrow space is the free monoid, unbounded, with no fuel.

Burned attack 1 — a Boolean `hasCompanion : verticalWord → Bool` that searches for a right-adjoint witness:
fails because the search ranges over an unbounded proarrow space (the free monoid on the atoms); there is no
structural-recursion measure, so no zero-axiom decider (a `WellFounded.fix` search is banned and anyway
undecidable in general).

Burned attack 2 — assume as a closed hypothesis "every vertical has a companion" and decide companion
equality: fails because without freeness the companion is unique only up to 2-cell iso, so companion
equality reduces to 2-cell iso equality — the walled full-2-cell problem `eqpHasFull2CellCoherence` above.
The two walls are mutually entangled; neither can be discharged without the other. -/
def eqpHasNonFreeCompanionExistence : Bool := false

end FX1Poly.Polygraph
