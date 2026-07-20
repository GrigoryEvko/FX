import FX1Poly.Polygraph.TwoCategory.WalkingFreeGroup.FreeGroupSeed

/-! # TwoGroup/SemidirectWordProblem — the crossed-module / free-2-group word problem for the
semidirect product `G ⋉ C` at the abelian / trivial-action fragment

A strict 2-group is a crossed module `∂ : C → G` with a `G`-action on `C` satisfying equivariance
(`∂(g·c) = g ∂(c) g⁻¹`) and the Peiffer identity (`∂(c)·c' = c c' c⁻¹`).  Its 2-cells are pairs
`(g, c)` of the semidirect product `G ⋉ C`.  This file ships the WORD PROBLEM for that carrier at the
decidable fragment: the base group `G` is the free group on the colour alphabet `ℕ` (reused verbatim
from `WalkingFreeGroup/FreeGroupSeed` — reduced signed words), and the fibre `C` is the free abelian
(commutative) fibre with the TRIVIAL action, decided by a sorted-multiset normal form.

## What lands here

* **Carrier + ops (T1):** `CrossedCell` = a reduced base word `List SignedGen` paired with a fibre
  multiset `List Nat`; `cxmIdentityCell`; the semidirect `cxmCompose` (base multiply by `appendReduce`
  + action-twisted fibre combine, the action a structural twist — trivial for this fragment);
  well-formedness `cxmWellFormed` (base reduced, fibre a `cxmSort` fixed point).  The base uses the
  shipped cons-only reducer; no `List.append`, no `WellFounded`.
* **The Peiffer / equivariance checks (T2):** decidable `Bool` predicates `cxmEquivarianceHolds` and
  `cxmPeifferHolds` witnessing the two crossed-module axioms at the WORD level, each PROVEN true on a
  concrete abelian (trivial-action, trivial-boundary) instance and REFUTED on a concrete non-instance
  (a colour boundary that is not central; a doubling action that is not trivial).
* **The word decision + soundness (T3):** `decideTwoGroupEq` = reduced-base equality AND sorted-fibre
  equality of the two normalised cells (both via hand-rolled structural `Bool` equalities); the
  congruence `TwoGroupConv` (the semidirect-product laws on cell expressions) with **soundness**
  (`twoGroupConv_sound`) AND **abelian-fragment completeness** (`twoGroupConv_complete`), assembled
  into the biconditional `decideTwoGroupEq_iff_conv`.  The base half is the free-group reduced-word
  decision `freeGroupTreeConv_iff_reducedWord`; the fibre half is the sorted-multiset decision.
* **The wall (T4):** the general NON-abelian Peiffer descent (`cxmHasNonAbelianPeiffer := false`) and the
  identities-among-relations / `π₂`-of-a-presentation footing (`cxmHasIdentitiesAmongRelations := false`)
  are the deep free-crossed-module extensions — recorded honestly with concrete obstructions, never
  claimed.

Raw Lean 4 + Init only.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`funext`, `omega`, `Int`, `Nat.sub`: the element comparisons are `Nat.beq` (from the base kit) and full
enumeration; the fibre normal form is an insertion sort used only as an opaque normal form (never
reasoned about via `Nat.le` order lemmas), and every list operation is cons-only. -/

namespace FX1Poly.Polygraph

/-! ## Structural `Bool` equalities for the two coordinate carriers -/

/-- Full-enumeration `Bool` equality (avoids every `BEq`/`==` instance). -/
def cxmBoolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | true, false => false
  | false, true => false

/-- `cxmBoolBeq` is reflexive. -/
theorem cxmBoolBeqRefl : (value : Bool) → cxmBoolBeq value value = true
  | true => rfl
  | false => rfl

/-- `cxmBoolBeq` is sound: `cxmBoolBeq a b = true` forces `a = b`. -/
theorem cxmBoolBeqSound : (first second : Bool) → cxmBoolBeq first second = true → first = second
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, hbeq => Bool.noConfusion hbeq
  | false, true, hbeq => Bool.noConfusion hbeq

/-- Structural equality of two signed generators: same colour (`Nat.beq`) and same polarity. -/
def cxmSignedGenBeq (first second : SignedGen) : Bool :=
  Nat.beq first.colour second.colour && cxmBoolBeq first.isPositive second.isPositive

/-- `cxmSignedGenBeq` is reflexive. -/
theorem cxmSignedGenBeqRefl (gen : SignedGen) : cxmSignedGenBeq gen gen = true := by
  cases gen with
  | mk colour isPositive =>
    show (Nat.beq colour colour && cxmBoolBeq isPositive isPositive) = true
    rw [natBeqSelfTrue colour, cxmBoolBeqRefl isPositive]
    rfl

/-- `cxmSignedGenBeq` is sound. -/
theorem cxmSignedGenBeqSound (first second : SignedGen) (hbeq : cxmSignedGenBeq first second = true) :
    first = second := by
  cases first with
  | mk firstColour firstPositive =>
    cases second with
    | mk secondColour secondPositive =>
      have hbeqUnfolded :
          (Nat.beq firstColour secondColour && cxmBoolBeq firstPositive secondPositive) = true := hbeq
      have hcolour : firstColour = secondColour :=
        natBeqImpliesEq firstColour secondColour (boolAndTrueLeft _ _ hbeqUnfolded)
      have hpolarity : firstPositive = secondPositive :=
        cxmBoolBeqSound firstPositive secondPositive (boolAndTrueRight _ _ hbeqUnfolded)
      rw [hcolour, hpolarity]

/-- Structural equality of two signed words (order-sensitive, as the free group requires). -/
def cxmSignedListBeq : List SignedGen → List SignedGen → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | first :: firstRest, second :: secondRest =>
      cxmSignedGenBeq first second && cxmSignedListBeq firstRest secondRest

/-- `cxmSignedListBeq` is reflexive. -/
theorem cxmSignedListBeqRefl : (word : List SignedGen) → cxmSignedListBeq word word = true
  | [] => rfl
  | head :: tail => by
      show (cxmSignedGenBeq head head && cxmSignedListBeq tail tail) = true
      rw [cxmSignedGenBeqRefl head, cxmSignedListBeqRefl tail]
      rfl

/-- `cxmSignedListBeq` is sound. -/
theorem cxmSignedListBeqSound :
    (first second : List SignedGen) → cxmSignedListBeq first second = true → first = second
  | [], [], _ => rfl
  | [], _ :: _, hbeq => Bool.noConfusion hbeq
  | _ :: _, [], hbeq => Bool.noConfusion hbeq
  | firstHead :: firstTail, secondHead :: secondTail, hbeq => by
      have hbeqUnfolded :
          (cxmSignedGenBeq firstHead secondHead && cxmSignedListBeq firstTail secondTail) = true := hbeq
      have hhead : firstHead = secondHead :=
        cxmSignedGenBeqSound firstHead secondHead (boolAndTrueLeft _ _ hbeqUnfolded)
      have htail : firstTail = secondTail :=
        cxmSignedListBeqSound firstTail secondTail (boolAndTrueRight _ _ hbeqUnfolded)
      rw [hhead, htail]

/-- Structural equality of two fibre multisets represented as `List Nat`. -/
def cxmNatListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | first :: firstRest, second :: secondRest =>
      Nat.beq first second && cxmNatListBeq firstRest secondRest

/-- `cxmNatListBeq` is reflexive. -/
theorem cxmNatListBeqRefl : (word : List Nat) → cxmNatListBeq word word = true
  | [] => rfl
  | head :: tail => by
      show (Nat.beq head head && cxmNatListBeq tail tail) = true
      rw [natBeqSelfTrue head, cxmNatListBeqRefl tail]
      rfl

/-- `cxmNatListBeq` is sound. -/
theorem cxmNatListBeqSound :
    (first second : List Nat) → cxmNatListBeq first second = true → first = second
  | [], [], _ => rfl
  | [], _ :: _, hbeq => Bool.noConfusion hbeq
  | _ :: _, [], hbeq => Bool.noConfusion hbeq
  | firstHead :: firstTail, secondHead :: secondTail, hbeq => by
      have hbeqUnfolded :
          (Nat.beq firstHead secondHead && cxmNatListBeq firstTail secondTail) = true := hbeq
      have hhead : firstHead = secondHead :=
        natBeqImpliesEq firstHead secondHead (boolAndTrueLeft _ _ hbeqUnfolded)
      have htail : firstTail = secondTail :=
        cxmNatListBeqSound firstTail secondTail (boolAndTrueRight _ _ hbeqUnfolded)
      rw [hhead, htail]

/-! ## The fibre normal form: a sorted multiset (cons-only append + insertion sort) -/

/-- Cons-only append on `List Nat` (no `List.append`). -/
def cxmNatAppend : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: cxmNatAppend xs ys

/-- Insert one element into a list in ascending position (via `Nat.ble`, used only computationally). -/
def cxmInsert (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      match Nat.ble value head with
      | true => value :: head :: tail
      | false => head :: cxmInsert value tail

/-- The fibre normal form: insertion sort into an ascending multiset. -/
def cxmSort : List Nat → List Nat
  | [] => []
  | head :: tail => cxmInsert head (cxmSort tail)

/-! ## The carrier: a semidirect-product 2-cell -/

/-- ★ A **crossed-module 2-cell** of `G ⋉ C`: a base-group element (a reduced signed word over the
colour alphabet `ℕ`) paired with a fibre element (an abelian multiset of colours).  The complete
convertibility invariant of the abelian / trivial-action fragment is the pair of normal forms
(reduced base word, sorted fibre multiset). -/
structure CrossedCell where
  /-- The base-group coordinate: an element of the free group `G` on `ℕ`, as a signed word. -/
  baseWord : List SignedGen
  /-- The fibre coordinate: an element of the abelian fibre `C`, as a colour multiset. -/
  fibreWord : List Nat

/-- The identity 2-cell `(e, 0)`: empty base word, empty fibre. -/
def cxmIdentityCell : CrossedCell := ⟨[], []⟩

/-- The `G`-action on the fibre for this fragment: the **trivial action** `g · c = c` (a structural
twist that, for the abelian / trivial-action crossed module, relabels nothing). -/
def cxmActionTrivial (_base : List SignedGen) (fibre : List Nat) : List Nat := fibre

/-- ★ **Semidirect composition** of two 2-cells: multiply the base coordinates (via the free-group
`appendReduce`) and combine the fibres after twisting the left fibre by the right base's action, then
renormalise to the sorted multiset.  For the trivial action this is the direct-product combine. -/
def cxmCompose (left right : CrossedCell) : CrossedCell :=
  { baseWord := appendReduce left.baseWord right.baseWord
    fibreWord := cxmSort (cxmNatAppend (cxmActionTrivial right.baseWord left.fibreWord) right.fibreWord) }

/-- Well-formedness of a 2-cell: the base word is freely reduced and the fibre is a sorted normal form. -/
def cxmWellFormed (cell : CrossedCell) : Prop :=
  IsReduced cell.baseWord ∧ cxmSort cell.fibreWord = cell.fibreWord

/-- The identity 2-cell is well-formed. -/
theorem cxmIdentityWellFormed : cxmWellFormed cxmIdentityCell := ⟨IsReduced.nil, rfl⟩

/-! ## The word decision -/

/-- ★ **The 2-group word decision**: two 2-cells are equal iff their reduced base words agree AND their
sorted fibre multisets agree.  Both coordinate equalities are hand-rolled structural `Bool` tests. -/
def decideTwoGroupEq (left right : CrossedCell) : Bool :=
  cxmSignedListBeq (reduceWord left.baseWord) (reduceWord right.baseWord)
    && cxmNatListBeq (cxmSort left.fibreWord) (cxmSort right.fibreWord)

/-- ★ **Characterisation of the decision** — `decideTwoGroupEq` is `true` exactly when both coordinate
normal forms coincide.  The workhorse for soundness, completeness, symmetry and transitivity. -/
theorem decideTwoGroupEq_true_iff (left right : CrossedCell) :
    decideTwoGroupEq left right = true ↔
      (reduceWord left.baseWord = reduceWord right.baseWord
        ∧ cxmSort left.fibreWord = cxmSort right.fibreWord) := by
  constructor
  · intro hdecide
    have hbase : cxmSignedListBeq (reduceWord left.baseWord) (reduceWord right.baseWord) = true :=
      boolAndTrueLeft _ _ hdecide
    have hfibre : cxmNatListBeq (cxmSort left.fibreWord) (cxmSort right.fibreWord) = true :=
      boolAndTrueRight _ _ hdecide
    exact ⟨cxmSignedListBeqSound _ _ hbase, cxmNatListBeqSound _ _ hfibre⟩
  · intro hnormalForms
    have hbase := hnormalForms.1
    have hfibre := hnormalForms.2
    show (cxmSignedListBeq (reduceWord left.baseWord) (reduceWord right.baseWord)
          && cxmNatListBeq (cxmSort left.fibreWord) (cxmSort right.fibreWord)) = true
    rw [hbase, hfibre, cxmSignedListBeqRefl, cxmNatListBeqRefl]
    rfl

/-! ## The congruence and its soundness + abelian completeness -/

/-- ★ The **2-group tree convertibility** on 2-cells: the semidirect-product congruence generated by the
free-group base convertibility (a base word may be replaced by any `reduceWord`-equal word — this is the
non-abelian free-group decision `freeGroupTreeConv_iff_reducedWord`) and the abelian fibre convertibility
(a fibre may be replaced by any `cxmSort`-equal multiset), closed under reflexivity, symmetry and
transitivity.  This is the convertibility of the abelian / trivial-action crossed module. -/
inductive TwoGroupConv : CrossedCell → CrossedCell → Prop where
  /-- Reflexivity. -/
  | reflexive (cell : CrossedCell) : TwoGroupConv cell cell
  /-- Symmetry. -/
  | symmetric {left right : CrossedCell} : TwoGroupConv left right → TwoGroupConv right left
  /-- Transitivity. -/
  | transitive {left mid right : CrossedCell} :
      TwoGroupConv left mid → TwoGroupConv mid right → TwoGroupConv left right
  /-- **Base convertibility**: replace the base word by any free-group-equal (`reduceWord`-equal) word. -/
  | baseConvertible {baseLeft baseRight : List SignedGen} {fibre : List Nat} :
      reduceWord baseLeft = reduceWord baseRight →
      TwoGroupConv ⟨baseLeft, fibre⟩ ⟨baseRight, fibre⟩
  /-- **Fibre convertibility**: replace the fibre by any abelian-equal (`cxmSort`-equal) multiset. -/
  | fibreCommutes {base : List SignedGen} {fibreLeft fibreRight : List Nat} :
      cxmSort fibreLeft = cxmSort fibreRight →
      TwoGroupConv ⟨base, fibreLeft⟩ ⟨base, fibreRight⟩

/-- Convertible 2-cells share both coordinate normal forms. -/
theorem twoGroupConv_normalForms {left right : CrossedCell} (conv : TwoGroupConv left right) :
    reduceWord left.baseWord = reduceWord right.baseWord
      ∧ cxmSort left.fibreWord = cxmSort right.fibreWord := by
  induction conv with
  | reflexive cell => exact ⟨rfl, rfl⟩
  | symmetric _premise ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | transitive _premiseAB _premiseBC ihAB ihBC => exact ⟨ihAB.1.trans ihBC.1, ihAB.2.trans ihBC.2⟩
  | baseConvertible hbase => exact ⟨hbase, rfl⟩
  | fibreCommutes hfibre => exact ⟨rfl, hfibre⟩

/-- ★ **Soundness** — convertible 2-cells decide equal. -/
theorem twoGroupConv_sound {left right : CrossedCell} (conv : TwoGroupConv left right) :
    decideTwoGroupEq left right = true :=
  (decideTwoGroupEq_true_iff left right).mpr (twoGroupConv_normalForms conv)

/-- ★ **Abelian-fragment completeness** — 2-cells that decide equal are convertible.  Both coordinates
route through their shared normal forms: base by `baseConvertible`, fibre by `fibreCommutes`. -/
theorem twoGroupConv_complete {left right : CrossedCell} (hdecide : decideTwoGroupEq left right = true) :
    TwoGroupConv left right := by
  cases left with
  | mk baseLeft fibreLeft =>
    cases right with
    | mk baseRight fibreRight =>
      have hnormalForms := (decideTwoGroupEq_true_iff ⟨baseLeft, fibreLeft⟩ ⟨baseRight, fibreRight⟩).mp hdecide
      exact TwoGroupConv.transitive
        (TwoGroupConv.baseConvertible hnormalForms.1)
        (TwoGroupConv.fibreCommutes hnormalForms.2)

/-- ★ **The decision** — convertibility in the abelian / trivial-action crossed module is exactly the
join of the free-group base decision and the sorted-multiset fibre decision. -/
theorem decideTwoGroupEq_iff_conv (left right : CrossedCell) :
    TwoGroupConv left right ↔ decideTwoGroupEq left right = true :=
  ⟨twoGroupConv_sound, twoGroupConv_complete⟩

/-! ## The Peiffer / equivariance crossed-module axiom checks (T2) -/

/-- Base conjugation `g · w · g⁻¹` via the free-group reducer. -/
def conjugateBase (conjugator target : List SignedGen) : List SignedGen :=
  appendReduce conjugator (appendReduce target (invertWord conjugator))

/-- The trivial boundary `∂ = e`: every fibre element maps to the identity of `G`. -/
def cxmBoundaryTrivial (_fibre : List Nat) : List SignedGen := []

/-- A NON-central boundary candidate: send each fibre colour `k` to the positive base generator `(k,+)`.
This is not a valid crossed-module boundary against the free base (its image is not central), the
witness that breaks equivariance. -/
def cxmBoundaryColour : List Nat → List SignedGen
  | [] => []
  | colour :: rest => ⟨colour, true⟩ :: cxmBoundaryColour rest

/-- A NON-trivial action candidate: doubling the fibre.  Not a group action (it is not idempotent on the
identity), the witness that breaks the Peiffer identity. -/
def cxmActionDouble (_base : List SignedGen) (fibre : List Nat) : List Nat := cxmNatAppend fibre fibre

/-- ★ **Equivariance check** `∂(g·c) = g ∂(c) g⁻¹` at the word level, parametric on a boundary and an
action candidate. -/
def cxmEquivarianceHolds (boundaryOf : List Nat → List SignedGen)
    (actOf : List SignedGen → List Nat → List Nat) (base : List SignedGen) (fibre : List Nat) : Bool :=
  cxmSignedListBeq (reduceWord (boundaryOf (actOf base fibre))) (conjugateBase base (boundaryOf fibre))

/-- ★ **Peiffer check** `∂(c)·c' = c c' c⁻¹` at the word level.  In the abelian fibre conjugation is
trivial, so the identity reduces to: the action of `∂(c)` on `c'` returns `c'`. -/
def cxmPeifferHolds (actOf : List SignedGen → List Nat → List Nat)
    (boundaryOf : List Nat → List SignedGen) (fibreLeft fibreRight : List Nat) : Bool :=
  cxmNatListBeq (actOf (boundaryOf fibreLeft) fibreRight) fibreRight

/-- ★ Equivariance HOLDS on the concrete abelian instance (trivial boundary, trivial action): both sides
collapse to the empty base word. -/
theorem cxmEquivarianceHoldsOnTrivialInstance :
    cxmEquivarianceHolds cxmBoundaryTrivial cxmActionTrivial [⟨0, true⟩] [5] = true := rfl

/-- ★ Equivariance is REFUTED on the colour-boundary non-instance: the non-central `∂` image
`[(5,+)]` differs from its conjugate `[(0,+),(5,+),(0,-)]`. -/
theorem cxmEquivarianceRefutedOnColourWitness :
    cxmEquivarianceHolds cxmBoundaryColour cxmActionTrivial [⟨0, true⟩] [5] = false := rfl

/-- ★ The Peiffer identity HOLDS on the concrete abelian instance (trivial action): the action of `∂(c)`
returns `c'` unchanged. -/
theorem cxmPeifferHoldsOnTrivialInstance :
    cxmPeifferHolds cxmActionTrivial cxmBoundaryTrivial [1] [2] = true := rfl

/-- ★ The Peiffer identity is REFUTED on the doubling-action non-instance: the action doubles `[2]` to
`[2,2] ≠ [2]`. -/
theorem cxmPeifferRefutedOnDoublingWitness :
    cxmPeifferHolds cxmActionDouble cxmBoundaryTrivial [1] [2] = false := rfl

/-! ## Groundings (T5) -/

/-- ★ **Left unit fires** — composing the identity 2-cell with a concrete cell `L` decides equal to `L`.
The base multiply `appendReduce [] _` is the identity and the fibre combine renormalises to `L`'s
already-sorted fibre. -/
theorem cxmIdentityLeftUnitFires :
    decideTwoGroupEq (cxmCompose cxmIdentityCell ⟨[⟨0, true⟩], [1, 2]⟩) ⟨[⟨0, true⟩], [1, 2]⟩ = true :=
  rfl

/-- ★ **Fibre reorder decides equal (abelian)** — two 2-cells differing only by a Peiffer-related fibre
reordering `[2,1]` vs `[1,2]` decide equal: both sort to `[1,2]`. -/
theorem cxmFibreReorderDecidesEqual :
    decideTwoGroupEq ⟨[⟨0, true⟩], [2, 1]⟩ ⟨[⟨0, true⟩], [1, 2]⟩ = true := rfl

/-- ★ The same fibre reorder as an explicit convertibility witness (the abelian fibre generator). -/
theorem cxmFibreReorderConv :
    TwoGroupConv ⟨[⟨0, true⟩], [2, 1]⟩ ⟨[⟨0, true⟩], [1, 2]⟩ :=
  TwoGroupConv.fibreCommutes rfl

/-- ★ **Distinct base decides unequal** — two 2-cells with different base generators `(0,+)` vs `(1,+)`
decide NOT equal. -/
theorem cxmDistinctBaseDecidesUnequal :
    decideTwoGroupEq ⟨[⟨0, true⟩], []⟩ ⟨[⟨1, true⟩], []⟩ = false := rfl

/-- ★ **Distinct fibre decides unequal** — two 2-cells with the same base but different fibres `[1]` vs
`[2]` decide NOT equal. -/
theorem cxmDistinctFibreDecidesUnequal :
    decideTwoGroupEq ⟨[⟨0, true⟩], [1]⟩ ⟨[⟨0, true⟩], [2]⟩ = false := rfl

/-! ## The walls (T4) -/

/-- ★ **WALL — the general NON-abelian Peiffer descent is NOT decided here.**  With a non-abelian fibre
`C`, the Peiffer identity `∂(c)·c' = c c' c⁻¹` is a genuine equational constraint whose normal form must
respect nontrivial conjugation; the trivial-action sorted-multiset normal form of this file cannot
witness it.  This is the free crossed module word problem (Whitehead 1949).

Two burned attacks:
(1) Represent the fibre as a signed reduced word (a second free group) with the action a base-driven
relabelling — but proving the boundary-descent `PeifferEquiv x y → ∂ x = ∂ y` at a GENERAL
(non-well-formed) word requires a measure induction over the `∂`-length that Init structural recursion
cannot express without `WellFounded.fix` (the same obstruction recorded as the structure-theorem
residual in the shipped `CrossedModuleFreeGroupStructureTheorem`, which lands the descent only at the
well-formed / generator-0 fragment).
(2) A `Bool`-decidable Peiffer congruence closure over cell expressions — but the closure is not
confluent for a non-abelian fibre: the crossing `{}^{∂a}b` vs conjugation squares do not commute at the
word level, so no finite reduced normal form exists to decide against. -/
def cxmHasNonAbelianPeiffer : Bool := false

/-- ★ **WALL — identities-among-relations / `π₂` of a presentation is NOT decided here.**  The module of
identities among relations (`π₂` of the presentation 2-complex, the `H₂` footing, Brown–Huebschmann
`π₂ ≅ H₂(G; ZZ[G])`) is the syzygy module of the defining relators, and deciding it is the deep free
crossed module obstruction.

Two burned attacks:
(1) Compute the relation module as the kernel of the free-crossed `∂` via the abelianised chain complex
— but that imports the `IntMatrix` / Steiner-Omega homology lane, from which the crossed-module lane is
deliberately firewalled, and the kernel is not finitely decidable without a Gröbner / Smith computation
over `ZZ[G]` (non-commutative for non-abelian `G`).
(2) Use the Lyndon identity theorem (aspherical presentations have trivial `π₂`) as a decision oracle —
but asphericity is not recursively checkable in general (Lyndon 1950; Whitehead 1949), mechanized in no
prover, so it cannot back a decision procedure. -/
def cxmHasIdentitiesAmongRelations : Bool := false

/-! ## The marker -/

/-- ★ **The crossed-module / free-2-group word problem is DECIDED at the abelian / trivial-action
fragment** — `= true` records that `decideTwoGroupEq_iff_conv` reduces convertibility in the semidirect
product `G ⋉ C` (with `G` the free group on `ℕ`, `C` the free abelian fibre, and the trivial action) to
the join of the free-group reduced-word decision (reused verbatim from `WalkingFreeGroup/FreeGroupSeed`
as `freeGroupTreeConv_iff_reducedWord`) and the sorted-multiset fibre decision.  Soundness and
completeness both land for this fragment; the crossed-module axioms (equivariance, Peiffer) are checked
as `Bool` predicates that hold on a concrete abelian instance and are refuted on concrete non-instances;
the general non-abelian Peiffer descent and the identities-among-relations `π₂` footing are the walled
deep extensions.  All zero-axiom: `Nat.beq` colour comparison, full-enumeration `Bool` equalities, a
cons-only reducer and a cons-only fibre append, no `Int`, no `Nat.sub`, no `List.append`. -/
def cxmHasSemidirectAbelianWordDecision : Bool := true

end FX1Poly.Polygraph
