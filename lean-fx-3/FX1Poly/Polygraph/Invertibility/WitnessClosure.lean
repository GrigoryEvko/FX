/-! # FX1Poly/Polygraph/Invertibility/WitnessClosure
    — the generic witness-closure operator and its two fixpoints.

This is the substrate-agnostic core shared by the Henry–Loubaton invertibility development
(arXiv 2301.11424) and the Tait/Girard strong-normalization development.  Both are instances of ONE
monotone operator on a family of "members", read at its two extremal fixpoints:

  * the **least** (inductive) fixpoint — the smallest family closed under the operator;
  * the **greatest** (coinductive) fixpoint — the largest family co-closed under the operator, encoded
    the standard way as the union of all post-fixed families (`∃ S, S ⊆ apply S ∧ S x`).  This is
    EXACTLY HL23 Def 4.15 / Remark 1.5: an invertibility set is a post-fixed family and `eq 𝒟` is the
    maximal one.

## Why the least fixpoint is impredicative here, not a `inductive`

Lean's positivity checker cannot see through an ABSTRACT operator's `apply` field (a bare function
`(Carrier → Prop) → (Carrier → Prop)` could be non-monotone), so `inductive L | mk : op.apply L x → L x`
is rejected for an arbitrary `op`.  The least fixpoint is therefore given by the impredicative
Knaster–Tarski encoding `inductiveClosure op x := ∀ P, apply-closed P → P x` — the intersection of all
`apply`-closed families.  For a MONOTONE operator this is provably the least pre-fixed point, hence the
least fixpoint (`inductiveClosure_closedUnderApply` + `inductiveClosure_unfold` below give both closure
directions), and its `inductiveClosure_least` field IS the induction principle.  At the concrete,
syntactically-positive reduct operator of `StrongNormalizationBridge.lean` this impredicative closure
coincides (up to `↔`) with Lean's genuine `Acc` inductive — that coincidence is the headline theorem.

## Zero-axiom verification

Pure `∀`/`→`/`∃`/`And`/`Iff` over an impredicative `Prop`; every proof is a constructive term or a
structural `refine`/`intro`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/Polygraph/Invertibility/WitnessClosure.lean`.
-/

namespace FX1Poly.Polygraph.Invertibility

variable {Carrier : Type}

/-- A **monotone witness operator** on families `Carrier → Prop`: an endofunction `apply` on families
together with a proof `monotone` that it preserves family containment.  Both the inductive and the
coinductive closures below are extremal fixpoints of such an operator; `monotone` is exactly the
hypothesis that makes those fixpoints well-behaved (closed in both directions). -/
structure WitnessOperator (Carrier : Type) where
  /-- One closure step: send a family of members to the family it justifies. -/
  apply : (Carrier → Prop) → (Carrier → Prop)
  /-- `apply` preserves containment of families (monotonicity / functoriality of the operator). -/
  monotone : ∀ {smaller larger : Carrier → Prop},
    (∀ element, smaller element → larger element) →
    ∀ element, apply smaller element → apply larger element

/-- The **least (inductive) fixpoint** of `operator`, impredicatively: the intersection of every family
closed under `operator.apply`.  A member of `inductiveClosure operator` lies in EVERY `apply`-closed
family — so this is the smallest such family, and its defining universal is the induction principle
(`inductiveClosure_least`). -/
def inductiveClosure (operator : WitnessOperator Carrier) (element : Carrier) : Prop :=
  ∀ family : Carrier → Prop,
    (∀ point, operator.apply family point → family point) → family element

/-- **Induction / least-ness.**  Any `apply`-closed family contains the inductive closure: to prove a
property of every inductive-closure member it suffices to show the property is `apply`-closed. -/
theorem inductiveClosure_least (operator : WitnessOperator Carrier) {family : Carrier → Prop}
    (familyClosed : ∀ point, operator.apply family point → family point) {element : Carrier}
    (member : inductiveClosure operator element) : family element :=
  member family familyClosed

/-- **Introduction / pre-fixed.**  The inductive closure is closed under one `apply` step: if every
member the operator asks for is already in the closure, the justified element is too.  (Needs
monotonicity to transport the closure-membership into an arbitrary `apply`-closed family.) -/
theorem inductiveClosure_closedUnderApply (operator : WitnessOperator Carrier) {element : Carrier}
    (applied : operator.apply (inductiveClosure operator) element) :
    inductiveClosure operator element := by
  intro family familyClosed
  have containedInFamily : ∀ point, inductiveClosure operator point → family point :=
    fun point member => member family familyClosed
  exact familyClosed element (operator.monotone containedInFamily element applied)

/-- **Unfolding / it is a fixpoint.**  The inductive closure is also a POST-fixed point
(`inductiveClosure ⊆ apply inductiveClosure`); combined with `inductiveClosure_closedUnderApply` this
makes it a genuine fixpoint.  Proof: `apply inductiveClosure` is itself `apply`-closed (by
monotonicity), so the least `apply`-closed family is contained in it. -/
theorem inductiveClosure_unfold (operator : WitnessOperator Carrier) {element : Carrier}
    (member : inductiveClosure operator element) :
    operator.apply (inductiveClosure operator) element :=
  member (operator.apply (inductiveClosure operator))
    (fun _point applied =>
      operator.monotone
        (fun _innerPoint innerMember => inductiveClosure_closedUnderApply operator innerMember)
        _point applied)

/-- A family is **post-fixed** under `operator` when it is contained in its own image
`family ⊆ operator.apply family`.  These are HL23's invertibility sets: every member's witnesses are
themselves demanded to be members. -/
def IsPostFixed (operator : WitnessOperator Carrier) (family : Carrier → Prop) : Prop :=
  ∀ element, family element → operator.apply family element

/-- The **greatest (coinductive) fixpoint** of `operator`: the union of all post-fixed families.  A
member is witnessed by SOME post-fixed family containing it — the standard "final coalgebra as union of
bisimulations" encoding, and HL23's `eq 𝒟` (the maximal invertibility set). -/
def coinductiveClosure (operator : WitnessOperator Carrier) (element : Carrier) : Prop :=
  ∃ family : Carrier → Prop, IsPostFixed operator family ∧ family element

/-- **Greatest-ness.**  Every post-fixed family is contained in the coinductive closure — it is that
family's own witness. -/
theorem IsPostFixed.subset_coinductiveClosure {operator : WitnessOperator Carrier}
    {family : Carrier → Prop} (postFixed : IsPostFixed operator family) {element : Carrier}
    (member : family element) : coinductiveClosure operator element :=
  ⟨family, postFixed, member⟩

/-- The coinductive closure is itself **post-fixed** (`coinductiveClosure ⊆ apply coinductiveClosure`).
Proof: a member's witnessing family `S` gives `apply S`, and `S ⊆ coinductiveClosure`, so monotonicity
lifts it to `apply coinductiveClosure`. -/
theorem coinductiveClosure_isPostFixed (operator : WitnessOperator Carrier) :
    IsPostFixed operator (coinductiveClosure operator) := by
  intro element member
  obtain ⟨family, postFixed, familyMember⟩ := member
  have containedInClosure : ∀ point, family point → coinductiveClosure operator point :=
    fun point pointMember => ⟨family, postFixed, pointMember⟩
  exact operator.monotone containedInClosure element (postFixed element familyMember)

/-- The coinductive closure is also **pre-fixed** (`apply coinductiveClosure ⊆ coinductiveClosure`),
completing the fixpoint.  Proof: `apply coinductiveClosure` is post-fixed (by monotonicity applied to
`coinductiveClosure_isPostFixed`), hence contained in the greatest post-fixed family. -/
theorem coinductiveClosure_closedUnderApply (operator : WitnessOperator Carrier) {element : Carrier}
    (applied : operator.apply (coinductiveClosure operator) element) :
    coinductiveClosure operator element := by
  refine ⟨operator.apply (coinductiveClosure operator), ?_, applied⟩
  intro point pointApplied
  exact operator.monotone (coinductiveClosure_isPostFixed operator) point pointApplied

/-- ★ **Least ⊆ greatest.**  The inductive (least) fixpoint is contained in the coinductive (greatest)
fixpoint.  Proof: the coinductive closure is `apply`-closed (`coinductiveClosure_closedUnderApply`), and
the inductive closure lies in every `apply`-closed family.  This is the abstract skeleton of the
headline coincidence — at the reduct operator (`StrongNormalizationBridge.lean`) the left side is strong
normalization and the right side is the folk invertibility structure. -/
theorem inductiveClosure_subset_coinductiveClosure (operator : WitnessOperator Carrier)
    {element : Carrier} (member : inductiveClosure operator element) :
    coinductiveClosure operator element :=
  member (coinductiveClosure operator)
    (fun _point applied => coinductiveClosure_closedUnderApply operator applied)

end FX1Poly.Polygraph.Invertibility
