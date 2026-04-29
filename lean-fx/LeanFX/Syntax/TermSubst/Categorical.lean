import LeanFX.Syntax.TermSubst.Compose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Categorical-structure laws on TermSubst (pointwise HEq).

Term-level analogues of the Ty-level monoid laws (`Subst.compose_*`).
Together with `Term.subst_id` (v1.25) and `Term.subst_compose` (v1.45)
they establish `(Ty, TermSubst, Term.subst)` as a category enriched
over `Ty` at the term level — identity is unital on both sides and
composition is associative.  Stated as pointwise HEq (per Fin position)
because `TermSubst` is Type-valued and per-position values can have
propositionally-distinct types between LHS and RHS. -/

/-- Composing the identity TermSubst on the left leaves a TermSubst
pointwise unchanged.  At each position, LHS is
`outer_cast ▸ Term.subst σt (inner_cast.symm ▸ Term.var i)`; cast
through `Term.subst_HEq_cast_input` and the var arm of `Term.subst`
collapses to `σt i`. -/
theorem TermSubst.compose_identity_left_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ) :
    ∀ i, HEq (TermSubst.compose (TermSubst.identity Γ) σt i) (σt i) := by
  intro i
  -- Strip outer cast from TermSubst.compose's definition.
  apply HEq.trans (eqRec_heq _ _)
  -- Push inner cast through Term.subst.
  apply HEq.trans
    (Term.subst_HEq_cast_input σt
      (Ty.subst_id (varType Γ i)).symm
      (Term.var (context := Γ) i))
  -- Term.subst σt (Term.var i) reduces definitionally to σt i.
  exact HEq.refl _

/-- Composing the identity TermSubst on the right leaves a TermSubst
pointwise unchanged.  At each position, the inner `Term.subst (identity
Δ) (σt i)` collapses via `Term.subst_id_HEq` (v1.25). -/
theorem TermSubst.compose_identity_right_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ) :
    ∀ i, HEq (TermSubst.compose σt (TermSubst.identity Δ) i) (σt i) := by
  intro i
  apply HEq.trans (eqRec_heq _ _)
  exact Term.subst_id_HEq (σt i)

/-- TermSubst composition is associative pointwise.  At each position,
LHS naked is `Term.subst (compose σt₂ σt₃) (σt₁ i)`, which by
`Term.subst_compose_HEq` (v1.45, applied .symm) equals
`Term.subst σt₃ (Term.subst σt₂ (σt₁ i))`.  RHS naked is the same
expression after pushing its inner `Ty.subst_compose` cast through
the outer `Term.subst σt₃` via `Term.subst_HEq_cast_input`. -/
theorem TermSubst.compose_assoc_pointwise
    {m : Mode} {level scope₁ scope₂ scope₃ scope₄ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂}
    {Γ₃ : Ctx m level scope₃} {Γ₄ : Ctx m level scope₄}
    {σ₁ : Subst level scope₁ scope₂}
    {σ₂ : Subst level scope₂ scope₃}
    {σ₃ : Subst level scope₃ scope₄}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (σt₃ : TermSubst Γ₃ Γ₄ σ₃) :
    ∀ i, HEq
      (TermSubst.compose σt₁ (TermSubst.compose σt₂ σt₃) i)
      (TermSubst.compose (TermSubst.compose σt₁ σt₂) σt₃ i) := by
  intro i
  -- Strip outer cast on LHS.
  apply HEq.trans (eqRec_heq _ _)
  -- LHS naked: Term.subst (compose σt₂ σt₃) (σt₁ i).
  -- By v1.45.symm: ≃HEq≃ Term.subst σt₃ (Term.subst σt₂ (σt₁ i)).
  apply HEq.trans
    (Term.subst_compose_HEq σt₂ σt₃ (σt₁ i)).symm
  -- Strip outer cast on RHS (via symm orientation).
  apply HEq.symm
  apply HEq.trans (eqRec_heq _ _)
  -- RHS naked: Term.subst σt₃ ((compose σt₁ σt₂) i)
  --          = Term.subst σt₃ (cast ▸ Term.subst σt₂ (σt₁ i)).
  -- Push the inner cast through Term.subst σt₃.
  exact Term.subst_HEq_cast_input σt₃
    (Ty.subst_compose (varType Γ₁ i) σ₁ σ₂)
    (Term.subst σt₂ (σt₁ i))


end LeanFX.Syntax
