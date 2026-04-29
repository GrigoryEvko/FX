import LeanFX.Syntax.TermSubst.Core

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## HEq bridge helpers for term-substitution functoriality.

`Term.subst_id` and `Term.subst_compose` need to bridge terms whose
types differ propositionally (e.g. `Term Γ (T.subst Subst.identity)`
vs `Term Γ T`).  HEq is the right notion of equality; the lemmas
below collapse outer casts and align cons-extended contexts. -/

/-- Constructor-level HEq congruence closer.

All `Term.<ctor>_HEq_congr` lemmas have the same proof shape:
substitute propositional equalities and heterogeneous equalities until
both constructor applications are definitionally identical, then close
with `rfl`.  Keeping this as a local tactic makes future constructors
add one proof line instead of another hand-written `cases` cascade. -/
macro "term_heq_congr" : tactic =>
  `(tactic| (subst_vars; rfl))

/-- Close a context-equality leaf case where both sides are the same
constructor after substituting the context equality. -/
macro "term_context_refl" : tactic =>
  `(tactic| (subst_vars; exact HEq.refl _))

/-- **HEq across context-shape change for `Term.var`**: if two
contexts at the same scope are propositionally equal, then the
`Term.var` constructor at the same Fin position produces HEq
values across them.  Proven by `cases` on the context equality —
both sides become identical, and HEq reduces to Eq.refl. -/
theorem heq_var_across_ctx_eq {m : Mode} {level scope : Nat}
    {Γ Δ : Ctx m level scope} (h_ctx : Γ = Δ) (i : Fin scope) :
    HEq (Term.var (context := Γ) i) (Term.var (context := Δ) i) := by
  cases h_ctx
  rfl

/-- **Strip an inner type-cast through `Term.weaken`.**  The
generic helper: weakening a term commutes with a propositional
type cast on the input.  Proven by `cases` on the equation —
both T₁ and T₂ are local variables, so the substitution succeeds
and the cast vanishes. -/
theorem Term.heq_weaken_strip_cast
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (newType : Ty level scope) {T₁ T₂ : Ty level scope} (h : T₁ = T₂)
    (t : Term Γ T₁) :
    HEq (Term.weaken newType (h ▸ t)) (Term.weaken newType t) := by
  cases h
  rfl

/-- **HEq across context-shape change for `Term.weaken (... ▸
Term.var)`**: at position k+1 of the lifted-identity, the LHS
shape is `Term.weaken X ((Ty.subst_id _).symm ▸ Term.var ⟨k, _⟩)`,
which equals `Term.var ⟨k+1, _⟩` in the extended context modulo
context-shape and the inner cast.  Uses
`Term.heq_weaken_strip_cast` to discharge the inner cast, then
`Term.weaken X (Term.var ⟨k, _⟩) = Term.var ⟨k+1, _⟩` by `rfl`
(through `Term.rename`'s var arm + `TermRenaming.weaken`'s
rfl-pointwise + `Renaming.weaken = Fin.succ`). -/
theorem heq_weaken_var_across_ctx_eq {m : Mode} {level scope : Nat}
    {Γ Δ : Ctx m level scope} (h_ctx : Γ = Δ)
    (newTypeΓ : Ty level scope) (newTypeΔ : Ty level scope)
    (h_new : newTypeΓ = newTypeΔ)
    (k : Nat) (hk : k + 1 < scope + 1) :
    HEq
      (Term.weaken newTypeΓ
        ((Ty.subst_id (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).symm ▸
          Term.var (context := Γ) ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (Term.var (context := Δ.cons newTypeΔ) ⟨k + 1, hk⟩) := by
  -- Reduce both sides simultaneously by `cases`-ing the context
  -- and newType equalities — this aligns Γ = Δ and newTypeΓ =
  -- newTypeΔ pointwise.
  cases h_ctx
  cases h_new
  -- Strip the inner cast via the helper.
  apply HEq.trans (Term.heq_weaken_strip_cast newTypeΓ
    (Ty.subst_id (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).symm
    (Term.var ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
  -- Goal: HEq (Term.weaken newTypeΓ (Term.var ⟨k, _⟩))
  --           (Term.var (context := Γ.cons newTypeΓ) ⟨k+1, hk⟩)
  -- Term.weaken X (Term.var ⟨k, _⟩) reduces (rfl) to
  --   Term.var (Renaming.weaken ⟨k, _⟩) = Term.var ⟨k+1, _⟩
  rfl

/-- **The HEq stepping stone for `Term.subst_id`'s recursive cases.**
Lifting `TermSubst.identity Γ` under a binder produces a TermSubst
that, pointwise, agrees with `TermSubst.identity (Γ.cons newType)`
modulo HEq.  The contexts and underlying substitutions differ
propositionally (via `Ty.subst_id newType` and
`Subst.lift_identity_equiv`); HEq is the right notion of equality
because both differences manifest at the type level of the
substituent terms. -/
theorem TermSubst.lift_identity_pointwise
    {m : Mode} {level scope : Nat}
    (Γ : Ctx m level scope) (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.lift (TermSubst.identity Γ) newType i)
        (TermSubst.identity (Γ.cons newType) i) := by
  intro i
  -- The bridging Ty-level fact, used in both Fin cases.
  have h_subst_id : newType.subst Subst.identity = newType :=
    Ty.subst_id newType
  -- Lift to context-level equality.
  have h_ctx :
      Γ.cons (newType.subst Subst.identity) = Γ.cons newType := by
    rw [h_subst_id]
  match i with
  | ⟨0, h0⟩ =>
    -- LHS = (Ty.subst_weaken_commute newType Subst.identity).symm ▸
    --        Term.var (context := Γ.cons (newType.subst Subst.identity)) ⟨0, h0⟩
    -- RHS = (Ty.subst_id newType.weaken).symm ▸
    --        Term.var (context := Γ.cons newType) ⟨0, h0⟩
    --
    -- Strip both outer casts via eqRec_heq, then bridge the two
    -- naked Term.var values via heq_var_across_ctx_eq + h_ctx.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (heq_var_across_ctx_eq h_ctx ⟨0, h0⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) Subst.identity).symm ▸
    --        Term.weaken (newType.subst Subst.identity)
    --          (TermSubst.identity Γ ⟨k, _⟩)
    --      = ... ▸ Term.weaken (newType.subst Subst.identity)
    --                ((Ty.subst_id (varType Γ ⟨k,_⟩)).symm ▸
    --                  Term.var ⟨k, _⟩)
    -- RHS = (Ty.subst_id (varType Γ ⟨k,_⟩).weaken).symm ▸
    --        Term.var (context := Γ.cons newType) ⟨k + 1, hk⟩
    --
    -- Strip outer cast on each side, then bridge via
    -- heq_weaken_var_across_ctx_eq applied at the identity ctx
    -- equality (Γ = Γ) plus the newType equality.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_weaken_var_across_ctx_eq (rfl : Γ = Γ)
        (newType.subst Subst.identity) newType
        h_subst_id k hk)
    exact (eqRec_heq _ _).symm

/-! ## HEq congruence helpers per `Term` constructor.

Each `Term.C_HEq_congr` says: two `C`-applications are HEq when their
type-level implicits are propositionally equal and their value
arguments are HEq.  Building blocks for any inductive proof that
descends through `Term.subst` / `Term.rename` and needs to bridge
`Term` values across different type indices. -/

/-- HEq congruence for `Term.app`. -/
theorem Term.app_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T₁_a T₁_b T₂_a T₂_b : Ty level scope}
    (h_T₁ : T₁_a = T₁_b) (h_T₂ : T₂_a = T₂_b)
    (f₁ : Term Γ (T₁_a.arrow T₂_a)) (f₂ : Term Γ (T₁_b.arrow T₂_b))
    (h_f : HEq f₁ f₂)
    (a₁ : Term Γ T₁_a) (a₂ : Term Γ T₁_b) (h_a : HEq a₁ a₂) :
    HEq (Term.app f₁ a₁) (Term.app f₂ a₂) := by
  term_heq_congr

/-- HEq congruence for `Term.lam`. -/
theorem Term.lam_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level scope} (h_cod : cod₁ = cod₂)
    (body₁ : Term (Γ.cons dom₁) cod₁.weaken)
    (body₂ : Term (Γ.cons dom₂) cod₂.weaken)
    (h_body : HEq body₁ body₂) :
    HEq (Term.lam body₁) (Term.lam body₂) := by
  term_heq_congr

/-- HEq congruence for `Term.lamPi`. -/
theorem Term.lamPi_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level (scope + 1)} (h_cod : cod₁ = cod₂)
    (body₁ : Term (Γ.cons dom₁) cod₁)
    (body₂ : Term (Γ.cons dom₂) cod₂)
    (h_body : HEq body₁ body₂) :
    HEq (Term.lamPi body₁) (Term.lamPi body₂) := by
  term_heq_congr

/-- HEq congruence for `Term.appPi`. -/
theorem Term.appPi_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level (scope + 1)} (h_cod : cod₁ = cod₂)
    (f₁ : Term Γ (Ty.piTy dom₁ cod₁))
    (f₂ : Term Γ (Ty.piTy dom₂ cod₂))
    (h_f : HEq f₁ f₂)
    (a₁ : Term Γ dom₁) (a₂ : Term Γ dom₂) (h_a : HEq a₁ a₂) :
    HEq (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) := by
  term_heq_congr

/-- HEq congruence for `Term.pair`. -/
theorem Term.pair_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (v₁ : Term Γ first₁) (v₂ : Term Γ first₂) (h_v : HEq v₁ v₂)
    (w₁ : Term Γ (second₁.subst0 first₁))
    (w₂ : Term Γ (second₂.subst0 first₂)) (h_w : HEq w₁ w₂) :
    HEq (Term.pair v₁ w₁) (Term.pair v₂ w₂) := by
  term_heq_congr

/-- HEq congruence for `Term.fst`. -/
theorem Term.fst_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.fst p₁) (Term.fst p₂) := by
  term_heq_congr

/-- HEq congruence for `Term.snd`. -/
theorem Term.snd_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.snd p₁) (Term.snd p₂) := by
  term_heq_congr

/-- **General HEq congruence for `Term.weaken`.**  Stronger than
`Term.heq_weaken_strip_cast` (which only handled an inner cast):
this allows the newType parameter AND the input term to differ
across the HEq.  Three `cases` discharge the three propositional
equalities; once unified, `rfl`. -/
theorem Term.weaken_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {newType₁ newType₂ : Ty level scope} (h_new : newType₁ = newType₂)
    {T₁ T₂ : Ty level scope} (h_T : T₁ = T₂)
    (t₁ : Term Γ T₁) (t₂ : Term Γ T₂) (h_t : HEq t₁ t₂) :
    HEq (Term.weaken newType₁ t₁) (Term.weaken newType₂ t₂) := by
  term_heq_congr

/-- Apply the same type cast to both sides of a same-source HEq. -/
theorem Term.castSame_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {firstTerm secondTerm : Term Γ sourceType}
    (termEquality : HEq firstTerm secondTerm) :
    HEq (typeEquality ▸ firstTerm) (typeEquality ▸ secondTerm) := by
  cases typeEquality
  exact termEquality

/-- Relate a term to the same term cast along a type equality. -/
theorem Term.castRight_HEq
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    (sourceTerm : Term Γ sourceType) :
    HEq sourceTerm (typeEquality ▸ sourceTerm) := by
  cases typeEquality
  rfl

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.bool) (h_s : s₁ = s₂)
    (t₁ : Term Γ result₁) (t₂ : Term Γ result₂) (h_t : HEq t₁ t₂)
    (e₁ : Term Γ result₁) (e₂ : Term Γ result₂) (h_e : HEq e₁ e₂) :
    HEq (Term.boolElim s₁ t₁ e₁) (Term.boolElim s₂ t₂ e₂) := by
  term_heq_congr

/-- HEq congruence for `Term.natSucc`.  natSucc has no type-level
indices that vary, so this collapses to plain equality of the
predecessor-term — we accept HEq for symmetry with the other
constructor congruences. -/
theorem Term.natSucc_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (p₁ p₂ : Term Γ Ty.nat) (h_p : HEq p₁ p₂) :
    HEq (Term.natSucc p₁) (Term.natSucc p₂) := by
  term_heq_congr

/-- HEq congruence for `Term.natElim`. -/
theorem Term.natElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.nat) (h_s : s₁ = s₂)
    (z₁ : Term Γ result₁) (z₂ : Term Γ result₂) (h_z : HEq z₁ z₂)
    (f₁ : Term Γ (Ty.arrow Ty.nat result₁))
    (f₂ : Term Γ (Ty.arrow Ty.nat result₂))
    (h_f : HEq f₁ f₂) :
    HEq (Term.natElim s₁ z₁ f₁) (Term.natElim s₂ z₂ f₂) := by
  term_heq_congr

/-- HEq congruence for `Term.natRec`.  Same shape as `natElim_HEq_congr`
but with succBranch typed `Ty.arrow Ty.nat (Ty.arrow result result)` —
the predecessor + IH curried form for primitive recursion. -/
theorem Term.natRec_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.nat) (h_s : s₁ = s₂)
    (z₁ : Term Γ result₁) (z₂ : Term Γ result₂) (h_z : HEq z₁ z₂)
    (f₁ : Term Γ (Ty.arrow Ty.nat (Ty.arrow result₁ result₁)))
    (f₂ : Term Γ (Ty.arrow Ty.nat (Ty.arrow result₂ result₂)))
    (h_f : HEq f₁ f₂) :
    HEq (Term.natRec s₁ z₁ f₁) (Term.natRec s₂ z₂ f₂) := by
  term_heq_congr

/-- HEq congruence for `Term.listNil`.  Only the elementType varies
between sides; no value arguments. -/
theorem Term.listNil_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂) :
    HEq (Term.listNil (context := Γ) (elementType := elem₁))
        (Term.listNil (context := Γ) (elementType := elem₂)) := by
  term_heq_congr

/-- HEq congruence for `Term.listCons`. -/
theorem Term.listCons_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    (h₁ : Term Γ elem₁) (h₂ : Term Γ elem₂) (h_h : HEq h₁ h₂)
    (t₁ : Term Γ (Ty.list elem₁)) (t₂ : Term Γ (Ty.list elem₂))
    (h_t : HEq t₁ t₂) :
    HEq (Term.listCons h₁ t₁) (Term.listCons h₂ t₂) := by
  term_heq_congr

/-- HEq congruence for `Term.listElim`.  Both `elementType` and
`resultType` may vary; the consBranch type
`elem → list elem → result` mentions `elementType` twice. -/
theorem Term.listElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ : Term Γ (Ty.list elem₁)) (s₂ : Term Γ (Ty.list elem₂))
    (h_s : HEq s₁ s₂)
    (n₁ : Term Γ result₁) (n₂ : Term Γ result₂) (h_n : HEq n₁ n₂)
    (c₁ : Term Γ (Ty.arrow elem₁ (Ty.arrow (Ty.list elem₁) result₁)))
    (c₂ : Term Γ (Ty.arrow elem₂ (Ty.arrow (Ty.list elem₂) result₂)))
    (h_c : HEq c₁ c₂) :
    HEq (Term.listElim s₁ n₁ c₁) (Term.listElim s₂ n₂ c₂) := by
  term_heq_congr

/-- HEq congruence for `Term.optionNone` — only elementType varies. -/
theorem Term.optionNone_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂) :
    HEq (Term.optionNone (context := Γ) (elementType := elem₁))
        (Term.optionNone (context := Γ) (elementType := elem₂)) := by
  term_heq_congr

/-- HEq congruence for `Term.optionSome`. -/
theorem Term.optionSome_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    (v₁ : Term Γ elem₁) (v₂ : Term Γ elem₂) (h_v : HEq v₁ v₂) :
    HEq (Term.optionSome v₁) (Term.optionSome v₂) := by
  term_heq_congr

/-- HEq congruence for `Term.optionMatch`. -/
theorem Term.optionMatch_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ : Term Γ (Ty.option elem₁)) (s₂ : Term Γ (Ty.option elem₂))
    (h_s : HEq s₁ s₂)
    (n₁ : Term Γ result₁) (n₂ : Term Γ result₂) (h_n : HEq n₁ n₂)
    (sm₁ : Term Γ (Ty.arrow elem₁ result₁))
    (sm₂ : Term Γ (Ty.arrow elem₂ result₂))
    (h_sm : HEq sm₁ sm₂) :
    HEq (Term.optionMatch s₁ n₁ sm₁) (Term.optionMatch s₂ n₂ sm₂) := by
  term_heq_congr

/-- HEq congruence for `Term.eitherInl`.  Both `leftType` and
`rightType` may vary; only the `leftType` value is supplied. -/
theorem Term.eitherInl_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    (v₁ : Term Γ left₁) (v₂ : Term Γ left₂) (h_v : HEq v₁ v₂) :
    HEq (Term.eitherInl (rightType := right₁) v₁)
        (Term.eitherInl (rightType := right₂) v₂) := by
  term_heq_congr

/-- HEq congruence for `Term.eitherInr`.  Symmetric to `eitherInl_HEq_congr`. -/
theorem Term.eitherInr_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    (v₁ : Term Γ right₁) (v₂ : Term Γ right₂) (h_v : HEq v₁ v₂) :
    HEq (Term.eitherInr (leftType := left₁) v₁)
        (Term.eitherInr (leftType := left₂) v₂) := by
  term_heq_congr

/-- HEq congruence for `Term.eitherMatch`.  Three Ty-index equalities
(left, right, result) and three sub-term HEqs (scrutinee, leftBranch,
rightBranch). -/
theorem Term.eitherMatch_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ : Term Γ (Ty.either left₁ right₁))
    (s₂ : Term Γ (Ty.either left₂ right₂)) (h_s : HEq s₁ s₂)
    (lb₁ : Term Γ (Ty.arrow left₁ result₁))
    (lb₂ : Term Γ (Ty.arrow left₂ result₂)) (h_lb : HEq lb₁ lb₂)
    (rb₁ : Term Γ (Ty.arrow right₁ result₁))
    (rb₂ : Term Γ (Ty.arrow right₂ result₂)) (h_rb : HEq rb₁ rb₂) :
    HEq (Term.eitherMatch s₁ lb₁ rb₁) (Term.eitherMatch s₂ lb₂ rb₂) := by
  term_heq_congr

/-- HEq congruence for `Term.refl`.  Only the `carrier` Ty varies
between sides; the open endpoint `rawTerm : RawTerm scope` is shared
verbatim, so it does not need an HEq parameter.  Two
propositionally-distinct carriers produce `Term`s at
propositionally-distinct types `Ty.id carrier₁ rawTerm rawTerm` vs
`Ty.id carrier₂ rawTerm rawTerm`; HEq collapses them via `cases
h_carrier`. -/
theorem Term.refl_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {carrier₁ carrier₂ : Ty level scope} (h_carrier : carrier₁ = carrier₂)
    {rawTerm₁ rawTerm₂ : RawTerm scope} (h_rawTerm : rawTerm₁ = rawTerm₂) :
    HEq (Term.refl (context := Γ) (carrier := carrier₁) rawTerm₁)
        (Term.refl (context := Γ) (carrier := carrier₂) rawTerm₂) := by
  term_heq_congr

/-- HEq congruence for `Term.idJ`.  Four Ty-level equations (carrier,
leftEnd, rightEnd, resultType) and two HEq sub-term arguments
(baseCase and witness).  The witness's type depends on `carrier`,
`leftEnd`, `rightEnd`, so its HEq must travel via `cases` on those
three equations before HEq collapses to plain equality. -/
theorem Term.idJ_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {carrier₁ carrier₂ : Ty level scope} (h_carrier : carrier₁ = carrier₂)
    {leftEnd₁ leftEnd₂ : RawTerm scope} (h_leftEnd : leftEnd₁ = leftEnd₂)
    {rightEnd₁ rightEnd₂ : RawTerm scope} (h_rightEnd : rightEnd₁ = rightEnd₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (base₁ : Term Γ result₁) (base₂ : Term Γ result₂) (h_base : HEq base₁ base₂)
    (witness₁ : Term Γ (Ty.id carrier₁ leftEnd₁ rightEnd₁))
    (witness₂ : Term Γ (Ty.id carrier₂ leftEnd₂ rightEnd₂))
    (h_witness : HEq witness₁ witness₂) :
    HEq (Term.idJ base₁ witness₁) (Term.idJ base₂ witness₂) := by
  term_heq_congr

/-! ## `Term.subst_id_HEq` leaf cases.

Four leaf constructors: `var` strips the inner `(Ty.subst_id _).symm
▸ Term.var i` cast via `eqRec_heq`; `unit`/`boolTrue`/`boolFalse`
have substitution-independent types so reduce to `HEq.refl`. -/

/-- Leaf HEq case of `Term.subst_id` for `var`. -/
theorem Term.subst_id_HEq_var
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} (i : Fin scope) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.var i))
        (Term.var (context := Γ) i) := by
  show HEq ((Ty.subst_id (varType Γ i)).symm ▸ Term.var i) (Term.var i)
  exact eqRec_heq _ _

/-- Leaf HEq case of `Term.subst_id` for `unit`. -/
theorem Term.subst_id_HEq_unit
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.unit (context := Γ)))
        (Term.unit (context := Γ)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolTrue`. -/
theorem Term.subst_id_HEq_boolTrue
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolTrue (context := Γ)))
        (Term.boolTrue (context := Γ)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolFalse`. -/
theorem Term.subst_id_HEq_boolFalse
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolFalse (context := Γ)))
        (Term.boolFalse (context := Γ)) :=
  HEq.refl _

/-! ## `Term.subst_id_HEq` closed-context cases.

Constructors whose subterms live in the same context as the parent
(no `TermSubst.lift`).  Each takes per-subterm HEq IHs and combines
via the constructor-HEq congruences with `Ty.subst_id` bridges.
The cast-bearing cases (`appPi`, `pair`, `snd`) strip the outer
`Ty.subst0_subst_commute` cast via `eqRec_heq` first. -/

/-- Recursive HEq case of `Term.subst_id` for `app`. -/
theorem Term.subst_id_HEq_app
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T₁ T₂ : Ty level scope}
    (f : Term Γ (T₁.arrow T₂)) (a : Term Γ T₁)
    (ih_f : HEq (Term.subst (TermSubst.identity Γ) f) f)
    (ih_a : HEq (Term.subst (TermSubst.identity Γ) a) a) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.app f a))
        (Term.app (context := Γ) f a) := by
  show HEq (Term.app (Term.subst (TermSubst.identity Γ) f)
                     (Term.subst (TermSubst.identity Γ) a))
           (Term.app f a)
  exact Term.app_HEq_congr (Ty.subst_id T₁) (Ty.subst_id T₂)
    _ _ ih_f _ _ ih_a

/-- Recursive HEq case of `Term.subst_id` for `fst`. -/
theorem Term.subst_id_HEq_fst
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first : Ty level scope} {second : Ty level (scope + 1)}
    (p : Term Γ (Ty.sigmaTy first second))
    (ih_p : HEq (Term.subst (TermSubst.identity Γ) p) p) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.fst p))
        (Term.fst (context := Γ) p) := by
  show HEq (Term.fst (Term.subst (TermSubst.identity Γ) p))
           (Term.fst p)
  apply Term.fst_HEq_congr (Ty.subst_id first)
    ((Ty.subst_congr Subst.lift_identity_equiv second).trans
     (Ty.subst_id second))
  exact ih_p

/-- Recursive HEq case of `Term.subst_id` for `boolElim`. -/
theorem Term.subst_id_HEq_boolElim
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} {result : Ty level scope}
    (s : Term Γ Ty.bool) (t : Term Γ result) (e : Term Γ result)
    (ih_s : HEq (Term.subst (TermSubst.identity Γ) s) s)
    (ih_t : HEq (Term.subst (TermSubst.identity Γ) t) t)
    (ih_e : HEq (Term.subst (TermSubst.identity Γ) e) e) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolElim s t e))
        (Term.boolElim (context := Γ) s t e) := by
  show HEq (Term.boolElim
            (Term.subst (TermSubst.identity Γ) s)
            (Term.subst (TermSubst.identity Γ) t)
            (Term.subst (TermSubst.identity Γ) e))
           (Term.boolElim s t e)
  apply Term.boolElim_HEq_congr (Ty.subst_id result)
    _ _ (eq_of_heq ih_s)
    _ _ ih_t
    _ _ ih_e

/-- Recursive HEq case of `Term.subst_id` for `appPi`.  The
substituted result carries a `Ty.subst0_subst_commute` cast on
the outside; `eqRec_heq` strips it before constructor congruence. -/
theorem Term.subst_id_HEq_appPi
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom : Ty level scope} {cod : Ty level (scope + 1)}
    (f : Term Γ (Ty.piTy dom cod)) (a : Term Γ dom)
    (ih_f : HEq (Term.subst (TermSubst.identity Γ) f) f)
    (ih_a : HEq (Term.subst (TermSubst.identity Γ) a) a) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.appPi f a))
        (Term.appPi (context := Γ) f a) := by
  show HEq
    ((Ty.subst0_subst_commute cod dom Subst.identity).symm ▸
      Term.appPi (Term.subst (TermSubst.identity Γ) f)
                 (Term.subst (TermSubst.identity Γ) a))
    (Term.appPi f a)
  apply HEq.trans (eqRec_heq _ _)
  exact Term.appPi_HEq_congr (Ty.subst_id dom)
    ((Ty.subst_congr Subst.lift_identity_equiv cod).trans
     (Ty.subst_id cod))
    _ _ ih_f _ _ ih_a

/-- Recursive HEq case of `Term.subst_id` for `pair`. -/
theorem Term.subst_id_HEq_pair
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first : Ty level scope} {second : Ty level (scope + 1)}
    (v : Term Γ first) (w : Term Γ (second.subst0 first))
    (ih_v : HEq (Term.subst (TermSubst.identity Γ) v) v)
    (ih_w : HEq (Term.subst (TermSubst.identity Γ) w) w) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.pair v w))
        (Term.pair (context := Γ) v w) := by
  show HEq
    (Term.pair (Term.subst (TermSubst.identity Γ) v)
      ((Ty.subst0_subst_commute second first Subst.identity) ▸
        (Term.subst (TermSubst.identity Γ) w)))
    (Term.pair v w)
  apply Term.pair_HEq_congr (Ty.subst_id first)
    ((Ty.subst_congr Subst.lift_identity_equiv second).trans
     (Ty.subst_id second))
    _ _ ih_v
  apply HEq.trans (eqRec_heq _ _)
  exact ih_w

/-- Recursive HEq case of `Term.subst_id` for `snd`. -/
theorem Term.subst_id_HEq_snd
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first : Ty level scope} {second : Ty level (scope + 1)}
    (p : Term Γ (Ty.sigmaTy first second))
    (ih_p : HEq (Term.subst (TermSubst.identity Γ) p) p) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.snd p))
        (Term.snd (context := Γ) p) := by
  show HEq
    ((Ty.subst0_subst_commute second first Subst.identity).symm ▸
      Term.snd (Term.subst (TermSubst.identity Γ) p))
    (Term.snd p)
  apply HEq.trans (eqRec_heq _ _)
  apply Term.snd_HEq_congr (Ty.subst_id first)
    ((Ty.subst_congr Subst.lift_identity_equiv second).trans
     (Ty.subst_id second))
  exact ih_p


end LeanFX.Syntax
