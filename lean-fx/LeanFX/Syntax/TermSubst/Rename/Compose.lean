import LeanFX.Syntax.TermSubst.Rename.Identity

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-rename composition. -/

/-- Composition of term-level renamings.  Position-equality witness
chains the two `TermRenaming`s through `Ty.rename_compose`. -/
theorem TermRenaming.compose
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    TermRenaming Γ₁ Γ₃ (Renaming.compose ρ₁ ρ₂) := fun i => by
  show varType Γ₃ (ρ₂ (ρ₁ i))
     = (varType Γ₁ i).rename (Renaming.compose ρ₁ ρ₂)
  rw [ρt₂ (ρ₁ i)]
  rw [ρt₁ i]
  exact Ty.rename_compose (varType Γ₁ i) ρ₁ ρ₂

/-- Push a propositional type-cast on the input of `Term.rename ρt`
out to an HEq.  Mirror of `Term.subst_HEq_cast_input` and
`Term.weaken_HEq_cast_input`. -/
theorem Term.rename_HEq_cast_input
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    {T₁ T₂ : Ty level scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.rename ρt (h ▸ t)) (Term.rename ρt t) := by
  cases h
  rfl

/-! ## `Term.rename_compose_HEq`.

Double-rename equals single-rename by composed rawRenaming, modulo HEq.
The two sides have types `Term Γ₃ ((T.rename ρ₁).rename ρ₂)` and
`Term Γ₃ (T.rename (Renaming.compose ρ₁ ρ₂))`; these agree
propositionally by `Ty.rename_compose`.  Pattern-matched structural
induction on the term.

Binder cases bridge `TermRenaming.lift (compose ρt₁ ρt₂) dom` against
`compose (lift ρt₁ dom) (lift ρt₂ (dom.rename ρ₁))` via
`Term.rename_HEq_pointwise` over `Renaming.lift_compose_equiv`. -/
theorem Term.rename_compose_HEq
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    {T : Ty level scope₁} → (t : Term Γ₁ T) →
      HEq (Term.rename ρt₂ (Term.rename ρt₁ t))
          (Term.rename (TermRenaming.compose ρt₁ ρt₂) t)
  | _, .var i => by
    -- LHS: Term.rename ρt₂ ((ρt₁ i) ▸ Term.var (ρ₁ i))
    -- Push the inner cast through Term.rename ρt₂.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂ (ρt₁ i) (Term.var (ρ₁ i)))
    -- Now: Term.rename ρt₂ (Term.var (ρ₁ i))
    --    = (ρt₂ (ρ₁ i)) ▸ Term.var (ρ₂ (ρ₁ i))
    -- RHS: ((compose ρt₁ ρt₂) i) ▸ Term.var ((Renaming.compose ρ₁ ρ₂) i)
    --    where (Renaming.compose ρ₁ ρ₂) i ≡ ρ₂ (ρ₁ i) definitionally.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename ρt₂ (Term.rename ρt₁ f))
                (Term.rename ρt₂ (Term.rename ρt₁ a)))
      (Term.app (Term.rename (TermRenaming.compose ρt₁ ρt₂) f)
                (Term.rename (TermRenaming.compose ρt₁ ρt₂) a))
    exact Term.app_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      (Ty.rename_compose cod ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ f)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename ρt₂ (Term.rename ρt₁ p)))
      (Term.fst (Term.rename (TermRenaming.compose ρt₁ ρt₂) p))
    apply Term.fst_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
    exact Term.rename_compose_HEq ρt₁ ρt₂ p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename ρt₂ (Term.rename ρt₁ s))
                     (Term.rename ρt₂ (Term.rename ρt₁ t))
                     (Term.rename ρt₂ (Term.rename ρt₁ e)))
      (Term.boolElim (Term.rename (TermRenaming.compose ρt₁ ρt₂) s)
                     (Term.rename (TermRenaming.compose ρt₁ ρt₂) t)
                     (Term.rename (TermRenaming.compose ρt₁ ρt₂) e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ s))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ t)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- Outer-cast peeling on each side, then constructor congruence.
    -- LHS: Term.rename ρt₂ ((cast₁).symm ▸ Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a))
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute cod dom ρ₁).symm
        (Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a)))
    -- Now: Term.rename ρt₂ (Term.appPi (...) (...))
    -- Strip outer cast from Term.rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and process RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      ((Ty.rename_compose cod ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) cod))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ f)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    -- Outer Term.pair has no cast; secondVal carries nested casts on both sides.
    apply Term.pair_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
    -- LHS secondVal: cast_outer ▸ Term.rename ρt₂ (cast_inner ▸ Term.rename ρt₁ w)
    -- RHS secondVal: cast_compose ▸ Term.rename (compose ρt₁ ρt₂) w
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.rename ρt₂.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute second first ρ₁)
        (Term.rename ρt₁ w))
    -- Use IH on w.
    apply HEq.trans (Term.rename_compose_HEq ρt₁ ρt₂ w)
    -- Strip outer cast on RHS.
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    -- Mirror of fst plus outer cast strips on each side.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute second first ρ₁).symm
        (Term.snd (Term.rename ρt₁ p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body: cast₂ ▸ rename (lift ρt₂ (dom.rename ρ₁)) (cast₁ ▸ rename (lift ρt₁ dom) body)
    -- RHS body: cast_compose ▸ rename (lift (compose ρt₁ ρt₂) dom) body
    apply Term.lam_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      (Ty.rename_compose cod ρ₁ ρ₂)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift ρt₂ (dom.rename ρ₁)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift ρt₂ (dom.rename ρ₁))
        (Ty.rename_weaken_commute cod ρ₁)
        (Term.rename (TermRenaming.lift ρt₁ dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)) body)
    -- Bridge compose-of-lifts to lift-of-compose via rename_HEq_pointwise.
    apply HEq.symm
    -- Strip outer cast on RHS (now in symm orientation, so it's the LHS goal).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.rename_HEq_pointwise
      (congrArg Γ₃.cons (Ty.rename_compose dom ρ₁ ρ₂))
      (TermRenaming.compose
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)))
      (TermRenaming.lift (TermRenaming.compose ρt₁ ρt₂) dom)
      (Renaming.lift_compose_equiv ρ₁ ρ₂)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    -- LHS body: rename (lift ρt₂ (dom.rename ρ₁)) (rename (lift ρt₁ dom) body)
    --          (no outer casts because Term.rename's lamPi clause has no cast)
    -- RHS body: rename (lift (compose ρt₁ ρt₂) dom) body
    apply Term.lamPi_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      ((Ty.rename_compose cod ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) cod))
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)) body)
    exact Term.rename_HEq_pointwise
      (congrArg Γ₃.cons (Ty.rename_compose dom ρ₁ ρ₂))
      (TermRenaming.compose
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)))
      (TermRenaming.lift (TermRenaming.compose ρt₁ ρt₂) dom)
      (Renaming.lift_compose_equiv ρ₁ ρ₂)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_compose_HEq ρt₁ ρt₂ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename ρt₂ (Term.rename ρt₁ scrutinee))
        (Term.rename ρt₂ (Term.rename ρt₁ zeroBranch))
        (Term.rename ρt₂ (Term.rename ρt₁ succBranch)))
      (Term.natElim
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) scrutinee)
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) zeroBranch)
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ zeroBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ zeroBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_compose elem ρ₁ ρ₂)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ hd)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ nilBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_compose elem ρ₁ ρ₂)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ noneBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ leftBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_compose carrier ρ₁ ρ₂)
      (RawTerm.rename_compose rawTerm ρ₁ ρ₂)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_compose carrier ρ₁ ρ₂)
      (RawTerm.rename_compose leftEnd ρ₁ ρ₂)
      (RawTerm.rename_compose rightEnd ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ baseCase)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ witness)


end LeanFX.Syntax
