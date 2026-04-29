import LeanFX.Syntax.TypedTerm

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-level substitution.

`TermSubst Γ Δ σ` supplies for each `i : Fin scope` a term in `Δ`
whose type is `(varType Γ i).subst σ`.  `TermSubst.lift` extends
under a binder by `Term.weaken`-ing predecessor terms into the
extended target. -/

/-- A term-level substitution maps each position of `Γ` to a term in
`Δ` whose type is `varType Γ` substituted by the underlying type-level
σ.  The type-equality is computed via `Ty.subst`. -/
abbrev TermSubst {m : Mode} {level scope scope' : Nat}
    (Γ : Ctx m level scope) (Δ : Ctx m level scope')
    (σ : Subst level scope scope') : Type :=
  ∀ (i : Fin scope), Term Δ ((varType Γ i).subst σ)

/-- Lift a term-level substitution under a binder.  Position 0 in the
extended source context maps to `Term.var ⟨0, _⟩` in the extended
target (cast through `Ty.subst_weaken_commute`); positions `k + 1`
weaken the predecessor's image into the extended target context. -/
def TermSubst.lift {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'}
    (σt : TermSubst Γ Δ σ) (newType : Ty level scope) :
    TermSubst (Γ.cons newType) (Δ.cons (newType.subst σ)) σ.lift :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        (Ty.subst_weaken_commute newType σ).symm ▸
          (Term.var ⟨0, Nat.zero_lt_succ _⟩ :
            Term (Δ.cons (newType.subst σ)) (newType.subst σ).weaken)
    | ⟨k + 1, h⟩ =>
        (Ty.subst_weaken_commute
            (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩) σ).symm ▸
          Term.weaken (newType.subst σ)
            (σt ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Weakening then substituting with the singleton substitution is
the identity on `Ty`.  The shift renames every original variable up
by one, then `Subst.singleton X` at position `k + 1` returns the
`Ty.tyVar k` corresponding to the original position — i.e., the
substitution acts as the identity. -/
theorem Ty.weaken_subst_singleton {level scope : Nat}
    (T : Ty level scope) (X : Ty level scope) :
    T.weaken.subst (Subst.singleton X) = T := by
  show (T.rename Renaming.weaken).subst (Subst.singleton X) = T
  have hRSC :=
    Ty.rename_subst_commute T Renaming.weaken (Subst.singleton X)
  have hPointwise :
      Subst.equiv
        (Subst.precompose Renaming.weaken (Subst.singleton X))
        Subst.identity :=
    Subst.precompose_weaken_singleton_equiv_identity X
  have hCong := Ty.subst_congr hPointwise T
  have hId := Ty.subst_id T
  exact hRSC.trans (hCong.trans hId)

/-- The single-substituent term substitution: position 0 maps to
`arg`, positions `k + 1` map to `Term.var ⟨k, _⟩` in the original
context (variable shifts down by one because the outer scope has one
fewer binder than the input).  The underlying type-level σ is
`Subst.singleton T_arg` for the argument's type `T_arg`.  Both Fin
cases require a cast through `Ty.weaken_subst_singleton` to align the
substituted-varType form. -/
def TermSubst.singleton {m : Mode} {level scope : Nat}
    {Γ : Ctx m level scope} {T_arg : Ty level scope}
    (arg : Term Γ T_arg) :
    TermSubst (Γ.cons T_arg) Γ (Subst.singleton T_arg) :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        (Ty.weaken_subst_singleton T_arg T_arg).symm ▸ arg
    | ⟨k + 1, h⟩ =>
        (Ty.weaken_subst_singleton
            (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩) T_arg).symm ▸
          Term.var ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-! ## Substitution-substitution commutativity.

`subst0` distributes through an outer subst by lifting the codomain's
substitution and substituting the substituted substituent.  Used by
`Term.subst`'s `appPi` / `pair` / `snd` cases to align result types. -/

/-- The pointwise equivalence underpinning `Ty.subst0_subst_commute`:
substituting then composing with σ equals lifting σ under the binder
then composing with the singleton-substituent (already substituted by
σ).  Both sides at position 0 evaluate to `(substituent).subst σ`;
at positions `k + 1`, both evaluate to `σ ⟨k, _⟩`. -/
theorem Subst.singleton_compose_equiv_lift_compose_singleton
    {level scope target : Nat}
    (substituent : Ty level scope) (σ : Subst level scope target) :
    Subst.equiv
      (Subst.compose (Subst.singleton substituent) σ)
      (Subst.compose σ.lift (Subst.singleton (substituent.subst σ))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨k + 1, h⟩  => by
          show (Ty.tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩).subst σ
             = ((σ ⟨k, Nat.lt_of_succ_lt_succ h⟩).rename Renaming.weaken).subst
                 (Subst.singleton (substituent.subst σ))
          have hRSC :=
            Ty.rename_subst_commute (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩)
              Renaming.weaken (Subst.singleton (substituent.subst σ))
          have hPointwise :
              Subst.equiv
                (Subst.precompose Renaming.weaken
                  (Subst.singleton (substituent.subst σ)))
                Subst.identity :=
            Subst.precompose_weaken_singleton_equiv_identity
              (substituent.subst σ)
          have hCong := Ty.subst_congr hPointwise
                          (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩)
          have hId := Ty.subst_id (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩)
          exact (hRSC.trans (hCong.trans hId)).symm)
    fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨k + 1, h⟩  =>
          (RawTerm.weaken_subst_dropNewest
            (σ.forRaw ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm

/-- The practical specialisation: substituting the outermost variable
then applying an outer substitution equals lifting the outer
substitution under the binder then substituting the substituted
substituent. -/
theorem Ty.subst0_subst_commute {level scope target : Nat}
    (T : Ty level (scope + 1)) (X : Ty level scope) (σ : Subst level scope target) :
    (T.subst0 X).subst σ
      = (T.subst σ.lift).subst0 (X.subst σ) := by
  show (T.subst (Subst.singleton X)).subst σ
     = (T.subst σ.lift).subst (Subst.singleton (X.subst σ))
  have hLeft := Ty.subst_compose T (Subst.singleton X) σ
  have hRight := Ty.subst_compose T σ.lift (Subst.singleton (X.subst σ))
  have hCong := Ty.subst_congr
    (Subst.singleton_compose_equiv_lift_compose_singleton X σ) T
  exact hLeft.trans (hCong.trans hRight.symm)

/-- **Term-level substitution** — apply a term-level substitution `σt`
(and the underlying type-level σ) to a `Term`, producing a `Term` in
the target context with the substituted type.

The variable case looks up the substituent term via `σt`; the binder
cases (`lam`, `lamPi`) use `TermSubst.lift` to extend σt under the new
binder and align body types via `Ty.subst_weaken_commute`; the
projection-laden cases (`appPi`, `pair`, `snd`) use
`Ty.subst0_subst_commute` to align `subst0`-shaped result types. -/
def Term.subst {m scope scope'}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'}
    (σt : TermSubst Γ Δ σ) :
    {T : Ty level scope} → Term Γ T → Term Δ (T.subst σ)
  | _, .var i      => σt i
  | _, .unit       => Term.unit
  | _, .lam (codomainType := codomainType) body =>
      Term.lam (codomainType := codomainType.subst σ)
        ((Ty.subst_weaken_commute codomainType σ) ▸
          (Term.subst (TermSubst.lift σt _) body))
  | _, .app f a    =>
      Term.app (Term.subst σt f) (Term.subst σt a)
  | _, .lamPi (domainType := domainType) body =>
      Term.lamPi (Term.subst (TermSubst.lift σt domainType) body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType) f a =>
      (Ty.subst0_subst_commute codomainType domainType σ).symm ▸
        Term.appPi (Term.subst σt f) (Term.subst σt a)
  | _, .pair (firstType := firstType) (secondType := secondType)
             firstVal secondVal =>
      Term.pair (Term.subst σt firstVal)
        ((Ty.subst0_subst_commute secondType firstType σ) ▸
          (Term.subst σt secondVal))
  | _, .fst p      => Term.fst (Term.subst σt p)
  | _, .snd (firstType := firstType) (secondType := secondType) p =>
      (Ty.subst0_subst_commute secondType firstType σ).symm ▸
        Term.snd (Term.subst σt p)
  | _, .boolTrue   => Term.boolTrue
  | _, .boolFalse  => Term.boolFalse
  | _, .boolElim scrutinee thenBr elseBr =>
      Term.boolElim (Term.subst σt scrutinee)
                    (Term.subst σt thenBr)
                    (Term.subst σt elseBr)
  | _, .natZero      => Term.natZero
  | _, .natSucc pred => Term.natSucc (Term.subst σt pred)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.subst σt scrutinee)
                  (Term.subst σt zeroBranch)
                  (Term.subst σt succBranch)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.subst σt scrutinee)
                   (Term.subst σt zeroBranch)
                   (Term.subst σt succBranch)
  | _, .listNil       => Term.listNil
  | _, .listCons hd tl =>
      Term.listCons (Term.subst σt hd) (Term.subst σt tl)
  | _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.subst σt scrutinee)
                    (Term.subst σt nilBranch)
                    (Term.subst σt consBranch)
  | _, .optionNone     => Term.optionNone
  | _, .optionSome v   => Term.optionSome (Term.subst σt v)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.subst σt scrutinee)
                       (Term.subst σt noneBranch)
                       (Term.subst σt someBranch)
  | _, .eitherInl v    => Term.eitherInl (Term.subst σt v)
  | _, .eitherInr v    => Term.eitherInr (Term.subst σt v)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.subst σt scrutinee)
                       (Term.subst σt leftBranch)
                       (Term.subst σt rightBranch)
  | _, .refl rawTerm => Term.refl (rawTerm.subst σ.forRaw)
  | _, .idJ baseCase witness =>
      Term.idJ (Term.subst σt baseCase) (Term.subst σt witness)

/-- **Single-variable term substitution** — substitute `arg` for var 0
in `body`.  Used by β-reduction.  Result type is computed via
`Ty.subst0` at the type level, matching `Term.appPi`'s result-type
shape exactly. -/
def Term.subst0 {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T_arg : Ty level scope} {T_body : Ty level (scope + 1)}
    (body : Term (Γ.cons T_arg) T_body) (arg : Term Γ T_arg) :
    Term Γ (T_body.subst0 T_arg) :=
  Term.subst (TermSubst.singleton arg) body

/-! ## Categorical structure on TermSubst.

The term-level analogues of `Subst.identity` and `Subst.compose`,
witnessing the same enriched-category structure at the term level.
Functoriality theorems (`Term.subst_id`, `Term.subst_compose`) need
dependent-cast wrangling because `Term.subst σt t : Term Δ (T.subst
σ)` is not definitionally `Term Δ T` even when `σ = Subst.identity`. -/

/-- Identity term-substitution: each position `i` maps to `Term.var i`,
cast through `Ty.subst_id` to live at `(varType Γ i).subst Subst.identity`. -/
def TermSubst.identity {m : Mode} {level scope : Nat} (Γ : Ctx m level scope) :
    TermSubst Γ Γ Subst.identity := fun i =>
  (Ty.subst_id (varType Γ i)).symm ▸ Term.var i

/-- Compose two term-substitutions: apply `σt₁` then substitute the
result by `σt₂`, casting through `Ty.subst_compose`. -/
def TermSubst.compose {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂) :
    TermSubst Γ₁ Γ₃ (Subst.compose σ₁ σ₂) := fun i =>
  Ty.subst_compose (varType Γ₁ i) σ₁ σ₂ ▸ Term.subst σt₂ (σt₁ i)

/-! ## HEq bridge helpers for term-substitution functoriality.

`Term.subst_id` and `Term.subst_compose` need to bridge terms whose
types differ propositionally (e.g. `Term Γ (T.subst Subst.identity)`
vs `Term Γ T`).  HEq is the right notion of equality; the lemmas
below collapse outer casts and align cons-extended contexts. -/

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
  cases h_T₁
  cases h_T₂
  cases h_f
  cases h_a
  rfl

/-- HEq congruence for `Term.lam`. -/
theorem Term.lam_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level scope} (h_cod : cod₁ = cod₂)
    (body₁ : Term (Γ.cons dom₁) cod₁.weaken)
    (body₂ : Term (Γ.cons dom₂) cod₂.weaken)
    (h_body : HEq body₁ body₂) :
    HEq (Term.lam body₁) (Term.lam body₂) := by
  cases h_dom
  cases h_cod
  cases h_body
  rfl

/-- HEq congruence for `Term.lamPi`. -/
theorem Term.lamPi_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level (scope + 1)} (h_cod : cod₁ = cod₂)
    (body₁ : Term (Γ.cons dom₁) cod₁)
    (body₂ : Term (Γ.cons dom₂) cod₂)
    (h_body : HEq body₁ body₂) :
    HEq (Term.lamPi body₁) (Term.lamPi body₂) := by
  cases h_dom
  cases h_cod
  cases h_body
  rfl

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
  cases h_dom
  cases h_cod
  cases h_f
  cases h_a
  rfl

/-- HEq congruence for `Term.pair`. -/
theorem Term.pair_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (v₁ : Term Γ first₁) (v₂ : Term Γ first₂) (h_v : HEq v₁ v₂)
    (w₁ : Term Γ (second₁.subst0 first₁))
    (w₂ : Term Γ (second₂.subst0 first₂)) (h_w : HEq w₁ w₂) :
    HEq (Term.pair v₁ w₁) (Term.pair v₂ w₂) := by
  cases h_first
  cases h_second
  cases h_v
  cases h_w
  rfl

/-- HEq congruence for `Term.fst`. -/
theorem Term.fst_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.fst p₁) (Term.fst p₂) := by
  cases h_first
  cases h_second
  cases h_p
  rfl

/-- HEq congruence for `Term.snd`. -/
theorem Term.snd_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.snd p₁) (Term.snd p₂) := by
  cases h_first
  cases h_second
  cases h_p
  rfl

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
  cases h_new
  cases h_T
  cases h_t
  rfl

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.bool) (h_s : s₁ = s₂)
    (t₁ : Term Γ result₁) (t₂ : Term Γ result₂) (h_t : HEq t₁ t₂)
    (e₁ : Term Γ result₁) (e₂ : Term Γ result₂) (h_e : HEq e₁ e₂) :
    HEq (Term.boolElim s₁ t₁ e₁) (Term.boolElim s₂ t₂ e₂) := by
  cases h_result
  cases h_s
  cases h_t
  cases h_e
  rfl

/-- HEq congruence for `Term.natSucc`.  natSucc has no type-level
indices that vary, so this collapses to plain equality of the
predecessor-term — we accept HEq for symmetry with the other
constructor congruences. -/
theorem Term.natSucc_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (p₁ p₂ : Term Γ Ty.nat) (h_p : HEq p₁ p₂) :
    HEq (Term.natSucc p₁) (Term.natSucc p₂) := by
  cases h_p
  rfl

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
  cases h_result
  cases h_s
  cases h_z
  cases h_f
  rfl

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
  cases h_result
  cases h_s
  cases h_z
  cases h_f
  rfl

/-- HEq congruence for `Term.listNil`.  Only the elementType varies
between sides; no value arguments. -/
theorem Term.listNil_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂) :
    HEq (Term.listNil (context := Γ) (elementType := elem₁))
        (Term.listNil (context := Γ) (elementType := elem₂)) := by
  cases h_elem
  rfl

/-- HEq congruence for `Term.listCons`. -/
theorem Term.listCons_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    (h₁ : Term Γ elem₁) (h₂ : Term Γ elem₂) (h_h : HEq h₁ h₂)
    (t₁ : Term Γ (Ty.list elem₁)) (t₂ : Term Γ (Ty.list elem₂))
    (h_t : HEq t₁ t₂) :
    HEq (Term.listCons h₁ t₁) (Term.listCons h₂ t₂) := by
  cases h_elem
  cases h_h
  cases h_t
  rfl

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
  cases h_elem
  cases h_result
  cases h_s
  cases h_n
  cases h_c
  rfl

/-- HEq congruence for `Term.optionNone` — only elementType varies. -/
theorem Term.optionNone_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂) :
    HEq (Term.optionNone (context := Γ) (elementType := elem₁))
        (Term.optionNone (context := Γ) (elementType := elem₂)) := by
  cases h_elem
  rfl

/-- HEq congruence for `Term.optionSome`. -/
theorem Term.optionSome_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    (v₁ : Term Γ elem₁) (v₂ : Term Γ elem₂) (h_v : HEq v₁ v₂) :
    HEq (Term.optionSome v₁) (Term.optionSome v₂) := by
  cases h_elem
  cases h_v
  rfl

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
  cases h_elem
  cases h_result
  cases h_s
  cases h_n
  cases h_sm
  rfl

/-- HEq congruence for `Term.eitherInl`.  Both `leftType` and
`rightType` may vary; only the `leftType` value is supplied. -/
theorem Term.eitherInl_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    (v₁ : Term Γ left₁) (v₂ : Term Γ left₂) (h_v : HEq v₁ v₂) :
    HEq (Term.eitherInl (rightType := right₁) v₁)
        (Term.eitherInl (rightType := right₂) v₂) := by
  cases h_left
  cases h_right
  cases h_v
  rfl

/-- HEq congruence for `Term.eitherInr`.  Symmetric to `eitherInl_HEq_congr`. -/
theorem Term.eitherInr_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    (v₁ : Term Γ right₁) (v₂ : Term Γ right₂) (h_v : HEq v₁ v₂) :
    HEq (Term.eitherInr (leftType := left₁) v₁)
        (Term.eitherInr (leftType := left₂) v₂) := by
  cases h_left
  cases h_right
  cases h_v
  rfl

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
  cases h_left
  cases h_right
  cases h_result
  cases h_s
  cases h_lb
  cases h_rb
  rfl

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
  cases h_carrier
  cases h_rawTerm
  rfl

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
  cases h_carrier
  cases h_leftEnd
  cases h_rightEnd
  cases h_result
  cases h_base
  cases h_witness
  rfl

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

/-! ## `TermSubst.lift_HEq_pointwise`.

Pointwise HEq for the lifts of two TermSubsts that are pointwise HEq
themselves (and whose underlying Substs are pointwise equal).  Used
by the binder cases of `Term.subst_HEq_pointwise` to extend the
hypothesis under each new binder. -/
theorem TermSubst.lift_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ₁ σ₂ : Subst level scope scope'}
    (σt₁ : TermSubst Γ Δ σ₁) (σt₂ : TermSubst Γ Δ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i))
    (newType : Ty level scope) :
    ∀ i, HEq (TermSubst.lift σt₁ newType i)
             (TermSubst.lift σt₂ newType i) := by
  -- Bridging fact: newType.subst σ₁ = newType.subst σ₂.
  have h_new : newType.subst σ₁ = newType.subst σ₂ :=
    Ty.subst_congr h_subst newType
  intro i
  match i with
  | ⟨0, _⟩ =>
    -- LHS = (Ty.subst_weaken_commute newType σ₁).symm ▸
    --        Term.var (context := Δ.cons (newType.subst σ₁)) ⟨0, _⟩
    -- RHS = (Ty.subst_weaken_commute newType σ₂).symm ▸
    --        Term.var (context := Δ.cons (newType.subst σ₂)) ⟨0, _⟩
    -- Strip outer casts on both sides via eqRec_heq, bridge naked
    -- Term.var values via heq_var_across_ctx_eq + congrArg-cons.
    -- Note: Term.var lives at scope' + 1, so the Fin uses
    -- Nat.zero_lt_succ scope' (NOT the Fin destructure's h0 which
    -- is at scope + 1).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq (congrArg (Δ.cons) h_new)
        ⟨0, Nat.zero_lt_succ scope'⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) σ₁).symm ▸
    --        Term.weaken (newType.subst σ₁) (σt₁ ⟨k, _⟩)
    -- RHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) σ₂).symm ▸
    --        Term.weaken (newType.subst σ₂) (σt₂ ⟨k, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.weaken (newType.subst σ₂)
        (σt₂ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    · exact Term.weaken_HEq_congr h_new
        (Ty.subst_congr h_subst
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
        (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (σt₂ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (h_pointwise ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
    · exact (eqRec_heq _ _).symm

/-! ## `Term.subst_HEq_pointwise`.

Substitution respects pointwise HEq of TermSubsts.  The `h_ctx :
Δ₁ = Δ₂` parameter accommodates binder-case recursive calls where
`TermSubst.lift σt_i dom` lands in `Δ.cons (dom.subst σ_i)` —
same scope, different concrete contexts. -/
theorem Term.subst_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ₁ Δ₂ : Ctx m level scope'}
    (h_ctx : Δ₁ = Δ₂)
    {σ₁ σ₂ : Subst level scope scope'}
    (σt₁ : TermSubst Γ Δ₁ σ₁) (σt₂ : TermSubst Γ Δ₂ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i)) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst σt₁ t) (Term.subst σt₂ t)
  | _, .var i => h_pointwise i
  | _, .unit => by cases h_ctx; exact HEq.refl _
  | _, .app (domainType := T₁) (codomainType := T₂) f a => by
    cases h_ctx
    show HEq (Term.app (Term.subst σt₁ f) (Term.subst σt₁ a))
             (Term.app (Term.subst σt₂ f) (Term.subst σt₂ a))
    exact Term.app_HEq_congr
      (Ty.subst_congr h_subst T₁) (Ty.subst_congr h_subst T₂)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise f)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise a)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lam (codomainType := cod.subst σ₁)
        ((Ty.subst_weaken_commute cod σ₁) ▸
          (Term.subst (TermSubst.lift σt₁ dom) body)))
      (Term.lam (codomainType := cod.subst σ₂)
        ((Ty.subst_weaken_commute cod σ₂) ▸
          (Term.subst (TermSubst.lift σt₂ dom) body)))
    apply Term.lam_HEq_congr
      (Ty.subst_congr h_subst dom) (Ty.subst_congr h_subst cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Δ₁.cons (Ty.subst_congr h_subst dom))
        (TermSubst.lift σt₁ dom) (TermSubst.lift σt₂ dom)
        (Subst.lift_equiv h_subst)
        (TermSubst.lift_HEq_pointwise σt₁ σt₂ h_subst h_pointwise dom)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift σt₁ dom) body))
      (Term.lamPi (Term.subst (TermSubst.lift σt₂ dom) body))
    apply Term.lamPi_HEq_congr
      (Ty.subst_congr h_subst dom)
      (Ty.subst_congr (Subst.lift_equiv h_subst) cod)
    exact Term.subst_HEq_pointwise
      (congrArg Δ₁.cons (Ty.subst_congr h_subst dom))
      (TermSubst.lift σt₁ dom) (TermSubst.lift σt₂ dom)
      (Subst.lift_equiv h_subst)
      (TermSubst.lift_HEq_pointwise σt₁ σt₂ h_subst h_pointwise dom)
      body
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    cases h_ctx
    show HEq
      ((Ty.subst0_subst_commute cod dom σ₁).symm ▸
        Term.appPi (Term.subst σt₁ f) (Term.subst σt₁ a))
      ((Ty.subst0_subst_commute cod dom σ₂).symm ▸
        Term.appPi (Term.subst σt₂ f) (Term.subst σt₂ a))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.subst σt₂ f) (Term.subst σt₂ a))
    · exact Term.appPi_HEq_congr
        (Ty.subst_congr h_subst dom)
        (Ty.subst_congr (Subst.lift_equiv h_subst) cod)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise f)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise a)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := first) (secondType := second) v w => by
    cases h_ctx
    show HEq
      (Term.pair (Term.subst σt₁ v)
        ((Ty.subst0_subst_commute second first σ₁) ▸ (Term.subst σt₁ w)))
      (Term.pair (Term.subst σt₂ v)
        ((Ty.subst0_subst_commute second first σ₂) ▸ (Term.subst σt₂ w)))
    apply Term.pair_HEq_congr
      (Ty.subst_congr h_subst first)
      (Ty.subst_congr (Subst.lift_equiv h_subst) second)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise w)
    exact (eqRec_heq _ _).symm
  | _, .fst (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq (Term.fst (Term.subst σt₁ p)) (Term.fst (Term.subst σt₂ p))
    exact Term.fst_HEq_congr
      (Ty.subst_congr h_subst first)
      (Ty.subst_congr (Subst.lift_equiv h_subst) second)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise p)
  | _, .snd (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      ((Ty.subst0_subst_commute second first σ₁).symm ▸
        Term.snd (Term.subst σt₁ p))
      ((Ty.subst0_subst_commute second first σ₂).symm ▸
        Term.snd (Term.subst σt₂ p))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.subst σt₂ p))
    · exact Term.snd_HEq_congr
        (Ty.subst_congr h_subst first)
        (Ty.subst_congr (Subst.lift_equiv h_subst) second)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise p)
    · exact (eqRec_heq _ _).symm
  | _, .boolTrue => by cases h_ctx; exact HEq.refl _
  | _, .boolFalse => by cases h_ctx; exact HEq.refl _
  | _, .boolElim (resultType := result) s t e => by
    cases h_ctx
    show HEq
      (Term.boolElim (Term.subst σt₁ s) (Term.subst σt₁ t) (Term.subst σt₁ e))
      (Term.boolElim (Term.subst σt₂ s) (Term.subst σt₂ t) (Term.subst σt₂ e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise s))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise t)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise e)
  | _, .natZero => by cases h_ctx; exact HEq.refl _
  | _, .natSucc pred => by
    cases h_ctx
    show HEq (Term.natSucc (Term.subst σt₁ pred))
             (Term.natSucc (Term.subst σt₂ pred))
    exact Term.natSucc_HEq_congr _ _
      (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    show HEq
      (Term.natElim (Term.subst σt₁ scrutinee)
                    (Term.subst σt₁ zeroBranch)
                    (Term.subst σt₁ succBranch))
      (Term.natElim (Term.subst σt₂ scrutinee)
                    (Term.subst σt₂ zeroBranch)
                    (Term.subst σt₂ succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    exact Term.natRec_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise succBranch)
  | _, .listNil (elementType := elem) => by
    cases h_ctx
    exact Term.listNil_HEq_congr (Ty.subst_congr h_subst elem)
  | _, .listCons (elementType := elem) hd tl => by
    cases h_ctx
    show HEq (Term.listCons (Term.subst σt₁ hd) (Term.subst σt₁ tl))
             (Term.listCons (Term.subst σt₂ hd) (Term.subst σt₂ tl))
    exact Term.listCons_HEq_congr
      (Ty.subst_congr h_subst elem)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise hd)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch => by
    cases h_ctx
    show HEq
      (Term.listElim (Term.subst σt₁ scrutinee)
                     (Term.subst σt₁ nilBranch)
                     (Term.subst σt₁ consBranch))
      (Term.listElim (Term.subst σt₂ scrutinee)
                     (Term.subst σt₂ nilBranch)
                     (Term.subst σt₂ consBranch))
    exact Term.listElim_HEq_congr
      (Ty.subst_congr h_subst elem)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise nilBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise consBranch)
  | _, .optionNone (elementType := elem) => by
    cases h_ctx
    exact Term.optionNone_HEq_congr (Ty.subst_congr h_subst elem)
  | _, .optionSome (elementType := elem) v => by
    cases h_ctx
    show HEq (Term.optionSome (Term.subst σt₁ v))
             (Term.optionSome (Term.subst σt₂ v))
    exact Term.optionSome_HEq_congr
      (Ty.subst_congr h_subst elem)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch => by
    cases h_ctx
    show HEq
      (Term.optionMatch (Term.subst σt₁ scrutinee)
                        (Term.subst σt₁ noneBranch)
                        (Term.subst σt₁ someBranch))
      (Term.optionMatch (Term.subst σt₂ scrutinee)
                        (Term.subst σt₂ noneBranch)
                        (Term.subst σt₂ someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.subst_congr h_subst elem)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise noneBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInl_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInr_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch => by
    cases h_ctx
    exact Term.eitherMatch_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise leftBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise rightBranch)
  | _, .refl (carrier := carrier) rawTerm => by
    cases h_ctx
    exact Term.refl_HEq_congr
      (Ty.subst_congr h_subst carrier)
      (RawTerm.subst_congr (Subst.equiv_forRaw h_subst) rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness => by
    cases h_ctx
    exact Term.idJ_HEq_congr
      (Ty.subst_congr h_subst carrier)
      (RawTerm.subst_congr (Subst.equiv_forRaw h_subst) leftEnd)
      (RawTerm.subst_congr (Subst.equiv_forRaw h_subst) rightEnd)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise baseCase)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise witness)

/-! ## `Term.subst_id_HEq`.

Full HEq form of subst-by-identity.  Structural induction; binder
cases use `Term.subst_HEq_pointwise` to bridge
`TermSubst.lift (TermSubst.identity Γ)` to
`TermSubst.identity (Γ.cons _)` via `lift_identity_pointwise`. -/
theorem Term.subst_id_HEq {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst (TermSubst.identity Γ) t) t
  | _, .var i => Term.subst_id_HEq_var i
  | _, .unit => Term.subst_id_HEq_unit
  | _, .app f a =>
    Term.subst_id_HEq_app f a
      (Term.subst_id_HEq f) (Term.subst_id_HEq a)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lam (codomainType := cod.subst Subst.identity)
        ((Ty.subst_weaken_commute cod Subst.identity) ▸
          (Term.subst (TermSubst.lift (TermSubst.identity Γ) dom) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr (Ty.subst_id dom) (Ty.subst_id cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Γ.cons (Ty.subst_id dom))
        (TermSubst.lift (TermSubst.identity Γ) dom)
        (TermSubst.identity (Γ.cons dom))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise Γ dom)
        body)
    exact Term.subst_id_HEq body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift (TermSubst.identity Γ) dom) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr (Ty.subst_id dom)
      ((Ty.subst_congr Subst.lift_identity_equiv cod).trans
       (Ty.subst_id cod))
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Γ.cons (Ty.subst_id dom))
        (TermSubst.lift (TermSubst.identity Γ) dom)
        (TermSubst.identity (Γ.cons dom))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise Γ dom)
        body)
    exact Term.subst_id_HEq body
  | _, .appPi f a =>
    Term.subst_id_HEq_appPi f a
      (Term.subst_id_HEq f) (Term.subst_id_HEq a)
  | _, .pair v w =>
    Term.subst_id_HEq_pair v w
      (Term.subst_id_HEq v) (Term.subst_id_HEq w)
  | _, .fst p =>
    Term.subst_id_HEq_fst p (Term.subst_id_HEq p)
  | _, .snd p =>
    Term.subst_id_HEq_snd p (Term.subst_id_HEq p)
  | _, .boolTrue => Term.subst_id_HEq_boolTrue
  | _, .boolFalse => Term.subst_id_HEq_boolFalse
  | _, .boolElim s t e =>
    Term.subst_id_HEq_boolElim s t e
      (Term.subst_id_HEq s) (Term.subst_id_HEq t) (Term.subst_id_HEq e)
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_id_HEq pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim (Term.subst (TermSubst.identity Γ) scrutinee)
                    (Term.subst (TermSubst.identity Γ) zeroBranch)
                    (Term.subst (TermSubst.identity Γ) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.subst_id result)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_id result)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_id elem)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_id elem)
      _ _ (Term.subst_id_HEq hd)
      _ _ (Term.subst_id_HEq tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_id elem) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq nilBranch)
      _ _ (Term.subst_id_HEq consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_id elem)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_id elem)
      _ _ (Term.subst_id_HEq v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_id elem) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq noneBranch)
      _ _ (Term.subst_id_HEq someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT)
      _ _ (Term.subst_id_HEq v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT)
      _ _ (Term.subst_id_HEq v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq leftBranch)
      _ _ (Term.subst_id_HEq rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr (Ty.subst_id carrier) (RawTerm.subst_id rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_id carrier) (RawTerm.subst_id leftEnd) (RawTerm.subst_id rightEnd)
      (Ty.subst_id result)
      _ _ (Term.subst_id_HEq baseCase)
      _ _ (Term.subst_id_HEq witness)

/-! ## `Term.subst_id` (explicit-`▸` form).

Corollary of `Term.subst_id_HEq` + `eqRec_heq`. -/
theorem Term.subst_id {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T : Ty level scope} (t : Term Γ T) :
    (Ty.subst_id T) ▸ Term.subst (TermSubst.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.subst_id_HEq t))

/-! ## Cast-through-Term.subst HEq helper.

Pushes a type-cast on the input out through `Term.subst` so the
substitution's structural recursion can fire on the bare
constructor.  Bridge for `lift_compose_pointwise_zero` and the
cast-bearing closed-context commute cases. -/
theorem Term.subst_HEq_cast_input
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ)
    {T₁ T₂ : Ty level scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.subst σt (h ▸ t)) (Term.subst σt t) := by
  cases h
  rfl

/-! ## `TermSubst.lift_compose_pointwise` at position 0.

Lifting a composed term-substitution under a binder agrees HEq with
composing the two lifts on the freshly-bound variable.  The position-
`k+1` case requires `Term.subst_weaken_commute_HEq` (binder cases
deferred) and is shipped as a separate companion. -/
theorem TermSubst.lift_compose_pointwise_zero
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty level scope₁) :
    HEq
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) newType
        ⟨0, Nat.zero_lt_succ _⟩)
      (TermSubst.compose (σt₁.lift newType)
                          (σt₂.lift (newType.subst σ₁))
        ⟨0, Nat.zero_lt_succ _⟩) := by
  -- LHS = (Ty.subst_weaken_commute newType (Subst.compose σ₁ σ₂)).symm ▸
  --        Term.var (context := Γ₃.cons (newType.subst (Subst.compose σ₁ σ₂))) ⟨0, _⟩
  --
  -- RHS = Ty.subst_compose newType.weaken σ₁.lift σ₂.lift ▸
  --        Term.subst (σt₂.lift (newType.subst σ₁))
  --          ((Ty.subst_weaken_commute newType σ₁).symm ▸
  --            Term.var (context := Γ₂.cons (newType.subst σ₁)) ⟨0, _⟩)
  --
  -- Strip outer cast on LHS via eqRec_heq.
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩) RHS
  --
  -- Flip and strip outer cast on RHS too.
  apply HEq.symm
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.subst (σt₂.lift _) (cast ▸ Term.var ⟨0, _⟩))
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Push the inner cast out through Term.subst via v1.26 helper.
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (σt₂.lift (newType.subst σ₁))
      (Ty.subst_weaken_commute newType σ₁).symm
      (Term.var (context := Γ₂.cons (newType.subst σ₁))
        ⟨0, Nat.zero_lt_succ _⟩))
  -- Goal: HEq (Term.subst (σt₂.lift _) (Term.var ⟨0, _⟩))
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Term.subst σt (Term.var i) ≡ σt i (Term.subst's var arm).
  show HEq ((σt₂.lift (newType.subst σ₁)) ⟨0, Nat.zero_lt_succ _⟩) _
  -- (σt₂.lift X) ⟨0, _⟩ = (Ty.subst_weaken_commute X σ₂).symm ▸ Term.var ⟨0, _⟩
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.var (context := Γ₃.cons ((newType.subst σ₁).subst σ₂)) ⟨0, _⟩)
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Bridge via Ty.subst_compose newType σ₁ σ₂ at the context level.
  exact heq_var_across_ctx_eq
    (congrArg Γ₃.cons (Ty.subst_compose newType σ₁ σ₂))
    ⟨0, Nat.zero_lt_succ _⟩

/-! ## `Term.rename_HEq_pointwise`.

Two TermRenamings whose underlying Renamings agree pointwise produce
HEq results when applied to the same term.  The rawRenaming-side analogue
of `Term.subst_HEq_pointwise`.  The `h_ctx : Δ₁ = Δ₂` parameter
accommodates the binder cases, where `TermRenaming.lift ρt_i dom`
lands in `Δ_i.cons (dom.rename ρ_i)` — different cons-extensions
across i = 1, 2. -/
theorem Term.rename_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ₁ Δ₂ : Ctx m level scope'}
    (h_ctx : Δ₁ = Δ₂)
    {ρ₁ ρ₂ : Renaming scope scope'}
    (ρt₁ : TermRenaming Γ Δ₁ ρ₁) (ρt₂ : TermRenaming Γ Δ₂ ρ₂)
    (h_ρ : Renaming.equiv ρ₁ ρ₂) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename ρt₁ t) (Term.rename ρt₂ t)
  | _, .var i => by
    cases h_ctx
    -- Term.rename ρt₁ (Term.var i) = (ρt₁ i) ▸ Term.var (ρ₁ i)
    -- Term.rename ρt₂ (Term.var i) = (ρt₂ i) ▸ Term.var (ρ₂ i)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Goal: HEq (Term.var (ρ₁ i)) (Term.var (ρ₂ i))
    -- Use h_ρ i to align the Fin positions.
    rw [h_ρ i]
  | _, .unit => by cases h_ctx; exact HEq.refl _
  | _, .app f a => by
    cases h_ctx
    show HEq
      (Term.app (Term.rename ρt₁ f) (Term.rename ρt₁ a))
      (Term.app (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    exact Term.app_HEq_congr
      (Ty.rename_congr h_ρ _)
      (Ty.rename_congr h_ρ _)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ f)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      (Term.fst (Term.rename ρt₁ p))
      (Term.fst (Term.rename ρt₂ p))
    apply Term.fst_HEq_congr
      (Ty.rename_congr h_ρ first)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
    exact Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ p
  | _, .boolTrue => by cases h_ctx; exact HEq.refl _
  | _, .boolFalse => by cases h_ctx; exact HEq.refl _
  | _, .boolElim (resultType := result) s t e => by
    cases h_ctx
    show HEq
      (Term.boolElim (Term.rename ρt₁ s)
                     (Term.rename ρt₁ t)
                     (Term.rename ρt₁ e))
      (Term.boolElim (Term.rename ρt₂ s)
                     (Term.rename ρt₂ t)
                     (Term.rename ρt₂ e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ s))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ t)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    cases h_ctx
    show HEq
      ((Ty.subst0_rename_commute cod dom ρ₁).symm ▸
        Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a))
      ((Ty.subst0_rename_commute cod dom ρ₂).symm ▸
        Term.appPi (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    · exact Term.appPi_HEq_congr
        (Ty.rename_congr h_ρ dom)
        (Ty.rename_congr (Renaming.lift_equiv h_ρ) cod)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ f)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ a)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := first) (secondType := second) v w => by
    cases h_ctx
    show HEq
      (Term.pair (Term.rename ρt₁ v)
        ((Ty.subst0_rename_commute second first ρ₁) ▸
          (Term.rename ρt₁ w)))
      (Term.pair (Term.rename ρt₂ v)
        ((Ty.subst0_rename_commute second first ρ₂) ▸
          (Term.rename ρt₂ w)))
    apply Term.pair_HEq_congr
      (Ty.rename_congr h_ρ first)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      ((Ty.subst0_rename_commute second first ρ₁).symm ▸
        Term.snd (Term.rename ρt₁ p))
      ((Ty.subst0_rename_commute second first ρ₂).symm ▸
        Term.snd (Term.rename ρt₂ p))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.rename ρt₂ p))
    · exact Term.snd_HEq_congr
        (Ty.rename_congr h_ρ first)
        (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ p)
    · exact (eqRec_heq _ _).symm
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lam (codomainType := cod.rename ρ₁)
        ((Ty.rename_weaken_commute cod ρ₁) ▸
          (Term.rename (TermRenaming.lift ρt₁ dom) body)))
      (Term.lam (codomainType := cod.rename ρ₂)
        ((Ty.rename_weaken_commute cod ρ₂) ▸
          (Term.rename (TermRenaming.lift ρt₂ dom) body)))
    apply Term.lam_HEq_congr
      (Ty.rename_congr h_ρ dom) (Ty.rename_congr h_ρ cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg (·.cons (dom.rename ρ₁)) (rfl : Δ₁ = Δ₁) |>.trans
          (congrArg Δ₁.cons (Ty.rename_congr h_ρ dom)))
        (TermRenaming.lift ρt₁ dom)
        (TermRenaming.lift ρt₂ dom)
        (Renaming.lift_equiv h_ρ)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lamPi (Term.rename (TermRenaming.lift ρt₁ dom) body))
      (Term.lamPi (Term.rename (TermRenaming.lift ρt₂ dom) body))
    apply Term.lamPi_HEq_congr
      (Ty.rename_congr h_ρ dom)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) cod)
    exact Term.rename_HEq_pointwise
      (congrArg Δ₁.cons (Ty.rename_congr h_ρ dom))
      (TermRenaming.lift ρt₁ dom)
      (TermRenaming.lift ρt₂ dom)
      (Renaming.lift_equiv h_ρ)
      body
  | _, .natZero => by cases h_ctx; exact HEq.refl _
  | _, .natSucc pred => by
    cases h_ctx
    show HEq (Term.natSucc (Term.rename ρt₁ pred))
             (Term.natSucc (Term.rename ρt₂ pred))
    exact Term.natSucc_HEq_congr _ _
      (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    show HEq
      (Term.natElim (Term.rename ρt₁ scrutinee)
                    (Term.rename ρt₁ zeroBranch)
                    (Term.rename ρt₁ succBranch))
      (Term.natElim (Term.rename ρt₂ scrutinee)
                    (Term.rename ρt₂ zeroBranch)
                    (Term.rename ρt₂ succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    exact Term.natRec_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ succBranch)
  | _, .listNil (elementType := elem) => by
    cases h_ctx
    exact Term.listNil_HEq_congr (Ty.rename_congr h_ρ elem)
  | _, .listCons (elementType := elem) hd tl => by
    cases h_ctx
    show HEq (Term.listCons (Term.rename ρt₁ hd) (Term.rename ρt₁ tl))
             (Term.listCons (Term.rename ρt₂ hd) (Term.rename ρt₂ tl))
    exact Term.listCons_HEq_congr
      (Ty.rename_congr h_ρ elem)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ hd)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch => by
    cases h_ctx
    show HEq
      (Term.listElim (Term.rename ρt₁ scrutinee)
                     (Term.rename ρt₁ nilBranch)
                     (Term.rename ρt₁ consBranch))
      (Term.listElim (Term.rename ρt₂ scrutinee)
                     (Term.rename ρt₂ nilBranch)
                     (Term.rename ρt₂ consBranch))
    exact Term.listElim_HEq_congr
      (Ty.rename_congr h_ρ elem) (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ nilBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ consBranch)
  | _, .optionNone (elementType := elem) => by
    cases h_ctx
    exact Term.optionNone_HEq_congr (Ty.rename_congr h_ρ elem)
  | _, .optionSome (elementType := elem) v => by
    cases h_ctx
    show HEq (Term.optionSome (Term.rename ρt₁ v))
             (Term.optionSome (Term.rename ρt₂ v))
    exact Term.optionSome_HEq_congr
      (Ty.rename_congr h_ρ elem)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch => by
    cases h_ctx
    show HEq
      (Term.optionMatch (Term.rename ρt₁ scrutinee)
                        (Term.rename ρt₁ noneBranch)
                        (Term.rename ρt₁ someBranch))
      (Term.optionMatch (Term.rename ρt₂ scrutinee)
                        (Term.rename ρt₂ noneBranch)
                        (Term.rename ρt₂ someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.rename_congr h_ρ elem) (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ noneBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInl_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInr_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch => by
    cases h_ctx
    exact Term.eitherMatch_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ leftBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ rightBranch)
  | _, .refl (carrier := carrier) rawTerm => by
    cases h_ctx
    exact Term.refl_HEq_congr
      (Ty.rename_congr h_ρ carrier)
      (RawTerm.rename_congr h_ρ rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness => by
    cases h_ctx
    exact Term.idJ_HEq_congr
      (Ty.rename_congr h_ρ carrier)
      (RawTerm.rename_congr h_ρ leftEnd)
      (RawTerm.rename_congr h_ρ rightEnd)
      (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ baseCase)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ witness)

/-! ## `Term.rename_id_HEq`.

Renaming-side identity, the companion to `Term.subst_id_HEq` (v1.25):

  HEq (Term.rename (TermRenaming.identity Γ) t) t

Mirrors `Term.subst_id_HEq`'s 12-case structural induction.  Simpler
than the subst version because `TermRenaming` is `Prop`-valued —
the binder cases bridge `TermRenaming.lift (identity Γ) dom` against
`TermRenaming.identity (Γ.cons dom)` directly via
`Term.rename_HEq_pointwise` over `Renaming.lift_identity_equiv`,
without needing a separate `lift_identity_pointwise` stepping stone
(those existed for subst because TermSubst is Type-valued and pointwise
HEq on the witness is non-trivial).

Closed-context cases use the constructor HEq congruences plus
`Ty.rename_identity` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) strip outer casts via `eqRec_heq`. -/
theorem Term.rename_id_HEq {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename (TermRenaming.identity Γ) t) t
  | _, .var i => by
    -- LHS: (TermRenaming.identity Γ i) ▸ Term.var (Renaming.identity i)
    --    = (Ty.rename_identity (varType Γ i)).symm ▸ Term.var i
    show HEq ((Ty.rename_identity (varType Γ i)).symm ▸ Term.var i) (Term.var i)
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename (TermRenaming.identity Γ) f)
                (Term.rename (TermRenaming.identity Γ) a))
      (Term.app f a)
    exact Term.app_HEq_congr
      (Ty.rename_identity dom) (Ty.rename_identity cod)
      _ _ (Term.rename_id_HEq f)
      _ _ (Term.rename_id_HEq a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename (TermRenaming.identity Γ) p))
      (Term.fst p)
    apply Term.fst_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
    exact Term.rename_id_HEq p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename (TermRenaming.identity Γ) s)
                     (Term.rename (TermRenaming.identity Γ) t)
                     (Term.rename (TermRenaming.identity Γ) e))
      (Term.boolElim s t e)
    exact Term.boolElim_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq s))
      _ _ (Term.rename_id_HEq t)
      _ _ (Term.rename_id_HEq e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: (Ty.subst0_rename_commute cod dom Renaming.identity).symm ▸
    --        Term.appPi (Term.rename (identity Γ) f)
    --                   (Term.rename (identity Γ) a)
    show HEq
      ((Ty.subst0_rename_commute cod dom Renaming.identity).symm ▸
        Term.appPi (Term.rename (TermRenaming.identity Γ) f)
                   (Term.rename (TermRenaming.identity Γ) a))
      (Term.appPi f a)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.appPi_HEq_congr
      (Ty.rename_identity dom)
      ((Ty.rename_congr Renaming.lift_identity_equiv cod).trans
        (Ty.rename_identity cod))
      _ _ (Term.rename_id_HEq f)
      _ _ (Term.rename_id_HEq a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    show HEq
      (Term.pair (Term.rename (TermRenaming.identity Γ) v)
        ((Ty.subst0_rename_commute second first Renaming.identity) ▸
          (Term.rename (TermRenaming.identity Γ) w)))
      (Term.pair v w)
    apply Term.pair_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
      _ _ (Term.rename_id_HEq v)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.rename_id_HEq w
  | _, .snd (firstType := first) (secondType := second) p => by
    show HEq
      ((Ty.subst0_rename_commute second first Renaming.identity).symm ▸
        Term.snd (Term.rename (TermRenaming.identity Γ) p))
      (Term.snd p)
    apply HEq.trans (eqRec_heq _ _)
    apply Term.snd_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
    exact Term.rename_id_HEq p
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lam (codomainType := cod.rename Renaming.identity)
        ((Ty.rename_weaken_commute cod Renaming.identity) ▸
          (Term.rename (TermRenaming.lift (TermRenaming.identity Γ) dom) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr
      (Ty.rename_identity dom) (Ty.rename_identity cod)
    -- Strip outer cast.
    apply HEq.trans (eqRec_heq _ _)
    -- Bridge `TermRenaming.lift (identity Γ) dom` to
    -- `TermRenaming.identity (Γ.cons dom)` via rename_HEq_pointwise
    -- + Renaming.lift_identity_equiv, then recurse.
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg Γ.cons (Ty.rename_identity dom))
        (TermRenaming.lift (TermRenaming.identity Γ) dom)
        (TermRenaming.identity (Γ.cons dom))
        Renaming.lift_identity_equiv
        body)
    exact Term.rename_id_HEq body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lamPi
        (Term.rename (TermRenaming.lift (TermRenaming.identity Γ) dom) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr
      (Ty.rename_identity dom)
      ((Ty.rename_congr Renaming.lift_identity_equiv cod).trans
        (Ty.rename_identity cod))
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg Γ.cons (Ty.rename_identity dom))
        (TermRenaming.lift (TermRenaming.identity Γ) dom)
        (TermRenaming.identity (Γ.cons dom))
        Renaming.lift_identity_equiv
        body)
    exact Term.rename_id_HEq body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_id_HEq pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename (TermRenaming.identity Γ) scrutinee)
        (Term.rename (TermRenaming.identity Γ) zeroBranch)
        (Term.rename (TermRenaming.identity Γ) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_identity elem)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_identity elem)
      _ _ (Term.rename_id_HEq hd)
      _ _ (Term.rename_id_HEq tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_identity elem) (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq nilBranch)
      _ _ (Term.rename_id_HEq consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_identity elem)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_identity elem)
      _ _ (Term.rename_id_HEq v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_identity elem) (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq noneBranch)
      _ _ (Term.rename_id_HEq someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      _ _ (Term.rename_id_HEq v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      _ _ (Term.rename_id_HEq v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq leftBranch)
      _ _ (Term.rename_id_HEq rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_identity carrier)
      (RawTerm.rename_identity (level := level) rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_identity carrier)
      (RawTerm.rename_identity (level := level) leftEnd)
      (RawTerm.rename_identity (level := level) rightEnd)
      (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq baseCase)
      _ _ (Term.rename_id_HEq witness)

/-- The explicit-`▸` form of `Term.rename_id`: `eq_of_heq` plus an
outer cast strip.  Mirrors v1.25's `Term.subst_id` derivation from
`Term.subst_id_HEq`. -/
theorem Term.rename_id {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T : Ty level scope} (t : Term Γ T) :
    (Ty.rename_identity T) ▸ Term.rename (TermRenaming.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.rename_id_HEq t))

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

/-! ## `Term.rename_weaken_commute_HEq`.

Term-level analogue of `Ty.rename_weaken_commute`:

  Term.rename (lift ρt X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.rename ρ) (Term.rename ρt t)

Both sides factor into double-rename forms because `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`.  By v1.37 each side
collapses to a single rename along a composed TermRenaming; the two
underlying renamings (`compose Renaming.weaken ρ.lift` and `compose
ρ Renaming.weaken`) are pointwise equal — both reduce to `Fin.succ ∘ ρ`
modulo Fin proof-irrelevance.  The bridge is `Term.rename_HEq_pointwise`
(v1.36) over the trivial pointwise witness. -/
theorem Term.rename_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.rename (TermRenaming.lift ρt newType) (Term.weaken newType t))
        (Term.weaken (newType.rename ρ) (Term.rename ρt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.rename (TermRenaming.lift ρt newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.rename ρ))
      (Term.rename ρt t))
  -- Collapse LHS via v1.37 to a single composed rename.
  apply HEq.trans
    (Term.rename_compose_HEq
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType)
      t)
  -- Same for RHS, in symm orientation so it lands on the right of HEq.
  apply HEq.symm
  apply HEq.trans
    (Term.rename_compose_HEq
      ρt
      (TermRenaming.weaken Δ (newType.rename ρ))
      t)
  apply HEq.symm
  -- The two composed underlying renamings agree pointwise — `fun _ => rfl`.
  exact Term.rename_HEq_pointwise rfl
    (TermRenaming.compose
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType))
    (TermRenaming.compose ρt
      (TermRenaming.weaken Δ (newType.rename ρ)))
    (fun _ => rfl)
    t

/-! ## Term-level `renameAfter` and its lift commute.

`TermSubst.renameAfter σt ρt` composes a subst with a downstream
rename, producing a subst along `Subst.renameAfter σ ρ`.  The
companion lemma `lift_renameAfter_pointwise` says lifting then
composing agrees with composing then lifting (pointwise HEq) —
the term-level analogue of `Subst.lift_renameAfter_commute`. -/

/-- Term-level `renameAfter`: subst σt then rename ρt to a downstream
context.  At each position, applies σt then renames the result via
ρt; the result type is bridged via `Ty.subst_rename_commute`. -/
def TermSubst.renameAfter
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ) :
    TermSubst Γ Δ' (Subst.renameAfter σ ρ) := fun i =>
  Ty.subst_rename_commute (varType Γ i) σ ρ ▸ Term.rename ρt (σt i)

/-- Lifting commutes with `renameAfter` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets, bridged by `heq_var_across_ctx_eq`
over `Ty.subst_rename_commute newType σ ρ`.  Position `k + 1`
reduces both sides to a `Term.weaken` of `Term.rename ρt (σt k)`
with propositionally-distinct `newType` and inner type — the v1.38
`rename_weaken_commute_HEq` collapses LHS to weaken-of-rename, then
`Term.weaken_HEq_congr` bridges the two `Term.weaken` shapes. -/
theorem TermSubst.lift_renameAfter_pointwise
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ)
    (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.renameAfter (σt.lift newType)
          (ρt.lift (newType.subst σ)) i)
        ((TermSubst.renameAfter σt ρt).lift newType i) := by
  -- Bridge the cons-extended target contexts at the type level.
  have h_subst_rename :
      (newType.subst σ).rename ρ = newType.subst (Subst.renameAfter σ ρ) :=
    Ty.subst_rename_commute newType σ ρ
  have h_ctx :
      Δ'.cons ((newType.subst σ).rename ρ)
        = Δ'.cons (newType.subst (Subst.renameAfter σ ρ)) :=
    congrArg Δ'.cons h_subst_rename
  intro i
  match i with
  | ⟨0, h0⟩ =>
    -- LHS reduces to: outer_cast ▸ rename (ρt.lift (newType.subst σ))
    --                              (inner_cast.symm ▸ Term.var ⟨0, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (ρt.lift (newType.subst σ))
        (Ty.subst_weaken_commute newType σ).symm
        (Term.var (context := Δ.cons (newType.subst σ))
          ⟨0, Nat.zero_lt_succ _⟩))
    -- Now: rename (ρt.lift (newType.subst σ)) (Term.var ⟨0, _⟩)
    --    = ((ρt.lift (newType.subst σ)) ⟨0, _⟩) ▸ Term.var (ρ.lift ⟨0, _⟩)
    --    where ρ.lift ⟨0, _⟩ = ⟨0, _⟩ definitionally.
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.var ⟨0, _⟩ in Δ'.cons ((newType.subst σ).rename ρ)
    -- Naked RHS: Term.var ⟨0, _⟩ in Δ'.cons (newType.subst (Subst.renameAfter σ ρ))
    apply HEq.trans
      (heq_var_across_ctx_eq h_ctx ⟨0, Nat.zero_lt_succ _⟩)
    -- RHS = (Ty.subst_weaken_commute newType (Subst.renameAfter σ ρ)).symm
    --        ▸ Term.var ⟨0, _⟩
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = outer_cast ▸ rename (ρt.lift X)
    --                        (inner_cast.symm ▸ Term.weaken X (σt k'))
    -- where X = newType.subst σ, k' = ⟨k, Nat.lt_of_succ_lt_succ hk⟩.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (ρt.lift (newType.subst σ))
        (Ty.subst_weaken_commute
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ).symm
        (Term.weaken (newType.subst σ)
          (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))
    -- Now: rename (ρt.lift X) (Term.weaken X (σt k'))
    --    ≃HEq≃ Term.weaken (X.rename ρ) (Term.rename ρt (σt k'))    [by v1.38]
    apply HEq.trans
      (Term.rename_weaken_commute_HEq ρt (newType.subst σ)
        (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    -- Now LHS = Term.weaken ((newType.subst σ).rename ρ)
    --             (Term.rename ρt (σt ⟨k, _⟩))
    -- in target context Δ'.cons ((newType.subst σ).rename ρ).
    --
    -- RHS at k+1 = outer_cast ▸ Term.weaken (newType.subst (renameAfter σ ρ))
    --                              ((renameAfter σt ρt) ⟨k, _⟩)
    --             where (renameAfter σt ρt) ⟨k, _⟩
    --                   = inner_cast ▸ Term.rename ρt (σt ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Now: HEq RHS_naked LHS_naked, where
    --   RHS_naked = Term.weaken (newType.subst (renameAfter σ ρ))
    --                 (inner_cast ▸ Term.rename ρt (σt ⟨k, _⟩))
    --   LHS_naked = Term.weaken ((newType.subst σ).rename ρ)
    --                 (Term.rename ρt (σt ⟨k, _⟩))
    -- Bridge via Term.weaken_HEq_congr.
    apply HEq.symm
    -- Use the cast-input helper to push the inner cast on RHS through
    -- Term.weaken — but actually Term.weaken_HEq_congr handles both
    -- newType differences AND a per-side type-cast difference, so we
    -- just supply the HEq.
    exact Term.weaken_HEq_congr
      h_subst_rename
      (Ty.subst_rename_commute
        (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ ρ)
      (Term.rename ρt (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (_)
      (eqRec_heq _ _).symm

/-! ## Term-level `precompose` and its lift commute.

`TermSubst.precompose ρt σt'` composes a rename with a downstream
subst, producing a subst along `Subst.precompose ρ σ'`.  Companion
lemma `lift_precompose_pointwise` is the structural mirror of
`lift_renameAfter_pointwise` (v1.39). -/

/-- Term-level `precompose`: rename ρt to a Γ' source, then subst σt'.
At each position i, looks up σt' at the renamed position ρ i; the
result type is bridged via the TermRenaming's witness lifted by
`congrArg (·.subst σ')` and chained with `Ty.rename_subst_commute`. -/
def TermSubst.precompose
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ') :
    TermSubst Γ Δ (Subst.precompose ρ σ') := fun i =>
  let h_witness : (varType Γ' (ρ i)).subst σ'
                    = ((varType Γ i).rename ρ).subst σ' :=
    congrArg (·.subst σ') (ρt i)
  let h_commute : ((varType Γ i).rename ρ).subst σ'
                    = (varType Γ i).subst (Subst.precompose ρ σ') :=
    Ty.rename_subst_commute (varType Γ i) ρ σ'
  (h_witness.trans h_commute) ▸ σt' (ρ i)

/-- Lifting commutes with `precompose` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets bridged by `Ty.rename_subst_commute
newType ρ σ'`.  Position `k + 1` reduces both sides to `Term.weaken`
forms that `Term.weaken_HEq_congr` collapses. -/
theorem TermSubst.lift_precompose_pointwise
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ')
    (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.precompose (ρt.lift newType)
          (σt'.lift (newType.rename ρ)) i)
        ((TermSubst.precompose ρt σt').lift newType i) := by
  have h_rename_subst :
      (newType.rename ρ).subst σ' = newType.subst (Subst.precompose ρ σ') :=
    Ty.rename_subst_commute newType ρ σ'
  have h_ctx :
      Δ.cons ((newType.rename ρ).subst σ')
        = Δ.cons (newType.subst (Subst.precompose ρ σ')) :=
    congrArg Δ.cons h_rename_subst
  intro i
  match i with
  | ⟨0, _⟩ =>
    -- LHS: outer_witness_compose ▸ σt'.lift (newType.rename ρ) ((lift ρt newType) ⟨0, _⟩)
    -- (lift ρt newType) ⟨0, _⟩ = ⟨0, _⟩ definitionally; σt'.lift's 0 arm
    -- emits inner_cast.symm ▸ Term.var ⟨0, _⟩.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq h_ctx ⟨0, Nat.zero_lt_succ _⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS: outer_witness_compose ▸ σt'.lift (newType.rename ρ) (Fin.succ (ρ ⟨k, _⟩))
    --    = outer_witness_compose ▸ (inner_subst_weaken.symm ▸
    --        Term.weaken ((newType.rename ρ).subst σ') (σt' (ρ ⟨k, _⟩)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.weaken ((newType.rename ρ).subst σ') (σt' (ρ ⟨k, _⟩))
    -- RHS at k+1: outer ▸ Term.weaken (newType.subst (precompose ρ σ'))
    --                       ((precompose ρt σt') ⟨k, _⟩)
    -- where (precompose ρt σt') ⟨k, _⟩
    --     = (h_w.trans h_c) ▸ σt' (ρ ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.  The h_T equation chains
    -- `congrArg (·.subst σ') (ρt k')` (varType bridge from Γ' to Γ-renamed)
    -- with `Ty.rename_subst_commute` (rename-subst commute), matching the
    -- chain inside `TermSubst.precompose`'s definition.
    exact Term.weaken_HEq_congr
      h_rename_subst
      ((congrArg (·.subst σ')
          (ρt ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).trans
        (Ty.rename_subst_commute
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) ρ σ'))
      (σt' (ρ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (_)
      (eqRec_heq _ _).symm

/-! ## `Term.subst_rename_commute_HEq`.

Term-level analogue of `Ty.subst_rename_commute`:

  Term.rename ρt (Term.subst σt t)
    ≃HEq≃
  Term.subst (TermSubst.renameAfter σt ρt) t

12-case structural induction on the term.  Closed-context cases
combine the constructor HEq congruence (v1.21) with
`Ty.subst_rename_commute` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) peel outer casts via `eqRec_heq` and push inner
casts through `Term.{rename,subst}_HEq_cast_input` (v1.26 / v1.37).
Binder cases (lam/lamPi) use the IH at lifted TermSubst/TermRenaming,
then bridge `renameAfter (lift σt dom) (lift ρt (dom.subst σ))`
against `lift (renameAfter σt ρt) dom` via `Term.subst_HEq_pointwise`
(v1.24) over `TermSubst.lift_renameAfter_pointwise` (v1.39). -/
theorem Term.subst_rename_commute_HEq
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename ρt (Term.subst σt t))
          (Term.subst (TermSubst.renameAfter σt ρt) t)
  | _, .var i => by
    -- LHS: Term.rename ρt (σt i)
    -- RHS: (renameAfter σt ρt) i = (Ty.subst_rename_commute _ σ ρ) ▸ Term.rename ρt (σt i)
    show HEq (Term.rename ρt (σt i))
             ((Ty.subst_rename_commute (varType Γ i) σ ρ) ▸
                Term.rename ρt (σt i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename ρt (Term.subst σt f))
                (Term.rename ρt (Term.subst σt a)))
      (Term.app (Term.subst (TermSubst.renameAfter σt ρt) f)
                (Term.subst (TermSubst.renameAfter σt ρt) a))
    exact Term.app_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      (Ty.subst_rename_commute cod σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt f)
      _ _ (Term.subst_rename_commute_HEq σt ρt a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename ρt (Term.subst σt p)))
      (Term.fst (Term.subst (TermSubst.renameAfter σt ρt) p))
    apply Term.fst_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
    exact Term.subst_rename_commute_HEq σt ρt p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename ρt (Term.subst σt s))
                     (Term.rename ρt (Term.subst σt t))
                     (Term.rename ρt (Term.subst σt e)))
      (Term.boolElim (Term.subst (TermSubst.renameAfter σt ρt) s)
                     (Term.subst (TermSubst.renameAfter σt ρt) t)
                     (Term.subst (TermSubst.renameAfter σt ρt) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt s))
      _ _ (Term.subst_rename_commute_HEq σt ρt t)
      _ _ (Term.subst_rename_commute_HEq σt ρt e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.rename ρt (cast_subst.symm ▸ Term.appPi (subst f) (subst a))
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute cod dom σ).symm
        (Term.appPi (Term.subst σt f) (Term.subst σt a)))
    -- After helper: rename ρt (Term.appPi ...)
    -- Strip outer cast from rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- RHS side: (renameAfter σt ρt) on Term.appPi emits cast.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      ((Ty.subst_rename_commute cod σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) cod))
      _ _ (Term.subst_rename_commute_HEq σt ρt f)
      _ _ (Term.subst_rename_commute_HEq σt ρt a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
    -- LHS secondVal: cast_outer_LHS ▸ rename ρt (cast_inner_LHS ▸ subst σt w)
    -- RHS secondVal: cast_compose ▸ subst (renameAfter σt ρt) w
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute second first σ)
        (Term.subst σt w))
    apply HEq.trans (Term.subst_rename_commute_HEq σt ρt w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute second first σ).symm
        (Term.snd (Term.subst σt p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
      _ _ (Term.subst_rename_commute_HEq σt ρt p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body lives at scope+1; double-traversed via lift σt then lift ρt.
    -- RHS body uses lift (renameAfter σt ρt) dom, pointwise HEq to
    -- renameAfter (lift σt dom) (lift ρt (dom.subst σ)) via v1.39.
    apply Term.lam_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      (Ty.subst_rename_commute cod σ ρ)
    -- Strip outer cast on LHS (rename's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift ρt (dom.subst σ)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift ρt (dom.subst σ))
        (Ty.subst_weaken_commute cod σ)
        (Term.subst (TermSubst.lift σt dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ))
        body)
    -- Now LHS_naked = Term.subst (renameAfter (lift σt dom)
    --                              (lift ρt (dom.subst σ))) body
    -- Bridge to RHS_naked = Term.subst (lift (renameAfter σt ρt) dom) body
    -- via subst_HEq_pointwise + v1.39.
    apply HEq.symm
    -- Strip outer cast on RHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Δ'.cons (Ty.subst_rename_commute dom σ ρ))
      (TermSubst.renameAfter
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ)))
      ((TermSubst.renameAfter σt ρt).lift dom)
      (Subst.lift_renameAfter_commute σ ρ)
      (TermSubst.lift_renameAfter_pointwise σt ρt dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      ((Ty.subst_rename_commute cod σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) cod))
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Δ'.cons (Ty.subst_rename_commute dom σ ρ))
      (TermSubst.renameAfter
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ)))
      ((TermSubst.renameAfter σt ρt).lift dom)
      (Subst.lift_renameAfter_commute σ ρ)
      (TermSubst.lift_renameAfter_pointwise σt ρt dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_rename_commute_HEq σt ρt pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename ρt (Term.subst σt scrutinee))
        (Term.rename ρt (Term.subst σt zeroBranch))
        (Term.rename ρt (Term.subst σt succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.renameAfter σt ρt) scrutinee)
        (Term.subst (TermSubst.renameAfter σt ρt) zeroBranch)
        (Term.subst (TermSubst.renameAfter σt ρt) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt scrutinee))
      _ _ (Term.subst_rename_commute_HEq σt ρt zeroBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt scrutinee))
      _ _ (Term.subst_rename_commute_HEq σt ρt zeroBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_rename_commute elem σ ρ)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt hd)
      _ _ (Term.subst_rename_commute_HEq σt ρt tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt nilBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_rename_commute elem σ ρ)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt noneBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt leftBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.subst_rename_commute carrier σ ρ)
      (RawTerm.rename_subst_commute rawTerm σ.forRaw ρ)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_rename_commute carrier σ ρ)
      (RawTerm.rename_subst_commute leftEnd σ.forRaw ρ)
      (RawTerm.rename_subst_commute rightEnd σ.forRaw ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt baseCase)
      _ _ (Term.subst_rename_commute_HEq σt ρt witness)

/-! ## `Term.rename_subst_commute_HEq`.

Term-level analogue of `Ty.rename_subst_commute`:

  Term.subst σt' (Term.rename ρt t)
    ≃HEq≃
  Term.subst (TermSubst.precompose ρt σt') t

Mirrors v1.40 (subst-rename commute) with rename and subst swapped.
12-case structural induction with constructor HEq congruences for
the closed-context cases, outer-cast strips + inner-cast pushes
for the cast-bearing cases, and `Term.subst_HEq_pointwise` over
`TermSubst.lift_precompose_pointwise` (v1.41) for the binder
cases. -/
theorem Term.rename_subst_commute_HEq
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ') :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst σt' (Term.rename ρt t))
          (Term.subst (TermSubst.precompose ρt σt') t)
  | _, .var i => by
    -- LHS: Term.subst σt' ((ρt i) ▸ Term.var (ρ i)).
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input σt' (ρt i)
        (Term.var (context := Γ') (ρ i)))
    -- LHS reduces to σt' (ρ i); RHS = (precompose ρt σt') i,
    -- which by precompose's definition is `chain ▸ σt' (ρ i)`.
    -- Stage the chained equation via `have` so Lean β-reduces the
    -- congrArg-on-lambda before checking the ▸ type alignment.
    have h_witness : (varType Γ' (ρ i)).subst σ'
                       = ((varType Γ i).rename ρ).subst σ' :=
      congrArg (fun T : Ty level scope_m => T.subst σ') (ρt i)
    have h_chain : (varType Γ' (ρ i)).subst σ'
                     = (varType Γ i).subst (Subst.precompose ρ σ') :=
      h_witness.trans
        (Ty.rename_subst_commute (varType Γ i) ρ σ')
    show HEq (σt' (ρ i)) (h_chain ▸ σt' (ρ i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst σt' (Term.rename ρt f))
                (Term.subst σt' (Term.rename ρt a)))
      (Term.app (Term.subst (TermSubst.precompose ρt σt') f)
                (Term.subst (TermSubst.precompose ρt σt') a))
    exact Term.app_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      (Ty.rename_subst_commute cod ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' f)
      _ _ (Term.rename_subst_commute_HEq ρt σt' a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst σt' (Term.rename ρt p)))
      (Term.fst (Term.subst (TermSubst.precompose ρt σt') p))
    apply Term.fst_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
    exact Term.rename_subst_commute_HEq ρt σt' p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst σt' (Term.rename ρt s))
                     (Term.subst σt' (Term.rename ρt t))
                     (Term.subst σt' (Term.rename ρt e)))
      (Term.boolElim (Term.subst (TermSubst.precompose ρt σt') s)
                     (Term.subst (TermSubst.precompose ρt σt') t)
                     (Term.subst (TermSubst.precompose ρt σt') e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' s))
      _ _ (Term.rename_subst_commute_HEq ρt σt' t)
      _ _ (Term.rename_subst_commute_HEq ρt σt' e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.subst σt' (cast_rename.symm ▸ Term.appPi (rename f) (rename a))
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute cod dom ρ).symm
        (Term.appPi (Term.rename ρt f) (Term.rename ρt a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      ((Ty.rename_subst_commute cod ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') cod))
      _ _ (Term.rename_subst_commute_HEq ρt σt' f)
      _ _ (Term.rename_subst_commute_HEq ρt σt' a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
    -- LHS secondVal: cast_outer_LHS ▸ subst σt' (cast_inner_LHS ▸ rename ρt w)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute second first ρ)
        (Term.rename ρt w))
    apply HEq.trans (Term.rename_subst_commute_HEq ρt σt' w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute second first ρ).symm
        (Term.snd (Term.rename ρt p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
      _ _ (Term.rename_subst_commute_HEq ρt σt' p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      (Ty.rename_subst_commute cod ρ σ')
    -- Strip outer cast on LHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through subst (lift σt' (dom.rename ρ)).
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift σt' (dom.rename ρ))
        (Ty.rename_weaken_commute cod ρ)
        (Term.rename (TermRenaming.lift ρt dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ))
        body)
    -- Bridge via subst_HEq_pointwise + v1.41.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Δ.cons (Ty.rename_subst_commute dom ρ σ'))
      (TermSubst.precompose
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ)))
      ((TermSubst.precompose ρt σt').lift dom)
      (Subst.lift_precompose_commute ρ σ')
      (TermSubst.lift_precompose_pointwise ρt σt' dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      ((Ty.rename_subst_commute cod ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') cod))
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Δ.cons (Ty.rename_subst_commute dom ρ σ'))
      (TermSubst.precompose
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ)))
      ((TermSubst.precompose ρt σt').lift dom)
      (Subst.lift_precompose_commute ρ σ')
      (TermSubst.lift_precompose_pointwise ρt σt' dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_subst_commute_HEq ρt σt' pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst σt' (Term.rename ρt scrutinee))
        (Term.subst σt' (Term.rename ρt zeroBranch))
        (Term.subst σt' (Term.rename ρt succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.precompose ρt σt') scrutinee)
        (Term.subst (TermSubst.precompose ρt σt') zeroBranch)
        (Term.subst (TermSubst.precompose ρt σt') succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' scrutinee))
      _ _ (Term.rename_subst_commute_HEq ρt σt' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' scrutinee))
      _ _ (Term.rename_subst_commute_HEq ρt σt' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_subst_commute elem ρ σ')
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' hd)
      _ _ (Term.rename_subst_commute_HEq ρt σt' tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' nilBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_subst_commute elem ρ σ')
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' noneBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' leftBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_subst_commute carrier ρ σ')
      (RawTerm.subst_rename_commute rawTerm ρ σ'.forRaw)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_subst_commute carrier ρ σ')
      (RawTerm.subst_rename_commute leftEnd ρ σ'.forRaw)
      (RawTerm.subst_rename_commute rightEnd ρ σ'.forRaw)
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' baseCase)
      _ _ (Term.rename_subst_commute_HEq ρt σt' witness)

/-! ## `Term.subst_weaken_commute_HEq`.

Term-level analogue of `Ty.subst_weaken_commute`:

  Term.subst (σt.lift X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.subst σ) (Term.subst σt t)

Direct corollary of v1.40 + v1.42 — no fresh structural induction.
Both sides factor into rename/subst forms (since `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`).  v1.42 collapses
LHS to `Term.subst (precompose (weaken Γ X) (σt.lift X)) t`; v1.40
collapses RHS to `Term.subst (renameAfter σt (weaken Δ (X.subst σ))) t`.
The two underlying Substs (`precompose Renaming.weaken σ.lift` and
`renameAfter σ Renaming.weaken`) are pointwise rfl-equal — both
reduce to `(σ i).weaken`.  `Term.subst_HEq_pointwise` (v1.24)
bridges them.

This subsumes the v1.28–v1.33 standalone closed-context case
lemmas (`Term.subst_weaken_commute_HEq_{var,unit,boolTrue,boolFalse,
app,boolElim,fst,snd,pair,appPi}`); the binder cases (`lam`,
`lamPi`) that were missing in those layered theorems are now
covered by the same corollary.  Mirrors v1.38 exactly. -/
theorem Term.subst_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.subst (σt.lift newType) (Term.weaken newType t))
        (Term.weaken (newType.subst σ) (Term.subst σt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.subst (σt.lift newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.subst σ))
      (Term.subst σt t))
  -- Collapse LHS via v1.42 to a single composed subst.
  apply HEq.trans
    (Term.rename_subst_commute_HEq
      (TermRenaming.weaken Γ newType)
      (σt.lift newType)
      t)
  -- Same for RHS via v1.40, in symm orientation.
  apply HEq.symm
  apply HEq.trans
    (Term.subst_rename_commute_HEq
      σt
      (TermRenaming.weaken Δ (newType.subst σ))
      t)
  apply HEq.symm
  -- The two composed underlying Substs agree pointwise — `fun _ => rfl`.
  -- The pointwise HEq between the term-level composed TermSubsts
  -- follows from the cast-strip identity: at each i both reduce
  -- (modulo casts) to `Term.weaken (newType.subst σ) (σt i)`.
  exact Term.subst_HEq_pointwise rfl
    (TermSubst.precompose
      (TermRenaming.weaken Γ newType) (σt.lift newType))
    (TermSubst.renameAfter σt
      (TermRenaming.weaken Δ (newType.subst σ)))
    (Subst.precompose_weaken_lift_equiv_renameAfter_weaken σ)
    (fun _ => by
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact eqRec_heq _ _)
    t

/-! ## `TermSubst.lift_compose_pointwise` (full theorem).

Lifting commutes with TermSubst composition pointwise (HEq).  Position 0
delegates to the existing `lift_compose_pointwise_zero` fragment.
Position `k + 1` is the substantive case:

  * LHS at `k+1`: `outer_subst_weaken_commute.symm ▸ Term.weaken
    (newType.subst (Subst.compose σ₁ σ₂)) (Ty.subst_compose ...
    ▸ Term.subst σt₂ (σt₁ k'))`.

  * RHS at `k+1`: `outer_subst_compose ▸ Term.subst (σt₂.lift
    (newType.subst σ₁)) ((Ty.subst_weaken_commute ...).symm ▸
    Term.weaken (newType.subst σ₁) (σt₁ k'))`.

The RHS inner reduces, via `Term.subst_HEq_cast_input` + v1.43
`Term.subst_weaken_commute_HEq`, to `Term.weaken ((newType.subst
σ₁).subst σ₂) (Term.subst σt₂ (σt₁ k'))`.  The two `Term.weaken`
forms differ only by `Ty.subst_compose newType σ₁ σ₂` on the
`newType` and the per-position analogue on the inner type;
`Term.weaken_HEq_congr` closes via `eqRec_heq`. -/
theorem TermSubst.lift_compose_pointwise
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty level scope₁) :
    ∀ (i : Fin (scope₁ + 1)),
      HEq
        (TermSubst.lift (TermSubst.compose σt₁ σt₂) newType i)
        (TermSubst.compose (σt₁.lift newType)
          (σt₂.lift (newType.subst σ₁)) i)
  | ⟨0, _⟩ =>
      TermSubst.lift_compose_pointwise_zero σt₁ σt₂ newType
  | ⟨k + 1, hk⟩ => by
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and strip outer cast on RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast on RHS through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (σt₂.lift (newType.subst σ₁))
        (Ty.subst_weaken_commute
          (varType Γ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₁).symm
        (Term.weaken (newType.subst σ₁)
          (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))
    -- After helper: Term.subst (σt₂.lift X) (Term.weaken X (σt₁ k')).
    -- Apply v1.43 to get Term.weaken (X.subst σ₂) (Term.subst σt₂ (σt₁ k')).
    apply HEq.trans
      (Term.subst_weaken_commute_HEq
        σt₂ (newType.subst σ₁)
        (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    -- Flip back to LHS-orientation.
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.
    exact Term.weaken_HEq_congr
      (Ty.subst_compose newType σ₁ σ₂).symm
      (Ty.subst_compose
        (varType Γ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₁ σ₂).symm
      _ _ (eqRec_heq _ _)

/-! ## `Term.subst_compose`.

The cap-stone of substitution functoriality at the term level:

  Term.subst σt₂ (Term.subst σt₁ t)
    ≃HEq≃
  Term.subst (TermSubst.compose σt₁ σt₂) t

Both sides have type `Term Γ₃ T'` for propositionally-equal `T'`s
(`((T.subst σ₁).subst σ₂)` vs `T.subst (Subst.compose σ₁ σ₂)`,
bridged by `Ty.subst_compose`).  HEq carries the difference.

12-case structural induction on the term.

  * Closed-context cases (var, unit/boolTrue/boolFalse, app, fst,
    boolElim) combine constructor HEq congruences with
    `Ty.subst_compose` at each Ty level index.
  * Cast-bearing cases (appPi/pair/snd) peel outer casts via
    `eqRec_heq` and push inner casts through
    `Term.subst_HEq_cast_input`.  The sigmaTy/piTy second-component
    bridge chains `Ty.subst_compose` at scope+1 with
    `Subst.lift_compose_equiv`.
  * Binder cases (lam, lamPi) recurse via the IH at lifted
    TermSubsts (`lift σt₁ dom` and `lift σt₂ (dom.subst σ₁)`),
    then bridge `compose (lift σt₁) (lift σt₂)` against
    `lift (compose σt₁ σt₂)` via `Term.subst_HEq_pointwise` (v1.24)
    over `TermSubst.lift_compose_pointwise` (v1.44).

Mirrors v1.40 / v1.42 with subst on both sides instead of mixed
subst+rename. -/
theorem Term.subst_compose_HEq
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂) :
    {T : Ty level scope₁} → (t : Term Γ₁ T) →
      HEq (Term.subst σt₂ (Term.subst σt₁ t))
          (Term.subst (TermSubst.compose σt₁ σt₂) t)
  | _, .var i => by
    -- LHS: Term.subst σt₂ (σt₁ i).
    -- RHS: (compose σt₁ σt₂) i = (Ty.subst_compose ...) ▸ Term.subst σt₂ (σt₁ i).
    show HEq (Term.subst σt₂ (σt₁ i))
      ((Ty.subst_compose (varType Γ₁ i) σ₁ σ₂)
        ▸ Term.subst σt₂ (σt₁ i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst σt₂ (Term.subst σt₁ f))
                (Term.subst σt₂ (Term.subst σt₁ a)))
      (Term.app (Term.subst (TermSubst.compose σt₁ σt₂) f)
                (Term.subst (TermSubst.compose σt₁ σt₂) a))
    exact Term.app_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      (Ty.subst_compose cod σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ f)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst σt₂ (Term.subst σt₁ p)))
      (Term.fst (Term.subst (TermSubst.compose σt₁ σt₂) p))
    apply Term.fst_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
    exact Term.subst_compose_HEq σt₁ σt₂ p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst σt₂ (Term.subst σt₁ s))
                     (Term.subst σt₂ (Term.subst σt₁ t))
                     (Term.subst σt₂ (Term.subst σt₁ e)))
      (Term.boolElim (Term.subst (TermSubst.compose σt₁ σt₂) s)
                     (Term.subst (TermSubst.compose σt₁ σt₂) t)
                     (Term.subst (TermSubst.compose σt₁ σt₂) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ s))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ t)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute cod dom σ₁).symm
        (Term.appPi (Term.subst σt₁ f) (Term.subst σt₁ a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      ((Ty.subst_compose cod σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) cod))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ f)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute second first σ₁)
        (Term.subst σt₁ w))
    apply HEq.trans (Term.subst_compose_HEq σt₁ σt₂ w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute second first σ₁).symm
        (Term.snd (Term.subst σt₁ p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      (Ty.subst_compose cod σ₁ σ₂)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift σt₂ (dom.subst σ₁))
        (Ty.subst_weaken_commute cod σ₁)
        (Term.subst (TermSubst.lift σt₁ dom) body))
    -- IH on body with the lifts.
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁))
        body)
    -- Bridge compose-of-lifts to lift-of-compose.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Γ₃.cons (Ty.subst_compose dom σ₁ σ₂))
      (TermSubst.compose
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁)))
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) dom)
      (Subst.lift_compose_equiv σ₁ σ₂)
      (fun i =>
        (TermSubst.lift_compose_pointwise σt₁ σt₂ dom i).symm)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      ((Ty.subst_compose cod σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) cod))
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Γ₃.cons (Ty.subst_compose dom σ₁ σ₂))
      (TermSubst.compose
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁)))
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) dom)
      (Subst.lift_compose_equiv σ₁ σ₂)
      (fun i =>
        (TermSubst.lift_compose_pointwise σt₁ σt₂ dom i).symm)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_compose_HEq σt₁ σt₂ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst σt₂ (Term.subst σt₁ scrutinee))
        (Term.subst σt₂ (Term.subst σt₁ zeroBranch))
        (Term.subst σt₂ (Term.subst σt₁ succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.compose σt₁ σt₂) scrutinee)
        (Term.subst (TermSubst.compose σt₁ σt₂) zeroBranch)
        (Term.subst (TermSubst.compose σt₁ σt₂) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ scrutinee))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ zeroBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ scrutinee))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ zeroBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_compose elem σ₁ σ₂)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ hd)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ nilBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_compose elem σ₁ σ₂)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ noneBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ leftBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.subst_compose carrier σ₁ σ₂)
      (RawTerm.subst_compose rawTerm σ₁.forRaw σ₂.forRaw)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_compose carrier σ₁ σ₂)
      (RawTerm.subst_compose leftEnd σ₁.forRaw σ₂.forRaw)
      (RawTerm.subst_compose rightEnd σ₁.forRaw σ₂.forRaw)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ baseCase)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ witness)

/-- The explicit-`▸` form of `Term.subst_compose`: `eq_of_heq` plus
the outer cast strip.  Mirrors the v1.25 derivation of `Term.subst_id`
from `Term.subst_id_HEq`. -/
theorem Term.subst_compose
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    {T : Ty level scope₁} (t : Term Γ₁ T) :
    Term.subst σt₂ (Term.subst σt₁ t)
      = (Ty.subst_compose T σ₁ σ₂).symm
          ▸ Term.subst (TermSubst.compose σt₁ σt₂) t :=
  eq_of_heq
    ((Term.subst_compose_HEq σt₁ σt₂ t).trans (eqRec_heq _ _).symm)

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
