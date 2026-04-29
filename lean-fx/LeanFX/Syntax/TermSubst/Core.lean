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


end LeanFX.Syntax
