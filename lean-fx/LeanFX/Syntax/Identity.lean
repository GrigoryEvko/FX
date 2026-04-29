import LeanFX.Syntax.Reduction

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## External identity proofs.

`IdProof t₁ t₂` witnesses that two terms of the same FX type are
intensionally equal at the kernel meta-level — a `Type`-valued
inductive family with the single constructor `refl`.

The family lives outside `Term` because the surface FX `Id A a b :
Type` requires universe codes (`El : Term Γ (Ty.universe u rfl) →
Ty u scope`) before it can be promoted into a Term-level type
former.  Until v1.51's El bridge lands, IdProof scaffolds FX-level
cast, transport, and conversion-witness reasoning at the metatheory
layer — the structural lemmas (symm, trans, cong, subst-commute,
rename-commute) are exactly the ones the bridge will translate
into Term-level operations.

Distinct from Lean's `Eq` because IdProof carries the FX type `T`
and the context `Γ` explicitly, and is intentionally `Type`-valued
so that a future J eliminator (v1.43+) can compute over its proof
content rather than collapsing into proof-irrelevance.  This is the
HoTT-friendly choice: the path between two terms is data, not a
mere proposition. -/
inductive IdProof : {mode : Mode} → {level scope : Nat} →
    {context : Ctx mode level scope} → {resultType : Ty level scope} →
    Term context resultType → Term context resultType → Type
  /-- Reflexivity — every term is identity-related to itself.  The
  unique constructor; pattern-matching on `refl` definitionally
  collapses both sides to the same term. -/
  | refl : {mode : Mode} → {level scope : Nat} →
           {context : Ctx mode level scope} →
           {resultType : Ty level scope} →
           (term : Term context resultType) → IdProof term term

namespace IdProof

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
         {resultType : Ty level scope}

/-- Symmetry — flip the sides of an identity proof.  Pattern-on-refl
collapses both sides to a single term, after which `refl` discharges
in the swapped orientation. -/
def symm {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ → IdProof term₂ term₁
  | .refl _ => IdProof.refl _

/-- Transitivity — chain two identity proofs through a common
midpoint.  Pattern-matching on the first proof's `refl` collapses
`term₁ = term₂`, leaving the second proof witnessing
`IdProof term₂ term₃` — exactly what we return. -/
def trans {term₁ term₂ term₃ : Term context resultType} :
    IdProof term₁ term₂ → IdProof term₂ term₃ → IdProof term₁ term₃
  | .refl _, proof => proof

/-- Function congruence — apply an arbitrary `Term → Term` operation
to both sides of an identity proof.  Lean's `congrArg` analogue,
specialised to Term-valued functions on a single FX context. -/
def cong {sourceType targetType : Ty level scope}
    (function : Term context sourceType → Term context targetType)
    {term₁ term₂ : Term context sourceType} :
    IdProof term₁ term₂ → IdProof (function term₁) (function term₂)
  | .refl _ => IdProof.refl _

/-- Application congruence — both function and argument may differ.
Composition of two `cong` calls; provided directly because it's the
most common shape (`Term.app f a` propagates IdProof through both
positions). -/
def cong_app {domainType codomainType : Ty level scope}
    {function₁ function₂ : Term context (Ty.arrow domainType codomainType)}
    {argument₁ argument₂ : Term context domainType}
    (h_function : IdProof function₁ function₂)
    (h_argument : IdProof argument₁ argument₂) :
    IdProof (Term.app function₁ argument₁) (Term.app function₂ argument₂) :=
  match h_function, h_argument with
  | .refl _, .refl _ => IdProof.refl _

/-- Substitution-commute — applying a `TermSubst` to both sides of
an identity proof yields an identity proof on the substituted terms.
Pattern-on-refl collapses both sides; `IdProof.refl` on the
substituted term discharges. -/
def subst {scope' : Nat} {context' : Ctx mode level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst context context' σ)
    {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ →
    IdProof (Term.subst σt term₁) (Term.subst σt term₂)
  | .refl _ => IdProof.refl _

/-- Renaming-commute — analogue of `subst` for `TermRenaming`. -/
def rename {scope' : Nat} {context' : Ctx mode level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming context context' ρ)
    {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ →
    IdProof (Term.rename ρt term₁) (Term.rename ρt term₂)
  | .refl _ => IdProof.refl _

/-- IdProof-to-equality bridge — every IdProof witnesses a Lean
`Eq` between the underlying terms.  Useful for stating metatheory
lemmas that mix the two notions; the reverse direction
(`Eq → IdProof`) is just `· ▸ IdProof.refl _`. -/
def toEq {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ → term₁ = term₂
  | .refl _ => rfl

/-- Equality-to-IdProof bridge — promote a Lean `Eq` between Terms
of the same type into an IdProof.  The companion of `toEq`. -/
def ofEq {term₁ term₂ : Term context resultType} :
    term₁ = term₂ → IdProof term₁ term₂
  | rfl => IdProof.refl _

/-- Dependent path induction for external identity proofs.

The motive may depend on the right endpoint and on the path itself.
Pattern matching on `refl` reduces both endpoint and proof to the base
case, giving the full J eliminator for the external `IdProof` layer. -/
def idJ {leftTerm : Term context resultType}
    (motive :
      (rightTerm : Term context resultType) →
        IdProof leftTerm rightTerm → Type)
    (baseCase : motive leftTerm (IdProof.refl leftTerm)) :
    {rightTerm : Term context resultType} →
      (path : IdProof leftTerm rightTerm) →
        motive rightTerm path
  | _, .refl _ => baseCase

/-- Non-dependent transport along an external identity proof. -/
def transport {leftTerm : Term context resultType}
    (motive : Term context resultType → Type)
    (baseCase : motive leftTerm) :
    {rightTerm : Term context resultType} →
      IdProof leftTerm rightTerm → motive rightTerm
  | _, .refl _ => baseCase

/-- The dependent eliminator computes at reflexivity. -/
example {leftTerm : Term context resultType}
    (motive :
      (rightTerm : Term context resultType) →
        IdProof leftTerm rightTerm → Type)
    (baseCase : motive leftTerm (IdProof.refl leftTerm)) :
    IdProof.idJ motive baseCase (IdProof.refl leftTerm) = baseCase := rfl

/-- Transport computes at reflexivity. -/
example {leftTerm : Term context resultType}
    (motive : Term context resultType → Type)
    (baseCase : motive leftTerm) :
    IdProof.transport motive baseCase (IdProof.refl leftTerm) = baseCase := rfl

end IdProof

end LeanFX.Syntax
