import FX1Poly.Core.SimpleTypeInterpretation
import FX1Poly.Core.RawTermSubstCompose
import FX1Poly.Core.RawTermSubstPointwise
import FX1Poly.Core.RawTermSubstIdentity
import FX1Poly.Core.SubstPreservationProbes
import FX1Poly.Core.CompoundSubstPreservation

/-! # Foundation/PolyCell/Core/SimplyTypedNormalization
    — the Tait fundamental theorem for the simply-typed skeleton: every simply-typed
      `RawTerm` is strongly normalizing

This file assembles the four type-agnostic case lemmas of `SimpleTypeInterpretation`
(`reducibleVariable`, `reducibleApplication`, `reducibleAbstraction`,
`Red_isStronglyNormalizing`) into the classical Tait reducibility theorem for the
simply-typed lambda calculus, mechanized over the `RawTerm` substrate:

  `SimplyTyped context term resultType → IsStronglyNormalizing term`.

## Why the simply-typed skeleton (and not raw type erasure)

Strong normalization of the dependent kernel factors through the simple-type skeleton
because β-reduction ignores type dependency.  The tempting shortcut — a structural
`eraseType : RawTerm → SimpleType` — is NOT stable under term substitution once a type
variable can be instantiated by a Π: `eraseType (variable) = base` but
`eraseType (piTyCode A B) = arrow`, so substituting a Π for a type variable would change
the erased type (the classical System-F-ω obstacle).  Factoring through an explicit
`SimplyTyped` judgment sidesteps this: simple types are term-substitution-invariant by
construction.  The bridge from the dependent `HasType` layer — erasure of a typing
DERIVATION (which records each variable's simple type in the erased context, restoring
substitution stability) — is a separate, later brick; this file proves the skeleton
result it will consume.

## The reducible-substitution method

The fundamental theorem is stated with an explicit environment.  A `SimpleTypeContext`
assigns a simple type to every variable; a `ReducibleSubst` is a parallel substitution
mapping each variable to a term reducible at that variable's type.  The theorem reads
"under any reducible substitution, a simply-typed term is reducible at its type"; the
λ-case extends the environment with a fresh reducible argument (`RawTermSubst.cons`) and
uses the β-substitution lemma `subst0 (subst (lift ρ) body) arg = subst (cons arg ρ) body`
to align the IH.  Specialising to the identity substitution (reducible because every
variable is reducible, `reducibleVariable`) and `subst_identity_apply` yields the SN
corollary.

## Zero-axiom verification

A three-constructor `Prop` inductive over distinct generator head-shapes (so `induction`
needs no impossible-case elimination) + the shipped substitution ladder
(`subst_compose`, `subst_pointwise`, `weaken_subst_singleton`, `subst_identity_apply`).
The `Fin` positions are split by the blessed explicit `⟨0, _⟩` / `⟨k + 1, _⟩` match
(mirroring `RawTermSubst.lift` / `lift_pointwise`), never `Fin.cases`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A simple-typing context assigns a `SimpleType` to every variable in scope. -/
@[reducible] def SimpleTypeContext (scope : Nat) : Type := Fin scope → SimpleType

/-- Extend a context with a fresh binder of type `headType` at position 0; every prior
variable shifts up by one.  Mirrors the `⟨0, _⟩` / `⟨k + 1, _⟩` shape of
`RawTermSubst.lift`. -/
def SimpleTypeContext.cons {scope : Nat} (headType : SimpleType)
    (tailContext : SimpleTypeContext scope) : SimpleTypeContext (scope + 1) :=
  fun position =>
    match position with
    | ⟨0, _⟩ => headType
    | ⟨priorValue + 1, hBound⟩ => tailContext ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- Extend a parallel substitution with a fresh substituent `headArg` at position 0 — the
term-level dual of `SimpleTypeContext.cons` and of `RawTermSubst.lift` (lift weakens; cons
substitutes).  `RawTermSubst.singleton a` is `cons a identity`. -/
def RawTermSubst.cons {scope targetScope : Nat} (headArg : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) : RawTermSubst (scope + 1) targetScope :=
  fun position =>
    match position with
    | ⟨0, _⟩ => headArg
    | ⟨priorValue + 1, hBound⟩ => tailSubst ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- The simply-typed lambda calculus over `RawTerm`: three rules over the `gen_var` /
`gen_app` / `gen_lam` shapes.  The skeleton through which strong normalization of the
dependent kernel factors.  Distinct generator heads per constructor mean `induction` faces
no impossible-case elimination. -/
inductive SimplyTyped : {scope : Nat} → SimpleTypeContext scope → RawTerm scope → SimpleType → Prop where
  | var {scope : Nat} {context : SimpleTypeContext scope} {position : Fin scope}
      {resultType : SimpleType} :
      context position = resultType →
      SimplyTyped context (.mkGen .gen_var position .childNil) resultType
  | app {scope : Nat} {context : SimpleTypeContext scope} {function argument : RawTerm scope}
      {domainType codomainType : SimpleType} :
      SimplyTyped context function (.arrow domainType codomainType) →
      SimplyTyped context argument domainType →
      SimplyTyped context
        (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
        codomainType
  | lam {scope : Nat} {context : SimpleTypeContext scope} {body : RawTerm (scope + 1)}
      {domainType codomainType : SimpleType} :
      SimplyTyped (SimpleTypeContext.cons domainType context) body codomainType →
      SimplyTyped context
        (.mkGen .gen_lam () (.childCons body .childNil))
        (.arrow domainType codomainType)

/-- A parallel substitution is reducible for a context when every variable maps to a term
reducible at that variable's simple type — the logical-relation environment the fundamental
theorem threads. -/
@[reducible] def ReducibleSubst {scope targetScope : Nat}
    (context : SimpleTypeContext scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ position : Fin scope, Red (context position) (substitution position)

/-- Consing a reducible argument onto a reducible substitution stays reducible for the
consed context — the environment extension the λ-case performs. -/
theorem reducibleSubst_cons {scope targetScope : Nat}
    {context : SimpleTypeContext scope} {substitution : RawTermSubst scope targetScope}
    {domainType : SimpleType} {argument : RawTerm targetScope}
    (argumentReducible : Red domainType argument)
    (substReducible : ReducibleSubst context substitution) :
    ReducibleSubst (SimpleTypeContext.cons domainType context)
      (RawTermSubst.cons argument substitution) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact argumentReducible
  | ⟨priorValue + 1, hBound⟩ =>
      exact substReducible ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- **The β-substitution lemma** aligning the λ-case IH: substituting `argument` into a
body already under the lifted substitution equals substituting under the consed
substitution.  Proof: `subst0` is `subst (singleton ·)`, so `subst_compose` folds the two
substitutions into `compose (lift ρ) (singleton argument)`, which is pointwise
`cons argument ρ` — position 0 reduces both sides to `argument`; position `k + 1` is exactly
the weakening cancellation `weaken_subst_singleton`. -/
theorem subst0_subst_lift_eq_subst_cons {scope targetScope : Nat}
    (body : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope)
    (argument : RawTerm targetScope) :
    RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument =
      RawTerm.subst (RawTermSubst.cons argument substitution) body := by
  show RawTerm.subst (RawTermSubst.singleton argument)
        (RawTerm.subst (RawTermSubst.lift substitution) body) =
      RawTerm.subst (RawTermSubst.cons argument substitution) body
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorValue + 1, hBound⟩ =>
      exact RawTerm.weaken_subst_singleton
        (substitution ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩) argument

/-- **The Tait fundamental theorem** for the simply-typed skeleton: under any reducible
substitution, a simply-typed term is reducible at its simple type.  Induction on the typing
derivation — variable from the environment, application by `reducibleApplication`,
abstraction by `reducibleAbstraction` after the β-substitution alignment. -/
theorem SimplyTyped.fundamental {scope : Nat} {context : SimpleTypeContext scope}
    {term : RawTerm scope} {resultType : SimpleType}
    (derivation : SimplyTyped context term resultType) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
      ReducibleSubst context substitution →
      Red resultType (RawTerm.subst substitution term) := by
  induction derivation with
  | @var scope context position resultType contextEq =>
      intro targetScope substitution substReducible
      rw [RawTerm.subst_var_reduces]
      rw [← contextEq]
      exact substReducible position
  | @app scope context function argument domainType codomainType
      _functionDerivation _argumentDerivation functionIH argumentIH =>
      intro targetScope substitution substReducible
      rw [RawTerm.subst_app_reduces]
      exact reducibleApplication
        (functionIH substitution substReducible)
        (argumentIH substitution substReducible)
  | @lam scope context body domainType codomainType _bodyDerivation bodyIH =>
      intro targetScope substitution substReducible
      rw [RawTerm.subst_lam_reduces]
      apply reducibleAbstraction
      intro argument argumentReducible
      rw [subst0_subst_lift_eq_subst_cons]
      exact bodyIH (RawTermSubst.cons argument substitution)
        (reducibleSubst_cons argumentReducible substReducible)

/-- The identity substitution is reducible for any context — every variable is reducible at
every type (`reducibleVariable`).  This is the base environment that turns the fundamental
theorem into the SN corollary. -/
theorem reducibleSubst_identity {scope : Nat} {context : SimpleTypeContext scope} :
    ReducibleSubst context (RawTermSubst.identity : RawTermSubst scope scope) := by
  intro position
  exact reducibleVariable (context position) position

/-- **Strong normalization for the simply-typed skeleton** (the Tait corollary): every
simply-typed `RawTerm` is strongly normalizing.  Instantiate the fundamental theorem at the
reducible identity substitution, cancel it with `subst_identity_apply`, and project SN out
of reducibility (`Red_isStronglyNormalizing`). -/
theorem SimplyTyped.isStronglyNormalizing {scope : Nat} {context : SimpleTypeContext scope}
    {term : RawTerm scope} {resultType : SimpleType}
    (derivation : SimplyTyped context term resultType) :
    IsStronglyNormalizing term := by
  have reducible : Red resultType (RawTerm.subst RawTermSubst.identity term) :=
    derivation.fundamental RawTermSubst.identity reducibleSubst_identity
  rw [RawTerm.subst_identity_apply] at reducible
  exact Red_isStronglyNormalizing reducible

end FX1Poly.Core
