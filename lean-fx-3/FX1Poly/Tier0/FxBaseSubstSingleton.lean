import FX1Poly.Tier0.FxBaseSubstComprehension
import FX1Poly.Core.RawTermSubst0

/-! # FX1Poly/Tier0/FxBaseSubstSingleton
    — the single-substitution / β-contraction section (brick 5 of the term-carrying CwR base)

`FxBaseSubstComprehension.lean` (SUBSTVEC-4) shipped the comprehension morphism `SubstVec.cons`.  The most
important INSTANCE of comprehension is the **single-substitution**: extend the IDENTITY substitution with one
argument term.  This is `SubstVec.cons rawArg (SubstVec.identity scope) : SubstVec scope (scope + 1)` — the
morphism `scope + 1 ⟶ scope` that sends the freshly-bound variable `0` to `rawArg` and shifts every other
variable down by one.  It is EXACTLY the substitution the canonical β-reduction rule runs: `app (lam body) arg ↝
subst0 body arg` (RawTermSubst0.lean).  This file names it (`SubstVec.singleton`), exhibits it as a categorical
SECTION of the display map, and bridges it to the operational β-engine.

## What lands here (all zero-axiom)

  * `SubstVec.singleton rawArg : SubstVec scope (scope + 1)` — the single-substitution / β-contraction morphism
    (`cons rawArg (identity scope)`).
  * `SubstVec.singleton_lookup_zero` — its head is the argument (`rfl`).
  * **`SubstVec.weakening_compose_singleton`** — the β-contraction is a SECTION of the display map:
    `weakening ∘ singleton = identity`.  The genuine CwF content — a context-extension term induces a section of
    the display projection (an immediate consequence of the SUBSTVEC-4 comprehension p-law, instantiated at the
    identity tail).
  * `SubstVec.singleton_toRawTermSubst` — the categorical singleton IS the function-level `RawTermSubst.singleton`
    (pointwise).
  * **`SubstVec.subst_singleton_eq_subst0`** — the OPERATIONAL β bridge: substituting `body` via the categorical
    singleton equals `RawTerm.subst0 body rawArg`, the de Bruijn β-reduct the `Step` relation references.  This
    certifies the term-carrying comprehension structure models the kernel's β-reduction substitution exactly.

## Honest scope boundary

This is the single-substitution instance of comprehension + its display-map section + its β-engine bridge.  The
FULL `RepresentableMapCategory` `fxBaseSubstRMC` is a LATER brick and a multi-step arc: its `MorphismClass`
requires `memberDecidable`, and deciding whether a `SubstVec` (which carries TERMS, not just variable indices) is
a categorical isomorphism is genuinely harder than the renaming base's finite-bijectivity decider — it needs (a)
the characterization "a substitution iso is a variable-renaming bijection" and (b) a "is this lookup a variable"
check composed with the shipped renaming-iso decider.  The `GlobalSections` over the term base also differs from
the renaming base: the substitution category has NO terminal object (`SubstVec target X` is never a singleton for
`X ≥ 1`, since `RawTerm target` is infinite) — it has an INITIAL object (scope `0`), so closed terms are the
co-representable `Hom(0, -)`, not the representable-at-terminal the renaming base used.

## Zero-axiom verification

`singleton` is `cons` of the identity; `singleton_lookup_zero` is `cons_lookup_zero` (`rfl`);
`weakening_compose_singleton` is the SUBSTVEC-4 `weakening_compose_cons` at the identity tail;
`singleton_toRawTermSubst` is a per-position match (head `rfl`, tail `SubstVec.identity_lookup`); the β bridge is
`RawTerm.subst_pointwise` against that pointwise equality (`RawTerm.subst0` is `@[reducible]` = `subst singleton`,
so the conclusion holds by defeq).  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation

/-- The **single-substitution / β-contraction morphism** `scope + 1 ⟶ scope`: extend the identity substitution
with the argument term `rawArg`, sending the freshly-bound variable `0` to `rawArg` and shifting every other
variable down by one.  The categorical name for the substitution the canonical β-reduction rule runs. -/
def SubstVec.singleton {scope : Nat} (rawArg : RawTerm scope) : SubstVec scope (scope + 1) :=
  SubstVec.cons rawArg (SubstVec.identity scope)

/-- The single-substitution's head is the argument. -/
theorem SubstVec.singleton_lookup_zero {scope : Nat} (rawArg : RawTerm scope)
    (isLt : 0 < scope + 1) :
    (SubstVec.singleton rawArg).lookup ⟨0, isLt⟩ = rawArg := rfl

/-- **The β-contraction is a SECTION of the display map:** `weakening ∘ singleton = identity`.  A context-extension
term induces a section of the display projection (the comprehension p-law `weakening_compose_cons` instantiated at
the identity tail) — a genuine CwF fact. -/
theorem SubstVec.weakening_compose_singleton {scope : Nat} (rawArg : RawTerm scope) :
    (SubstVec.weakening scope).compose (SubstVec.singleton rawArg) = SubstVec.identity scope :=
  SubstVec.weakening_compose_cons rawArg (SubstVec.identity scope)

/-- The categorical single-substitution IS the function-level `RawTermSubst.singleton` (pointwise): head returns
the argument, every successor variable returns the shifted-down variable (via `SubstVec.identity_lookup`). -/
theorem SubstVec.singleton_toRawTermSubst {scope : Nat} (rawArg : RawTerm scope)
    (index : Fin (scope + 1)) :
    (SubstVec.singleton rawArg).toRawTermSubst index = RawTermSubst.singleton rawArg index :=
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isLt⟩ => SubstVec.identity_lookup scope ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- **The operational β bridge:** substituting `body` via the categorical single-substitution equals
`RawTerm.subst0 body rawArg` — the de Bruijn β-reduct the `Step` relation references for `app (lam body) arg`.
Certifies that the term-carrying comprehension structure models the kernel's β-reduction substitution exactly.
Via `subst_pointwise` against `singleton_toRawTermSubst` (`subst0` is `@[reducible]` = `subst singleton`). -/
theorem SubstVec.subst_singleton_eq_subst0 {scope : Nat} (body : RawTerm (scope + 1))
    (rawArg : RawTerm scope) :
    RawTerm.subst (SubstVec.singleton rawArg).toRawTermSubst body = RawTerm.subst0 body rawArg :=
  RawTerm.subst_pointwise (fun index => SubstVec.singleton_toRawTermSubst rawArg index) body

end FX1Poly.Tier0
