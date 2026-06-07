import FX1Poly.Tier0.FxBaseSubstVec
import FX1Poly.Core.RawTermSubstCompose
import FX1Poly.Core.RawTermSubstIdentity
import FX1Poly.Core.RawTermSubstPointwise
import FX1Poly.Tier0.RepresentableMapCategory

/-! # FX1Poly/Tier0/FxBaseSubstCategory
    — the TERM-CARRYING `RawCategory` of contexts-and-substitutions (brick 2 of the term-carrying CwR base)

`FxBaseSubstVec.lean` (SUBSTVEC-1) shipped the extensional substitution vector `SubstVec` + `lookup` + `ext` +
`tabulate`/`toRawTermSubst`.  This file lifts the function-level substitution algebra (identity, composition, and
their three category laws — already proven for `RawTermSubst` in `RawTermSubstCompose.lean` /
`RawTermSubstIdentity.lean` / `RawTermSubstPointwise.lean`) onto `SubstVec` via `lookup` / `ext`, and assembles
`fxBaseSubstCategory : RawCategory` — the genuine TERM-CARRYING category the sconing-transfer ladder needs
(objects are scopes, morphisms `source ⟶ target` are substitutions `SubstVec target source` carrying real
`RawTerm` content, unlike the renaming base whose morphisms are mere variable reindexings).

## What lands here (all zero-axiom)

  * `SubstVec.identity` (+ `identity_lookup`) — the identity substitution vector; its lookup is the variable term.
  * `SubstVec.compose` (+ `lookup_compose`) — substitution composition: apply the second substitution to every
    term of the first (`tabulate (RawTermSubst.compose ...)`); its lookup is `RawTerm.subst secondVec (firstVec
    index)`.  This is the genuine SUBSTITUTION action — strictly richer than renaming composition.
  * `SubstVec.identity_compose` / `compose_identity` / `compose_assoc` — the three category laws, each via `ext`
    pointwise: the LEFT identity reduces to subst-of-a-variable (`rfl`); the RIGHT identity to `subst_pointwise`
    (bridging `(identity).toRawTermSubst ≐ RawTermSubst.identity`) + `subst_identity_apply`; ASSOCIATIVITY to the
    shipped `RawTerm.subst_compose` (the subst-then-subst law) + `subst_pointwise`.
  * `fxBaseSubstCategory : RawCategory.{0,0}` — the assembled term-carrying category; `_identity_eq` /
    `_compose_eq` the defeq-sample bridges (the same shape `fxBaseRenamingVecCategory` exposes, which the sconing
    ladder consumes).

## Honest scope boundary

This lands the `underlying` term-carrying `RawCategory` of the eventual `fxBaseSubstRMC`.  It is NOT yet the full
`RepresentableMapCategory`: that still needs (a) the representable-map class (the display maps / context
projections — the substitution analogue of `weakening`) and (b) the three CwR axioms over THIS base.  Those, plus
the `GlobalSections` / `SconingPreservation` / extraction instances over the term-carrying base (the genuine
canonicity/normalization TRANSFER the renaming base could not host), are the later bricks of this arc.

## Zero-axiom verification

The operations are `tabulate` of the function-level operations; the lookup bridges are `lookup_tabulate`; the
laws are `ext` pointwise composing the shipped `RawTerm.subst_compose` / `subst_identity_apply` / `subst_pointwise`
+ subst-of-variable `rfl` (the variable bridge returns the substituent directly — needs default transparency, so
the left-identity arm closes with an explicit `rfl` after the reducible-only `rw`).  No `funext` (the whole point
of `SubstVec`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-- The identity substitution vector `scope ⟶ scope` (every variable maps to itself). -/
def SubstVec.identity (scope : Nat) : SubstVec scope scope :=
  SubstVec.tabulate RawTermSubst.identity

/-- The identity vector looks up to the variable term (`RawTermSubst.identity index`). -/
theorem SubstVec.identity_lookup (scope : Nat) (index : Fin scope) :
    (SubstVec.identity scope).lookup index = RawTerm.mkGen .gen_var index .childNil :=
  SubstVec.lookup_tabulate RawTermSubst.identity index

/-- **Substitution composition.**  Compose `source ⟶ mid` then `mid ⟶ target` by applying the second
substitution to every `RawTerm` of the first.  The genuine substitution action — strictly richer than renaming
composition. -/
def SubstVec.compose {sourceScope midScope targetScope : Nat}
    (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope) :
    SubstVec targetScope sourceScope :=
  SubstVec.tabulate (RawTermSubst.compose firstVec.toRawTermSubst secondVec.toRawTermSubst)

/-- The composition's lookup is the substitution of the second vector into the first's image. -/
theorem SubstVec.lookup_compose {sourceScope midScope targetScope : Nat}
    (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope)
    (index : Fin sourceScope) :
    (firstVec.compose secondVec).lookup index =
      RawTerm.subst secondVec.toRawTermSubst (firstVec.lookup index) :=
  SubstVec.lookup_tabulate _ index

/-- **Left identity law** — via `ext`; the composition's lookup is `subst v (var index) = v index`, closed by
subst-of-a-variable (`rfl`). -/
theorem SubstVec.identity_compose {targetScope sourceScope : Nat}
    (someVec : SubstVec targetScope sourceScope) :
    (SubstVec.identity sourceScope).compose someVec = someVec :=
  SubstVec.ext _ _ (fun index => by
    rw [SubstVec.lookup_compose, SubstVec.identity_lookup]; rfl)

/-- **Right identity law** — via `ext`; the composition's lookup is `subst (identity.toRawTermSubst) (v index)`,
bridged to `subst RawTermSubst.identity` by `subst_pointwise` and collapsed by `subst_identity_apply`. -/
theorem SubstVec.compose_identity {sourceScope targetScope : Nat}
    (someVec : SubstVec targetScope sourceScope) :
    someVec.compose (SubstVec.identity targetScope) = someVec :=
  SubstVec.ext _ _ (fun index => by
    rw [SubstVec.lookup_compose]
    exact (RawTerm.subst_pointwise (fun position => SubstVec.identity_lookup targetScope position)
      (someVec.lookup index)).trans (RawTerm.subst_identity_apply (someVec.lookup index)))

/-- **Associativity of substitution composition** — via `ext`; both sides reduce (pointwise, through
`lookup_compose`) to a subst-then-subst, equated by the shipped `RawTerm.subst_compose` and re-bridged through the
composed substitution by `subst_pointwise`. -/
theorem SubstVec.compose_assoc {scopeA scopeB scopeC scopeD : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (thirdVec : SubstVec scopeD scopeC) :
    (firstVec.compose secondVec).compose thirdVec =
      firstVec.compose (secondVec.compose thirdVec) :=
  SubstVec.ext _ _ (fun index =>
    calc ((firstVec.compose secondVec).compose thirdVec).lookup index
        = RawTerm.subst thirdVec.toRawTermSubst
            (RawTerm.subst secondVec.toRawTermSubst (firstVec.lookup index)) := by
          rw [SubstVec.lookup_compose, SubstVec.lookup_compose]
      _ = RawTerm.subst
            (RawTermSubst.compose secondVec.toRawTermSubst thirdVec.toRawTermSubst)
            (firstVec.lookup index) :=
          RawTerm.subst_compose secondVec.toRawTermSubst thirdVec.toRawTermSubst (firstVec.lookup index)
      _ = RawTerm.subst (secondVec.compose thirdVec).toRawTermSubst (firstVec.lookup index) :=
          RawTerm.subst_pointwise
            (fun position => (SubstVec.lookup_compose secondVec thirdVec position).symm)
            (firstVec.lookup index)
      _ = (firstVec.compose (secondVec.compose thirdVec)).lookup index :=
          (SubstVec.lookup_compose firstVec (secondVec.compose thirdVec) index).symm)

/-- **The TERM-CARRYING FX category of contexts-and-substitutions.**  Objects are scopes (`Nat`); morphisms
`source ⟶ target` are substitution vectors `SubstVec target source`, carrying real `RawTerm` content.  All three
category laws hold via `ext` (pointwise through the shipped substitution algebra).  Unlike the renaming base
`fxBaseRenamingVecCategory`, whose morphisms are variable reindexings, this base's morphisms are genuine
substitutions — the structure the sconing-transfer ladder needs. -/
def fxBaseSubstCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := fun sourceScope targetScope => SubstVec targetScope sourceScope
  identity := fun scope => SubstVec.identity scope
  compose := fun firstVec secondVec => firstVec.compose secondVec
  composeAssoc := fun firstVec secondVec thirdVec =>
    SubstVec.compose_assoc firstVec secondVec thirdVec
  identityLeft := fun morphism => SubstVec.identity_compose morphism
  identityRight := fun morphism => SubstVec.compose_identity morphism

/-- The categorical identity of `fxBaseSubstCategory` IS the identity substitution vector. -/
theorem fxBaseSubstCategory_identity_eq {scope : Nat} :
    fxBaseSubstCategory.identity scope = SubstVec.identity scope := rfl

/-- The categorical composition of `fxBaseSubstCategory` IS substitution-vector composition. -/
theorem fxBaseSubstCategory_compose_eq {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB) :
    fxBaseSubstCategory.compose firstVec secondVec = firstVec.compose secondVec := rfl

end FX1Poly.Tier0
