import FX1Poly.Tier0.FxBaseSubstDisplayMap
import FX1Poly.Tier0.CwRExtension
import FX1Poly.Tier0.FxBaseRenamingVecRMC
import FX1Poly.Core.RawTermSubstLiftWeaken

/-! # FX1Poly/Tier0/FxBaseSubstTypeFormers
    — Π/Σ as concrete type formers: presheaf-level natural transformations + the literal-record verdict (SN-087, #590)

Uemura's reading: adding Π-types = adding one representable natural transformation
`π : (A : U, B : U^A) → U` over the universe.  This file realizes the Π and Σ formers CONCRETELY in
the SN-086 vocabulary, and settles where the literal `TypeFormer` record can and cannot host them:

  * `SubstVec.liftUnderBinder` — the under-binder lift of a substitution vector (`cons (var 0)
    (substVec ∘ weakening)`), with the pointwise bridge to the kernel's `RawTermSubst.lift`
    (`liftUnderBinder_toRawTermSubst` / `_subst_apply`) and the lift functor laws at the subst level
    (`liftUnderBinder_identity_subst_apply` via the pointwise identity; `_compose_subst_apply` via the
    shipped `RawTermSubst.lift_pointwise` + `lift_compose_pointwise` + `subst_compose`).
  * `binderParameterFamily` — **the Π/Σ parameter object `(A : U, B : U^A)` cellularly**: sections at
    a scope are pairs (domain code, codomain code UNDER ONE BINDER); the action substitutes the
    domain directly and the codomain through the under-binder lift.
  * ★ `piFormerMap` / `sigmaFormerMap : SubstFamilyMap binderParameterFamily typeCellFamily` — **the
    concrete Π/Σ type formers as natural transformations into `Ty`**.  Naturality is the genuine
    substitution-commutes-with-the-former equation (`piFormer_subst_commutes`: the kernel's fold
    computes the former's children spine, the binder child through `RawTermSubst.lift`, identified
    with the categorical lift by `liftUnderBinder_subst_apply`).  These are the concrete instances
    the Uemura bijection (SN-088) pairs with representability and the BKS lift (SN-091) consumes.
  * `typeFormer_overRenamingVecRMC_resultIsIsomorphism` — **the literal-record verdict**: over the
    shipped `fxBaseRenamingVecRMC` the representable-map class is the categorical ISOMORPHISMS, so any
    literal `TypeFormer` record's result map is forced to be an iso renaming — no genuine Π (whose
    result is a FORMER, not an iso) can inhabit the literal record over that base.  The honest home
    of the Π/Σ content is the presheaf level above (exactly the natural-transformation side of
    Uemura's bijection).
  * `identityShapedTypeFormer` + `identityShapedFormerExtension` + `composedIdentityShapedExtensions`
    — the literal `TypeFormer` and `CwRExtension` records ARE inhabited (interface non-vacuity: the
    first extension with a NONEMPTY `newTypeFormers` list, conservativity + faithfulness +
    `CwRExtension.compose` exercised) — at the only shape the iso class admits, the identity, and
    honestly labeled as such.

## Honest scope boundary

The genuine Π/Σ former content lives at the PRESHEAF level (`piFormerMap`/`sigmaFormerMap`), not in
the literal `TypeFormer` record — and the verdict theorem shows that is forced, not a stylistic
choice.  Representability of the formers in the natural-model sense is the comprehension pullback of
the display map (SN-086, `displayClassifier_comprehension`), not iso-membership in the renaming RMC.
The `CwRExtensionConstructionLevel` ledger advances to `concreteTypeFormerInstances` on the strength
of the presheaf-level formers + the inhabited (degenerate-shaped) literal records; the Uemura
BIJECTION (`uemuraBijectionTheorem`) and conservative-extension THEOREM remain open (SN-088).

## Zero-axiom verification

The lift bridge is per-index structural (`rfl` at 0; `lookup_compose` + `weakening_subst_eq_rename` at
successors); the lift laws chain shipped pointwise lemmas through `subst_pointwise`; former naturality
is one rewrite plus the kernel fold's `rfl` computation on a concrete generator; the literal records
are direct constructions over `IsIsomorphism.identity`.  No `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The under-binder lift of a substitution vector -/

/-- **Lift a substitution vector under one binder**: the fresh variable `0` maps to itself, and every
prior variable's image is pushed through the display weakening — `cons (var 0) (substVec ∘
weakening)`.  The extensional analogue of the kernel's `RawTermSubst.lift`. -/
def SubstVec.liftUnderBinder {target source : Nat} (substVec : SubstVec target source) :
    SubstVec (target + 1) (source + 1) :=
  SubstVec.cons (RawTerm.mkGen .gen_var ⟨0, Nat.succ_pos target⟩ .childNil)
    (substVec.compose (SubstVec.weakening target))

/-- The under-binder lift agrees POINTWISE with the kernel's `RawTermSubst.lift`: at `0` both give
the fresh variable (`rfl`); at a successor both weaken the prior image (`lookup_compose` + the
SUBSTVEC-3 deep coherence `weakening_subst_eq_rename`). -/
theorem SubstVec.liftUnderBinder_toRawTermSubst {target source : Nat}
    (substVec : SubstVec target source) (index : Fin (source + 1)) :
    substVec.liftUnderBinder.toRawTermSubst index
      = RawTermSubst.lift substVec.toRawTermSubst index :=
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isLt⟩ => by
      show (substVec.compose (SubstVec.weakening target)).lookup
          ⟨position, Nat.lt_of_succ_lt_succ isLt⟩
        = RawTerm.weaken (substVec.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩)
      rw [SubstVec.lookup_compose, SubstVec.weakening_subst_eq_rename]
      rfl

/-- The under-binder lift acts on every binder-scoped term exactly as the kernel lift
(`subst_pointwise` over the pointwise bridge). -/
theorem SubstVec.liftUnderBinder_subst_apply {target source : Nat}
    (substVec : SubstVec target source) (binderTerm : RawTerm (source + 1)) :
    RawTerm.subst substVec.liftUnderBinder.toRawTermSubst binderTerm
      = RawTerm.subst (RawTermSubst.lift substVec.toRawTermSubst) binderTerm :=
  RawTerm.subst_pointwise
    (fun position => SubstVec.liftUnderBinder_toRawTermSubst substVec position) binderTerm

/-- The lift of the identity vector is pointwise the identity substitution: at `0` definitional; at a
successor the composed weakening of a variable is the shifted variable. -/
theorem SubstVec.liftUnderBinder_identity_pointwise (scope : Nat) (index : Fin (scope + 1)) :
    (SubstVec.identity scope).liftUnderBinder.toRawTermSubst index
      = RawTermSubst.identity index :=
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isLt⟩ => by
      show ((SubstVec.identity scope).compose (SubstVec.weakening scope)).lookup
          ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ = _
      rw [SubstVec.lookup_compose, SubstVec.identity_lookup]
      exact SubstVec.weakening_lookup scope ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- **Lift identity law at the subst level**: substituting a binder-scoped term along the lifted
identity vector is the identity. -/
theorem SubstVec.liftUnderBinder_identity_subst_apply {scope : Nat}
    (binderTerm : RawTerm (scope + 1)) :
    RawTerm.subst (SubstVec.identity scope).liftUnderBinder.toRawTermSubst binderTerm
      = binderTerm :=
  (RawTerm.subst_pointwise
      (fun position => SubstVec.liftUnderBinder_identity_pointwise scope position) binderTerm).trans
    (RawTerm.subst_identity_apply binderTerm)

/-- **Lift composition law at the subst level**: substituting along the lift of a composition is the
composite of the lifted substitutions — through the kernel bridge, the shipped
`RawTermSubst.lift_pointwise` + `lift_compose_pointwise` (the polynomial-monad binder pull), and
`subst_compose`. -/
theorem SubstVec.liftUnderBinder_compose_subst_apply {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (binderTerm : RawTerm (scopeA + 1)) :
    RawTerm.subst (firstVec.compose secondVec).liftUnderBinder.toRawTermSubst binderTerm
      = RawTerm.subst secondVec.liftUnderBinder.toRawTermSubst
          (RawTerm.subst firstVec.liftUnderBinder.toRawTermSubst binderTerm) :=
  calc RawTerm.subst (firstVec.compose secondVec).liftUnderBinder.toRawTermSubst binderTerm
      = RawTerm.subst (RawTermSubst.lift (firstVec.compose secondVec).toRawTermSubst) binderTerm :=
        SubstVec.liftUnderBinder_subst_apply (firstVec.compose secondVec) binderTerm
    _ = RawTerm.subst
          (RawTermSubst.lift
            (RawTermSubst.compose firstVec.toRawTermSubst secondVec.toRawTermSubst))
          binderTerm :=
        RawTerm.subst_pointwise
          (RawTermSubst.lift_pointwise
            (fun position => SubstVec.lookup_compose firstVec secondVec position))
          binderTerm
    _ = RawTerm.subst
          (RawTermSubst.compose
            (RawTermSubst.lift firstVec.toRawTermSubst)
            (RawTermSubst.lift secondVec.toRawTermSubst))
          binderTerm :=
        RawTerm.subst_pointwise
          (RawTermSubst.lift_compose_pointwise firstVec.toRawTermSubst secondVec.toRawTermSubst)
          binderTerm
    _ = RawTerm.subst (RawTermSubst.lift secondVec.toRawTermSubst)
          (RawTerm.subst (RawTermSubst.lift firstVec.toRawTermSubst) binderTerm) :=
        (RawTerm.subst_compose
          (RawTermSubst.lift firstVec.toRawTermSubst)
          (RawTermSubst.lift secondVec.toRawTermSubst) binderTerm).symm
    _ = RawTerm.subst (RawTermSubst.lift secondVec.toRawTermSubst)
          (RawTerm.subst firstVec.liftUnderBinder.toRawTermSubst binderTerm) :=
        congrArg (RawTerm.subst (RawTermSubst.lift secondVec.toRawTermSubst))
          (SubstVec.liftUnderBinder_subst_apply firstVec binderTerm).symm
    _ = RawTerm.subst secondVec.liftUnderBinder.toRawTermSubst
          (RawTerm.subst firstVec.liftUnderBinder.toRawTermSubst binderTerm) :=
        (SubstVec.liftUnderBinder_subst_apply secondVec
          (RawTerm.subst firstVec.liftUnderBinder.toRawTermSubst binderTerm)).symm

/-! ## The Π/Σ parameter object `(A : U, B : U^A)` as a family -/

/-- **The binder parameter family** — Uemura's Π/Σ parameter object `(A : U, B : U^A)` cellularly:
sections at a scope are pairs of a domain code and a codomain code UNDER ONE BINDER; the action
substitutes the domain directly and the codomain through the under-binder lift.  Functor laws are
the lift laws above componentwise (closing by product eta). -/
def binderParameterFamily : SubstActionFamily where
  sections := fun scope => RawTerm scope × RawTerm (scope + 1)
  substAction := fun substVec pair =>
    (RawTerm.subst substVec.toRawTermSubst pair.1,
      RawTerm.subst substVec.liftUnderBinder.toRawTermSubst pair.2)
  mapsIdentity := fun _scope pair => by
    show Prod.mk _ _ = pair
    rw [SubstVec.identity_subst_apply, SubstVec.liftUnderBinder_identity_subst_apply]
  mapsComposition := fun firstVec secondVec pair => by
    show Prod.mk _ _ = Prod.mk _ _
    rw [SubstVec.compose_subst_apply, SubstVec.liftUnderBinder_compose_subst_apply]

/-! ## The Π and Σ formers as natural transformations into `Ty` -/

/-- **Substitution commutes with the Π former** — the naturality square's content: building the
Π-code from substituted components equals substituting the Π-code, because the kernel fold computes
the former's children spine (the binder child through `RawTermSubst.lift`), identified with the
categorical under-binder lift by `liftUnderBinder_subst_apply`. -/
theorem piFormer_subst_commutes {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.mkGen .gen_piTyCode ()
        (.childCons (RawTerm.subst substVec.toRawTermSubst domainCode)
          (.childCons (RawTerm.subst substVec.liftUnderBinder.toRawTermSubst codomainCode)
            .childNil))
      = RawTerm.subst substVec.toRawTermSubst
          (RawTerm.mkGen .gen_piTyCode ()
            (.childCons domainCode (.childCons codomainCode .childNil))) := by
  rw [SubstVec.liftUnderBinder_subst_apply]
  rfl

/-- The Σ twin of `piFormer_subst_commutes` (only the head generator differs). -/
theorem sigmaFormer_subst_commutes {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.mkGen .gen_sigmaTyCode ()
        (.childCons (RawTerm.subst substVec.toRawTermSubst domainCode)
          (.childCons (RawTerm.subst substVec.liftUnderBinder.toRawTermSubst codomainCode)
            .childNil))
      = RawTerm.subst substVec.toRawTermSubst
          (RawTerm.mkGen .gen_sigmaTyCode ()
            (.childCons domainCode (.childCons codomainCode .childNil))) := by
  rw [SubstVec.liftUnderBinder_subst_apply]
  rfl

/-- ★ **The Π type former as a natural transformation** `(A : U, B : U^A) → Ty` — the concrete
presheaf-level type-former instance (the natural-transformation side of Uemura's bijection): the
component builds the Π-code cell; naturality is the substitution-commutes-with-the-former
equation. -/
def piFormerMap : SubstFamilyMap binderParameterFamily typeCellFamily where
  component := fun _scope pair =>
    RawTerm.mkGen .gen_piTyCode () (.childCons pair.1 (.childCons pair.2 .childNil))
  isNatural := fun substVec pair => piFormer_subst_commutes substVec pair.1 pair.2

/-- ★ **The Σ type former as a natural transformation** — the Σ twin of `piFormerMap`. -/
def sigmaFormerMap : SubstFamilyMap binderParameterFamily typeCellFamily where
  component := fun _scope pair =>
    RawTerm.mkGen .gen_sigmaTyCode () (.childCons pair.1 (.childCons pair.2 .childNil))
  isNatural := fun substVec pair => sigmaFormer_subst_commutes substVec pair.1 pair.2

/-! ## The literal `TypeFormer` record over the shipped RMC: the verdict + non-vacuity -/

/-- **The literal-record verdict.**  Over `fxBaseRenamingVecRMC` the representable-map class is the
categorical isomorphisms, so EVERY literal `TypeFormer`'s result map is an iso renaming — a genuine
Π former (whose result map is a type-CODE construction, not an invertible renaming) cannot inhabit
the literal record over that base.  The honest home of Π/Σ is the presheaf level
(`piFormerMap`/`sigmaFormerMap`). -/
theorem typeFormer_overRenamingVecRMC_resultIsIsomorphism {universeScope : Nat}
    (former : TypeFormer fxBaseRenamingVecRMC universeScope) :
    RenamingVec.IsCategoricalIsomorphism former.resultMap :=
  former.resultIsRepresentable

/-- The identity-shaped literal `TypeFormer` — the shape the iso class admits.  Inhabits the record
(interface non-vacuity); honestly DEGENERATE: no former content, per the verdict theorem. -/
def identityShapedTypeFormer (universeScope : Nat) :
    TypeFormer fxBaseRenamingVecRMC universeScope where
  parameterObject :=
    { domain := universeScope, projection := RenamingVec.identity universeScope }
  resultMap := RenamingVec.identity universeScope
  resultIsRepresentable :=
    RenamingVec.isCategoricalIsomorphism_identity universeScope

/-- The first `CwRExtension` with a NONEMPTY `newTypeFormers` list: the identity inclusion of
`fxBaseRenamingVecRMC` carrying the identity-shaped former.  Conservativity is the identity
reflection. -/
def identityShapedFormerExtension (universeScope : Nat) :
    CwRExtension fxBaseRenamingVecRMC :=
  { CwRExtension.identity fxBaseRenamingVecRMC universeScope with
      newTypeFormers := [identityShapedTypeFormer universeScope] }

/-- The extension is faithful (the identity inclusion collapses nothing). -/
theorem identityShapedFormerExtension_isFaithful (universeScope : Nat) :
    (identityShapedFormerExtension universeScope).isFaithful :=
  fun _morphismF _morphismG mapsAgree => mapsAgree

/-- `CwRExtension.compose` exercised on inhabited extensions (the Π-then-Σ packaging shape). -/
def composedIdentityShapedExtensions (universeScope : Nat) :
    CwRExtension fxBaseRenamingVecRMC :=
  (identityShapedFormerExtension universeScope).compose
    (identityShapedFormerExtension universeScope)

/-- Smoke: the composed extension carries the second extension's former list (one former). -/
theorem composedIdentityShapedExtensions_typeFormerCount (universeScope : Nat) :
    (composedIdentityShapedExtensions universeScope).typeFormerCount = 1 := rfl

end FX1Poly.Tier0
