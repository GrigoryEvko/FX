import FX1Poly.Tier0.FxBaseSubstTypeFormers

/-! # Tier0/ContextOmega/DimensionalFunctor — the dimensional weakening endofunctor (context-3, the adjoint-string half)

The RIGHT/transpension half of context-3 needs the dimensional adjoint string `Ⅎ ⊣ Σ ⊣ Ω ⊣ Π ⊣ ◊`
(Nuyts–Devriese 2008.08533) over the context base.  Every adjoint in that string is built from ONE
endofunctor on the presheaf category — the **dimensional weakening / dimension-extension functor**
that pushes a family `F` into a context with one extra (dimension) variable.  This module builds that
functor, `dimExtend`, with its full functor laws and its action on morphisms, all zero-axiom.  It is
the categorical substrate the adjoint string is assembled from.

## What is built

  * `SubstVec.liftUnderBinder_identity` / `SubstVec.liftUnderBinder_compose` — the under-binder lift is
    FUNCTORIAL at the VEC level: it preserves the identity substitution and substitution composition.
    The shipped `FxBaseSubstTypeFormers` proved these only at the term-action level
    (`liftUnderBinder_identity_subst_apply` / `_compose_subst_apply`); here they are lifted to genuine
    `SubstVec` equalities via `SubstVec.ext` (pointwise), because a general family's action is abstract
    (not `RawTerm.subst`), so it needs the vec-level law to feed `mapsIdentity` / `mapsComposition`.
  * ★ `dimExtend` — **the dimensional weakening endofunctor** on `SubstActionFamily`.  `(dimExtend F)`
    at scope `n` is `F (n + 1)` (the family `F` re-read in a context with one more variable), with
    action `F.substAction closingVec.liftUnderBinder` (substitute under the new binder).  Its two
    functor laws are exactly the shipped family laws of `F` precomposed with the two vec-level lift
    laws.  This is the `Ω`/reindexing functor of the dimensional adjoint string — `δ : PSh ⟶ PSh`.
  * `dimExtendMap` — `dimExtend`'s action on morphisms: a natural transformation `F ⟶ G` lifts to a
    natural transformation `dimExtend F ⟶ dimExtend G`, its naturality being the original naturality
    evaluated at the lifted closing vector.  Together with `dimExtend` this exhibits `dimExtend` as an
    endofunctor on the natural-transformation category (the presheaf category) — on objects AND arrows.

## Honest boundaries (recorded, not faked)

  * **The adjunctions `Σ ⊣ Ω ⊣ Π` and the transpension `◊`** — the full dimensional adjoint string —
    are NOT proven here.  This module ships the central functor they are built from; exhibiting the
    hom-set bijections of `SubstFamilyMap`s is the next increment, and the transpension `◊` (the
    rightmost adjoint) does NOT commute with substitution (Nuyts–Devriese §2.1.7), so it additionally
    needs the affine/fresh layer — the shipped `Core/TranspensionAffineContractionEquivariance`
    (TRANSP-DSL) and `gen_transpension` (TRANSP-1 #1418) are its SYNTACTIC build-out.
  * **The 2-functor laws** `dimExtend (id) = id` and `dimExtend (g ∘ f) = dimExtend g ∘ dimExtend f`
    are equalities of `SubstFamilyMap`s, which require `funext` on the `component` field — and `funext`
    is derived from `Quot.sound` in Lean, so it is OFF the zero-axiom path.  The per-morphism action
    `dimExtendMap` is funext-free (it is an equality of elements) and IS shipped.

## Zero-axiom verification

The two vec lift laws are `SubstVec.ext` + the shipped pointwise lift lemmas (`liftUnderBinder`'s
identity-pointwise and its `subst`-apply law at a variable argument, where `subst σ (var i) = σ i` by
`subst_var_reduces`); `dimExtend`'s functor laws are `rw` of those vec laws then `F`'s own family laws;
`dimExtendMap`'s naturality is the source map's naturality at the lifted vector.  No `funext`, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The under-binder lift is functorial at the vector level -/

/-- **The lift of the identity vector is the identity vector** (one scope up).  Proven pointwise via
`SubstVec.ext`: at each index the shipped `liftUnderBinder_identity_pointwise` gives
`RawTermSubst.identity index`, which is definitionally the variable cell `identity_lookup` returns. -/
theorem SubstVec.liftUnderBinder_identity (scope : Nat) :
    (SubstVec.identity scope).liftUnderBinder = SubstVec.identity (scope + 1) :=
  SubstVec.ext _ _ (fun index =>
    (SubstVec.liftUnderBinder_identity_pointwise scope index).trans
      (SubstVec.identity_lookup (scope + 1) index).symm)

/-- **The lift of a composition is the composition of the lifts** — the lift is a functor on the
substitution category.  Proven pointwise via `SubstVec.ext`: the shipped term-action law
`liftUnderBinder_compose_subst_apply` at the variable argument `var index` (where `subst σ (var i)` is
`σ i` definitionally, `subst_var_reduces`) gives exactly the looked-up composition after
`lookup_compose`. -/
theorem SubstVec.liftUnderBinder_compose {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB) :
    (firstVec.compose secondVec).liftUnderBinder
      = firstVec.liftUnderBinder.compose secondVec.liftUnderBinder :=
  SubstVec.ext _ _ (fun index => by
    -- `subst σ (var index) = σ index` is definitional (`subst_var_reduces` is `rfl`), so the shipped
    -- term-action law at the variable argument IS the looked-up-composition equation after
    -- `lookup_compose` — closed by `exact` through defeq.
    rw [SubstVec.lookup_compose]
    exact SubstVec.liftUnderBinder_compose_subst_apply firstVec secondVec
      (RawTerm.mkGen .gen_var index .childNil))

end FX1Poly.Tier0

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The dimensional weakening endofunctor -/

/-- ★ **The dimensional weakening endofunctor `δ` on the presheaf category.**  `(dimExtend family)`
re-reads `family` in a context with one extra (dimension) variable: its sections at scope `n` are
`family.sections (n + 1)`, and a closing substitution acts by lifting under the new binder
(`liftUnderBinder`) and then applying `family`'s action.  The functor laws are `family`'s own functor
laws transported across the two vector-level lift laws.  This is the `Ω`/reindexing functor the
dimensional adjoint string `Σ ⊣ Ω ⊣ Π` is built from. -/
def dimExtend (family : SubstActionFamily) : SubstActionFamily where
  sections := fun scope => family.sections (scope + 1)
  substAction := fun closingVec element => family.substAction closingVec.liftUnderBinder element
  mapsIdentity := fun scope element => by
    show family.substAction (SubstVec.identity scope).liftUnderBinder element = element
    rw [SubstVec.liftUnderBinder_identity]
    exact family.mapsIdentity (scope + 1) element
  mapsComposition := fun firstVec secondVec element => by
    show family.substAction (firstVec.compose secondVec).liftUnderBinder element
      = family.substAction secondVec.liftUnderBinder (family.substAction firstVec.liftUnderBinder element)
    rw [SubstVec.liftUnderBinder_compose]
    exact family.mapsComposition firstVec.liftUnderBinder secondVec.liftUnderBinder element

/-- **`dimExtend`'s action on morphisms.**  A natural transformation `F ⟶ G` lifts to
`dimExtend F ⟶ dimExtend G` by shifting every component one scope up.  Naturality is the source map's
naturality evaluated at the LIFTED closing vector — no new proof obligation.  Together with `dimExtend`
on objects this is the dimensional weakening endofunctor on the whole presheaf (natural-transformation)
category. -/
def dimExtendMap {sourceFamily targetFamily : SubstActionFamily}
    (natTrans : SubstFamilyMap sourceFamily targetFamily) :
    SubstFamilyMap (dimExtend sourceFamily) (dimExtend targetFamily) where
  component := fun scope element => natTrans.component (scope + 1) element
  isNatural := fun substVec element => natTrans.isNatural substVec.liftUnderBinder element

/-- Smoke: the dimensional weakening of the `Ty` family shifts type-position cells one scope up. -/
theorem dimExtend_typeCellFamily_sections (scope : Nat) :
    (dimExtend typeCellFamily).sections scope = RawTerm (scope + 1) := rfl

/-- Smoke: lifting the display map `Tm ↠ Ty` under the dimensional functor shifts its component. -/
theorem dimExtendMap_displayClassifier_component (scope : Nat)
    (cell : (dimExtend classifiedCellFamily).sections scope) :
    (dimExtendMap displayClassifier).component scope cell = cell.classifierCell := rfl

end FX1Poly.Tier0.ContextOmega
