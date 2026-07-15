import FX1Poly.Axis.Context.Context
import FX1Poly.Axis.Context.Instances.Renaming.FxBaseRenamingVecCategory
import FX1Poly.Axis.Context.Instances.Subst.FxBaseSubstCategory

/-! # The renaming ⊂ substitution inclusion (`context-1`, the two-category connector)

`context-0` shipped the context axis as a *pair* of categories side by side —
the renaming RMC (`fxBaseRenamingVecCategory`, the representable maps / variables)
and the substitution category (`fxBaseSubstCategory`, the terms).  This file
*connects* them: the genuine inclusion functor `renaming ⊂ substitution` that
sends each variable-index image of a renaming to its variable *term*.

This is the load-bearing brick of Uemura's renaming-mode / substitution-mode
separation: the renaming category is a subcategory of the substitution category,
and that inclusion is exactly the data normalization (NbE) runs over.

## What lands here (all zero-axiom)

* `RawFunctor` — the generic functor between two `RawCategory`s now lives in
  `RepresentableMapCategory` (the canonical home, shared by the lock carrier,
  the model functors, and this inclusion); imported here, not re-declared.
* `RenamingVec.toSubstVec` (+ `toSubstVec_lookup`) — the morphism map: a
  renaming `RenamingVec target source` becomes the substitution
  `SubstVec target source` whose every entry is the variable term of the
  corresponding image.
* **`RenamingVec.toSubstVec_identity` / `toSubstVec_compose`** — the two functor
  laws, PROVED (not definitional pins): the inclusion sends the identity
  renaming to the identity substitution, and renaming composition to
  substitution composition.  The composition law is the real content — it holds
  because `subst σ (var i)` computes to `σ i` and `RenamingVec` composition is
  variable-reindexing.
* `renamingInclusion : RawFunctor fxBaseRenamingVecCategory fxBaseSubstCategory`
  — the assembled inclusion functor.
* `fxContextAxis_inclusion` — the inclusion typed as a functor between the
  *bundle's* two categories (`fxContextAxis.renamingMode.underlying →
  fxContextAxis.substMode`), so the `context-0` two-category structure is now
  genuinely connected, not two categories side by side.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

open FX1Poly.Core

universe u v

/-- The inclusion of a renaming into a substitution: each variable-index image
`renaming.lookup index` becomes its variable term `var (renaming.lookup index)`. -/
def RenamingVec.toSubstVec {target source : Nat} (renamingVec : RenamingVec target source) :
    SubstVec target source :=
  SubstVec.tabulate (fun index => RawTerm.mkGen .gen_var (renamingVec.lookup index) .childNil)

/-- The inclusion's lookup is the variable term of the renaming's lookup. -/
theorem RenamingVec.toSubstVec_lookup {target source : Nat}
    (renamingVec : RenamingVec target source) (index : Fin source) :
    renamingVec.toSubstVec.lookup index =
      RawTerm.mkGen .gen_var (renamingVec.lookup index) .childNil :=
  SubstVec.lookup_tabulate _ index

/-- **Functor law (identity).**  The inclusion sends the identity renaming to the
identity substitution — both look up to the variable term at each index. -/
theorem RenamingVec.toSubstVec_identity (scope : Nat) :
    (RenamingVec.identity scope).toSubstVec = SubstVec.identity scope :=
  SubstVec.ext _ _ (fun index => by
    rw [RenamingVec.toSubstVec_lookup, RenamingVec.identity_lookup,
        SubstVec.identity_lookup])

/-- **Functor law (composition).**  The inclusion sends renaming composition to
substitution composition.  Pointwise: the left side is the variable term of the
reindexed lookup `second ∘ first`; the right side substitutes the included
`second` into the variable `var (first.lookup index)`, and `subst σ (var j)`
computes to `σ j` — the included `second`'s lookup — which is that same variable
term. -/
theorem RenamingVec.toSubstVec_compose {sourceScope midScope targetScope : Nat}
    (firstRenaming : RenamingVec midScope sourceScope)
    (secondRenaming : RenamingVec targetScope midScope) :
    (firstRenaming.compose secondRenaming).toSubstVec =
      firstRenaming.toSubstVec.compose secondRenaming.toSubstVec :=
  SubstVec.ext _ _ (fun index => by
    rw [RenamingVec.toSubstVec_lookup, RenamingVec.lookup_compose,
        SubstVec.lookup_compose, RenamingVec.toSubstVec_lookup]
    exact (RenamingVec.toSubstVec_lookup secondRenaming
      (firstRenaming.lookup index)).symm)

/-- **The renaming ⊂ substitution inclusion functor.**  Objects are fixed
(both categories' objects are scopes); morphisms are the variable-term inclusion
`toSubstVec`, with the two functor laws above.  The renaming category (the
representable maps) is a genuine subcategory of the substitution category. -/
def renamingInclusion : RawFunctor fxBaseRenamingVecCategory fxBaseSubstCategory where
  mapObject := fun scope => scope
  mapMorphism := fun renamingVec => renamingVec.toSubstVec
  preservesIdentity := fun scope => RenamingVec.toSubstVec_identity scope
  preservesComposition := fun firstRenaming secondRenaming =>
    RenamingVec.toSubstVec_compose firstRenaming secondRenaming

/-- ★ The inclusion typed as a functor between the **FX context axis bundle's**
two categories: `fxContextAxis.renamingMode.underlying → fxContextAxis.substMode`.
This is what makes the `context-0` two-category structure genuinely *connected*
— the renaming-mode includes into the substitution-mode — rather than two
categories declared side by side. -/
def fxContextAxis_inclusion :
    RawFunctor fxContextAxis.renamingMode.underlying fxContextAxis.substMode :=
  renamingInclusion

end FX1Poly.Axis
