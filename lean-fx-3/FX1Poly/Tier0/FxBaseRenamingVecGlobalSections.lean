import FX1Poly.Tier0.InternalSconing
import FX1Poly.Tier0.FxBaseRenamingVecCategory

/-! # FX1Poly/Tier0/FxBaseRenamingVecGlobalSections
    — the `GlobalSections` instance over the extensional renaming base (SN-089, #592)

`InternalSconing.lean` defines `GlobalSections category` — a contravariant presheaf
(`sections : Object → Type w`, `sectionMap : Morphism A B → sections B → sections A`, with
identity/composition functoriality laws) plus a distinguished `terminalObject`.  It is the "global
elements / closed-substitution" functor the BKS sconing construction glues semantic domains onto
(`SconingObject.realizationMap : semanticDomain → globalSections.sections syntacticObject`).

This file supplies the FIRST `GlobalSections` over a genuine FX category — the extensional renaming
base `fxBaseRenamingVecCategory` (closed by the `fxBaseRMC` track, SN-084/085/085a).  The canonical
global-sections functor is the REPRESENTABLE presheaf `Hom(-, T)` at a terminal object `T`:
`sections X = Morphism X T`, `sectionMap = precomposition`, functoriality = the category's
identity/associativity laws.  In the renaming category the terminal object is scope `1`
(`Hom(X, 1)` is a singleton — there is exactly one renaming into a one-variable scope, every source
variable mapping to variable 0); scope `0` is NOT terminal, since `Hom(X, 0)` is EMPTY for `X > 0`.

## What lands here (all zero-axiom)

  * `GlobalSections.representable chosenObject` — the representable presheaf `Hom(-, chosenObject)` as
    a `GlobalSections` over ANY `RawCategory`.  `sectionMap` = `category.compose` (precomposition);
    `mapsIdentity` = `category.identityLeft`; `mapsComposition` = `category.composeAssoc`.  Generic,
    reusable for any future CwR base.
  * `finOneIsZero` — every `Fin 1` value has component `0` (`Fin 1` is a subsingleton), by structural
    index split (`⟨0,_⟩` / `⟨_+1,_⟩` with `Nat.not_lt_zero`), no `Fin.cases` (which leaks `propext`).
  * `fxBaseRenamingVecScopeOneTerminal` — scope `1` is terminal: any two renamings `scope ⟶ 1` are
    equal, via `RenamingVec.ext` (every lookup lands in `Fin 1`, forced to `0` by `finOneIsZero`).
  * `fxBaseRenamingVecGlobalSections` — THE instance: `GlobalSections.representable` at scope `1`.
  * `fxBaseRenamingVecGlobalSections_terminal_subsingleton` — smoke: the sections at the terminal are
    a subsingleton (the "exactly one closed renaming" reading of global elements).

## Honest scope boundary

This is the representable-at-terminal `GlobalSections` — the STANDARD global-sections shape (the
contravariant `Hom(-, T)` functor with its functoriality laws), realized zero-axiom over the renaming
base.  It is the structural prerequisite the sconing ladder consumes (`SconingObject` /
`SconingPreservation` take a `GlobalSections` as a parameter).  It is NOT yet a NON-VACUOUS
canonicity-extracting global-sections functor: the pure renaming category carries no term/type
structure, so the realization presheaves whose sections are "canonical forms at a type" are downstream
work, available only once a term-carrying CwR base replaces the pure renaming base (SN-086 display map
/ SN-088 Uemura bijection need exactly that term structure and are NOT buildable over this base).

## Zero-axiom verification

`GlobalSections.representable` is pure structure population over the category laws (`identityLeft` /
`composeAssoc`).  The terminality proof is `RenamingVec.ext` (the extensional base's load-bearing
lemma) composed with a structural `Fin 1` subsingleton argument (`finOneIsZero` by index split +
`Nat.not_lt_zero`, then `Fin.eq_of_val_eq`).  No `funext`, no `Fin.cases`, no numeral `OfNat` on the
`Object` projection (the terminal scope is fixed by `(1 : Nat)` ascription).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

universe u v

/-- The representable presheaf `Hom(-, chosenObject)` as a `GlobalSections` over any `RawCategory`:
`sections X` = morphisms `X ⟶ chosenObject`, `sectionMap` = precomposition.  Functoriality is the
category's identity/associativity laws.  Generic — reusable for any future CwR base. -/
def GlobalSections.representable {category : RawCategory.{u, v}} (chosenObject : category.Object) :
    GlobalSections.{u, v, v} category where
  terminalObject := chosenObject
  sections := fun objectX => category.Morphism objectX chosenObject
  sectionMap := fun morphismAB sectionB => category.compose morphismAB sectionB
  mapsIdentity := fun _objectA closedSection => category.identityLeft closedSection
  mapsComposition := fun morphismF morphismG closedSection =>
    category.composeAssoc morphismF morphismG closedSection

/-- Every `Fin 1` value has component `0` (`Fin 1` is a subsingleton).  Structural index split — no
`Fin.cases` (which leaks `propext`). -/
theorem finOneIsZero : (oneIndex : Fin 1) → oneIndex.val = 0
  | ⟨0, _⟩ => rfl
  | ⟨_position + 1, isLt⟩ => absurd (Nat.lt_of_succ_lt_succ isLt) (Nat.not_lt_zero _)

/-- **Scope 1 is terminal in the renaming category.**  There is a unique morphism from any scope into
it: any two renamings `scope ⟶ 1` are equal, by `ext` (every lookup lands in `Fin 1`, forced to `0`
by `finOneIsZero`).  This is what makes `Hom(-, 1)` the canonical global-sections functor. -/
theorem fxBaseRenamingVecScopeOneTerminal (scope : Nat)
    (firstMorphism secondMorphism : RenamingVec 1 scope) :
    firstMorphism = secondMorphism :=
  RenamingVec.ext firstMorphism secondMorphism (fun index =>
    Fin.eq_of_val_eq ((finOneIsZero (firstMorphism.lookup index)).trans
      (finOneIsZero (secondMorphism.lookup index)).symm))

/-- **The `GlobalSections` instance for the renaming base** — the representable presheaf at the
terminal scope `1`.  `sections X = RenamingVec 1 X` (the closed renamings into the terminal scope);
`sectionMap` = renaming precomposition. -/
def fxBaseRenamingVecGlobalSections : GlobalSections.{0, 0, 0} fxBaseRenamingVecCategory :=
  GlobalSections.representable (category := fxBaseRenamingVecCategory) (1 : Nat)

/-- Smoke: the sections at the terminal are a subsingleton — the "exactly one closed renaming into the
terminal scope" reading of global elements. -/
theorem fxBaseRenamingVecGlobalSections_terminal_subsingleton (scope : Nat)
    (firstSection secondSection : fxBaseRenamingVecGlobalSections.sections scope) :
    firstSection = secondSection :=
  fxBaseRenamingVecScopeOneTerminal scope firstSection secondSection

end FX1Poly.Tier0
