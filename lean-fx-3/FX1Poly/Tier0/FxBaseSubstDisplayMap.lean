import FX1Poly.Tier0.FxBaseSubstComprehension

/-! # FX1Poly/Tier0/FxBaseSubstDisplayMap
    — the cellular Tm↠Ty display map over the term-carrying base + its comprehension pullback (SN-086, #589)

The Natural-Model reading of a type theory presents typing as a map of presheaves `Tm ↠ Ty` over the
category of contexts-and-substitutions, REPRESENTABLE in the sense that pulling it back along any
generalized element of `Ty` is context extension.  This file realizes that display map CELLULARLY over
the shipped term-carrying base `fxBaseSubstCategory` (SUBSTVEC 1–9):

  * `SubstActionFamily` — a scope-indexed family with a functorial substitution action: the COVARIANT
    functor `fxBaseSubstCategory → Type` (in this base's orientation a morphism `X ⟶ Y` is
    `SubstVec Y X`, so `RawTerm.subst` acts `sections X → sections Y`; the shipped `GlobalSections`
    is the contravariant twin).
  * `SubstVec.identity_subst_apply` / `compose_subst_apply` — the term-level functor laws, lifted from
    the shipped substitution algebra (`subst_identity_apply` / `subst_compose` / `subst_pointwise`).
  * `typeCellFamily` — `Ty`: type-position cells (`sections scope = RawTerm scope`) with the
    substitution action.
  * `ClassifiedCell` + `classifiedCellFamily` — `Tm`: term-position cells PAIRED with their
    classifiers, action componentwise.
  * `displayClassifier : SubstFamilyMap classifiedCellFamily typeCellFamily` — **the display map**:
    the natural transformation sending a classified term-cell to its classifier ("a term goes to its
    type"); naturality is `rfl` (substitution acts componentwise).
  * `genericClassifiedCell typeCell` — the GENERIC element over the extended scope: subject = the
    fresh variable `0`, classifier = the weakened `typeCell` (`displayClassifier` sends it to the
    weakening-pushforward of `typeCell` — `genericClassifiedCell_display`, `rfl`).
  * ★ `displayClassifier_comprehension` — **the comprehension pullback universal property**: for every
    generalized element (`closingVec : scope ⟶ ambientScope` and a classified cell lying over
    `typeCell`'s pushforward), there is a UNIQUE mediator `(scope + 1) ⟶ ambientScope` that projects
    to `closingVec` through the display substitution `SubstVec.weakening` and carries the generic cell
    to the given one.  Existence = `SubstVec.cons` (comprehension); uniqueness = `SubstVec.cons_unique`.
    This is the natural-model representability of the display map, in generalized-element form, proved
    entirely from the shipped comprehension bricks (SUBSTVEC-3/4).

## Honest scope boundary

This is the RAW cellular display map: `Tm` carries (subject, classifier) PAIRS with no typing
judgment — the pullback property is the de Bruijn comprehension algebra, not a metatheorem.  The FX
content — "representability = the DECIDABLE TYPING FIBRATION" (#486: the typed refinement of each
display fiber has decidable membership, via the shipped `HasTypeDesc.decidableOfWellFormed`) — lives
in `FX1Poly/Typed/DisplayMapDecidableFibration.lean`, which imports this module (Tier0 stays free of
`FX1Poly.Typed` imports, preserving the established dependency direction).  Also honest: in the
RENAMING RMC (`fxBaseRenamingVecRMC`) the representable-map class is the categorical isomorphisms, and
the weakening is NOT an iso — the display map's representability is the COMPREHENSION property over the
TERM-carrying base stated here, exactly as `FxBaseRenamingVecGlobalSections` predicted ("SN-086 …
needs that term structure and is NOT buildable over the [pure renaming] base").

## Zero-axiom verification

Functor laws are the shipped substitution algebra through `subst_pointwise`; the family records close
by structure eta after componentwise rewrites; the pullback existence is `cons` + the p/v laws and its
uniqueness is `cons_unique`; naturality and the generic-element computations are `rfl`.  No `funext`
(the whole point of `SubstVec`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-- Substituting along the identity vector is the identity on terms — the term-level identity functor
law, bridged through `subst_pointwise` (the vector's lookup is the identity substitution pointwise)
and collapsed by the shipped `subst_identity_apply`. -/
theorem SubstVec.identity_subst_apply {scope : Nat} (term : RawTerm scope) :
    RawTerm.subst (SubstVec.identity scope).toRawTermSubst term = term :=
  (RawTerm.subst_pointwise (fun position => SubstVec.identity_lookup scope position) term).trans
    (RawTerm.subst_identity_apply term)

/-- Substituting along a composed vector is the composite of the substitutions — the term-level
composition functor law, bridged through `subst_pointwise` (the composed vector's lookup is the
function-level composed substitution pointwise) and the shipped `subst_compose`. -/
theorem SubstVec.compose_subst_apply {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (term : RawTerm scopeA) :
    RawTerm.subst (firstVec.compose secondVec).toRawTermSubst term =
      RawTerm.subst secondVec.toRawTermSubst (RawTerm.subst firstVec.toRawTermSubst term) :=
  (RawTerm.subst_pointwise
      (fun position => SubstVec.lookup_compose firstVec secondVec position) term).trans
    (RawTerm.subst_compose firstVec.toRawTermSubst secondVec.toRawTermSubst term).symm

/-- A scope-indexed family with a functorial substitution action — the COVARIANT functor
`fxBaseSubstCategory → Type`.  In this base's orientation a morphism `X ⟶ Y` is `SubstVec Y X`
(X-many terms over scope `Y`), so the action carries `sections X` to `sections Y`; the shipped
contravariant `GlobalSections` is its dual.  The presheaf vocabulary the display map lives in. -/
structure SubstActionFamily where
  sections : Nat → Type
  substAction : {sourceScope targetScope : Nat} →
    SubstVec targetScope sourceScope → sections sourceScope → sections targetScope
  mapsIdentity : ∀ (scope : Nat) (element : sections scope),
    substAction (SubstVec.identity scope) element = element
  mapsComposition : ∀ {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (element : sections scopeA),
    substAction (firstVec.compose secondVec) element =
      substAction secondVec (substAction firstVec element)

/-- **`Ty` — the family of type-position cells.**  Sections at a scope are the raw cells available in
type position there; the action is the substitution itself.  Functor laws are the term-level laws. -/
def typeCellFamily : SubstActionFamily where
  sections := RawTerm
  substAction := fun substVec typeCell => RawTerm.subst substVec.toRawTermSubst typeCell
  mapsIdentity := fun _scope typeCell => SubstVec.identity_subst_apply typeCell
  mapsComposition := fun firstVec secondVec typeCell =>
    SubstVec.compose_subst_apply firstVec secondVec typeCell

/-- A term-position cell PAIRED with its classifier — the elements of the `Tm` family.  The display
map projects the classifier component. -/
structure ClassifiedCell (scope : Nat) where
  subjectCell : RawTerm scope
  classifierCell : RawTerm scope

/-- Two classified cells with equal components are equal (structure eta via component matching). -/
theorem ClassifiedCell.componentsEqual {scope : Nat}
    {firstCell secondCell : ClassifiedCell scope}
    (subjectsAgree : firstCell.subjectCell = secondCell.subjectCell)
    (classifiersAgree : firstCell.classifierCell = secondCell.classifierCell) :
    firstCell = secondCell :=
  match firstCell, secondCell, subjectsAgree, classifiersAgree with
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- **`Tm` — the family of classified term-cells.**  The substitution action is componentwise; the
functor laws reduce to the term-level laws on each component (closing by structure eta). -/
def classifiedCellFamily : SubstActionFamily where
  sections := ClassifiedCell
  substAction := fun substVec cell =>
    { subjectCell := RawTerm.subst substVec.toRawTermSubst cell.subjectCell
      classifierCell := RawTerm.subst substVec.toRawTermSubst cell.classifierCell }
  mapsIdentity := fun _scope cell => by
    show ClassifiedCell.mk _ _ = cell
    rw [SubstVec.identity_subst_apply, SubstVec.identity_subst_apply]
  mapsComposition := fun firstVec secondVec cell => by
    show ClassifiedCell.mk _ _ = ClassifiedCell.mk _ _
    rw [SubstVec.compose_subst_apply, SubstVec.compose_subst_apply]

/-- A map of scope-indexed families commuting with the substitution action — a natural transformation
between the covariant functors. -/
structure SubstFamilyMap (sourceFamily targetFamily : SubstActionFamily) where
  component : (scope : Nat) → sourceFamily.sections scope → targetFamily.sections scope
  isNatural : ∀ {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope)
    (element : sourceFamily.sections sourceScope),
    component targetScope (sourceFamily.substAction substVec element) =
      targetFamily.substAction substVec (component sourceScope element)

/-- ★ **The Tm↠Ty display map**: the natural transformation sending a classified term-cell to its
classifier — "a term goes to its type".  Naturality is `rfl` because the `Tm` action is componentwise
and the classifier component's action IS the `Ty` action. -/
def displayClassifier : SubstFamilyMap classifiedCellFamily typeCellFamily where
  component := fun _scope cell => cell.classifierCell
  isNatural := fun _substVec _cell => rfl

/-- **The generic element of the comprehension**: over the extended scope, the freshly-bound variable
`0` classified by the weakened `typeCell`.  The universal classified cell the comprehension pullback
carries to every other cell lying over `typeCell`. -/
def genericClassifiedCell {scope : Nat} (typeCell : RawTerm scope) :
    ClassifiedCell (scope + 1) where
  subjectCell := RawTerm.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil
  classifierCell := RawTerm.subst (SubstVec.weakening scope).toRawTermSubst typeCell

/-- The display map sends the generic element to the weakening-pushforward of its type cell — the
commuting boundary of the comprehension square (`rfl`). -/
theorem genericClassifiedCell_display {scope : Nat} (typeCell : RawTerm scope) :
    displayClassifier.component (scope + 1) (genericClassifiedCell typeCell) =
      typeCellFamily.substAction (SubstVec.weakening scope) typeCell := rfl

/-- ★ **The comprehension pullback universal property — the display map is representable.**  For
every generalized element of `Ty` (a closing vector `scope ⟶ ambientScope` together with a classified
cell lying over `typeCell`'s pushforward), there is a mediator `(scope + 1) ⟶ ambientScope` that
(a) projects to the closing vector through the display substitution `SubstVec.weakening` and
(b) carries the generic classified cell to the given cell — and the mediator is UNIQUE with those two
properties.  Existence is comprehension (`SubstVec.cons` + the p/v laws); uniqueness is
`SubstVec.cons_unique`.  This is the Natural-Model pullback square in generalized-element form:
context extension represents the display map. -/
theorem displayClassifier_comprehension {scope ambientScope : Nat}
    (typeCell : RawTerm scope) (closingVec : SubstVec ambientScope scope)
    (cell : ClassifiedCell ambientScope)
    (liesOverTypeCell :
      cell.classifierCell = RawTerm.subst closingVec.toRawTermSubst typeCell) :
    ∃ mediator : SubstVec ambientScope (scope + 1),
      ((SubstVec.weakening scope).compose mediator = closingVec ∧
        classifiedCellFamily.substAction mediator (genericClassifiedCell typeCell) = cell) ∧
      ∀ otherMediator : SubstVec ambientScope (scope + 1),
        (SubstVec.weakening scope).compose otherMediator = closingVec →
        classifiedCellFamily.substAction otherMediator (genericClassifiedCell typeCell) = cell →
        otherMediator = SubstVec.cons cell.subjectCell closingVec := by
  refine ⟨SubstVec.cons cell.subjectCell closingVec,
    ⟨SubstVec.weakening_compose_cons cell.subjectCell closingVec, ?actsToCell⟩,
    fun otherMediator projectsToClosing actsToCell => ?uniqueness⟩
  case actsToCell =>
    -- the classifier component travels through the composed substitution and the p-law
    have classifierComputes :
        RawTerm.subst (SubstVec.cons cell.subjectCell closingVec).toRawTermSubst
            (RawTerm.subst (SubstVec.weakening scope).toRawTermSubst typeCell)
          = cell.classifierCell :=
      calc RawTerm.subst (SubstVec.cons cell.subjectCell closingVec).toRawTermSubst
              (RawTerm.subst (SubstVec.weakening scope).toRawTermSubst typeCell)
          = RawTerm.subst
              ((SubstVec.weakening scope).compose
                (SubstVec.cons cell.subjectCell closingVec)).toRawTermSubst typeCell :=
            (SubstVec.compose_subst_apply (SubstVec.weakening scope)
              (SubstVec.cons cell.subjectCell closingVec) typeCell).symm
        _ = RawTerm.subst closingVec.toRawTermSubst typeCell := by
            rw [SubstVec.weakening_compose_cons]
        _ = cell.classifierCell := liesOverTypeCell.symm
    -- the subject component is the v-law (definitional); assemble by components
    exact ClassifiedCell.componentsEqual rfl classifierComputes
  case uniqueness =>
    -- the subject component of the action condition recovers the zeroth lookup
    have zerothIsSubject :
        otherMediator.lookup ⟨0, Nat.succ_pos scope⟩ = cell.subjectCell :=
      congrArg ClassifiedCell.subjectCell actsToCell
    exact SubstVec.cons_unique cell.subjectCell closingVec otherMediator
      projectsToClosing zerothIsSubject

end FX1Poly.Tier0
