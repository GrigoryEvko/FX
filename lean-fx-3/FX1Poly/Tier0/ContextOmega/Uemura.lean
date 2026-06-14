import FX1Poly.Tier0.FxBaseSubstTypeFormers

/-! # Tier0/ContextOmega/Uemura — type-formers ARE representable natural transformations (context-2, SN-088)

The Uemura keystone of the context axis.  In a representable map category the display map `Tm ↠ Ty`
is representable (its pullback along any generalized element of `Ty` is context extension), and
Uemura's reading of a type-former is: a representable natural transformation into the universe `Ty`.
This module proves the BIJECTION direction that was left open by `FxBaseSubstTypeFormers`
(`uemuraBijectionTheorem … remain open (SN-088)`): for the FX cellular base, EVERY natural
transformation `F ⟶ Ty` (every type-former) is automatically representable, with Π and Σ as
instances, and the former is recovered from its generic element.

## What is built (all from shipped pieces, zero new substrate)

  * `IsRepresentableFormer formerMap` — the representability property of a former: the pullback of the
    display map `displayClassifier` along `formerMap` has the comprehension universal property at every
    parameter (existence + uniqueness of the mediator, in generalized-element form).
  * ★ `formerComprehension` — **THE keystone**: every `formerMap : F ⟶ Ty` satisfies
    `IsRepresentableFormer`.  The proof is one line: rewrite "lies over the formed type at the
    substituted parameter" through the former's naturality into "lies over the pushforward of the
    formed type," then apply the shipped `displayClassifier_comprehension` at the formed type.  This is
    Uemura's content — representability is uniform in the type, so a type-former adds NOTHING to it; it
    rides along.  Categorically: representable maps are closed under pullback (CwR Axiom 1), here
    instantiated at the universe display map.
  * `piFormerComprehension` / `sigmaFormerComprehension` — the Π/Σ instances: the comprehension of
    Π-types / Σ-types as concrete representable formers.
  * `RepresentableTypeFormer F` + `ofFormer` / `toFormer` + `toFormer_ofFormer` / `ofFormer_toFormer`
    — **the bijection** `RepresentableTypeFormer F ≃ (F ⟶ Ty)`: bundling a former with its (automatic)
    representability witness is a structure equivalent to the bare former.  The `ofFormer_toFormer`
    round-trip closes by Lean's definitional proof irrelevance on the `Prop`-valued witness field — no
    `propext`.  This is "type-formers and representable natural transformations coincide for the FX
    base."
  * `piRepresentableFormer` / `sigmaRepresentableFormer` — Π and Σ inhabit the bundle (non-vacuity).
  * `formerDeterminedByGenericClassifier` — the converse half: the former is RECOVERED from its
    generic element by taking its classifier (`displayClassifier` of `genericClassifiedCell`), up to
    the canonical weakening.  The natural-model statement "a type-former is determined by its generic
    element."

## Honest boundary

This establishes the bijection over the term-carrying CELLULAR base (`displayClassifier`,
`classifiedCellFamily`, the SN-086/087 substrate) — the genuine natural-model home Uemura predicts.
The fully-abstract Uemura theorem (a universe object classifying an ARBITRARY representable-map class
over an arbitrary CwR) is not re-stated here; the FX instance is the cellular display map, whose
representability is the shipped `displayClassifier_comprehension`.  This module does NOT promote
`fxContextOmega`'s representable class (still the renaming-RMC isomorphisms) to the display maps —
exactly as `context-1` built `comprehensionBijection` over the subst base without re-wiring the
renaming base.  The content here is what a future subst-RMC-promotion capstone (context-21) would
wire in.

## Zero-axiom verification

`formerComprehension` is `displayClassifier_comprehension` precomposed with `SubstFamilyMap.isNatural`
(`Eq.trans`); the bijection's hard round-trip is `cases` + `rfl` through definitional proof
irrelevance on a `Prop` field; the generic-element determination is `genericClassifiedCell_display`
chained with naturality.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The representability property of a type-former -/

/-- **A type-former is representable** when the pullback of the display map `Tm ↠ Ty` along it has the
comprehension universal property at every parameter.  Spelled in generalized-element form (matching
the shipped `displayClassifier_comprehension`): for every parameter `param : F scope`, closing vector
`closingVec : scope ⟶ ambientScope`, and classified cell lying over the formed type at the substituted
parameter, there is a UNIQUE mediator `(scope + 1) ⟶ ambientScope` projecting to `closingVec` through
the display weakening and carrying the generic classified cell to the given one.  This is exactly
"`formerMap` is a representable natural transformation into `Ty`". -/
def IsRepresentableFormer {parameterFamily : SubstActionFamily}
    (formerMap : SubstFamilyMap parameterFamily typeCellFamily) : Prop :=
  ∀ {scope ambientScope : Nat}
    (param : parameterFamily.sections scope)
    (closingVec : SubstVec ambientScope scope)
    (cell : ClassifiedCell ambientScope),
    cell.classifierCell
      = formerMap.component ambientScope (parameterFamily.substAction closingVec param) →
    ∃ mediator : SubstVec ambientScope (scope + 1),
      ((SubstVec.weakening scope).compose mediator = closingVec ∧
        classifiedCellFamily.substAction mediator
          (genericClassifiedCell (formerMap.component scope param)) = cell) ∧
      ∀ otherMediator : SubstVec ambientScope (scope + 1),
        (SubstVec.weakening scope).compose otherMediator = closingVec →
        classifiedCellFamily.substAction otherMediator
          (genericClassifiedCell (formerMap.component scope param)) = cell →
        otherMediator = SubstVec.cons cell.subjectCell closingVec

/-- ★ **THE Uemura keystone: every type-former is representable.**  A natural transformation
`formerMap : F ⟶ Ty` is automatically a representable natural transformation, because the display map
is representable and representability is uniform in the type.  The proof rewrites the "lies over the
formed type at the substituted parameter" hypothesis through the former's naturality
(`SubstFamilyMap.isNatural`: `formerMap (F.substAction closingVec param) = subst closingVec (formerMap
param)`) into the "lies over the pushforward of the formed type" shape, then hands off to the shipped
comprehension representability of the display map (`displayClassifier_comprehension`) at the formed
type `formerMap.component scope param`. -/
theorem formerComprehension {parameterFamily : SubstActionFamily}
    (formerMap : SubstFamilyMap parameterFamily typeCellFamily) :
    IsRepresentableFormer formerMap := by
  intro scope ambientScope param closingVec cell liesOverFormedType
  exact displayClassifier_comprehension (formerMap.component scope param) closingVec cell
    (liesOverFormedType.trans (formerMap.isNatural closingVec param))

/-- The Π type-former is representable — the comprehension of Π-types as a concrete instance of the
keystone over `piFormerMap`. -/
theorem piFormerComprehension : IsRepresentableFormer piFormerMap :=
  formerComprehension piFormerMap

/-- The Σ type-former is representable — the Σ twin of `piFormerComprehension`. -/
theorem sigmaFormerComprehension : IsRepresentableFormer sigmaFormerMap :=
  formerComprehension sigmaFormerMap

/-! ## The bijection: representable-formers ≃ type-formers -/

/-- **A representable type-former**: a natural transformation into `Ty` bundled with its
representability witness.  Uemura's "representable natural transformation."  The witness is `Prop`
-valued, so this bundle is equivalent to the bare former (`ofFormer` / `toFormer` below). -/
structure RepresentableTypeFormer (parameterFamily : SubstActionFamily) where
  /-- The underlying type-former `F ⟶ Ty`. -/
  formerMap : SubstFamilyMap parameterFamily typeCellFamily
  /-- It is representable (always inhabited via `formerComprehension`). -/
  isRepresentable : IsRepresentableFormer formerMap

/-- **Every former is representable** — pack a bare `formerMap` with its automatic witness.  The
forward leg of the bijection. -/
def RepresentableTypeFormer.ofFormer {parameterFamily : SubstActionFamily}
    (formerMap : SubstFamilyMap parameterFamily typeCellFamily) :
    RepresentableTypeFormer parameterFamily where
  formerMap := formerMap
  isRepresentable := formerComprehension formerMap

/-- Forget the representability witness — the backward leg of the bijection. -/
def RepresentableTypeFormer.toFormer {parameterFamily : SubstActionFamily}
    (representableFormer : RepresentableTypeFormer parameterFamily) :
    SubstFamilyMap parameterFamily typeCellFamily :=
  representableFormer.formerMap

/-- **Round-trip (forget ∘ pack = id).**  Forgetting the witness of a freshly-packed former recovers
the former definitionally. -/
theorem RepresentableTypeFormer.toFormer_ofFormer {parameterFamily : SubstActionFamily}
    (formerMap : SubstFamilyMap parameterFamily typeCellFamily) :
    (RepresentableTypeFormer.ofFormer formerMap).toFormer = formerMap := rfl

/-- **Round-trip (pack ∘ forget = id).**  Re-packing a representable former recovers it, because its
two representability witnesses are equal by definitional proof irrelevance on the `Prop`-valued field
(no `propext`).  Together with `toFormer_ofFormer` this is the bijection
`RepresentableTypeFormer F ≃ (F ⟶ Ty)` — type-formers and representable natural transformations
coincide for the FX cellular base. -/
theorem RepresentableTypeFormer.ofFormer_toFormer {parameterFamily : SubstActionFamily}
    (representableFormer : RepresentableTypeFormer parameterFamily) :
    RepresentableTypeFormer.ofFormer representableFormer.toFormer = representableFormer := by
  cases representableFormer
  rfl

/-- Π is a representable type-former (the bundle is inhabited — non-vacuity). -/
def piRepresentableFormer : RepresentableTypeFormer binderParameterFamily :=
  RepresentableTypeFormer.ofFormer piFormerMap

/-- Σ is a representable type-former. -/
def sigmaRepresentableFormer : RepresentableTypeFormer binderParameterFamily :=
  RepresentableTypeFormer.ofFormer sigmaFormerMap

/-- Smoke: the Π bundle's underlying former is `piFormerMap`. -/
theorem piRepresentableFormer_toFormer :
    piRepresentableFormer.toFormer = piFormerMap := rfl

/-- Smoke: the Σ bundle's underlying former is `sigmaFormerMap`. -/
theorem sigmaRepresentableFormer_toFormer :
    sigmaRepresentableFormer.toFormer = sigmaFormerMap := rfl

/-! ## The converse half: a former is determined by its generic element -/

/-- **The former is recovered from its generic element.**  Applying the display map to the generic
classified cell of the formed type at `param` (the freshly-bound variable classified by the weakened
formed type) returns the formed type at the weakened parameter — i.e. the former is determined by its
generic element, up to the canonical display weakening.  This is the natural-model converse to
`formerComprehension`: the generic-element side of the Uemura correspondence.  Proof:
`genericClassifiedCell_display` (the display of the generic cell is the weakening-pushforward of its
type) chained with the former's naturality at the weakening. -/
theorem formerDeterminedByGenericClassifier {parameterFamily : SubstActionFamily}
    (formerMap : SubstFamilyMap parameterFamily typeCellFamily) {scope : Nat}
    (param : parameterFamily.sections scope) :
    displayClassifier.component (scope + 1)
        (genericClassifiedCell (formerMap.component scope param))
      = formerMap.component (scope + 1)
          (parameterFamily.substAction (SubstVec.weakening scope) param) :=
  (genericClassifiedCell_display (formerMap.component scope param)).trans
    (formerMap.isNatural (SubstVec.weakening scope) param).symm

end FX1Poly.Tier0.ContextOmega
