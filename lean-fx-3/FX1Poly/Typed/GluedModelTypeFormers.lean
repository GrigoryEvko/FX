import FX1Poly.Tier0.FxBaseSubstTypeFormers
import FX1Poly.Core.ReducibleTypeReducibilityCandidate
import FX1Poly.Core.SconingWitness
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.ReducibleMemberFormation

/-! # FX1Poly/Typed/GluedModelTypeFormers
    — BKS preservation: the Π/Σ/universe formers lift to the glued model (SN-091, #594)

The BKS preservation lemma (arXiv:2302.05190 §2-3): the glued category `Gl(Γ)` inherits the type
formers from the base — concretely, **the sconing of a Π-type is the Π of the sconings**.  This file
realizes that lemma over the shipped substrate, marrying three layers that were built separately:

  * the CELLULAR formers (`piFormerMap`/`sigmaFormerMap`, SN-087) and the universe code cell,
  * the MODEL (`ReducibleType`, the dependent reducibility relation — the kernel's own glued
    semantics: `piType` assigns the dependent function-space candidate, `neutral` assigns the
    strong-normalization candidate to every weak-head-normal non-Π former),
  * the SCONE packaging (`SconingWitness`/`reducibilityScone`, SN-092).

What lands:

  * `GluedTypeCell` — **the glued-model type object**: a type cell PAIRED with its computability
    predicate AND the model tie (`isModeled : ReducibleType typeCell computable`).  The tie is what
    makes the pairing a point of the glued model rather than an arbitrary decoration; candidate-hood
    (CR1/CR2/CR3) is DERIVED from it (`GluedTypeCell.isCandidate`, via the SN-038 capstone
    `ReducibleType.isReducibilityCandidate`), and every glued type yields a `SconingWitness`
    (`GluedTypeCell.scone` — BKS extraction free by CR1).
  * ★ `GluedTypeCell.piLift` — **the Π former lifts to the glued model**: from a glued domain and a
    modeled codomain family, the glued Π whose cell is the SN-087 former's output and whose scone is
    the SN-038 dependent-arrow predicate; the model tie is ONE constructor
    (`ReducibleType.piType`).  The categorical-twin identifications are definitional
    (`piLift_typeCell` / `piLift_computable`, both `rfl`) — "the sconing of the Π is the Π of the
    sconings", made literal.
  * `GluedTypeCell.sigmaLift` / `universeLift` — the Σ former and the universe lift through the
    model's `neutral` arm: their cells are weak-head-normal non-Π formers (the table-generic
    `formationGenerator_noWeakHeadStep` for Σ; `universeCodeCell_noWeakHeadStep` for the universe),
    so the model assigns them the strong-normalization scone.
  * `piLift_isCandidate` / `sigmaLift_isCandidate` / `universeLift_isCandidate` — **the preservation
    payoff**: every lifted glued type's scone is again a full Girard reducibility candidate, so the
    glued model is closed under the three formers and the metatheory-extraction records
    (SN-093/094/095) have their objects.

## Honest scope boundary

The glued model packaged here is the shipped `ReducibleType` semantics (Π = dependent arrow,
everything weak-head-normal non-Π = the SN candidate) — in particular the Σ scone is the model's
NEUTRAL assignment (strong normalization), not a surjective-pairing predicate; a Σ-structured scone
(projections land in component scones) would be a model refinement, not this lemma.  The
candidate-hood derivations live at `scope + 1` exactly as the SN-038 capstone does (the dependent
arrow's CR1 needs a variable inhabitant).  This is the categorical PACKAGING of proven content — the
load-bearing mathematics (the dependent-arrow candidate, the model, CR1/2/3) shipped in SN-038 and
its capstone; the new content is the former-by-former closure of the glued model, the definitional
identification with the SN-087 cellular formers, and the scone hand-off.

## Zero-axiom verification

A structure, three constructions whose model ties are single `ReducibleType` constructors over
shipped no-weak-head-step suppliers, `rfl` identifications, and candidate-hood/scone corollaries by
direct application of the shipped capstones.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Universe
open StepStar

/-- **The glued-model type object**: a type cell paired with its computability predicate (the scone
over it) and the MODEL TIE — the cell denotes that predicate in the dependent reducibility relation.
The tie is what distinguishes a glued-model point from an arbitrary (cell, predicate) pairing. -/
structure GluedTypeCell (scope : Nat) where
  typeCell : RawTerm scope
  computable : RawTerm scope → Prop
  isModeled : ReducibleType typeCell computable

/-- Every glued type's scone is a full Girard reducibility candidate — the SN-038 capstone
(`ReducibleType.isReducibilityCandidate`) transported to the glued object.  At `scope + 1` because
the dependent arrow's CR1 needs a variable inhabitant, exactly as the capstone. -/
theorem GluedTypeCell.isCandidate {scope : Nat} (glued : GluedTypeCell (scope + 1)) :
    IsReducibilityCandidate glued.computable :=
  glued.isModeled.isReducibilityCandidate

/-- Every glued type yields a `SconingWitness` for strong-normalization canonicity: the extraction
obligation is free by CR1 (`reducibilityScone`), leaving the fundamental obligation as the one
genuine input — the BKS reading of the glued object. -/
def GluedTypeCell.scone {scope : Nat} (glued : GluedTypeCell (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term) :
    SconingWitness isWellTyped IsStronglyNormalizing :=
  reducibilityScone glued.isCandidate fundamental

/-- ★ **The Π former lifts to the glued model** — the BKS preservation lemma at Π: from a glued
domain and a modeled codomain family, the glued Π whose CELL is the SN-087 cellular former's output
and whose SCONE is the SN-038 dependent function-space predicate.  The model tie is one constructor:
`ReducibleType.piType`. -/
def GluedTypeCell.piLift {scope : Nat} (domainGlued : GluedTypeCell scope)
    (codomainCode : RawTerm (scope + 1))
    (codomainComputable : RawTerm scope → (RawTerm scope → Prop))
    (codomainModeled : ∀ argument : RawTerm scope, domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument)) :
    GluedTypeCell scope where
  typeCell := piFormerMap.component scope (domainGlued.typeCell, codomainCode)
  computable := IsDependentArrowReducible domainGlued.computable codomainComputable
  isModeled := ReducibleType.piType codomainComputable domainGlued.isModeled codomainModeled

/-- **The sconing of the Π is the Π of the sconings — cell half** (`rfl`): the lifted Π's cell IS
the SN-087 cellular Π former's output. -/
theorem GluedTypeCell.piLift_typeCell {scope : Nat} (domainGlued : GluedTypeCell scope)
    (codomainCode : RawTerm (scope + 1))
    (codomainComputable : RawTerm scope → (RawTerm scope → Prop))
    (codomainModeled : ∀ argument : RawTerm scope, domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument)) :
    (domainGlued.piLift codomainCode codomainComputable codomainModeled).typeCell
      = piFormerMap.component scope (domainGlued.typeCell, codomainCode) := rfl

/-- **The sconing of the Π is the Π of the sconings — scone half** (`rfl`): the lifted Π's
computability predicate IS the SN-038 dependent function-space predicate over the component
scones. -/
theorem GluedTypeCell.piLift_computable {scope : Nat} (domainGlued : GluedTypeCell scope)
    (codomainCode : RawTerm (scope + 1))
    (codomainComputable : RawTerm scope → (RawTerm scope → Prop))
    (codomainModeled : ∀ argument : RawTerm scope, domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument)) :
    (domainGlued.piLift codomainCode codomainComputable codomainModeled).computable
      = IsDependentArrowReducible domainGlued.computable codomainComputable := rfl

/-- **The Σ former lifts to the glued model** through the model's `neutral` arm: the Σ cell is a
weak-head-normal non-Π former (table-generic `formationGenerator_noWeakHeadStep` over the
`gen_sigmaTyCode` formation row), so the model assigns it the strong-normalization scone. -/
def GluedTypeCell.sigmaLift {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    GluedTypeCell scope where
  typeCell := sigmaFormerMap.component scope (domainCode, codomainCode)
  computable := IsStronglyNormalizing
  isModeled := ReducibleType.neutral
    (formationGenerator_noWeakHeadStep typingRuleDescOf_sigmaTyCode)
    (fun absurdEq => nomatch absurdEq)

/-- **The universe lifts to the glued model** through the model's `neutral` arm: the universe code
is weak-head normal (`universeCodeCell_noWeakHeadStep`) and not Π-rooted, so the model assigns it
the strong-normalization scone. -/
def GluedTypeCell.universeLift {scope : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    GluedTypeCell scope where
  typeCell := universeCodeCell levelExpr flag
  computable := IsStronglyNormalizing
  isModeled := ReducibleType.neutral
    (universeCodeCell_noWeakHeadStep levelExpr flag)
    (fun absurdEq => nomatch absurdEq)

/-- **Preservation payoff (Π)**: the lifted Π's scone is again a full Girard reducibility candidate
— the glued model is closed under the Π former. -/
theorem GluedTypeCell.piLift_isCandidate {scope : Nat} (domainGlued : GluedTypeCell (scope + 1))
    (codomainCode : RawTerm (scope + 1 + 1))
    (codomainComputable : RawTerm (scope + 1) → (RawTerm (scope + 1) → Prop))
    (codomainModeled : ∀ argument : RawTerm (scope + 1), domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument)) :
    IsReducibilityCandidate
      (domainGlued.piLift codomainCode codomainComputable codomainModeled).computable :=
  (domainGlued.piLift codomainCode codomainComputable codomainModeled).isCandidate

/-- **Preservation payoff (Σ)**: the lifted Σ's scone is a reducibility candidate (the SN candidate,
at any scope). -/
theorem GluedTypeCell.sigmaLift_isCandidate {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    IsReducibilityCandidate (GluedTypeCell.sigmaLift domainCode codomainCode).computable :=
  isStronglyNormalizing_isReducibilityCandidate

/-- **Preservation payoff (universe)**: the lifted universe's scone is a reducibility candidate (the
SN candidate, at any scope). -/
theorem GluedTypeCell.universeLift_isCandidate {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibilityCandidate
      (GluedTypeCell.universeLift (scope := scope) levelExpr flag).computable :=
  isStronglyNormalizing_isReducibilityCandidate

/-- The lifted Π yields a `SconingWitness` (BKS: extraction free by CR1) — the witness-level form of
the preservation lemma, the shape the extraction ledgers (SN-093/094/095) consume. -/
def GluedTypeCell.piLiftScone {scope : Nat} (domainGlued : GluedTypeCell (scope + 1))
    (codomainCode : RawTerm (scope + 1 + 1))
    (codomainComputable : RawTerm (scope + 1) → (RawTerm (scope + 1) → Prop))
    (codomainModeled : ∀ argument : RawTerm (scope + 1), domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term →
      (domainGlued.piLift codomainCode codomainComputable codomainModeled).computable term) :
    SconingWitness isWellTyped IsStronglyNormalizing :=
  (domainGlued.piLift codomainCode codomainComputable codomainModeled).scone fundamental

end FX1Poly.Typed
