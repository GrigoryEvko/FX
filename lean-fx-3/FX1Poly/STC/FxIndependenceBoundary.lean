import FX1Poly.STC.FxBoolCanonicity
import FX1Poly.STC.FxNormalization
/-! # FX1Poly/STC/FxIndependenceBoundary — the independence VERDICT (the STC arc's final rung)

The question the STC arc leaves open is whether the glued
computability gives an INDEPENDENT second strong-normalization proof.
This module answers it as committed theorems, and the answer is NO —
sharper than "not yet built":

**On the shipped zero-axiom scaffold, independence through the STC
interface is impossible at the object level.**  Every semantic payload
the shipped relations display (`fxStcRelationAt` /
`fxStcBoolRelation` / `fxStcNormalizationRelation`) is a `PLift`-ed
PROPOSITION, and Lean's definitional proof irrelevance makes any two
proofs of a proposition equal.  Consequently:

  * the glue families are SYNTAX-DETERMINED — two glues with the same
    syntactic side are the SAME GLUE (`stcPropGlue_syntaxDetermined`);
  * EVERY inhabitant's semantic component IS the kernel witness,
    definitionally — not only our constructions
    (`anyStcSNGlue_semantic_isTaitWitness` and friends generalize the
    per-construction bridge pins to ALL inhabitants);
  * every syntax-faithful SN-fundamental function IS
    `fxStcFundamental` (`anySNFundamental_eq_fxStcFundamental`) — the
    STC twin of the sconing leg's `anySconingSN_eq_taitComposition`.

A "second SN proof" through this interface would be EQUAL to the
first; independence cannot even be STATED here, let alone proved.

## Where independence could live — the two exits, both pinned shut

1. **The HIT closed modality.**  The paper's ● is a pushout quotient
   genuinely collapsing the syntactic phase.  The shipped `ClosedMod`
   is a one-constructor wrapper — a definitional RETRACTION PAIR with
   the identity (`ClosedMod.extract_unit` / `ClosedMod.unit_extract`),
   so it identifies nothing.  The genuine HIT pulls `Quot.sound` — the
   permanent zero-axiom boundary.  Likewise the single-phase ○ is
   pointwise constant (`OpenMod.pointwiseConstant`).
2. **A proof-relevant semantic side.**  A Type-valued computability
   structure (normalization data a la Gratzer, not a `PLift`ed Prop)
   could carry distinguishing information.  No such relation is
   shipped; building one is genuine future work, NOT claimed.

Accordingly the final ledger rung stays unclaimed:
`fxSTC_hasNoFXGenericSTCReplacement` (the STC route cannot REPLACE the
generic Tait route — its every semantic payload IS the Tait/kernel
witness), and the parity ledger's sconing/STC cells stay BRIDGED.

Zero-axiom: everything is `cases` + `rfl` — definitional proof
irrelevance and structure eta, no `funext` (which would pull
`Quot.sound`), no `propext`, no `Classical`.  Gated in
`FX1PolyAudit/AuditProfile.lean`. -/

namespace FX1Poly.STC

open FX1Poly.Core FX1Poly.Typed

/-! ## The general collapse: Prop-payload glues are syntax-determined -/

/-- **Syntax-determination for every Prop-payload glue family.**  Two
glues over the same syntax with a `PLift`ed propositional payload are
EQUAL — the semantic dimension carries zero distinguishing
information, by definitional proof irrelevance. -/
theorem stcPropGlue_syntaxDetermined {synType : Type}
    {payload : synType → Prop}
    (glueLeft glueRight :
      canonicalSTCModel.Glue synType (fun syn => PLift (payload syn)))
    (syntacticAgree : glueLeft.syntactic = glueRight.syntactic) :
    glueLeft = glueRight := by
  obtain ⟨syntacticLeft, ⟨payloadProofLeft⟩⟩ := glueLeft
  obtain ⟨syntacticRight, ⟨payloadProofRight⟩⟩ := glueRight
  cases syntacticAgree
  rfl

/-- The SN relation is syntax-determined. -/
theorem fxStcRelation_syntaxDetermined {profile : PolyProfile}
    {classifier : RawTerm 0}
    (glueLeft glueRight : fxStcRelationAt profile classifier)
    (syntacticAgree : glueLeft.syntactic = glueRight.syntactic) :
    glueLeft = glueRight :=
  stcPropGlue_syntaxDetermined glueLeft glueRight syntacticAgree

/-- The bool canonicity relation is syntax-determined. -/
theorem fxStcBoolRelation_syntaxDetermined {profile : PolyProfile}
    (glueLeft glueRight : fxStcBoolRelation profile)
    (syntacticAgree : glueLeft.syntactic = glueRight.syntactic) :
    glueLeft = glueRight :=
  stcPropGlue_syntaxDetermined glueLeft glueRight syntacticAgree

/-- The normalization relation is syntax-determined. -/
theorem fxStcNormalizationRelation_syntaxDetermined
    {profile : PolyProfile} {classifier : RawTerm 0}
    (glueLeft glueRight : fxStcNormalizationRelation profile classifier)
    (syntacticAgree : glueLeft.syntactic = glueRight.syntactic) :
    glueLeft = glueRight :=
  stcPropGlue_syntaxDetermined glueLeft glueRight syntacticAgree

/-! ## Every inhabitant carries the kernel witness — not only ours

The per-construction bridge pins
(`fxStcFundamental_semantic_isTaitWitness`,
`canonicityViaSTC_semantic_isKernelWitness`,
`normalizationViaSTC_semantic_isKernelWitness`) identified OUR
constructions with the kernel.  These theorems identify EVERY
inhabitant: whatever produced the glue, its semantic component is
definitionally the kernel's witness. -/

/-- ★ ANY SN-relation inhabitant's semantic component IS the Tait
witness — definitionally, by proof irrelevance plus structure eta. -/
theorem anyStcSNGlue_semantic_isTaitWitness {profile : PolyProfile}
    {classifier : RawTerm 0}
    (glued : fxStcRelationAt profile classifier) :
    glued.semantic
      = ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc
          WfContextDesc.emptyIsWellFormed glued.syntactic.typed⟩ := rfl

/-- ANY bool-canonicity-relation inhabitant's semantic component IS the
kernel's syntactic canonicity witness. -/
theorem anyStcBoolGlue_semantic_isKernelWitness {profile : PolyProfile}
    (glued : fxStcBoolRelation profile) :
    glued.semantic
      = ⟨closedBoolCanonicalForms glued.syntactic.typed⟩ := rfl

/-- ANY normalization-relation inhabitant's semantic component IS the
kernel's computed-normalizer witness. -/
theorem anyStcNormalizationGlue_semantic_isKernelWitness
    {profile : PolyProfile} {classifier : RawTerm 0}
    (glued : fxStcNormalizationRelation profile classifier) :
    glued.semantic
      = ⟨⟨glued.syntactic.typed.normalForm,
          glued.syntactic.typed.normalForm_reducesTo,
          glued.syntactic.typed.normalForm_isStepNormalForm⟩⟩ := rfl

/-- ★★ **The verdict capstone** (the STC twin of the sconing leg's
`anySconingSN_eq_taitComposition`): every syntax-faithful
SN-fundamental function — any candidate "independent second SN proof"
packaged through the STC interface — produces glues EQUAL to
`fxStcFundamental`'s.  There is exactly one SN-fundamental up to
equality; a second proof cannot differ from the first. -/
theorem anySNFundamental_eq_fxStcFundamental {profile : PolyProfile}
    {classifier : RawTerm 0}
    (alternativeFundamental :
      {term : RawTerm 0} →
        HasTypeDescPi profile TypingContext.empty term classifier →
          fxStcRelationAt profile classifier)
    {term : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty term classifier)
    (syntacticFaithful :
      (alternativeFundamental typed).syntactic
        = (⟨term, typed⟩ : ClosedTypedTerm profile classifier)) :
    alternativeFundamental typed = fxStcFundamental typed :=
  fxStcRelation_syntaxDetermined
    (alternativeFundamental typed) (fxStcFundamental typed)
    syntacticFaithful

/-! ## The exits, pinned shut: degenerate modalities

The shipped ● and ○ cannot host an independent semantics. -/

/-- The shipped ● retracts onto the identity, leg one: extract after
unit is the identity. -/
theorem ClosedMod.extract_unit {carrier : Type} (value : carrier) :
    ClosedMod.extract (ClosedMod.unit value) = value := rfl

/-- The shipped ● retracts onto the identity, leg two: unit after
extract is the identity.  Together with `extract_unit`: ● is a
definitional bijection with the identity functor — a wrapper, NOT the
paper's pushout quotient.  It identifies nothing, so it cannot collapse
the syntactic phase into a genuinely semantic world; the genuine HIT ●
pulls `Quot.sound`, outside the zero-axiom discipline. -/
theorem ClosedMod.unit_extract {carrier : Type}
    (closedValue : ClosedMod carrier) :
    ClosedMod.unit (ClosedMod.extract closedValue) = closedValue := by
  cases closedValue
  rfl

/-- The single-phase ○ is pointwise constant: every phase reads the
syntactic value.  (Stated pointwise — the function-level statement
would need `funext`, which pulls `Quot.sound`.) -/
theorem OpenMod.pointwiseConstant {carrier : Type}
    (openValue : OpenMod carrier) (phase : SynPhase) :
    openValue phase = openValue SynPhase.syntactic := by
  cases phase
  rfl

end FX1Poly.STC
