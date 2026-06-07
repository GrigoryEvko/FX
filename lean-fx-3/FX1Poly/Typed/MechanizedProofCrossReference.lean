import FX1Poly.Typed.KnownUnsoundnessCorpus
import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.GrownBetaRedexInAction
import FX1Poly.Typed.EmptyTypeConsistencyUnconditional
import FX1Poly.Core.Normalize
import FX1Poly.Core.Newman

/-! # FX1Poly/Typed/MechanizedProofCrossReference
    — the §27.3 Layer-3 defense: every core metatheory rule cross-referenced to a PUBLISHED MECHANIZED proof,
      and ANCHORED to the real, zero-axiom kernel theorem that realizes it

Layer 3 of the §27.3 five-layer defense is "cross-reference published mechanized proofs — every rule cites a
machine-checked source in Coq / Agda / Lean / F*."  A free-floating citation list would be unverified prose;
this file gives the cross-reference TEETH by ANCHORING each cited rule to the actual shipped kernel theorem
that realizes it (`crossRef_<rule> := @<kernelTheorem>`).  Each anchor:

  * verifies the cited kernel theorem EXISTS — the file fails to compile if a rule is renamed or deleted, so
    the cross-reference can never silently drift from the kernel;
  * is gated `#assert_no_axioms`, so it RE-CERTIFIES that each classical rule's kernel proof is itself
    zero-axiom (a second, independent confirmation alongside the rule's own audit gate).

The `@`-alias deliberately does not re-spell each theorem's signature — re-stating a long dependent signature
would only invite drift between the cross-reference and the source; binding the proof term by `@`-reference is
the tightest possible tie.

## The catalog (`KernelMetatheoryRule`)

Nine CLASSICAL rules — each with a published mechanized precedent AND a kernel anchor — plus two FX-ORIGINAL
entries flagged honestly as having no direct mechanized precedent:

  | rule                          | mechanized precedent                          | kernel anchor                                |
  | ----------------------------- | --------------------------------------------- | -------------------------------------------- |
  | correctedLam                  | Wood-Atkey 2022 (Agda)                        | `Modal.atkey_rejected`                       |
  | subjectReductionBeta          | Abel-Ohman-Vezzosi 2018 (Agda)                | `HasTypeDescPi.betaSubjectReductionDescPi`   |
  | strongNormalization           | Tait 1967 / Girard 1972; Abel et al. (Agda)   | `HasTypeDescPi.stronglyNormalizingOfWf…`     |
  | progress                      | Wright-Felleisen 1994; PFPL (Coq)             | `HasTypeDescPi.closedProgress`               |
  | consistency                   | logical relations, Abel et al. (Agda)         | `HasTypeDescPi.emptyTypeConsistency`         |
  | universePredicativity         | Girard 1972 (System U)                        | `grownUniverseTypingForcesSuccessor`         |
  | uniqueNormalForm              | Church-Rosser 1936; Takahashi 1995            | `HasTypeDescPi.closedHasUniqueNormalForm`    |
  | decidableConversion           | Abel-Ohman-Vezzosi 2018 (Agda)                | `Conv.decidableOfStronglyNormalizing`        |
  | newmanLemma                   | Newman 1942; IsaFoR/CeTA (Isabelle)           | `newman`                                     |
  | gradedDimensionOrthogonality  | FX-original (partial: graded MTT)             | (none — FX-original)                         |
  | polyCellSubstrate             | FX-original (no precedent)                    | (none — FX-original)                         |

`mechanizedSource` / `hasClassicalPrecedent` / `kernelAnchor` record this as machine-checked data; the
`…_hasClassicalPrecedent` / `…_isFxOriginal` rfl-facts pin the honest classical-vs-original split.

## Zero-axiom verification

The catalog functions are full-enumeration non-dependent matches (String / Bool); the anchors are bare
`@`-references to shipped zero-axiom theorems; the ledger facts close by `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## Part 1 — the catalog as machine-checked data -/

/-- **The core kernel metatheory rules** cross-referenced by the §27.3 Layer-3 defense.  Nine classical rules
(each with a published mechanized precedent and a kernel anchor) plus two FX-original entries. -/
inductive KernelMetatheoryRule where
  | correctedLam
  | subjectReductionBeta
  | strongNormalization
  | progress
  | consistency
  | universePredicativity
  | uniqueNormalForm
  | decidableConversion
  | newmanLemma
  | gradedDimensionOrthogonality
  | polyCellSubstrate

/-- The published mechanized-proof source §27.3 Layer-3 cites for each rule (ASCII rendering of names). -/
def KernelMetatheoryRule.mechanizedSource : KernelMetatheoryRule → String
  | .correctedLam => "Wood-Atkey 2022 (Agda); McBride 2016 linear de Bruijn"
  | .subjectReductionBeta => "Abel-Ohman-Vezzosi 2018 Decidability of Conversion (Agda)"
  | .strongNormalization => "Tait 1967; Girard 1972; Abel et al. logical relations (Agda)"
  | .progress => "Wright-Felleisen 1994; Harper PFPL mechanizations (Coq)"
  | .consistency => "logical-relations consistency, Abel et al. (Agda)"
  | .universePredicativity => "Girard 1972 System U paradox; mechanized predicative hierarchies"
  | .uniqueNormalForm => "Church-Rosser 1936; Takahashi 1995 parallel reduction"
  | .decidableConversion => "Abel-Ohman-Vezzosi 2018 (Agda)"
  | .newmanLemma => "Newman 1942; IsaFoR/CeTA (Isabelle)"
  | .gradedDimensionOrthogonality => "FX-original; partial precedent in graded MTT (Atkey 2018, Granule)"
  | .polyCellSubstrate => "FX-original; no direct mechanized precedent"

/-- Whether the rule has a published CLASSICAL mechanized precedent (`true`) or is FX-original (`false`).
Full enumeration — every catalog entry is classified, none falls through a wildcard. -/
def KernelMetatheoryRule.hasClassicalPrecedent : KernelMetatheoryRule → Bool
  | .correctedLam => true
  | .subjectReductionBeta => true
  | .strongNormalization => true
  | .progress => true
  | .consistency => true
  | .universePredicativity => true
  | .uniqueNormalForm => true
  | .decidableConversion => true
  | .newmanLemma => true
  | .gradedDimensionOrthogonality => false
  | .polyCellSubstrate => false

/-- The shipped FX1Poly kernel declaration that realizes each rule (`(none)` for the FX-original entries,
which are not anchored to a single theorem). -/
def KernelMetatheoryRule.kernelAnchor : KernelMetatheoryRule → String
  | .correctedLam => "FX1Poly.Modal.atkey_rejected"
  | .subjectReductionBeta => "FX1Poly.Typed.HasTypeDescPi.betaSubjectReductionDescPi"
  | .strongNormalization => "FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDesc"
  | .progress => "FX1Poly.Typed.HasTypeDescPi.closedProgress"
  | .consistency => "FX1Poly.Typed.HasTypeDescPi.emptyTypeConsistency"
  | .universePredicativity => "FX1Poly.Typed.grownUniverseTypingForcesSuccessor"
  | .uniqueNormalForm => "FX1Poly.Typed.HasTypeDescPi.closedHasUniqueNormalForm"
  | .decidableConversion => "FX1Poly.Core.Conv.decidableOfStronglyNormalizing"
  | .newmanLemma => "FX1Poly.Core.newman"
  | .gradedDimensionOrthogonality => "(none -- FX-original)"
  | .polyCellSubstrate => "(none -- FX-original)"

/-! ## Part 2 — the kernel anchors (each verifies a real, zero-axiom kernel theorem)

Each `crossRef_<rule>` binds the cited kernel theorem by `@`-reference.  Compiling it certifies the rule
exists; its audit gate certifies it is zero-axiom.  The docstrings carry the mechanized-proof citation. -/

/-- Cross-reference — **corrected Lam rule** (the Wood-Atkey 2022 correction of Atkey 2018), anchored to the
usage dimension's broken-Lam rejection. -/
def crossRef_correctedLam := @FX1Poly.Modal.atkey_rejected

/-- Cross-reference — **subject reduction (β)**, anchored to the grown engine's β subject-reduction theorem.
Mechanized precedent: Abel-Ohman-Vezzosi 2018 (Agda). -/
def crossRef_subjectReductionBeta := @HasTypeDescPi.betaSubjectReductionDescPi

/-- Cross-reference — **strong normalization** (Tait/Girard logical relations), anchored to SN-for-well-typed.
-/
def crossRef_strongNormalization := @HasTypeDescPi.stronglyNormalizingOfWfContextDesc

/-- Cross-reference — **progress** (Wright-Felleisen), anchored to grown closed progress. -/
def crossRef_progress := @HasTypeDescPi.closedProgress

/-- Cross-reference — **consistency** (no closed proof of the empty type), anchored to the unconditional grown
consistency theorem. -/
def crossRef_consistency := @HasTypeDescPi.emptyTypeConsistency

/-- Cross-reference — **universe predicativity** (no Girard System-U paradox), anchored to the
universe-typing-is-the-successor-function theorem. -/
def crossRef_universePredicativity := @grownUniverseTypingForcesSuccessor

/-- Cross-reference — **unique normal forms** (Church-Rosser / Takahashi confluence), anchored to the
closed-term unique-normal-form theorem. -/
def crossRef_uniqueNormalForm := @HasTypeDescPi.closedHasUniqueNormalForm

/-- Cross-reference — **decidable conversion** (Abel-Ohman-Vezzosi), anchored to the SN-driven decision
procedure for raw conversion. -/
@[reducible] def crossRef_decidableConversion := @Conv.decidableOfStronglyNormalizing

/-- Cross-reference — **Newman's lemma** (local confluence + SN implies global confluence), anchored to the
abstract Newman theorem. -/
def crossRef_newmanLemma := @newman

/-! ## Part 3 — the honest coverage ledger -/

/-- Ledger fact: subject reduction has a classical mechanized precedent. -/
theorem subjectReductionBeta_hasClassicalPrecedent :
    KernelMetatheoryRule.subjectReductionBeta.hasClassicalPrecedent = true := rfl

/-- Ledger fact: consistency has a classical mechanized precedent. -/
theorem consistency_hasClassicalPrecedent :
    KernelMetatheoryRule.consistency.hasClassicalPrecedent = true := rfl

/-- Ledger fact: strong normalization has a classical mechanized precedent. -/
theorem strongNormalization_hasClassicalPrecedent :
    KernelMetatheoryRule.strongNormalization.hasClassicalPrecedent = true := rfl

/-- Ledger fact (HONEST): the 21-dimension graded-composition orthogonality is FX-original — no direct
mechanized precedent (graded MTT exists, but not the orthogonal 21-dimension composition). -/
theorem gradedDimensionOrthogonality_isFxOriginal :
    KernelMetatheoryRule.gradedDimensionOrthogonality.hasClassicalPrecedent = false := rfl

/-- Ledger fact (HONEST): the (inf, omega)-categorical PolyCell substrate is FX-original — no mechanized
precedent. -/
theorem polyCellSubstrate_isFxOriginal :
    KernelMetatheoryRule.polyCellSubstrate.hasClassicalPrecedent = false := rfl

end FX1Poly.Typed
