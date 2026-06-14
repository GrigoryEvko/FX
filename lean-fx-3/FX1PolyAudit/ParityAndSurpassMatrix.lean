import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.TypedByTableUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms
import FX1PolyAudit.OneSystemSignoff

/-! # FX1PolyAudit/ParityAndSurpassMatrix — the union judgment vs the retired bespoke engines

The NATIVE-42..45 endgame DELETED ~23 standalone typing engines (the bool/option/either/nat/list/id
data intro+elim engines, the projection engines, `HasTypeDescBaseType` / `HasTypeDescDataIntro` /
the flat-formation engine, and the `HasTypeDescBridge`).  Their data / former / eliminator families
were absorbed into the 25 arms of the ONE union judgment `HasTypeUnion`.  This module is the
machine-checked PARITY-and-SURPASS ledger of that replacement, BY CITATION (it re-proves nothing).

## PARITY — the union types the same closed corpus

For each retired bespoke FAMILY, the union judgment types the SAME closed normal corpus, witnessed by
two shipped facts:

  * the family's eliminator/intro HEAD is a TABLE ROW of the union classifier
    (`hasTableTypingRule_<head> = true` — the union admits the family's cells through a table row, not a
    bespoke arm); and

  * the family's CLOSED-NORMAL CANONICITY is restated and proven over the union judgment
    (`HasTypeUnion.closedNormal<Family>CanonicalForms` — the union restatement of the retired
    standalone-engine canonicity, freeing the canonical-forms assembly from the deleted engine).

The flagship cross-check fixtures (`unionCrossCheckCoverageWitness`, via the Stage-3 system sign-off)
additionally run three union-typed subjects end-to-end through the independent external verifier.

## SURPASS — one generic table replaces N bespoke arms

The architectural surpass is `hasSomeTypingRule_eq_hasTableTypingRule`: the table-driven classifier
`hasTableTypingRule` classifies the SAME generator set as the honest disjunction-of-engines classifier
`hasSomeTypingRule`, but via `Option.isSome` over rule TABLES — the sixteen data-family `decide` head
equalities and the two cubical-path decides of the bespoke disjunction all DISSOLVE into table
membership.  One generic arm (a table row) per family replaces the family's bespoke engine, with only
an honest four-head residual (`tableClassifierResidualHeadsLive`: `natZero` / `listNil` / `var` /
`universeCode`).  And the table classifier's reserved verdicts stay truthful
(`reservedTableHeadUntypedBySurvivingEngines`: a head the table reports reserved is typed by no
surviving standalone engine).

## What this certificate ties together (named carriers)

  * `FX1Poly.Typed.hasSomeTypingRule_eq_hasTableTypingRule` — SURPASS: same set, table-driven.
  * `FX1Poly.Typed.tableClassifierResidualHeadsLive` — the honest four-head residual floor.
  * `FX1Poly.Typed.reservedTableHeadUntypedBySurvivingEngines` — the table classifier is truthful.
  * `FX1Poly.Typed.hasTableTypingRule_{boolElim,optionMatch,eitherMatch,idJ,fst,snd,natSucc,listCons,
    optionSome,optionNone,eitherInl,eitherInr,pair,refl}` — every retired data-family head is a table
    row (PARITY of admission).
  * `FX1Poly.Typed.HasTypeUnion.closedNormal{Bool,Nat,Option,Either,Product,Identity,List,Pi}CanonicalForms`
    — the per-family closed-normal canonicity, restated over the union (PARITY of canonical forms).
  * `FX1PolyAudit.oneSystemSignoffHolds` — the Stage-3 grand sign-off (one engine + one reduction +
    table-native eta), carrying the cross-check fixtures.

## The bundle inhabitant's reading

`parityAndSurpassMatrix` certifies: **the union judgment achieves PARITY with every retired bespoke
engine (it admits the same family heads through table rows and proves the same per-family closed-normal
canonicity) and SURPASSES them (one generic table classifier replaces the N-engine disjunction, with an
honest four-head residual and truthful reserved verdicts).**

## Layering note

Lives in the AUDIT layer because it cites the Stage-3 `oneSystemSignoffHolds`.

## Zero-axiom verification

`ParityAndSurpassMatrix` is a `Prop` structure whose every field is the type of a shipped zero-axiom
theorem or a `rfl`-checkable Bool equality; the per-family canonicity carriers are `@`-anchored
proof-term aliases (the `MetatheoryParityLedger` cross-reference idiom) re-gated below.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
below in this same file. -/

namespace FX1PolyAudit

open FX1Poly.Core (PolyProfile RawTerm Generator)
open FX1Poly.Typed
  (hasTableTypingRule hasSomeTypingRule hasSomeTypingRule_eq_hasTableTypingRule
   tableClassifierResidualHeadsLive
   hasTableTypingRule_boolElim hasTableTypingRule_optionMatch hasTableTypingRule_eitherMatch
   hasTableTypingRule_idJ hasTableTypingRule_fst hasTableTypingRule_snd hasTableTypingRule_natSucc
   hasTableTypingRule_listCons hasTableTypingRule_optionSome hasTableTypingRule_optionNone
   hasTableTypingRule_eitherInl hasTableTypingRule_eitherInr hasTableTypingRule_pair
   hasTableTypingRule_refl)
open FX1PolyAudit (OneSystemSignoff oneSystemSignoffHolds)

/-! ## Per-family canonical-forms anchors (the PARITY-of-canonical-forms teeth)

Each anchor binds the shipped union-side canonical-forms master by reference; its gate re-certifies
the proof is zero-axiom, and the file breaks if the theorem is renamed.  These are the union
restatements of the retired standalone-engine canonicities. -/

/-- Bool canonicity over the union (restates the retired bool standalone-engine canonicity). -/
def parityAnchor_boolCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalBoolCanonicalForms
/-- Nat canonicity over the union (restates the retired nat standalone-engine canonicity). -/
def parityAnchor_natCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalNatCanonicalForms
/-- Option canonicity over the union (restates the retired option standalone-engine canonicity). -/
def parityAnchor_optionCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalOptionCanonicalForms
/-- Either canonicity over the union (restates the retired either standalone-engine canonicity). -/
def parityAnchor_eitherCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalEitherCanonicalForms
/-- Product canonicity over the union (restates the retired product standalone-engine canonicity). -/
def parityAnchor_productCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalProductCanonicalForms
/-- Identity canonicity over the union (restates the retired id standalone-engine canonicity). -/
def parityAnchor_identityCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalIdentityCanonicalForms
/-- List canonicity over the union (restates the retired list standalone-engine canonicity). -/
def parityAnchor_listCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalListCanonicalForms
/-- Pi canonicity over the union (restates the retired Pi standalone-engine canonicity). -/
def parityAnchor_piCanonicity := @FX1Poly.Typed.HasTypeUnion.closedNormalPiCanonicalForms

/-- The SURPASS-truthfulness anchor: a head the table classifier reports reserved is typed by no
surviving standalone engine (`reservedTableHeadUntypedBySurvivingEngines`). -/
def surpassAnchor_reservedTableHeadTruthful :=
  @FX1Poly.Typed.reservedTableHeadUntypedBySurvivingEngines

/-- **The PARITY-and-SURPASS matrix certificate.**  One `Prop` whose fields bundle, by citation, the
union judgment's PARITY with and SURPASS of the retired bespoke engines: the table classifier
classifies the same set (surpass), with an honest four-head residual and truthful reserved verdicts,
and every retired data-family head is a table row (parity of admission), backed by the per-family
union canonicity anchors (parity of canonical forms) and the Stage-3 grand sign-off. -/
structure ParityAndSurpassMatrix (profile : PolyProfile) : Prop where
  /-- SURPASS: the table-driven classifier classifies the SAME generator set as the
  disjunction-of-engines classifier — one generic table replaces the N bespoke arms
  (`hasSomeTypingRule_eq_hasTableTypingRule`). -/
  tableClassifierEqualsEngineDisjunction :
    ∀ generator : Generator, hasSomeTypingRule generator = hasTableTypingRule generator
  /-- SURPASS (honest floor): the four heads that cannot become table membership are classified live by
  the residual decide (`natZero` / `listNil` / `var` / `universeCode`). -/
  honestFourHeadResidual :
    hasTableTypingRule Generator.gen_natZero = true ∧
      hasTableTypingRule Generator.gen_listNil = true ∧
        hasTableTypingRule Generator.gen_var = true ∧
          hasTableTypingRule Generator.gen_universeCode = true
  /-- SURPASS (truthfulness): a head the TABLE classifier reports reserved is typed by no surviving
  standalone engine (`reservedTableHeadUntypedBySurvivingEngines`). -/
  reservedTableHeadsTruthful :
    ∀ {scope : Nat} {context : FX1Poly.Typed.TypingContext profile scope} {subject : RawTerm scope},
      hasTableTypingRule (FX1Poly.Typed.RawTerm.headGenerator subject) = false →
      ∀ classifier : RawTerm scope,
        ¬ FX1Poly.Typed.HasTypeDescPi profile context subject classifier
  /-- PARITY of admission (retired two-branch-match engines): boolElim / optionMatch / eitherMatch
  heads are all table rows. -/
  retiredMatchEnginesAreTableRows :
    hasTableTypingRule Generator.gen_boolElim = true ∧
      hasTableTypingRule Generator.gen_optionMatch = true ∧
        hasTableTypingRule Generator.gen_eitherMatch = true
  /-- PARITY of admission (retired path-induction + projection engines): idJ / fst / snd heads are all
  table rows. -/
  retiredPathAndProjectionEnginesAreTableRows :
    hasTableTypingRule Generator.gen_idJ = true ∧
      hasTableTypingRule Generator.gen_fst = true ∧ hasTableTypingRule Generator.gen_snd = true
  /-- PARITY of admission (retired data-intro engines): natSucc / listCons / optionSome / optionNone /
  eitherInl / eitherInr / pair / refl heads are all table rows. -/
  retiredDataIntroEnginesAreTableRows :
    hasTableTypingRule Generator.gen_natSucc = true ∧
      hasTableTypingRule Generator.gen_listCons = true ∧
        hasTableTypingRule Generator.gen_optionSome = true ∧
          hasTableTypingRule Generator.gen_optionNone = true ∧
            hasTableTypingRule Generator.gen_eitherInl = true ∧
              hasTableTypingRule Generator.gen_eitherInr = true ∧
                hasTableTypingRule Generator.gen_pair = true ∧
                  hasTableTypingRule Generator.gen_refl = true
  /-- PARITY of canonical forms (retired nat engine): the closed-normal nat canonicity is restated and
  proven over the union judgment — a closed normal union-typed term at `Nat` on the core fragment is
  `natZero` or a `natSucc` (the per-family canonical-forms parity; the eight families' canonicity is
  carried in full by the `parityAnchor_*Canonicity` aliases). -/
  retiredNatCanonicityRestatedOverUnion : ∀ {subject : RawTerm 0},
    FX1Poly.Typed.HasTypeUnion profile
        (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        subject FX1Poly.Typed.natTypeCell →
      RawTerm.isStepNormalForm subject →
      RawTerm.containsGeneratorBool .gen_pathApp subject = false →
      RawTerm.containsGeneratorBool .gen_pathLam subject = false →
      subject = FX1Poly.Typed.natZeroCell ∨
        ∃ predecessor : RawTerm 0, subject = FX1Poly.Typed.natSuccCell predecessor
  /-- The Stage-3 grand sign-off (one engine + one reduction + table-native eta), carrying the
  union cross-check fixtures. -/
  oneSystemSignedOff : OneSystemSignoff profile

/-- **★ The PARITY-and-SURPASS matrix HOLDS.**  Every field is the shipped named carrier:
`hasSomeTypingRule_eq_hasTableTypingRule`, `tableClassifierResidualHeadsLive`,
`reservedTableHeadUntypedBySurvivingEngines`, the fourteen `hasTableTypingRule_<head>` LIVE witnesses,
`HasTypeUnion.closedNormalNatCanonicalForms` (plus the eight `parityAnchor_*Canonicity` aliases), and
the Stage-3 `oneSystemSignoffHolds`.  The union
judgment achieves PARITY with and SURPASSES every retired bespoke engine — one checked object. -/
theorem parityAndSurpassMatrixHolds {profile : PolyProfile} : ParityAndSurpassMatrix profile where
  tableClassifierEqualsEngineDisjunction := hasSomeTypingRule_eq_hasTableTypingRule
  honestFourHeadResidual := tableClassifierResidualHeadsLive
  reservedTableHeadsTruthful reserved classifier :=
    FX1Poly.Typed.reservedTableHeadUntypedBySurvivingEngines reserved classifier
  retiredMatchEnginesAreTableRows :=
    ⟨hasTableTypingRule_boolElim, hasTableTypingRule_optionMatch, hasTableTypingRule_eitherMatch⟩
  retiredPathAndProjectionEnginesAreTableRows :=
    ⟨hasTableTypingRule_idJ, hasTableTypingRule_fst, hasTableTypingRule_snd⟩
  retiredDataIntroEnginesAreTableRows :=
    ⟨hasTableTypingRule_natSucc, hasTableTypingRule_listCons, hasTableTypingRule_optionSome,
     hasTableTypingRule_optionNone, hasTableTypingRule_eitherInl, hasTableTypingRule_eitherInr,
     hasTableTypingRule_pair, hasTableTypingRule_refl⟩
  retiredNatCanonicityRestatedOverUnion typed normal pathAppFree pathLamFree :=
    FX1Poly.Typed.HasTypeUnion.closedNormalNatCanonicalForms typed normal pathAppFree pathLamFree
  oneSystemSignedOff := oneSystemSignoffHolds

end FX1PolyAudit

-- ===== Per-declaration zero-axiom audit gates =====
-- ★ the parity-and-surpass matrix bundle + its inhabitant
#assert_no_axioms FX1PolyAudit.ParityAndSurpassMatrix
#assert_no_axioms FX1PolyAudit.parityAndSurpassMatrixHolds
-- the per-family canonicity anchors (proof-term aliases, re-gated)
#assert_no_axioms FX1PolyAudit.parityAnchor_boolCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_natCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_optionCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_eitherCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_productCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_identityCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_listCanonicity
#assert_no_axioms FX1PolyAudit.parityAnchor_piCanonicity
#assert_no_axioms FX1PolyAudit.surpassAnchor_reservedTableHeadTruthful
-- the SURPASS carriers, re-verified zero-axiom at the bundle site
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_eq_hasTableTypingRule
#assert_no_axioms FX1Poly.Typed.tableClassifierResidualHeadsLive
#assert_no_axioms FX1Poly.Typed.reservedTableHeadUntypedBySurvivingEngines
-- the Stage-3 grand sign-off
#assert_no_axioms FX1PolyAudit.oneSystemSignoffHolds
