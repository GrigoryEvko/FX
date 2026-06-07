import FX1Poly.Tier0.FxBaseSubstScone
import FX1Poly.Core.SconingWitness

/-! # FX1Poly/Tier0/FxBaseSubstWitnessScone
    — the Path-A witness → Tier-0 categorical scone bridge (brick 8 of the term-carrying CwR base)

FX has TWO sconing framings.  The CONCRETE one (`FX1Poly/Core/SconingWitness.lean`, SN-092): a
`SconingWitness isWellTyped isCanonical` is the Path-A logical relation — a `computable` predicate on terms with
a `fundamental` obligation (every well-typed term is computable) and an `extraction` obligation (every computable
term is canonical), whose composite is canonicity; `reducibilityScone` builds one from any reducibility candidate.
The ABSTRACT one (`FX1Poly/Tier0/InternalSconing.lean`, the Uemura/BKS categorical framing): a `SconingObject` is
a syntactic object + a semantic domain + a `realizationMap` into the global sections.  The SUBSTVEC arc built the
abstract framing over a genuine term-carrying base (bricks 1-7); SUBSTVEC-7's `fxBaseSubstClosedTermScone` glued
the bare closed terms `RawTerm 0` onto the sections, carrying NO predicate.

This file connects the two: **any Path-A `SconingWitness` over closed terms induces a Tier-0 categorical
`SconingObject` over the term base**, whose semantic domain is the `computable` (hence, by `extraction`,
canonical) SUBSET of closed terms.  It is the first PREDICATE-carrying Tier-0 scone, and the term-base instance of
the "sconing is enough" thesis (SN-110): the concrete reducibility witness IS a categorical sconing object.

## What lands here (all zero-axiom)

  * `witnessScone witness : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections` — semantic domain
    `{ closedTerm : RawTerm 0 // witness.computable closedTerm }`, realization `closedTermAsSection ∘ Subtype.val`.
    The bridge from any closed-scope `SconingWitness` to a categorical scone.
  * `witnessScone_realizationInjective` — the realization is FAITHFUL (distinct computable terms realize
    distinctly), via `Subtype.ext` + `closedTermAsSection_injective`.
  * **`witnessScone_semanticIsCanonical`** — the scone's semantic domain consists of CANONICAL closed terms (the
    witness's `extraction` obligation): the categorical scone CARRIES the canonicity content.
  * `witnessSconeToClosedTermScone` — the witness-scone embeds into `fxBaseSubstClosedTermScone` via the subtype
    inclusion (`Subtype.val`); the realization square commutes by `mapsIdentity`.  Exhibits the predicate-carrying
    scone as a SUB-scone of the bare closed-term scone.

## Honest scope boundary

This is the bridge OBJECT + its faithfulness, canonicity, and sub-scone morphism — generic over any closed-scope
`SconingWitness` (so feeding `reducibilityScone` or any shipped data witness through it yields a concrete
predicate-carrying categorical scone).  It does NOT itself extract canonicity from arbitrary global sections (the
`extraction` direction over ALL sections would need a normalizer; the witness only certifies the computable
subset).  The full BKS `CanonicityExtraction` record — `extract` for EVERY sconing object — is not instantiable
non-vacuously (its semantic domains are arbitrary), so it stays a target signature.

## Zero-axiom verification

`witnessScone` is structure population (`Subtype` semantic domain, realization via `closedTermAsSection`).
Faithfulness composes `closedTermAsSection_injective` with `Subtype.ext`.  `_semanticIsCanonical` is the witness's
`extraction` field applied to the subtype's `property`.  The sub-scone morphism populates `SconingMorphism` with
the categorical identity and `Subtype.val`, commuting by `GlobalSections.mapsIdentity` (as SUBSTVEC-7).  No
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation

/-- **The Path-A witness → categorical scone bridge.**  Any closed-scope `SconingWitness` induces a Tier-0
`SconingObject` over the term base: syntactic object scope `1`, semantic domain the `computable` (= canonical)
subset of closed terms, realization the SUBSTVEC-6 iso restricted to that subset.  The first predicate-carrying
Tier-0 scone — the term-base instance of "the reducibility witness IS a categorical sconing object". -/
def witnessScone {isWellTyped isCanonical : RawTerm 0 → Prop}
    (witness : SconingWitness isWellTyped isCanonical) :
    SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections where
  syntacticObject := (1 : Nat)
  semanticDomain := { closedTerm : RawTerm 0 // witness.computable closedTerm }
  realizationMap := fun computableTerm => closedTermAsSection computableTerm.val

/-- The realization is FAITHFUL: distinct computable closed terms realize to distinct global elements. -/
theorem witnessScone_realizationInjective {isWellTyped isCanonical : RawTerm 0 → Prop}
    (witness : SconingWitness isWellTyped isCanonical)
    {firstComputable secondComputable : { closedTerm : RawTerm 0 // witness.computable closedTerm }}
    (realizationsEqual :
      (witnessScone witness).realizationMap firstComputable =
        (witnessScone witness).realizationMap secondComputable) :
    firstComputable = secondComputable :=
  Subtype.ext (closedTermAsSection_injective realizationsEqual)

/-- **The scone's semantic domain consists of CANONICAL closed terms** — the witness's `extraction` obligation
applied to each member's computability.  The categorical scone carries the canonicity content of the Path-A
witness. -/
theorem witnessScone_semanticIsCanonical {isWellTyped isCanonical : RawTerm 0 → Prop}
    (witness : SconingWitness isWellTyped isCanonical)
    (computableTerm : (witnessScone witness).semanticDomain) :
    isCanonical computableTerm.val :=
  witness.extraction computableTerm.val computableTerm.property

/-- The witness-scone embeds into the bare closed-term scone (`fxBaseSubstClosedTermScone`) via the subtype
inclusion `Subtype.val`; the realization square commutes by `mapsIdentity`.  Exhibits the predicate-carrying scone
as a SUB-scone of the closed-term scone. -/
def witnessSconeToClosedTermScone {isWellTyped isCanonical : RawTerm 0 → Prop}
    (witness : SconingWitness isWellTyped isCanonical) :
    SconingMorphism (witnessScone witness) fxBaseSubstClosedTermScone where
  syntacticMap := fxBaseSubstCategory.identity (1 : Nat)
  semanticMap := Subtype.val
  commutes := fun computableTerm =>
    fxBaseSubstGlobalSections.mapsIdentity (1 : Nat) (closedTermAsSection computableTerm.val)

end FX1Poly.Tier0
