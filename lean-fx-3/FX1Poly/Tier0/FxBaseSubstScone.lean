import FX1Poly.Tier0.FxBaseSubstGlobalSections

/-! # FX1Poly/Tier0/FxBaseSubstScone
    — the first non-trivial sconing object over the term base (brick 7 of the term-carrying CwR base)

`FxBaseSubstGlobalSections.lean` (SUBSTVEC-6) built the closed-terms `GlobalSections` `Hom(-, 0)` over the term
base, with the iso `sections 1 ≅ RawTerm 0` (global elements ARE closed terms).  `InternalSconing.lean` defines
`SconingObject category globalSections` — a syntactic object + a semantic domain + a `realizationMap :
semanticDomain → globalSections.sections syntacticObject` gluing the two — parameterized by a `GlobalSections`
ALONE (the RMC-gated parts of the ladder are `SconingLift` / `SconingPreservation`).  So a sconing object is
buildable over the term base right now, without the deferred substitution-iso RMC.

This file builds the FIRST NON-TRIVIAL sconing object for FX: the closed terms `RawTerm 0` glued onto the global
sections of the single-variable context via the SUBSTVEC-6 iso `closedTermAsSection` (a genuine syntactic-term
realization, NOT the tautological identity the renaming base was limited to).  It exhibits this scone as the
`RawTerm 0`-presentation of the canonical tautological scone at scope `1`, via mutually-inverse sconing morphisms.

## What lands here (all zero-axiom)

  * `fxBaseSubstClosedTermScone : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections` — syntactic object
    scope `1`, semantic domain `RawTerm 0` (the closed terms), realization `closedTermAsSection`.  The first
    sconing object for FX whose semantic domain is a real syntactic-term type realized into real closed-term
    sections.
  * `fxBaseSubstClosedTermScone_realizationInjective` — the realization is FAITHFUL: distinct closed terms realize
    to distinct global elements (via `closedTermAsSection_injective`).  A NON-DEGENERATE sconing object.
  * `closedTermSconeToTautological` / `tautologicalToClosedTermScone` — mutually-inverse sconing morphisms between
    the closed-term scone and the tautological scone at scope `1` (`SconingObject.tautological`), exhibiting the
    closed-term scone as the `RawTerm 0`-presentation of the canonical global-sections scone.  Their semantic maps
    are the SUBSTVEC-6 iso `closedTermAsSection` / `sectionAsClosedTerm`; the realization squares commute by
    `GlobalSections.mapsIdentity` (after collapsing the round-trip on the reverse direction).

## Honest scope boundary

This is a concrete sconing OBJECT + sconing MORPHISMS over the term base's `GlobalSections` — the genuine sconing
substrate the canonicity-extraction ladder (`CanonicityExtraction.extractRealizes`, SN-093) consumes, now
non-vacuous for the first time.  It is NOT the full BKS `SconingPreservation` (`liftsRepresentable` /
`liftsPullbacks`), which is parameterized over a `RepresentableMapCategory` — and the term base's RMC is deferred
(its `MorphismClass` needs a substitution-iso decider; see `FxBaseSubstSingleton.lean`).  The sconing-iso
composition laws (`comp _ _ = identity`) are intentionally NOT proved here: `SconingMorphism` equality compares the
semantic maps as functions, so it would require `funext` (which leaks `Quot.sound`); the SUBSTVEC-6 pointwise
round-trips already witness the two morphisms are mutually inverse at the element level without it.

## Zero-axiom verification

`fxBaseSubstClosedTermScone` is structure population (`realizationMap := closedTermAsSection`).  Faithfulness is
`closedTermAsSection_injective`.  The two morphisms populate `SconingMorphism` with `syntacticMap` the categorical
identity at scope `1` and `semanticMap` the SUBSTVEC-6 iso direction; the `commutes` squares are
`GlobalSections.mapsIdentity` (the reverse direction first `rw`s the round-trip `closedTermAsSection_sectionAsClosedTerm`).
The scope index `1` is the `(1 : Nat)` ascription on the `Object` argument (dodging `OfNat ... Object 1`, the same
trap SUBSTVEC-6 and the renaming base sidestep).  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation

/-- **The first non-trivial sconing object for FX.**  Glue the closed terms `RawTerm 0` onto the global sections of
the single-variable context (scope `1`) via the SUBSTVEC-6 iso `closedTermAsSection` — a genuine syntactic-term
realization, not the tautological identity.  The concrete sconing substrate the canonicity-extraction ladder needs,
non-vacuous for the first time over a term-carrying base. -/
def fxBaseSubstClosedTermScone : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections where
  syntacticObject := (1 : Nat)
  semanticDomain := RawTerm 0
  realizationMap := closedTermAsSection

/-- The realization is FAITHFUL: distinct closed terms realize to distinct global elements — a non-degenerate
sconing object (via the SUBSTVEC-6 faithful embedding). -/
theorem fxBaseSubstClosedTermScone_realizationInjective
    {firstClosedTerm secondClosedTerm : RawTerm 0}
    (realizationsEqual :
      fxBaseSubstClosedTermScone.realizationMap firstClosedTerm =
        fxBaseSubstClosedTermScone.realizationMap secondClosedTerm) :
    firstClosedTerm = secondClosedTerm :=
  closedTermAsSection_injective realizationsEqual

/-- The closed-term scone embeds into the tautological scone at scope `1` (semantic map = the iso
`closedTermAsSection`); the realization square commutes by `mapsIdentity`. -/
def closedTermSconeToTautological :
    SconingMorphism fxBaseSubstClosedTermScone
      (SconingObject.tautological fxBaseSubstGlobalSections (1 : Nat)) where
  syntacticMap := fxBaseSubstCategory.identity (1 : Nat)
  semanticMap := closedTermAsSection
  commutes := fun closedTerm =>
    fxBaseSubstGlobalSections.mapsIdentity (1 : Nat) (closedTermAsSection closedTerm)

/-- The reverse embedding: the tautological scone maps back via `sectionAsClosedTerm`, exhibiting the closed-term
scone as the `RawTerm 0`-presentation of the canonical global-sections scone.  The realization square commutes by
the SUBSTVEC-6 round-trip `closedTermAsSection_sectionAsClosedTerm` + `mapsIdentity`. -/
def tautologicalToClosedTermScone :
    SconingMorphism (SconingObject.tautological fxBaseSubstGlobalSections (1 : Nat))
      fxBaseSubstClosedTermScone where
  syntacticMap := fxBaseSubstCategory.identity (1 : Nat)
  semanticMap := sectionAsClosedTerm
  commutes := fun someSection => by
    show fxBaseSubstGlobalSections.sectionMap (fxBaseSubstCategory.identity (1 : Nat))
        (closedTermAsSection (sectionAsClosedTerm someSection)) = someSection
    rw [closedTermAsSection_sectionAsClosedTerm]
    exact fxBaseSubstGlobalSections.mapsIdentity (1 : Nat) someSection

end FX1Poly.Tier0
