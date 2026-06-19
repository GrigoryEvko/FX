import FX1Poly.Tier0.Term.Generator.GeneratorCore

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/ReducibilityCandidateDesc
    — the UNIVERSAL reducibility-candidate signature (FTGEN-1 design spike, the data layer)

This is the semantic mirror of the generator signature: a generator-agnostic combinator algebra
`ReducibilityCandidateDesc` whose shapes name, as DATA, the reducibility candidate of EVERY type former — the
live kernel formers now and the reserved (∞,ω) frontier formers pre-wired, exactly as the 208-generator
signature reserves slots.  The point (Option B / TYTAB-4): the Fundamental Theorem's per-former candidate
construction becomes ONE generic function keyed on this descriptor, so a new former = a new row + one local
candidate-validity obligation, inheriting SN/SR/canonicity/decidable-Conv.

## The shapes, and the `ReducibleTypeStepBounded` arm each generalizes

Existing candidate-assignment arms (DenoteKeyedBoundedReducibility.lean) ARE the seed; this descriptor lifts
them to data and extends them across the frontier:

  * `neutralSaturated`     ← the `neutral` arm (the CR3 base: SN neutral candidate).
  * `dependentProduct`     ← the `piType` arm (Π; ALSO subsumes the non-dependent `arrowCode` — a constant
                             codomain family — upgrading arrow from flat-data to genuine function-space).
  * `dependentSum`         ← NEW Σ arm (Σ; subsumes the non-dependent `productCode`).
  * `inductiveSaturated`   ← the `dataFlat` arm (already data-generic via `isFlatDataCode`), now carrying the
                             CONSTRUCTOR SPECS (arity + per-arg role) — the data the eliminator-induction
                             (FTGEN-11) cases on.  `emptyCode` = `inductiveSaturated []` (the `dataEmpty` arm).
  * `coinductiveSaturated` ← NEW (codata/streams, fx_design §3.5 / EXT-5): the observation-closed candidate.
  * `identitySaturated`    ← NEW (Id / idStrict via `isStrict`): the refl-saturated identity candidate.
  * `universeCandidate`    ← the `universeCode` arm (level-gated `universeDenotePredicate`).
  * `derivedUnfold`        ← NEW: a former whose candidate IS another former's — `equivCode ⇒ Σ(f:A→B),isEquiv`
                             (the cheap univalence-RHS unlock: CR-validity INHERITED from Σ, decoupled from
                             whether the unfolding is also a definitional reduction).
  * `relationalSaturated`  ← NEW (Gel / Bridge / transpension / parametricity): members are pairs related by R.
  * `quotientByRelation`   ← NEW (quotient types, fx_design §3.7 / EXT-2): the relation-quotiented candidate.
  * `propTruncated`        ← NEW (truncations / HIT set-levels, type-6): the level-truncated candidate.
  * `modalCandidate`       ← NEW (cohesion ♭/♯/ʃ, guarded ▷, clock, √ root — type-11/12/17 + mode axis):
                             the modal-fragment candidate.  RESERVED-frontier; the shape exists so a future
                             dispatch row needs no descriptor change.
  * `strictPropIrrelevant` ← NEW (SProp, type-19 / gen_sprop): the proof-irrelevant candidate.

## Scope of THIS file (honest)

This is the SIGNATURE/data layer only: the descriptor algebra + the 208-generator dispatch `candidateDescOf`
(composed propext-cleanly via `DecidableEq Generator` `if`-chains — NO wildcard match over 208 ctors) + the
per-former coverage theorems.  It does NOT build candidates (the denotation `desc → premise-cands → candidate`)
nor prove CR1/CR2/CR3 — those are FTGEN-1-proper / FTGEN-2 (the candidate-validity obligation interface) over
the carrier `RawTerm scope → Prop`.  The reserved frontier shapes (`coinductiveSaturated`, `quotientByRelation`,
`propTruncated`, `modalCandidate`) are pre-wired but mapped by `candidateDescOf` only where a live former exists
today; the rest correctly return `none`, mirroring the generator signature's reserved slots.

## Zero-axiom verification

Pure data (the descriptor + constructor-spec tables) + a total `DecidableEq Generator` `if`-chain dispatch +
`rfl` coverage theorems.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The role an eliminator-induction sees in a constructor's argument: a non-recursive parameter, a recursive
occurrence (the induction hypothesis site), or a type index. -/
inductive CandidateArgRole where
  | parameter
  | recursive
  | index

/-- A constructor's reducibility spec: which generator builds it and the role of each argument.  This is the
data the generic eliminator-reducibility proof (FTGEN-11) cases on — recursive args get the induction
hypothesis, parameter args get their sub-candidate. -/
structure CandidateConstructorSpec where
  constructorGenerator : Generator
  argRoles : List CandidateArgRole

/-- The modal fragments the reserved cohesion/guarded/clock frontier will instantiate (type-11/12/17 + mode
axis).  Pre-wired so activating a modal former is a dispatch row, not a descriptor change. -/
inductive CandidateModalShape where
  | flatComonad
  | sharpMonad
  | shapeModality
  | laterGuarded
  | clockUniversal
  | rootCohesion

/-- **The universal reducibility-candidate signature.**  One constructor per candidate SHAPE; the FT's generic
formation arm builds the candidate by recursion on this, the eliminator arm by recursion on the constructor
specs.  Generator-agnostic (reusable for any FX presentation, per SIG-3 / POLY-CAP). -/
inductive ReducibilityCandidateDesc where
  | neutralSaturated
  | dependentProduct
  | dependentSum
  | inductiveSaturated (constructors : List CandidateConstructorSpec)
  | coinductiveSaturated (observations : List Generator)
  | identitySaturated (isStrict : Bool)
  | universeCandidate
  | derivedUnfold (unfoldHead : Generator)
  | relationalSaturated
  | quotientByRelation
  | propTruncated (truncationLevel : Nat)
  | modalCandidate (modality : CandidateModalShape)
  | strictPropIrrelevant

/-! ## Constructor-spec tables for the live inductive formers (the eliminator-induction data) -/

/-- `bool` : two nullary constructors. -/
def boolCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_boolTrue, argRoles := [] }
  , { constructorGenerator := .gen_boolFalse, argRoles := [] } ]

/-- `nat` : zero + a recursive successor (the `recursive` arg is the induction site). -/
def natCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_natZero, argRoles := [] }
  , { constructorGenerator := .gen_natSucc, argRoles := [.recursive] } ]

/-- `list` : nil + cons (a parameter head and a recursive tail). -/
def listCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_listNil, argRoles := [] }
  , { constructorGenerator := .gen_listCons, argRoles := [.parameter, .recursive] } ]

/-- `option` : none + some (one parameter). -/
def optionCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_optionNone, argRoles := [] }
  , { constructorGenerator := .gen_optionSome, argRoles := [.parameter] } ]

/-- Binary coproduct (`either` / `sum`) : two single-parameter injections. -/
def coproductCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_eitherInl, argRoles := [.parameter] }
  , { constructorGenerator := .gen_eitherInr, argRoles := [.parameter] } ]

/-- `unit` : one nullary constructor. -/
def unitCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_unit, argRoles := [] } ]

/-- `interval` : the two endpoint constructors (connection-free affine fragment). -/
def intervalCandidateSpecs : List CandidateConstructorSpec :=
  [ { constructorGenerator := .gen_interval0, argRoles := [] }
  , { constructorGenerator := .gen_interval1, argRoles := [] } ]

/-! ## The dispatch — the candidate signature as a total function over the 208 generators

Composed propext-cleanly via `DecidableEq Generator` `if`-chains (the shipped, `rfl`-witnessed equality —
NO wildcard match over the 208-ctor enum).  Live formers map to their shape; everything else (constructors,
eliminators, levels, and the reserved frontier) returns `none`. -/
def candidateDescOf (generator : Generator) : Option ReducibilityCandidateDesc :=
  if generator = .gen_piTyCode then some .dependentProduct
  else if generator = .gen_arrowCode then some .dependentProduct
  else if generator = .gen_sigmaTyCode then some .dependentSum
  else if generator = .gen_productCode then some .dependentSum
  else if generator = .gen_boolCode then some (.inductiveSaturated boolCandidateSpecs)
  else if generator = .gen_natCode then some (.inductiveSaturated natCandidateSpecs)
  else if generator = .gen_listCode then some (.inductiveSaturated listCandidateSpecs)
  else if generator = .gen_optionCode then some (.inductiveSaturated optionCandidateSpecs)
  else if generator = .gen_eitherCode then some (.inductiveSaturated coproductCandidateSpecs)
  else if generator = .gen_sumCode then some (.inductiveSaturated coproductCandidateSpecs)
  else if generator = .gen_unitCode then some (.inductiveSaturated unitCandidateSpecs)
  else if generator = .gen_emptyCode then some (.inductiveSaturated [])
  else if generator = .gen_intervalCode then some (.inductiveSaturated intervalCandidateSpecs)
  else if generator = .gen_idCode then some (.identitySaturated false)
  else if generator = .gen_bridgeCode then some .relationalSaturated
  else if generator = .gen_equivCode then some (.derivedUnfold .gen_sigmaTyCode)
  else if generator = .gen_universeCode then some .universeCandidate
  else if generator = .gen_gelCode then some .relationalSaturated
  else if generator = .gen_sprop then some .strictPropIrrelevant
  else none

/-! ## Coverage theorems — every live former is assigned its shape, by `rfl` -/

theorem candidateDescOf_piTyCode : candidateDescOf .gen_piTyCode = some .dependentProduct := rfl
theorem candidateDescOf_arrowCode : candidateDescOf .gen_arrowCode = some .dependentProduct := rfl
theorem candidateDescOf_sigmaTyCode : candidateDescOf .gen_sigmaTyCode = some .dependentSum := rfl
theorem candidateDescOf_productCode : candidateDescOf .gen_productCode = some .dependentSum := rfl
theorem candidateDescOf_boolCode :
    candidateDescOf .gen_boolCode = some (.inductiveSaturated boolCandidateSpecs) := rfl
theorem candidateDescOf_natCode :
    candidateDescOf .gen_natCode = some (.inductiveSaturated natCandidateSpecs) := rfl
theorem candidateDescOf_listCode :
    candidateDescOf .gen_listCode = some (.inductiveSaturated listCandidateSpecs) := rfl
theorem candidateDescOf_optionCode :
    candidateDescOf .gen_optionCode = some (.inductiveSaturated optionCandidateSpecs) := rfl
theorem candidateDescOf_eitherCode :
    candidateDescOf .gen_eitherCode = some (.inductiveSaturated coproductCandidateSpecs) := rfl
theorem candidateDescOf_sumCode :
    candidateDescOf .gen_sumCode = some (.inductiveSaturated coproductCandidateSpecs) := rfl
theorem candidateDescOf_unitCode :
    candidateDescOf .gen_unitCode = some (.inductiveSaturated unitCandidateSpecs) := rfl
theorem candidateDescOf_emptyCode :
    candidateDescOf .gen_emptyCode = some (.inductiveSaturated []) := rfl
theorem candidateDescOf_intervalCode :
    candidateDescOf .gen_intervalCode = some (.inductiveSaturated intervalCandidateSpecs) := rfl
theorem candidateDescOf_idCode : candidateDescOf .gen_idCode = some (.identitySaturated false) := rfl
theorem candidateDescOf_bridgeCode : candidateDescOf .gen_bridgeCode = some .relationalSaturated := rfl
theorem candidateDescOf_equivCode :
    candidateDescOf .gen_equivCode = some (.derivedUnfold .gen_sigmaTyCode) := rfl
theorem candidateDescOf_universeCode : candidateDescOf .gen_universeCode = some .universeCandidate := rfl
theorem candidateDescOf_gelCode : candidateDescOf .gen_gelCode = some .relationalSaturated := rfl
theorem candidateDescOf_sprop : candidateDescOf .gen_sprop = some .strictPropIrrelevant := rfl

/-! ## Exclusion pins — non-formers (constructors, eliminators) and an inert frontier slot get no candidate -/

/-- A data CONSTRUCTOR is not a type former — no candidate (its reducibility is the intro obligation). -/
theorem candidateDescOf_lam_none : candidateDescOf .gen_lam = none := rfl
/-- An ELIMINATOR is not a type former — no candidate (its reducibility is the elim obligation). -/
theorem candidateDescOf_app_none : candidateDescOf .gen_app = none := rfl
/-- A still-inert frontier former (transpension `ungel`) gets no candidate yet — the descriptor SHAPE
(`relationalSaturated`) exists, but no dispatch row until the typed gel rows land (FTGEN-GEL). -/
theorem candidateDescOf_ungel_none : candidateDescOf .gen_ungel = none := rfl

/-- **The live candidate-signature roster** — the formers FTGEN-1-proper/FTGEN-2 must supply a candidate +
validity for.  Equivalent to: the union of the four bundle formation roles, plus the two pre-wired transpension
/ proof-irrelevance frontier formers (`gelCode`, `sprop`).  Count is the stale-guard. -/
def liveCandidateFormers : List Generator :=
  [ .gen_piTyCode, .gen_arrowCode, .gen_sigmaTyCode, .gen_productCode
  , .gen_boolCode, .gen_natCode, .gen_listCode, .gen_optionCode
  , .gen_eitherCode, .gen_sumCode, .gen_unitCode, .gen_emptyCode, .gen_intervalCode
  , .gen_idCode, .gen_bridgeCode, .gen_equivCode, .gen_universeCode
  , .gen_gelCode, .gen_sprop ]

/-- Stale-count guard: 19 live candidate formers. -/
theorem liveCandidateFormers_length : liveCandidateFormers.length = 19 := rfl

end FX1Poly.Typed
