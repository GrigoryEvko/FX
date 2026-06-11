import FX1Poly.Typed.SconingIsEnoughThesis
import FX1Poly.Typed.GeneratorHonestyOverview
import FX1Poly.Typed.GeneratorAdmissionSplit
import FX1Poly.Core.DataReducibilityCoverage

/-! # FX1Poly/Typed/LiveSignatureSconingCoverage
    — ★ the O-NORM admission gate: every semantically-live generator is sconing-covered (ONORM-M2, #1212)

The third SN-110 residual, closed: the operational O-NORM target is "one sconing witness total on the
semantically-live signature, plus a machine-checked admission gate".  This file IS that gate:

  * `LiveGenerator` — the 40-constructor enumeration of the live signature (every generator with
    `semanticTier = .live`: 14 type formers/codes, 15 value constructors including the variable and
    the lambda, 11 eliminators).  `LiveGenerator.isLive` proves every member live by `rfl`.
  * ★ `liveSignature_complete` — **the admission gate**: EVERY generator the classifier reports live
    is in the enumeration, by full 198-arm case analysis (reserved arms refute the hypothesis by
    kernel evaluation of the classifier; live arms decide list membership).  A generator going live
    — a new rule-table row, a new reduction rule — without a `LiveGenerator` constructor and a
    coverage arm BREAKS THIS THEOREM.  That is the admission discipline, machine-checked.
  * `SconingCoverageRole` + `LiveGenerator.sconingRole` — the six-way coverage taxonomy: dependent
    former (Π), neutral former (the 13 non-Π formers/codes), value constructor (13 data
    constructors), abstraction constructor (λ), neutral leaf (the variable), eliminator (11).
  * ★ `LiveGenerator.neutralFormerCellHasGluedLift` — **the new lifts**: every neutral-former cell,
    for EVERY payload and child vector, admits a glued-model lift with the SN scone (the ONORM-M1
    `modalityLift` recipe applied across the 13 live formers — the glued model is now closed over
    the ENTIRE live former signature).
  * `LiveGenerator.dependentFormerIsPi` + `piTyCode_hasConditionalGluedLift` — the Π former's lift
    is the SN-091 `piLift`, CONDITIONAL on the modeled-codomain data (the honest asymmetry: Π is
    the genuinely dependent former; its scone needs the model data, not just weak-head normality).
  * `LiveGenerator.constructorFamily` + `constructorFamilyHasTaitCandidate` — each of the 13 value
    constructors is pinned to ITS `DataFormerFamily`, whose canonical-forms Tait candidate is a full
    Girard reducibility candidate (the indexed dispatch prevents cross-family discharge).
  * `LiveGenerator.neutralLeafMemberOfEveryCandidate` — the variable is a member of EVERY
    canonical-forms candidate (`CanonicalFormsPredicate.containsVariable` — the candidate
    non-emptiness fact the fundamental theorem's variable case consumes).
  * `LiveGenerator.abstractionConstructorPreservesSn` — λ-cells with strongly-normalizing
    components are strongly normalizing (the SN scone closure; the full dependent-arrow MEMBERSHIP
    of the abstraction is the shipped `DependentArrowCandidate.abstraction` FT-arm content).
  * `LiveGenerator.eliminatorHasRedexHead` — every eliminator-role generator carries a root
    reduction rule (`rfl` per arm) — the operational half of its coverage; the per-eliminator
    candidate-membership facts are the shipped SN-058…069 arc (value-case ι-redex SN,
    neutral-scrutinee membership, closed-member facts), cited per regime there.

## Honest scope boundary

Coverage is PER ROLE, not one uniform statement — a former is covered by a glued lift, a constructor
by its family candidate, an eliminator by its reduction rule plus the per-regime reducibility arc.
The uniform "SN-closure for every live generator" is FALSE (an application of strongly-normalizing
children need not be strongly normalizing — the untyped `Ω`), which is exactly why the taxonomy
exists.  The modal fragment is correctly ABSENT from this enumeration: its generators are statically
untyped and β/ι-inert today (`modalTermFragment_isStaticallyUntypedToday`); its sconing coverage is
the ONORM-M1 semantic layer, joining this gate when a modal rule-table row lands.

## Zero-axiom verification

A plain 40-ctor enum with full-enumeration dispatches (no wildcard), the 198-arm completeness gate
(reserved arms by eager `absurd` + `of_decide_eq_true rfl` refutation of the kernel-reduced
classifier, live arms by `rfl` on the Boolean `contains` — the `List.Mem` decidability instance
leaks `propext` and is avoided), the lifts via `ReducibleType.neutral` per former, and citation
one-liners.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- **The live signature, enumerated**: one constructor per generator with `semanticTier = .live` —
14 type formers/codes, 15 value constructors (including the variable and the lambda), 11
eliminators.  The coverage dispatches below are total over this enumeration; `liveSignature_complete`
forces every live generator into it. -/
inductive LiveGenerator where
  | var
  | unit
  | lam
  | app
  | pair
  | fst
  | snd
  | boolTrue
  | boolFalse
  | boolElim
  | natZero
  | natSucc
  | natElim
  | natRec
  | listNil
  | listCons
  | listElim
  | optionNone
  | optionSome
  | optionMatch
  | eitherInl
  | eitherInr
  | eitherMatch
  | refl
  | idJ
  | idStrictRec
  | universeCode
  | arrowCode
  | piTyCode
  | sigmaTyCode
  | productCode
  | sumCode
  | listCode
  | optionCode
  | eitherCode
  | equivCode
  | emptyCode
  | boolCode
  | natCode
  | unitCode
  | intervalCode
  | bridgeCode
  | interval0
  | interval1
  | pathLam
  | pathApp

/-- The generator each live-signature member names. -/
def LiveGenerator.generator : LiveGenerator → Generator
  | .var => .gen_var
  | .unit => .gen_unit
  | .lam => .gen_lam
  | .app => .gen_app
  | .pair => .gen_pair
  | .fst => .gen_fst
  | .snd => .gen_snd
  | .boolTrue => .gen_boolTrue
  | .boolFalse => .gen_boolFalse
  | .boolElim => .gen_boolElim
  | .natZero => .gen_natZero
  | .natSucc => .gen_natSucc
  | .natElim => .gen_natElim
  | .natRec => .gen_natRec
  | .listNil => .gen_listNil
  | .listCons => .gen_listCons
  | .listElim => .gen_listElim
  | .optionNone => .gen_optionNone
  | .optionSome => .gen_optionSome
  | .optionMatch => .gen_optionMatch
  | .eitherInl => .gen_eitherInl
  | .eitherInr => .gen_eitherInr
  | .eitherMatch => .gen_eitherMatch
  | .refl => .gen_refl
  | .idJ => .gen_idJ
  | .idStrictRec => .gen_idStrictRec
  | .universeCode => .gen_universeCode
  | .arrowCode => .gen_arrowCode
  | .piTyCode => .gen_piTyCode
  | .sigmaTyCode => .gen_sigmaTyCode
  | .productCode => .gen_productCode
  | .sumCode => .gen_sumCode
  | .listCode => .gen_listCode
  | .optionCode => .gen_optionCode
  | .eitherCode => .gen_eitherCode
  | .equivCode => .gen_equivCode
  | .emptyCode => .gen_emptyCode
  | .boolCode => .gen_boolCode
  | .natCode => .gen_natCode
  | .unitCode => .gen_unitCode
  | .intervalCode => .gen_intervalCode
  | .bridgeCode => .gen_bridgeCode
  | .interval0 => .gen_interval0
  | .interval1 => .gen_interval1
  | .pathLam => .gen_pathLam
  | .pathApp => .gen_pathApp

/-- **Soundness of the enumeration**: every member of the live-signature enumeration is reported
live by the honest classifier — 40 kernel evaluations of `semanticTier`. -/
theorem LiveGenerator.isLive : ∀ liveGenerator : LiveGenerator,
    semanticTier liveGenerator.generator = .live := by
  intro liveGenerator
  cases liveGenerator <;> rfl

/-- The live-signature enumeration as a list, in constructor order. -/
def LiveGenerator.all : List LiveGenerator :=
  [.var, .unit, .lam, .app, .pair, .fst, .snd, .boolTrue, .boolFalse, .boolElim,
   .natZero, .natSucc, .natElim, .natRec, .listNil, .listCons, .listElim,
   .optionNone, .optionSome, .optionMatch, .eitherInl, .eitherInr, .eitherMatch,
   .refl, .idJ, .idStrictRec, .universeCode, .arrowCode, .piTyCode, .sigmaTyCode,
   .productCode, .sumCode, .listCode, .optionCode, .eitherCode, .equivCode,
   .emptyCode, .boolCode, .natCode, .unitCode,
   .intervalCode, .bridgeCode, .interval0, .interval1, .pathLam, .pathApp]

/-- The live signature as a generator list — the carrier of the admission gate. -/
def liveSignatureList : List Generator := LiveGenerator.all.map LiveGenerator.generator

/-- The live signature has exactly forty-six members — the count pin (breaks when the
enumeration grows or shrinks without updating the recorded size). -/
theorem liveSignature_count : liveSignatureList.length = 46 := rfl

/-- ★ **The O-NORM admission gate**: every generator the honest classifier reports semantically
LIVE is in the enumerated live signature (Boolean `contains` — the `List.Mem` decidability
instance leaks `propext`, so the gate is stated over the kernel-evaluable `contains`).  Full 198-arm
case analysis: reserved arms refute the hypothesis eagerly via `absurd` + `of_decide_eq_true rfl`
(a postponed `nomatch` escapes the `first` combinator); live arms evaluate `contains` by `rfl`.  A
generator going live — a new rule-table row, a new reduction rule — without a `LiveGenerator`
constructor (and hence without arms in every coverage dispatch below) BREAKS THIS THEOREM: that is
the machine-checked admission discipline. -/
theorem liveSignature_complete :
    ∀ generator : Generator, semanticTier generator = .live →
      liveSignatureList.contains generator = true := by
  intro generator
  cases generator <;> first
    | exact fun isLive => absurd isLive (of_decide_eq_true rfl)
    | exact fun _ => rfl

/-- **The six-way sconing-coverage taxonomy** over the live signature.  Coverage is per role — the
uniform "SN-closure for every live generator" is FALSE (untyped `Ω` is an application of
strongly-normalizing children), which is why the taxonomy exists. -/
inductive SconingCoverageRole where
  /-- The genuinely dependent former (Π): glued lift CONDITIONAL on modeled-codomain data. -/
  | dependentFormer
  /-- Weak-head-normal non-Π formers/codes: UNCONDITIONAL glued lift through the neutral arm. -/
  | neutralFormer
  /-- Data value constructors: value cells inhabit the family's shipped Tait candidate. -/
  | valueConstructor
  /-- The lambda: SN scone closure + the dependent-arrow abstraction membership. -/
  | abstractionConstructor
  /-- The variable: a member of EVERY canonical-forms candidate. -/
  | neutralLeaf
  /-- Root-reduction heads: covered by the reduction rule + the per-regime reducibility arc. -/
  | eliminator
  /-- Typed elimination heads with NO root reduction rule TODAY (the bridge `pathApp`, whose
  endpoint-ι is the recorded OP1-INT gap): β/ι-inert, hence weak-head normal — covered by the
  unconditional neutral lift; migrates to `eliminator` when its ι lands (this enum breaks then,
  by design). -/
  | inertEliminator

/-- The coverage role of each live-signature member. -/
def LiveGenerator.sconingRole : LiveGenerator → SconingCoverageRole
  | .var => .neutralLeaf
  | .unit => .valueConstructor
  | .lam => .abstractionConstructor
  | .app => .eliminator
  | .pair => .valueConstructor
  | .fst => .eliminator
  | .snd => .eliminator
  | .boolTrue => .valueConstructor
  | .boolFalse => .valueConstructor
  | .boolElim => .eliminator
  | .natZero => .valueConstructor
  | .natSucc => .valueConstructor
  | .natElim => .eliminator
  | .natRec => .eliminator
  | .listNil => .valueConstructor
  | .listCons => .valueConstructor
  | .listElim => .eliminator
  | .optionNone => .valueConstructor
  | .optionSome => .valueConstructor
  | .optionMatch => .eliminator
  | .eitherInl => .valueConstructor
  | .eitherInr => .valueConstructor
  | .eitherMatch => .eliminator
  | .refl => .valueConstructor
  | .idJ => .eliminator
  | .idStrictRec => .eliminator
  | .universeCode => .neutralFormer
  | .arrowCode => .neutralFormer
  | .piTyCode => .dependentFormer
  | .sigmaTyCode => .neutralFormer
  | .productCode => .neutralFormer
  | .sumCode => .neutralFormer
  | .listCode => .neutralFormer
  | .optionCode => .neutralFormer
  | .eitherCode => .neutralFormer
  | .equivCode => .neutralFormer
  | .emptyCode => .neutralFormer
  | .boolCode => .neutralFormer
  | .natCode => .neutralFormer
  | .unitCode => .neutralFormer
  | .intervalCode => .neutralFormer
  | .bridgeCode => .neutralFormer
  | .interval0 => .valueConstructor
  | .interval1 => .valueConstructor
  | .pathLam => .abstractionConstructor
  | .pathApp => .inertEliminator

/-- ★ **Every neutral-former cell admits a glued-model lift** — for EVERY payload and child vector,
unconditionally: the cell is weak-head normal (no β head, no root ι, no eliminator scrutinee — the
`cases`-`rootIota` script per former) and not Π-rooted, so `ReducibleType.neutral` assigns the SN
scone.  The ONORM-M1 `modalityLift` recipe applied across the 13 live non-Π formers: the glued
model is closed over the ENTIRE live former signature. -/
theorem LiveGenerator.neutralFormerCellHasGluedLift {scope : Nat} :
    (liveGenerator : LiveGenerator) →
      liveGenerator.sconingRole = .neutralFormer →
      ∀ (payload : (liveGenerator.generator).payload scope)
        (children : RawTermChildren (liveGenerator.generator).binderShifts scope),
        ∃ glued : GluedTypeCell scope,
          glued.typeCell = .mkGen liveGenerator.generator payload children
            ∧ glued.computable = IsStronglyNormalizing
  | .var, roleEq => nomatch roleEq
  | .unit, roleEq => nomatch roleEq
  | .lam, roleEq => nomatch roleEq
  | .app, roleEq => nomatch roleEq
  | .pair, roleEq => nomatch roleEq
  | .fst, roleEq => nomatch roleEq
  | .snd, roleEq => nomatch roleEq
  | .boolTrue, roleEq => nomatch roleEq
  | .boolFalse, roleEq => nomatch roleEq
  | .boolElim, roleEq => nomatch roleEq
  | .natZero, roleEq => nomatch roleEq
  | .natSucc, roleEq => nomatch roleEq
  | .natElim, roleEq => nomatch roleEq
  | .natRec, roleEq => nomatch roleEq
  | .listNil, roleEq => nomatch roleEq
  | .listCons, roleEq => nomatch roleEq
  | .listElim, roleEq => nomatch roleEq
  | .optionNone, roleEq => nomatch roleEq
  | .optionSome, roleEq => nomatch roleEq
  | .optionMatch, roleEq => nomatch roleEq
  | .eitherInl, roleEq => nomatch roleEq
  | .eitherInr, roleEq => nomatch roleEq
  | .eitherMatch, roleEq => nomatch roleEq
  | .refl, roleEq => nomatch roleEq
  | .idJ, roleEq => nomatch roleEq
  | .idStrictRec, roleEq => nomatch roleEq
  | .universeCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_universeCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .arrowCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_arrowCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .piTyCode, roleEq => nomatch roleEq
  | .sigmaTyCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_sigmaTyCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .productCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_productCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .sumCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_sumCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .listCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_listCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .optionCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_optionCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .eitherCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_eitherCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .equivCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_equivCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .emptyCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_emptyCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .boolCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_boolCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .natCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_natCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .unitCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_unitCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .intervalCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_intervalCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .bridgeCode, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_bridgeCode payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩
  | .interval0, roleEq => nomatch roleEq
  | .interval1, roleEq => nomatch roleEq
  | .pathLam, roleEq => nomatch roleEq
  | .pathApp, roleEq => nomatch roleEq

/-- **The dependent-former role is exactly Π** — the one live former whose glued lift is
CONDITIONAL (the SN-091 `piLift` needs the modeled-codomain data; weak-head normality alone cannot
classify a Π cell, whose scone is the dependent function-space predicate, not SN). -/
theorem LiveGenerator.dependentFormerIsPi :
    (liveGenerator : LiveGenerator) →
      liveGenerator.sconingRole = .dependentFormer →
      liveGenerator.generator = .gen_piTyCode
  | .var, roleEq => nomatch roleEq
  | .unit, roleEq => nomatch roleEq
  | .lam, roleEq => nomatch roleEq
  | .app, roleEq => nomatch roleEq
  | .pair, roleEq => nomatch roleEq
  | .fst, roleEq => nomatch roleEq
  | .snd, roleEq => nomatch roleEq
  | .boolTrue, roleEq => nomatch roleEq
  | .boolFalse, roleEq => nomatch roleEq
  | .boolElim, roleEq => nomatch roleEq
  | .natZero, roleEq => nomatch roleEq
  | .natSucc, roleEq => nomatch roleEq
  | .natElim, roleEq => nomatch roleEq
  | .natRec, roleEq => nomatch roleEq
  | .listNil, roleEq => nomatch roleEq
  | .listCons, roleEq => nomatch roleEq
  | .listElim, roleEq => nomatch roleEq
  | .optionNone, roleEq => nomatch roleEq
  | .optionSome, roleEq => nomatch roleEq
  | .optionMatch, roleEq => nomatch roleEq
  | .eitherInl, roleEq => nomatch roleEq
  | .eitherInr, roleEq => nomatch roleEq
  | .eitherMatch, roleEq => nomatch roleEq
  | .refl, roleEq => nomatch roleEq
  | .idJ, roleEq => nomatch roleEq
  | .idStrictRec, roleEq => nomatch roleEq
  | .universeCode, roleEq => nomatch roleEq
  | .arrowCode, roleEq => nomatch roleEq
  | .piTyCode, _roleEq => rfl
  | .sigmaTyCode, roleEq => nomatch roleEq
  | .productCode, roleEq => nomatch roleEq
  | .sumCode, roleEq => nomatch roleEq
  | .listCode, roleEq => nomatch roleEq
  | .optionCode, roleEq => nomatch roleEq
  | .eitherCode, roleEq => nomatch roleEq
  | .equivCode, roleEq => nomatch roleEq
  | .emptyCode, roleEq => nomatch roleEq
  | .boolCode, roleEq => nomatch roleEq
  | .natCode, roleEq => nomatch roleEq
  | .unitCode, roleEq => nomatch roleEq
  | .intervalCode, roleEq => nomatch roleEq
  | .bridgeCode, roleEq => nomatch roleEq
  | .interval0, roleEq => nomatch roleEq
  | .interval1, roleEq => nomatch roleEq
  | .pathLam, roleEq => nomatch roleEq
  | .pathApp, roleEq => nomatch roleEq

/-- **The Π former's conditional glued lift** — the SN-091 `piLift` restated as the dependent
former's coverage: given the modeled-codomain data, the Π cell admits a glued lift whose scone is
the dependent function-space predicate. -/
theorem piTyCode_hasConditionalGluedLift {scope : Nat} (domainGlued : GluedTypeCell scope)
    (codomainCode : RawTerm (scope + 1))
    (codomainComputable : RawTerm scope → (RawTerm scope → Prop))
    (codomainModeled : ∀ argument : RawTerm scope, domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument)) :
    ∃ glued : GluedTypeCell scope,
      glued.typeCell = piFormerMap.component scope (domainGlued.typeCell, codomainCode)
        ∧ glued.computable
            = IsDependentArrowReducible domainGlued.computable codomainComputable :=
  ⟨domainGlued.piLift codomainCode codomainComputable codomainModeled, rfl, rfl⟩

/-- **Each value constructor's data-former family** — the indexed pin: every valueConstructor-role
generator maps to ITS `DataFormerFamily`, so the candidate fact below cannot be discharged by
another family's candidate. -/
def LiveGenerator.constructorFamily :
    (liveGenerator : LiveGenerator) →
      liveGenerator.sconingRole = .valueConstructor → DataFormerFamily
  | .var, roleEq => nomatch roleEq
  | .unit, _roleEq => .unitFamily
  | .lam, roleEq => nomatch roleEq
  | .app, roleEq => nomatch roleEq
  | .pair, _roleEq => .pairFamily
  | .fst, roleEq => nomatch roleEq
  | .snd, roleEq => nomatch roleEq
  | .boolTrue, _roleEq => .boolFamily
  | .boolFalse, _roleEq => .boolFamily
  | .boolElim, roleEq => nomatch roleEq
  | .natZero, _roleEq => .natFamily
  | .natSucc, _roleEq => .natFamily
  | .natElim, roleEq => nomatch roleEq
  | .natRec, roleEq => nomatch roleEq
  | .listNil, _roleEq => .listFamily
  | .listCons, _roleEq => .listFamily
  | .listElim, roleEq => nomatch roleEq
  | .optionNone, _roleEq => .optionFamily
  | .optionSome, _roleEq => .optionFamily
  | .optionMatch, roleEq => nomatch roleEq
  | .eitherInl, _roleEq => .eitherFamily
  | .eitherInr, _roleEq => .eitherFamily
  | .eitherMatch, roleEq => nomatch roleEq
  | .refl, _roleEq => .identityFamily
  | .idJ, roleEq => nomatch roleEq
  | .idStrictRec, roleEq => nomatch roleEq
  | .universeCode, roleEq => nomatch roleEq
  | .arrowCode, roleEq => nomatch roleEq
  | .piTyCode, roleEq => nomatch roleEq
  | .sigmaTyCode, roleEq => nomatch roleEq
  | .productCode, roleEq => nomatch roleEq
  | .sumCode, roleEq => nomatch roleEq
  | .listCode, roleEq => nomatch roleEq
  | .optionCode, roleEq => nomatch roleEq
  | .eitherCode, roleEq => nomatch roleEq
  | .equivCode, roleEq => nomatch roleEq
  | .emptyCode, roleEq => nomatch roleEq
  | .boolCode, roleEq => nomatch roleEq
  | .natCode, roleEq => nomatch roleEq
  | .unitCode, roleEq => nomatch roleEq
  | .intervalCode, roleEq => nomatch roleEq
  | .bridgeCode, roleEq => nomatch roleEq
  | .interval0, _roleEq => .intervalFamily
  | .interval1, _roleEq => .intervalFamily
  | .pathLam, roleEq => nomatch roleEq
  | .pathApp, roleEq => nomatch roleEq

/-- **Every value constructor's family candidate is a full Girard reducibility candidate** — the
SN-082 coverage theorem applied at the constructor's own pinned family. -/
theorem LiveGenerator.constructorFamilyHasTaitCandidate {scope : Nat}
    (liveGenerator : LiveGenerator)
    (roleEq : liveGenerator.sconingRole = .valueConstructor) :
    IsReducibilityCandidate
      (CanonicalFormsPredicate
        ((liveGenerator.constructorFamily roleEq).valuePredicate (scope := scope))) :=
  DataFormerFamily.hasReducibilityCandidate (liveGenerator.constructorFamily roleEq)

/-- **The neutral leaf is covered by candidate non-emptiness**: a variable cell is a member of
EVERY canonical-forms candidate (neutral with no reducts — the fact the fundamental theorem's
variable case consumes). -/
theorem LiveGenerator.neutralLeafMemberOfEveryCandidate {scope : Nat} :
    (liveGenerator : LiveGenerator) →
      liveGenerator.sconingRole = .neutralLeaf →
      ∀ (isValue : RawTerm scope → Prop)
        (payload : (liveGenerator.generator).payload scope)
        (children : RawTermChildren (liveGenerator.generator).binderShifts scope),
        CanonicalFormsPredicate isValue (.mkGen liveGenerator.generator payload children)
  | .var, _roleEq => fun isValue payload children =>
      match children with
      | .childNil => CanonicalFormsPredicate.containsVariable (isValue := isValue) payload
  | .unit, roleEq => nomatch roleEq
  | .lam, roleEq => nomatch roleEq
  | .app, roleEq => nomatch roleEq
  | .pair, roleEq => nomatch roleEq
  | .fst, roleEq => nomatch roleEq
  | .snd, roleEq => nomatch roleEq
  | .boolTrue, roleEq => nomatch roleEq
  | .boolFalse, roleEq => nomatch roleEq
  | .boolElim, roleEq => nomatch roleEq
  | .natZero, roleEq => nomatch roleEq
  | .natSucc, roleEq => nomatch roleEq
  | .natElim, roleEq => nomatch roleEq
  | .natRec, roleEq => nomatch roleEq
  | .listNil, roleEq => nomatch roleEq
  | .listCons, roleEq => nomatch roleEq
  | .listElim, roleEq => nomatch roleEq
  | .optionNone, roleEq => nomatch roleEq
  | .optionSome, roleEq => nomatch roleEq
  | .optionMatch, roleEq => nomatch roleEq
  | .eitherInl, roleEq => nomatch roleEq
  | .eitherInr, roleEq => nomatch roleEq
  | .eitherMatch, roleEq => nomatch roleEq
  | .refl, roleEq => nomatch roleEq
  | .idJ, roleEq => nomatch roleEq
  | .idStrictRec, roleEq => nomatch roleEq
  | .universeCode, roleEq => nomatch roleEq
  | .arrowCode, roleEq => nomatch roleEq
  | .piTyCode, roleEq => nomatch roleEq
  | .sigmaTyCode, roleEq => nomatch roleEq
  | .productCode, roleEq => nomatch roleEq
  | .sumCode, roleEq => nomatch roleEq
  | .listCode, roleEq => nomatch roleEq
  | .optionCode, roleEq => nomatch roleEq
  | .eitherCode, roleEq => nomatch roleEq
  | .equivCode, roleEq => nomatch roleEq
  | .emptyCode, roleEq => nomatch roleEq
  | .boolCode, roleEq => nomatch roleEq
  | .natCode, roleEq => nomatch roleEq
  | .unitCode, roleEq => nomatch roleEq
  | .intervalCode, roleEq => nomatch roleEq
  | .bridgeCode, roleEq => nomatch roleEq
  | .interval0, roleEq => nomatch roleEq
  | .interval1, roleEq => nomatch roleEq
  | .pathLam, roleEq => nomatch roleEq
  | .pathApp, roleEq => nomatch roleEq

/-- **The abstraction constructor preserves the SN scone**: a λ-cell with strongly-normalizing
domain annotation and body is strongly normalizing (`lam_isStronglyNormalizing_of_body`).  The full
dependent-arrow MEMBERSHIP of the abstraction — λ-cells inhabit the Π scone — is the shipped
`DependentArrowCandidate.abstraction` / piIntro fundamental-theorem arm content. -/
theorem LiveGenerator.abstractionConstructorPreservesSn {scope : Nat}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainNormalizing : IsStronglyNormalizing domainAnn)
    (bodyNormalizing : IsStronglyNormalizing body) :
    IsStronglyNormalizing
      (.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons body .childNil)) : RawTerm scope) :=
  lam_isStronglyNormalizing_of_body domainNormalizing bodyNormalizing

/-- **Every eliminator-role generator carries a root reduction rule** — the operational half of
eliminator coverage (`rfl` per arm against the HON-2 classifier).  The semantic half — the
per-eliminator candidate facts (value-case ι-redex SN, neutral-scrutinee membership, closed-member
facts) — is the shipped SN-058…069 arc, per regime. -/
theorem LiveGenerator.eliminatorHasRedexHead :
    (liveGenerator : LiveGenerator) →
      liveGenerator.sconingRole = .eliminator →
      (liveGenerator.generator).hasRedexHead = true
  | .var, roleEq => nomatch roleEq
  | .unit, roleEq => nomatch roleEq
  | .lam, roleEq => nomatch roleEq
  | .app, _roleEq => rfl
  | .pair, roleEq => nomatch roleEq
  | .fst, _roleEq => rfl
  | .snd, _roleEq => rfl
  | .boolTrue, roleEq => nomatch roleEq
  | .boolFalse, roleEq => nomatch roleEq
  | .boolElim, _roleEq => rfl
  | .natZero, roleEq => nomatch roleEq
  | .natSucc, roleEq => nomatch roleEq
  | .natElim, _roleEq => rfl
  | .natRec, _roleEq => rfl
  | .listNil, roleEq => nomatch roleEq
  | .listCons, roleEq => nomatch roleEq
  | .listElim, _roleEq => rfl
  | .optionNone, roleEq => nomatch roleEq
  | .optionSome, roleEq => nomatch roleEq
  | .optionMatch, _roleEq => rfl
  | .eitherInl, roleEq => nomatch roleEq
  | .eitherInr, roleEq => nomatch roleEq
  | .eitherMatch, _roleEq => rfl
  | .refl, roleEq => nomatch roleEq
  | .idJ, _roleEq => rfl
  | .idStrictRec, _roleEq => rfl
  | .universeCode, roleEq => nomatch roleEq
  | .arrowCode, roleEq => nomatch roleEq
  | .piTyCode, roleEq => nomatch roleEq
  | .sigmaTyCode, roleEq => nomatch roleEq
  | .productCode, roleEq => nomatch roleEq
  | .sumCode, roleEq => nomatch roleEq
  | .listCode, roleEq => nomatch roleEq
  | .optionCode, roleEq => nomatch roleEq
  | .eitherCode, roleEq => nomatch roleEq
  | .equivCode, roleEq => nomatch roleEq
  | .emptyCode, roleEq => nomatch roleEq
  | .boolCode, roleEq => nomatch roleEq
  | .natCode, roleEq => nomatch roleEq
  | .unitCode, roleEq => nomatch roleEq
  | .intervalCode, roleEq => nomatch roleEq
  | .bridgeCode, roleEq => nomatch roleEq
  | .interval0, roleEq => nomatch roleEq
  | .interval1, roleEq => nomatch roleEq
  | .pathLam, roleEq => nomatch roleEq
  | .pathApp, roleEq => nomatch roleEq

/-- **The bridge abstraction constructor preserves the SN scone** — the `pathLam` twin of the
λ coverage: a path-abstraction cell with a strongly-normalizing body is strongly normalizing
(`pathLam_isStronglyNormalizing_of_body`, the unary-binder cong closure).  The full bridge
MEMBERSHIP of the abstraction — pathLam-cells inhabit the bridge scone — is the OP1-INT
verdict residual (the affine-dimension glued-model statement over the graded `pathIntro`
row). -/
theorem LiveGenerator.pathAbstractionConstructorPreservesSn {scope : Nat}
    {body : RawTerm (scope + 1)} (bodyNormalizing : IsStronglyNormalizing body) :
    IsStronglyNormalizing
      (.mkGen .gen_pathLam () (.childCons body .childNil) : RawTerm scope) :=
  pathLam_isStronglyNormalizing_of_body bodyNormalizing

/-- **The inert-eliminator coverage** — the typed-but-β/ι-inert elimination heads (today:
exactly `pathApp`, whose endpoint-ι is the recorded OP1-INT gap).  An inert eliminator's cells
are weak-head normal (no root rule exists), so the UNCONDITIONAL neutral lift covers them —
the honest contrast with the `.eliminator` role, whose coverage demands `hasRedexHead = true`.
When the endpoint-ι lands, `pathApp` migrates to `.eliminator` and this dispatch loses its
real arm (the enum breaks, by design). -/
theorem LiveGenerator.inertEliminatorCellHasGluedLift {scope : Nat} :
    (liveGenerator : LiveGenerator) →
      liveGenerator.sconingRole = .inertEliminator →
      ∀ (payload : (liveGenerator.generator).payload scope)
        (children : RawTermChildren (liveGenerator.generator).binderShifts scope),
        ∃ glued : GluedTypeCell scope,
          glued.typeCell = .mkGen liveGenerator.generator payload children
            ∧ glued.computable = IsStronglyNormalizing
  | .var, roleEq => nomatch roleEq
  | .unit, roleEq => nomatch roleEq
  | .lam, roleEq => nomatch roleEq
  | .app, roleEq => nomatch roleEq
  | .pair, roleEq => nomatch roleEq
  | .fst, roleEq => nomatch roleEq
  | .snd, roleEq => nomatch roleEq
  | .boolTrue, roleEq => nomatch roleEq
  | .boolFalse, roleEq => nomatch roleEq
  | .boolElim, roleEq => nomatch roleEq
  | .natZero, roleEq => nomatch roleEq
  | .natSucc, roleEq => nomatch roleEq
  | .natElim, roleEq => nomatch roleEq
  | .natRec, roleEq => nomatch roleEq
  | .listNil, roleEq => nomatch roleEq
  | .listCons, roleEq => nomatch roleEq
  | .listElim, roleEq => nomatch roleEq
  | .optionNone, roleEq => nomatch roleEq
  | .optionSome, roleEq => nomatch roleEq
  | .optionMatch, roleEq => nomatch roleEq
  | .eitherInl, roleEq => nomatch roleEq
  | .eitherInr, roleEq => nomatch roleEq
  | .eitherMatch, roleEq => nomatch roleEq
  | .refl, roleEq => nomatch roleEq
  | .idJ, roleEq => nomatch roleEq
  | .idStrictRec, roleEq => nomatch roleEq
  | .universeCode, roleEq => nomatch roleEq
  | .arrowCode, roleEq => nomatch roleEq
  | .piTyCode, roleEq => nomatch roleEq
  | .sigmaTyCode, roleEq => nomatch roleEq
  | .productCode, roleEq => nomatch roleEq
  | .sumCode, roleEq => nomatch roleEq
  | .listCode, roleEq => nomatch roleEq
  | .optionCode, roleEq => nomatch roleEq
  | .eitherCode, roleEq => nomatch roleEq
  | .equivCode, roleEq => nomatch roleEq
  | .emptyCode, roleEq => nomatch roleEq
  | .boolCode, roleEq => nomatch roleEq
  | .natCode, roleEq => nomatch roleEq
  | .unitCode, roleEq => nomatch roleEq
  | .intervalCode, roleEq => nomatch roleEq
  | .bridgeCode, roleEq => nomatch roleEq
  | .interval0, roleEq => nomatch roleEq
  | .interval1, roleEq => nomatch roleEq
  | .pathLam, roleEq => nomatch roleEq
  | .pathApp, _roleEq => fun payload children =>
      ⟨⟨.mkGen .gen_pathApp payload children, IsStronglyNormalizing,
        ReducibleType.neutral
          (fun _reduct weakHeadStep => by
            cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
          (fun absurdEq => nomatch absurdEq)⟩, rfl, rfl⟩

/-! ## The coverage carrier is EXACTLY the semantically-admissible set

The two directions together pin the reducibility/sconing coverage to the M30 admission
split: coverage is granted ONLY to semantically admissible generators (soundness — every
`LiveGenerator`, the carrier of every coverage dispatch above, is admissible), and EVERY
semantically admissible generator is covered (completeness — composing the M30 tier
bridge with the O-NORM admission gate `liveSignature_complete`).  Reserved names get no
reducibility story, and no admissible name is missing one. -/

/-- **Soundness**: every live-signature member is semantically admissible in the M30
split sense.  40 kernel evaluations of the admission classifier. -/
theorem LiveGenerator.memberIsSemanticallyAdmissible :
    ∀ liveGenerator : LiveGenerator, SemanticallyAdmissible liveGenerator.generator := by
  intro liveGenerator
  cases liveGenerator <;> rfl

/-- **Completeness**: every semantically admissible generator is in the live signature —
the reducibility-coverage carrier misses nothing admissible. -/
theorem liveSignatureMember_of_semanticallyAdmissible
    (generator : Generator) (semanticAdmission : SemanticallyAdmissible generator) :
    liveSignatureList.contains generator = true :=
  liveSignature_complete generator
    ((isSemanticallyAdmissible_iff_tierLive generator).mp semanticAdmission)

end FX1Poly.Typed
