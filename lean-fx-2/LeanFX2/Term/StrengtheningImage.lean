import LeanFX2.Term.PartialStrengthen.Weaken
import LeanFX2.Term.PartialStrengthen.RenameImage.TypeCodes
import LeanFX2.Term.PartialStrengthen.RenameImage.RefineSession
import LeanFX2.Term.PartialStrengthen.RenameImage.Equivalence
import LeanFX2.Term.PartialStrengthen.RenameImage.Cubical
import LeanFX2.Term.PartialStrengthen.RenameImage.CodataProjection
import LeanFX2.Term.PartialStrengthen.RenameImage.Effects
import LeanFX2.Term.PartialStrengthen.RenameImage.CastWrapped
import LeanFX2.Term.HEqCongr.Compound
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq
import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.Applications
import LeanFX2.Term.StrengtheningImage.EliminatorsAndModal
import LeanFX2.Term.StrengtheningImage.CollectionsSigmaInterval
import LeanFX2.Term.StrengtheningImage.TypeCodes
import LeanFX2.Term.StrengtheningImage.Reflexivity
import LeanFX2.Term.StrengtheningImage.MatcherSuccess
import LeanFX2.Term.StrengtheningImage.RefineRecordCodataSession
import LeanFX2.Term.StrengtheningImage.HoTTIntro
import LeanFX2.Term.StrengtheningImage.HoTTElimSuccess
import LeanFX2.Term.StrengtheningImage.Binders
import LeanFX2.Term.StrengtheningImage.CubicalTransport
import LeanFX2.Term.StrengtheningImage.CubicalComposition
import LeanFX2.Term.StrengtheningImage.EquivIntroAndEffects
import LeanFX2.Term.StrengtheningImage.MatcherWrappers
import LeanFX2.Term.StrengtheningImage.HoTTAppWrappers
import LeanFX2.Term.StrengtheningImage.DispatcherBasicCollections
import LeanFX2.Term.StrengtheningImage.DispatcherStructured
import LeanFX2.Term.StrengtheningImage.DispatcherEliminatorsApplications
import LeanFX2.Term.StrengtheningImage.DispatcherAtomicTypeCodes
import LeanFX2.Term.StrengtheningImage.DispatcherAdvanced
import LeanFX2.Term.StrengtheningImage.AggregatorSoundCore
import LeanFX2.Term.StrengtheningImage.AggregatorSoundUnary
import LeanFX2.Term.StrengtheningImage.AggregatorSoundStructured
import LeanFX2.Term.StrengtheningImage.AggregatorSoundEliminators
import LeanFX2.Term.StrengtheningImage.AggregatorSoundCubical
import LeanFX2.Term.StrengtheningImage.AggregatorSoundUniversal
import LeanFX2.Term.StrengtheningImage.AggregatorTotalCore
import LeanFX2.Term.StrengtheningImage.AggregatorTotalUnary
import LeanFX2.Term.StrengtheningImage.AggregatorTotalCodesRefl
import LeanFX2.Term.StrengtheningImage.AggregatorTotalStructured
import LeanFX2.Term.StrengtheningImage.AggregatorTotalWrapable
import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeShape
import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeHoTT
import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeAdvanced
import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeEliminators
import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeCasts
import LeanFX2.Term.StrengtheningImage.ImageCore
import LeanFX2.Term.StrengtheningImage.RenameImageAtomic
import LeanFX2.Term.StrengtheningImage.RenameImageUnary
import LeanFX2.Term.StrengtheningImage.RenameImageRecursive
import LeanFX2.Term.StrengtheningImage.RenameImageTypeCodes
import LeanFX2.Term.StrengtheningImage.RenameImageHoTTStructured
import LeanFX2.Term.StrengtheningImage.RenameImageCastWrapped
import LeanFX2.Term.StrengtheningImage.ImageUnweaken

/-! # Term/StrengtheningImage — soundness of typed strengthening.

`StrengtheningResult` records the index-level content of a successful
typed partial strengthening: the recovered target type/raw and the
forward-renaming equations for those indices.  This module adds the
term-level semantic content as a parallel certificate: successful
strengthening re-renames the recovered target term back to the original
source term.

The parallel record keeps the existing computational dispatcher stable.
Recursive constructor soundness lemmas can be added incrementally without
forcing every `StrengtheningResult` producer to grow a new field at once.
-/

namespace LeanFX2

namespace Term

/-! ## Closed-atomic unweaken? totality

The headline `Term.unweaken?_weaken : ∀ originalTerm newType,
  Term.unweaken? (Term.weaken newType originalTerm) = some originalTerm`
is the universal totality theorem on the weakening image.  A full
78-case structural induction proving it is mechanical — atomic ctors
reduce by `rfl`; recursive ctors compose via the per-ctor strengthening
builders and an `IsTotalOnWeaken` predicate.

This section ships the **closed-atomic foundation**: every ctor whose
typed `Term.weaken`-of-self reduces to a syntactic `Term.<ctor>` with
no per-ctor data carried at the surface (no element type, no codomain,
no payload).  Each such case is a one-line `rfl` because:

* `Term.weaken nt (Term.<ctor>) = Term.<ctor>` definitionally — `Term.rename`
  on a 0-arg ctor reduces directly.
* `partialStrengthenTyped? (Term.<ctor>)` is the dispatcher's closed-atomic
  arm, returning a concrete `StrengtheningResult` built from
  `partialStrengthenTyped<Ctor>` whose body is trivial.
* `unweaken?` matches that success and the type/raw alignment via
  `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken` resolves to
  `Term.<ctor>` again.

The 7 ctors covered: `Term.unit`, `Term.boolTrue`, `Term.boolFalse`,
`Term.natZero`, `Term.interval0`, `Term.interval1`, plus `Term.var`
whose `Fin.succ position` shape exhibits the same structural success.

Each theorem here is a CONCRETE totality witness — not a universal
headline — and is consumable directly by Step.eta-cascade subject
reduction proofs whose source-side term is one of these atomic
constructors.  The remaining 71 recursive ctors land in follow-up
phases using the `IsTotalOnWeaken` predicate (Term-level totality
counterpart to `RawTerm.usesNewestSlot?` at the raw layer). -/

/-- Total-on-weaken predicate: a typed term whose weakening under any
new binder allows the typed strengthening dispatcher to succeed.  The
universal headline `∀ sourceTerm, IsTotalOnWeaken sourceTerm` is
provable by structural induction with 78 per-ctor cases; this file
ships the predicate plus the closed-atomic base cases. -/
def IsTotalOnWeaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw) : Prop :=
  ∀ (newType : Ty level scope),
    (strengthenTyped? (Term.weaken newType sourceTerm)).isSome

/-- Cast-invariance helper: `strengthenTyped?.isSome` is invariant under
a propositional cast on the Term's `Ty` index.

This is the load-bearing helper for totality proofs of the 7
Eq.mpr-blocked ctors (appPi, snd, pair, boolElim, funextRefl,
equivIntroHet, oeqFunext): their `Term.weaken` arm produces a term
wrapped in `Eq.mpr h _` due to `Ty.subst0_rename_commute.symm ▸ ...`,
which blocks pattern-matching in the strengthening dispatcher.  This
lemma reduces the cast term's `.isSome` to the un-cast form by
discharging the equation via `cases h`.

The motive is implicit: `fun (T : Ty level (scope+1)) => Term ctx T R`
where `R` is fixed (since `weaken`'s raw-side computation has no cast). -/
theorem strengthenTyped?_isSome_castInvariant
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceTypeA sourceTypeB : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceTypeA sourceRaw)
    (typeEq : sourceTypeA = sourceTypeB) :
    (typeEq ▸ sourceTerm).strengthenTyped?.isSome =
      sourceTerm.strengthenTyped?.isSome := by
  cases typeEq
  rfl

/-- Closed-atomic totality: `Term.unit` strengthens through any
weakening.  Direct `rfl`-witness. -/
theorem isTotalOnWeaken_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.unit (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.boolTrue`. -/
theorem isTotalOnWeaken_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.boolTrue (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.boolFalse`. -/
theorem isTotalOnWeaken_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.boolFalse (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.natZero`. -/
theorem isTotalOnWeaken_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.natZero (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.interval0`. -/
theorem isTotalOnWeaken_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.interval0 (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.interval1`. -/
theorem isTotalOnWeaken_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.interval1 (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.var`.  The variable's renaming under
weakening lands at `Fin.succ position` which survives `dropNewest`
back to `position`. -/
theorem isTotalOnWeaken_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} (position : Fin scope) :
    IsTotalOnWeaken (Term.var (context := context) position) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.universeCode`.  The universe-code
ctor carries pure value-level data (`innerLevel`, `outerLevel`,
`cumulOk`, `levelLe`) — no scope-indexed payload to strengthen, so the
dispatcher's arm succeeds unconditionally and totality is direct. -/
theorem isTotalOnWeaken_universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsTotalOnWeaken (Term.universeCode (context := context) innerLevel
      outerLevel cumulOk levelLe) := by
  intro _; rfl

/-- 1-IH non-binder totality: `Term.natSucc` is total on weaken if its
predecessor is.  Composition pattern shipped here as the canonical
template; the remaining 14 single-IH non-binder ctors (optionSome,
modIntro/Elim, subsume, eitherInl/Inr, recordIntro/Proj, refineElim,
fst, snd, intervalOpp, codataDest, sessionRecv) follow the same
unfold + split + ▸ pattern, landing per follow-up. -/
theorem isTotalOnWeaken_natSucc {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    (predecessorIH : IsTotalOnWeaken predecessor) :
    IsTotalOnWeaken (Term.natSucc predecessor) := by
  intro newType
  show (strengthenTyped? (Term.natSucc (Term.weaken newType predecessor))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next predRecurse =>
      exfalso
      have totHyp := predecessorIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType predecessor))) = true :=
        predRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.intervalOpp`.  Cubical interval
negation; sibling of `natSucc` at a different carrier type. -/
theorem isTotalOnWeaken_intervalOpp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {pointRaw : RawTerm scope}
    {point : Term context Ty.interval pointRaw}
    (pointIH : IsTotalOnWeaken point) :
    IsTotalOnWeaken (Term.intervalOpp point) := by
  intro newType
  show (strengthenTyped? (Term.intervalOpp (Term.weaken newType point))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next pointRecurse =>
      exfalso
      have totHyp := pointIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType point))) = true :=
        pointRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.optionSome`.  Option-some carries
exactly one typed payload (the wrapped value); no Ty payload to
strengthen separately. -/
theorem isTotalOnWeaken_optionSome {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.optionSome valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.optionSome (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next valueRecurse =>
      exfalso
      have totHyp := valueIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType valueTerm))) = true :=
        valueRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.modIntro`.  Modal introduction;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_modIntro {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.modIntro innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.modIntro (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.modElim`.  Modal elimination;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_modElim {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.modElim innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.modElim (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.subsume`.  Mode subsumption;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_subsume {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.subsume innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.subsume (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.cumulUp`.  Cross-level cumulativity;
carries exactly one typed payload (the source type code).  No Ty payload
to strengthen separately — the universe levels are pure Nat data. -/
theorem isTotalOnWeaken_cumulUp {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeIH : IsTotalOnWeaken typeCode) :
    IsTotalOnWeaken (Term.cumulUp lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh typeCode) := by
  intro newType
  show (strengthenTyped? (Term.cumulUp lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh (Term.weaken newType typeCode))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next codeRecurse =>
      exfalso
      have totHyp := codeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType typeCode))) = true :=
        codeRecurse ▸ totHyp
      cases this
  · rfl

/-! ## Wave A: parametric atomic 0-IH totality

These ctors have no Term IH but carry one or more `Ty`/`RawTerm`
sub-payloads whose strengthening succeeds via `Ty.strengthen?_weaken`
or `RawTerm.strengthen?_weaken`.  The dispatcher's arm tests
`payload.partialStrengthen? strengthening.back`; under
`ContextStrengthening.dropNewest`, that is exactly `payload.weaken.strengthen?`
which always returns `some payload`.

Each proof follows the same shape: unfold the dispatcher, split on
the payload-strengthen success (the only `none` branch is impossible
because the payload here is `payload.weaken`), and discharge with
`rfl` after the success branch reduces. -/

/-- 0-IH parametric atomic totality: `Term.listNil`.  Element type
strengthens via `Ty.strengthen?_weaken`. -/
theorem isTotalOnWeaken_listNil {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    IsTotalOnWeaken (Term.listNil (context := context)
      (elementType := elementType)) := by
  intro newType
  show (strengthenTyped? (Term.listNil (context := context.cons newType)
      (elementType := elementType.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.optionNone`. -/
theorem isTotalOnWeaken_optionNone {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    IsTotalOnWeaken (Term.optionNone (context := context)
      (elementType := elementType)) := by
  intro newType
  show (strengthenTyped? (Term.optionNone (context := context.cons newType)
      (elementType := elementType.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.refl`.  Carries an explicit
Ty carrier + a raw witness, both at the outer scope.  Both strengthen
via `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken`. -/
theorem isTotalOnWeaken_refl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    IsTotalOnWeaken (Term.refl (context := context) carrier rawWitness) := by
  intro newType
  show (strengthenTyped? (Term.refl (context := context.cons newType)
      (carrier.weaken) (rawWitness.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next witnessFails =>
        exfalso
        have witnessSuccess :
            rawWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rawWitness :=
          RawTerm.strengthen?_weaken rawWitness
        rw [witnessSuccess] at witnessFails
        cases witnessFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.oeqRefl`.  Same shape as
`refl` — carrier (Ty) + rawWitness (RawTerm). -/
theorem isTotalOnWeaken_oeqRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    IsTotalOnWeaken (Term.oeqRefl (context := context) carrier rawWitness) := by
  intro newType
  show (strengthenTyped? (Term.oeqRefl (context := context.cons newType)
      (carrier.weaken) (rawWitness.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next witnessFails =>
        exfalso
        have witnessSuccess :
            rawWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rawWitness :=
          RawTerm.strengthen?_weaken rawWitness
        rw [witnessSuccess] at witnessFails
        cases witnessFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.idStrictRefl`.  Same shape
as `refl` plus a `modeIsStrict` value-level parameter. -/
theorem isTotalOnWeaken_idStrictRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    IsTotalOnWeaken (Term.idStrictRefl (context := context)
      modeIsStrict carrier rawWitness) := by
  intro newType
  show (strengthenTyped? (Term.idStrictRefl
      (context := context.cons newType) modeIsStrict
      (carrier.weaken) (rawWitness.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next witnessFails =>
        exfalso
        have witnessSuccess :
            rawWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rawWitness :=
          RawTerm.strengthen?_weaken rawWitness
        rw [witnessSuccess] at witnessFails
        cases witnessFails
    · rfl

/-! ## Wave B: 1-IH non-binder totality (single Term recursion).

These ctors combine one Term IH with zero or more Ty/RawTerm
sub-payloads.  Each proof: split first on the payload-strengthen
successes (discharge `none` impossibilities via
`Ty.strengthen?_weaken`/`RawTerm.strengthen?_weaken`), then on the
recursive Term success (discharge `none` via the IH), then close
with `rfl`. -/

/-- 1-IH non-binder totality: `Term.recordIntro`.  Pure 1-IH ctor
(no extra Ty/RawTerm payload).  Same template as `natSucc`. -/
theorem isTotalOnWeaken_recordIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (fieldIH : IsTotalOnWeaken firstField) :
    IsTotalOnWeaken (Term.recordIntro firstField) := by
  intro newType
  show (strengthenTyped? (Term.recordIntro (Term.weaken newType
      firstField))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next fieldRecurse =>
      exfalso
      have totHyp := fieldIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType firstField))) = true :=
        fieldRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.recordProj`.  Carries one Ty
payload (singleFieldType) + one Term IH. -/
theorem isTotalOnWeaken_recordProj {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIH : IsTotalOnWeaken recordValue) :
    IsTotalOnWeaken (Term.recordProj recordValue) := by
  intro newType
  show (strengthenTyped? (Term.recordProj (Term.weaken newType
      recordValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next fieldFails =>
      exfalso
      have fieldSuccess :
          singleFieldType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some singleFieldType :=
        Ty.strengthen?_weaken singleFieldType
      rw [fieldSuccess] at fieldFails
      cases fieldFails
  · split
    · next recordRecurse =>
        exfalso
        have totHyp := recordIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType recordValue))) = true :=
          recordRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.eitherInl`.  Carries one Ty
payload (rightType) + one Term IH. -/
theorem isTotalOnWeaken_eitherInl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context leftType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.eitherInl (rightType := rightType) valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.eitherInl
      (rightType := rightType.weaken)
      (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next rightFails =>
      exfalso
      have rightSuccess :
          rightType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some rightType :=
        Ty.strengthen?_weaken rightType
      rw [rightSuccess] at rightFails
      cases rightFails
  · split
    · next valueRecurse =>
        exfalso
        have totHyp := valueIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType valueTerm))) = true :=
          valueRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.eitherInr`.  Carries one Ty
payload (leftType) + one Term IH. -/
theorem isTotalOnWeaken_eitherInr {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context rightType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.eitherInr (leftType := leftType) valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.eitherInr
      (leftType := leftType.weaken)
      (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftType :=
        Ty.strengthen?_weaken leftType
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next valueRecurse =>
        exfalso
        have totHyp := valueIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType valueTerm))) = true :=
          valueRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.sessionRecv`.  Carries one RawTerm
payload (protocolStep) + one Term IH. -/
theorem isTotalOnWeaken_sessionRecv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term context (Ty.session protocolStep) channelRaw}
    (channelIH : IsTotalOnWeaken channel) :
    IsTotalOnWeaken (Term.sessionRecv channel) := by
  intro newType
  show (strengthenTyped? (Term.sessionRecv (Term.weaken newType
      channel))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next protocolFails =>
      exfalso
      have protocolSuccess :
          protocolStep.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some protocolStep :=
        RawTerm.strengthen?_weaken protocolStep
      rw [protocolSuccess] at protocolFails
      cases protocolFails
  · split
    · next channelRecurse =>
        exfalso
        have totHyp := channelIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType channel))) = true :=
          channelRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.codataDest`.  Carries two Ty
payloads (stateType, outputType) + one Term IH. -/
theorem isTotalOnWeaken_codataDest {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue : Term context (Ty.codata stateType outputType) codataRaw}
    (codataIH : IsTotalOnWeaken codataValue) :
    IsTotalOnWeaken (Term.codataDest codataValue) := by
  intro newType
  show (strengthenTyped? (Term.codataDest (Term.weaken newType
      codataValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next stateFails =>
      exfalso
      have stateSuccess :
          stateType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some stateType :=
        Ty.strengthen?_weaken stateType
      rw [stateSuccess] at stateFails
      cases stateFails
  · split
    · next outputFails =>
        exfalso
        have outputSuccess :
            outputType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some outputType :=
          Ty.strengthen?_weaken outputType
        rw [outputSuccess] at outputFails
        cases outputFails
    · split
      · next codataRecurse =>
          exfalso
          have totHyp := codataIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType codataValue))) = true :=
            codataRecurse ▸ totHyp
          cases this
      · rfl

/-! ## Wave C: 2-IH and 3-IH non-binder totality. -/

/-- 2-IH non-binder totality: `Term.listCons`.  Pure 2-IH ctor — no
extra Ty/RawTerm payloads. -/
theorem isTotalOnWeaken_listCons {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term context elementType headRaw}
    {tailTerm : Term context (Ty.listType elementType) tailRaw}
    (headIH : IsTotalOnWeaken headTerm)
    (tailIH : IsTotalOnWeaken tailTerm) :
    IsTotalOnWeaken (Term.listCons headTerm tailTerm) := by
  intro newType
  show (strengthenTyped? (Term.listCons (Term.weaken newType headTerm)
      (Term.weaken newType tailTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next headRecurse =>
      exfalso
      have totHyp := headIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType headTerm))) = true :=
        headRecurse ▸ totHyp
      cases this
  · split
    · next tailRecurse =>
        exfalso
        have totHyp := tailIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType tailTerm))) = true :=
          tailRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.intervalMeet`.  Pure 2-IH cubical
interval meet operator. -/
theorem isTotalOnWeaken_intervalMeet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftIH : IsTotalOnWeaken leftValue)
    (rightIH : IsTotalOnWeaken rightValue) :
    IsTotalOnWeaken (Term.intervalMeet leftValue rightValue) := by
  intro newType
  show (strengthenTyped? (Term.intervalMeet
      (Term.weaken newType leftValue)
      (Term.weaken newType rightValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftRecurse =>
      exfalso
      have totHyp := leftIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType leftValue))) = true :=
        leftRecurse ▸ totHyp
      cases this
  · split
    · next rightRecurse =>
        exfalso
        have totHyp := rightIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType rightValue))) = true :=
          rightRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.intervalJoin`.  Pure 2-IH cubical
interval join operator. -/
theorem isTotalOnWeaken_intervalJoin {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftIH : IsTotalOnWeaken leftValue)
    (rightIH : IsTotalOnWeaken rightValue) :
    IsTotalOnWeaken (Term.intervalJoin leftValue rightValue) := by
  intro newType
  show (strengthenTyped? (Term.intervalJoin
      (Term.weaken newType leftValue)
      (Term.weaken newType rightValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftRecurse =>
      exfalso
      have totHyp := leftIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType leftValue))) = true :=
        leftRecurse ▸ totHyp
      cases this
  · split
    · next rightRecurse =>
        exfalso
        have totHyp := rightIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType rightValue))) = true :=
          rightRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.app`.  Carries two Ty payloads
(domainType, codomainType) + two Term IH (function, argument). -/
theorem isTotalOnWeaken_app {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.arrow domainType codomainType)
      functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIH : IsTotalOnWeaken functionTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.app functionTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.app (Term.weaken newType functionTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next functionRecurse =>
          exfalso
          have totHyp := functionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType functionTerm))) = true :=
            functionRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.codataUnfold`.  One Ty (outputType)
+ two Term IH (initialState, transition).  Note: the dispatcher
strengthens only outputType (stateType is inferred from the IH). -/
theorem isTotalOnWeaken_codataUnfold {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term context stateType stateRaw}
    {transition : Term context (Ty.arrow stateType outputType)
      transitionRaw}
    (stateIH : IsTotalOnWeaken initialState)
    (transitionIH : IsTotalOnWeaken transition) :
    IsTotalOnWeaken (Term.codataUnfold initialState transition) := by
  intro newType
  show (strengthenTyped? (Term.codataUnfold
      (Term.weaken newType initialState)
      (Term.weaken newType transition))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next outputFails =>
      exfalso
      have outputSuccess :
          outputType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some outputType :=
        Ty.strengthen?_weaken outputType
      rw [outputSuccess] at outputFails
      cases outputFails
  · split
    · next stateRecurse =>
        exfalso
        have totHyp := stateIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType initialState))) = true :=
          stateRecurse ▸ totHyp
        cases this
    · split
      · next transitionRecurse =>
          exfalso
          have totHyp := transitionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType transition))) = true :=
            transitionRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.sessionSend`.  One RawTerm
(protocolStep) + one Ty (payloadType) + two Term IH. -/
theorem isTotalOnWeaken_sessionSend {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term context (Ty.session protocolStep) channelRaw}
    {payload : Term context payloadType payloadRaw}
    (channelIH : IsTotalOnWeaken channel)
    (payloadIH : IsTotalOnWeaken payload) :
    IsTotalOnWeaken (Term.sessionSend protocolStep channel payload) := by
  intro newType
  show (strengthenTyped? (Term.sessionSend protocolStep.weaken
      (Term.weaken newType channel)
      (Term.weaken newType payload))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next protocolFails =>
      exfalso
      have protocolSuccess :
          protocolStep.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some protocolStep :=
        RawTerm.strengthen?_weaken protocolStep
      rw [protocolSuccess] at protocolFails
      cases protocolFails
  · split
    · next channelRecurse =>
        exfalso
        have totHyp := channelIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType channel))) = true :=
          channelRecurse ▸ totHyp
        cases this
    · split
      · next payloadRecurse =>
          exfalso
          have totHyp := payloadIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType payload))) = true :=
            payloadRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.equivApp`.  Two Ty payloads
(carrierA, carrierB) + two Term IH (equiv, argument). -/
theorem isTotalOnWeaken_equivApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIH : IsTotalOnWeaken equivTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.equivApp equivTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.equivApp
      (Term.weaken newType equivTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next equivRecurse =>
          exfalso
          have totHyp := equivIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType equivTerm))) = true :=
            equivRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.equivApply`.  Same shape as
`equivApp` — two Ty payloads + two Term IH. -/
theorem isTotalOnWeaken_equivApply {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIH : IsTotalOnWeaken equivTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.equivApply equivTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.equivApply
      (Term.weaken newType equivTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next equivRecurse =>
          exfalso
          have totHyp := equivIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType equivTerm))) = true :=
            equivRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.idJ`.  One Ty (carrier) + two
RawTerm (leftEndpoint, rightEndpoint) + two Term IH (baseCase,
witness). -/
theorem isTotalOnWeaken_idJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.idJ baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.idJ (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.oeqJ`.  Same shape as `idJ`. -/
theorem isTotalOnWeaken_oeqJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.oeqJ baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.oeqJ (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.idStrictRec`.  Same shape as `idJ`
plus a `modeIsStrict` value-level parameter. -/
theorem isTotalOnWeaken_idStrictRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context
      (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.idStrictRec modeIsStrict baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.idStrictRec modeIsStrict
      (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-! ## Wave D: cubical / HoTT non-binder totality. -/

/-- 0-IH parametric atomic totality: `Term.equivReflId`.  One Ty
sub-payload (carrier), no Term IH. -/
theorem isTotalOnWeaken_equivReflId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) :
    IsTotalOnWeaken (Term.equivReflId (context := context) carrier) := by
  intro newType
  show (strengthenTyped? (Term.equivReflId
      (context := context.cons newType) carrier.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.equivReflIdAtId`.  One Ty
+ one RawTerm sub-payload, no Term IH. -/
theorem isTotalOnWeaken_equivReflIdAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.equivReflIdAtId (context := context)
      innerLevel innerLevelLt carrier carrierRaw) := by
  intro newType
  show (strengthenTyped? (Term.equivReflIdAtId
      (context := context.cons newType) innerLevel innerLevelLt
      carrier.weaken carrierRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next carrierRawFails =>
        exfalso
        have carrierRawSuccess :
            carrierRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierRaw :=
          RawTerm.strengthen?_weaken carrierRaw
        rw [carrierRawSuccess] at carrierRawFails
        cases carrierRawFails
    · rfl

/-- 1-IH non-binder totality: `Term.glueElim`.  One Ty (baseType) +
one RawTerm (boundaryWitness) + one Term IH (gluedValue). -/
theorem isTotalOnWeaken_glueElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIH : IsTotalOnWeaken gluedValue) :
    IsTotalOnWeaken (Term.glueElim modeIsUnivalent gluedValue) := by
  intro newType
  show (strengthenTyped? (Term.glueElim modeIsUnivalent
      (Term.weaken newType gluedValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next boundaryFails =>
        exfalso
        have boundarySuccess :
            boundaryWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some boundaryWitness :=
          RawTerm.strengthen?_weaken boundaryWitness
        rw [boundarySuccess] at boundaryFails
        cases boundaryFails
    · split
      · next gluedRecurse =>
          exfalso
          have totHyp := gluedIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType gluedValue))) = true :=
            gluedRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.hcomp`.  No Ty payloads in the
dispatcher arm — purely 2-IH. -/
theorem isTotalOnWeaken_hcomp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIH : IsTotalOnWeaken sidesValue)
    (capIH : IsTotalOnWeaken capValue) :
    IsTotalOnWeaken (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  intro newType
  show (strengthenTyped? (Term.hcomp modeIsUnivalent
      (Term.weaken newType sidesValue)
      (Term.weaken newType capValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next sidesRecurse =>
      exfalso
      have totHyp := sidesIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType sidesValue))) = true :=
        sidesRecurse ▸ totHyp
      cases this
  · split
    · next capRecurse =>
        exfalso
        have totHyp := capIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType capValue))) = true :=
          capRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.glueIntro`.  One Ty (baseType) +
one RawTerm (boundaryWitness) + two Term IH (baseValue, partialValue). -/
theorem isTotalOnWeaken_glueIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIH : IsTotalOnWeaken baseValue)
    (partialIH : IsTotalOnWeaken partialValue) :
    IsTotalOnWeaken (Term.glueIntro modeIsUnivalent baseType
      boundaryWitness baseValue partialValue) := by
  intro newType
  show (strengthenTyped? (Term.glueIntro modeIsUnivalent
      baseType.weaken boundaryWitness.weaken
      (Term.weaken newType baseValue)
      (Term.weaken newType partialValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next boundaryFails =>
        exfalso
        have boundarySuccess :
            boundaryWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some boundaryWitness :=
          RawTerm.strengthen?_weaken boundaryWitness
        rw [boundarySuccess] at boundaryFails
        cases boundaryFails
    · split
      · next baseRecurse =>
          exfalso
          have totHyp := baseIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType baseValue))) = true :=
            baseRecurse ▸ totHyp
          cases this
      · split
        · next partialRecurse =>
            exfalso
            have totHyp := partialIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType partialValue))) = true :=
              partialRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.transp`.  Two Ty (sourceType,
targetType) + two RawTerm (sourceTypeRaw, targetTypeRaw) + two Term
IH (typePath, sourceValue). -/
theorem isTotalOnWeaken_transp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIH : IsTotalOnWeaken typePath)
    (sourceIH : IsTotalOnWeaken sourceValue) :
    IsTotalOnWeaken (Term.transp modeIsUnivalent universeLevel
      universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
      typePath sourceValue) := by
  intro newType
  show (strengthenTyped? (Term.transp modeIsUnivalent universeLevel
      universeLevelLt sourceType.weaken targetType.weaken
      sourceTypeRaw.weaken targetTypeRaw.weaken
      (Term.weaken newType typePath)
      (Term.weaken newType sourceValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next sourceTypeFails =>
      exfalso
      have sourceTypeSuccess :
          sourceType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some sourceType :=
        Ty.strengthen?_weaken sourceType
      rw [sourceTypeSuccess] at sourceTypeFails
      cases sourceTypeFails
  · split
    · next targetTypeFails =>
        exfalso
        have targetTypeSuccess :
            targetType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some targetType :=
          Ty.strengthen?_weaken targetType
        rw [targetTypeSuccess] at targetTypeFails
        cases targetTypeFails
    · split
      · next sourceRawFails =>
          exfalso
          have sourceRawSuccess :
              sourceTypeRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some sourceTypeRaw :=
            RawTerm.strengthen?_weaken sourceTypeRaw
          rw [sourceRawSuccess] at sourceRawFails
          cases sourceRawFails
      · split
        · next targetRawFails =>
            exfalso
            have targetRawSuccess :
                targetTypeRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some targetTypeRaw :=
              RawTerm.strengthen?_weaken targetTypeRaw
            rw [targetRawSuccess] at targetRawFails
            cases targetRawFails
        · split
          · next pathRecurse =>
              exfalso
              have totHyp := pathIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType typePath))) = true :=
                pathRecurse ▸ totHyp
              cases this
          · split
            · next sourceRecurse =>
                exfalso
                have totHyp := sourceIH newType
                unfold strengthenTyped? at totHyp
                have : Option.isSome (none (α := StrengtheningResult
                    (ContextStrengthening.dropNewest context newType)
                    (Term.weaken newType sourceValue))) = true :=
                  sourceRecurse ▸ totHyp
                cases this
            · rfl

/-- 1-IH non-binder totality: `Term.uaToEquiv`.  Two Ty (leftTy,
rightTy) + two RawTerm (leftTyRaw, rightTyRaw) + one Term IH (proof). -/
theorem isTotalOnWeaken_uaToEquiv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    {proof : Term context
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                     leftTyRaw rightTyRaw)
              proofRaw}
    (proofIH : IsTotalOnWeaken proof) :
    IsTotalOnWeaken (Term.uaToEquiv innerLevel innerLevelLt leftTy
      rightTy leftTyRaw rightTyRaw proof) := by
  intro newType
  show (strengthenTyped? (Term.uaToEquiv innerLevel innerLevelLt
      leftTy.weaken rightTy.weaken
      leftTyRaw.weaken rightTyRaw.weaken
      (Term.weaken newType proof))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftTyFails =>
      exfalso
      have leftTySuccess :
          leftTy.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftTy :=
        Ty.strengthen?_weaken leftTy
      rw [leftTySuccess] at leftTyFails
      cases leftTyFails
  · split
    · next rightTyFails =>
        exfalso
        have rightTySuccess :
            rightTy.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightTy :=
          Ty.strengthen?_weaken rightTy
        rw [rightTySuccess] at rightTyFails
        cases rightTyFails
    · split
      · next leftRawFails =>
          exfalso
          have leftRawSuccess :
              leftTyRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some leftTyRaw :=
            RawTerm.strengthen?_weaken leftTyRaw
          rw [leftRawSuccess] at leftRawFails
          cases leftRawFails
      · split
        · next rightRawFails =>
            exfalso
            have rightRawSuccess :
                rightTyRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some rightTyRaw :=
              RawTerm.strengthen?_weaken rightTyRaw
            rw [rightRawSuccess] at rightRawFails
            cases rightRawFails
        · split
          · next proofRecurse =>
              exfalso
              have totHyp := proofIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType proof))) = true :=
                proofRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.pathApp`.  One Ty (carrierType)
+ two RawTerm (leftEndpoint, rightEndpoint) + two Term IH (pathTerm,
intervalTerm). -/
theorem isTotalOnWeaken_pathApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm : Term context
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (pathIH : IsTotalOnWeaken pathTerm)
    (intervalIH : IsTotalOnWeaken intervalTerm) :
    IsTotalOnWeaken (Term.pathApp modeIsUnivalent pathTerm
      intervalTerm) := by
  intro newType
  show (strengthenTyped? (Term.pathApp modeIsUnivalent
      (Term.weaken newType pathTerm)
      (Term.weaken newType intervalTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrierType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierType :=
        Ty.strengthen?_weaken carrierType
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next pathRecurse =>
            exfalso
            have totHyp := pathIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType pathTerm))) = true :=
              pathRecurse ▸ totHyp
            cases this
        · split
          · next intervalRecurse =>
              exfalso
              have totHyp := intervalIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType intervalTerm))) = true :=
                intervalRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.hcompPath`.  One Ty (carrierType)
+ two RawTerm (leftEndpoint, rightEndpoint) + two Term IH (sidesPath,
capValue). -/
theorem isTotalOnWeaken_hcompPath {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (leftEndpoint rightEndpoint : RawTerm scope)
    {sidesPathRaw capRaw : RawTerm scope}
    {sidesPath :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIH : IsTotalOnWeaken sidesPath)
    (capIH : IsTotalOnWeaken capValue) :
    IsTotalOnWeaken (Term.hcompPath modeIsUnivalent leftEndpoint
      rightEndpoint sidesPath capValue) := by
  intro newType
  show (strengthenTyped? (Term.hcompPath modeIsUnivalent
      leftEndpoint.weaken rightEndpoint.weaken
      (Term.weaken newType sidesPath)
      (Term.weaken newType capValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrierType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierType :=
        Ty.strengthen?_weaken carrierType
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next sidesRecurse =>
            exfalso
            have totHyp := sidesIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType sidesPath))) = true :=
              sidesRecurse ▸ totHyp
            cases this
        · split
          · next capRecurse =>
              exfalso
              have totHyp := capIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType capValue))) = true :=
                capRecurse ▸ totHyp
              cases this
          · rfl

/-- 1-IH non-binder totality: `Term.uaIntroHet`.  Two implicit Ty
(carrierA, carrierB) + two RawTerm (carrierARaw, carrierBRaw) +
one Term IH (equivWitness).  Dispatcher chains 6 successes (2 Ty
implicit + 4 RawTerm) before the IH split. -/
theorem isTotalOnWeaken_uaIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    {equivWitness : Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivIH : IsTotalOnWeaken equivWitness) :
    IsTotalOnWeaken (Term.uaIntroHet innerLevel innerLevelLt
      carrierARaw carrierBRaw equivWitness) := by
  intro newType
  show (strengthenTyped? (Term.uaIntroHet innerLevel innerLevelLt
      carrierARaw.weaken carrierBRaw.weaken
      (Term.weaken newType equivWitness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next carrierARawFails =>
          exfalso
          have carrierARawSuccess :
              carrierARaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some carrierARaw :=
            RawTerm.strengthen?_weaken carrierARaw
          rw [carrierARawSuccess] at carrierARawFails
          cases carrierARawFails
      · split
        · next carrierBRawFails =>
            exfalso
            have carrierBRawSuccess :
                carrierBRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some carrierBRaw :=
              RawTerm.strengthen?_weaken carrierBRaw
            rw [carrierBRawSuccess] at carrierBRawFails
            cases carrierBRawFails
        · split
          · next forwardRawFails =>
              exfalso
              have forwardRawSuccess :
                  forwardRaw.weaken.partialStrengthen?
                      (ContextStrengthening.dropNewest context newType).back =
                    some forwardRaw :=
                RawTerm.strengthen?_weaken forwardRaw
              rw [forwardRawSuccess] at forwardRawFails
              cases forwardRawFails
          · split
            · next backwardRawFails =>
                exfalso
                have backwardRawSuccess :
                    backwardRaw.weaken.partialStrengthen?
                        (ContextStrengthening.dropNewest context newType).back =
                      some backwardRaw :=
                  RawTerm.strengthen?_weaken backwardRaw
                rw [backwardRawSuccess] at backwardRawFails
                cases backwardRawFails
            · split
              · next equivRecurse =>
                  exfalso
                  have totHyp := equivIH newType
                  unfold strengthenTyped? at totHyp
                  have : Option.isSome (none (α := StrengtheningResult
                      (ContextStrengthening.dropNewest context newType)
                      (Term.weaken newType equivWitness))) = true :=
                    equivRecurse ▸ totHyp
                  cases this
              · rfl

/-- 3-IH non-binder totality: `Term.natElim`.  Pure 3-IH (no Ty
payload in dispatcher arm). -/
theorem isTotalOnWeaken_natElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (zeroIH : IsTotalOnWeaken zeroBranch)
    (succIH : IsTotalOnWeaken succBranch) :
    IsTotalOnWeaken (Term.natElim scrutinee zeroBranch succBranch) := by
  intro newType
  show (strengthenTyped? (Term.natElim
      (Term.weaken newType scrutinee)
      (Term.weaken newType zeroBranch)
      (Term.weaken newType succBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next scrutineeRecurse =>
      exfalso
      have totHyp := scrutineeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType scrutinee))) = true :=
        scrutineeRecurse ▸ totHyp
      cases this
  · split
    · next zeroRecurse =>
        exfalso
        have totHyp := zeroIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType zeroBranch))) = true :=
          zeroRecurse ▸ totHyp
        cases this
    · split
      · next succRecurse =>
          exfalso
          have totHyp := succIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType succBranch))) = true :=
            succRecurse ▸ totHyp
          cases this
      · rfl

/-- 3-IH non-binder totality: `Term.natRec`.  Pure 3-IH (no Ty
payload in dispatcher arm). -/
theorem isTotalOnWeaken_natRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context
      (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (zeroIH : IsTotalOnWeaken zeroBranch)
    (succIH : IsTotalOnWeaken succBranch) :
    IsTotalOnWeaken (Term.natRec scrutinee zeroBranch succBranch) := by
  intro newType
  show (strengthenTyped? (Term.natRec
      (Term.weaken newType scrutinee)
      (Term.weaken newType zeroBranch)
      (Term.weaken newType succBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next scrutineeRecurse =>
      exfalso
      have totHyp := scrutineeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType scrutinee))) = true :=
        scrutineeRecurse ▸ totHyp
      cases this
  · split
    · next zeroRecurse =>
        exfalso
        have totHyp := zeroIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType zeroBranch))) = true :=
          zeroRecurse ▸ totHyp
        cases this
    · split
      · next succRecurse =>
          exfalso
          have totHyp := succIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType succBranch))) = true :=
            succRecurse ▸ totHyp
          cases this
      · rfl

/-- 3-IH non-binder totality: `Term.listElim`.  One Ty (elementType)
+ 3 Term IH (scrutinee, nilBranch, consBranch). -/
theorem isTotalOnWeaken_listElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context
      (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (nilIH : IsTotalOnWeaken nilBranch)
    (consIH : IsTotalOnWeaken consBranch) :
    IsTotalOnWeaken (Term.listElim scrutinee nilBranch consBranch) := by
  intro newType
  show (strengthenTyped? (Term.listElim
      (Term.weaken newType scrutinee)
      (Term.weaken newType nilBranch)
      (Term.weaken newType consBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next nilRecurse =>
          exfalso
          have totHyp := nilIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType nilBranch))) = true :=
            nilRecurse ▸ totHyp
          cases this
      · split
        · next consRecurse =>
            exfalso
            have totHyp := consIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType consBranch))) = true :=
              consRecurse ▸ totHyp
            cases this
        · rfl

/-- 3-IH non-binder totality: `Term.optionMatch`.  One Ty (elementType)
+ 3 Term IH (scrutinee, noneBranch, someBranch). -/
theorem isTotalOnWeaken_optionMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (noneIH : IsTotalOnWeaken noneBranch)
    (someIH : IsTotalOnWeaken someBranch) :
    IsTotalOnWeaken (Term.optionMatch scrutinee noneBranch someBranch) := by
  intro newType
  show (strengthenTyped? (Term.optionMatch
      (Term.weaken newType scrutinee)
      (Term.weaken newType noneBranch)
      (Term.weaken newType someBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next noneRecurse =>
          exfalso
          have totHyp := noneIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType noneBranch))) = true :=
            noneRecurse ▸ totHyp
          cases this
      · split
        · next someRecurse =>
            exfalso
            have totHyp := someIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType someBranch))) = true :=
              someRecurse ▸ totHyp
            cases this
        · rfl

/-- 3-IH non-binder totality: `Term.eitherMatch`.  Three Ty (leftType,
rightType, motiveType) + 3 Term IH. -/
theorem isTotalOnWeaken_eitherMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee : Term context (Ty.eitherType leftType rightType)
      scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (leftIH : IsTotalOnWeaken leftBranch)
    (rightIH : IsTotalOnWeaken rightBranch) :
    IsTotalOnWeaken (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  intro newType
  show (strengthenTyped? (Term.eitherMatch
      (Term.weaken newType scrutinee)
      (Term.weaken newType leftBranch)
      (Term.weaken newType rightBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftType :=
        Ty.strengthen?_weaken leftType
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightType :=
          Ty.strengthen?_weaken rightType
        rw [rightSuccess] at rightFails
        cases rightFails
    · split
      · next motiveFails =>
          exfalso
          have motiveSuccess :
              motiveType.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some motiveType :=
            Ty.strengthen?_weaken motiveType
          rw [motiveSuccess] at motiveFails
          cases motiveFails
      · split
        · next scrutineeRecurse =>
            exfalso
            have totHyp := scrutineeIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType scrutinee))) = true :=
              scrutineeRecurse ▸ totHyp
            cases this
        · split
          · next leftRecurse =>
              exfalso
              have totHyp := leftIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType leftBranch))) = true :=
                leftRecurse ▸ totHyp
              cases this
          · split
            · next rightRecurse =>
                exfalso
                have totHyp := rightIH newType
                unfold strengthenTyped? at totHyp
                have : Option.isSome (none (α := StrengtheningResult
                    (ContextStrengthening.dropNewest context newType)
                    (Term.weaken newType rightBranch))) = true :=
                  rightRecurse ▸ totHyp
                cases this
            · rfl

/-- 2-IH non-binder totality: `Term.effectPerform`.  One RawTerm
(effectTag) + signature with two Ty carriers + two Term IH. -/
theorem isTotalOnWeaken_effectPerform {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag : Term context
      (Ty.effect operationSignature.argumentCarrier effectTag)
      operationRaw}
    {arguments : Term context operationSignature.argumentCarrier
      argumentsRaw}
    (operationIH : IsTotalOnWeaken operationTag)
    (argumentsIH : IsTotalOnWeaken arguments) :
    IsTotalOnWeaken (Term.effectPerform effectTag effectRow
      operationSignature canPerformOperation operationTag arguments) := by
  intro newType
  show (strengthenTyped? (Term.effectPerform effectTag.weaken
      effectRow
      (operationSignature.map
        (fun carrierType : Ty level scope =>
          (carrierType : Ty level scope).rename RawRenaming.weaken))
      (Effects.CanPerform.map
        (fun carrierType : Ty level scope =>
          (carrierType : Ty level scope).rename RawRenaming.weaken)
        canPerformOperation)
      (Term.weaken newType operationTag)
      (Term.weaken newType arguments))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next effectTagFails =>
      exfalso
      have effectTagSuccess :
          effectTag.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some effectTag :=
        RawTerm.strengthen?_weaken effectTag
      rw [effectTagSuccess] at effectTagFails
      cases effectTagFails
  · split
    · next argumentCarrierFails =>
        exfalso
        have argumentCarrierSuccess :
            (Effects.OperationSignature.map
              (fun carrierType : Ty level scope =>
                (carrierType : Ty level scope).rename RawRenaming.weaken)
              operationSignature).argumentCarrier.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some operationSignature.argumentCarrier := by
          change operationSignature.argumentCarrier.weaken.partialStrengthen?
              _ = _
          exact Ty.strengthen?_weaken operationSignature.argumentCarrier
        rw [argumentCarrierSuccess] at argumentCarrierFails
        cases argumentCarrierFails
    · split
      · next resultCarrierFails =>
          exfalso
          have resultCarrierSuccess :
              (Effects.OperationSignature.map
                (fun carrierType : Ty level scope =>
                  (carrierType : Ty level scope).rename RawRenaming.weaken)
                operationSignature).resultCarrier.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some operationSignature.resultCarrier := by
            change operationSignature.resultCarrier.weaken.partialStrengthen?
                _ = _
            exact Ty.strengthen?_weaken operationSignature.resultCarrier
          rw [resultCarrierSuccess] at resultCarrierFails
          cases resultCarrierFails
      · split
        · next operationRecurse =>
            exfalso
            have totHyp := operationIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType operationTag))) = true :=
              operationRecurse ▸ totHyp
            cases this
        · split
          · next argumentsRecurse =>
              exfalso
              have totHyp := argumentsIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType arguments))) = true :=
                argumentsRecurse ▸ totHyp
              cases this
          · rfl

/-- 0-IH parametric atomic totality: `Term.piTyCode` (universe-code
for `Ty.piTy`).  Domain at outer scope; codomain at scope+1 (under
binder).  Codomain strengthen uses `back.lift` and the lift-after-
lift composition lemma. -/
theorem isTotalOnWeaken_piTyCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.piTyCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.piTyCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken
      (codomainCodeRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainCodeRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainCodeRaw := by
          have := RawTerm.partialStrengthen?_rename_some codomainCodeRaw
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.sigmaTyCode` (universe-code
for `Ty.sigmaTy`).  Same shape as `piTyCode`. -/
theorem isTotalOnWeaken_sigmaTyCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.sigmaTyCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.sigmaTyCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken
      (codomainCodeRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainCodeRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainCodeRaw := by
          have := RawTerm.partialStrengthen?_rename_some codomainCodeRaw
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 1-IH non-binder totality: `Term.fst`.  One Ty (firstType) at outer
scope + one Ty (secondType) at scope+1 (lift) + one Term IH.  The
secondType strengthen uses `back.lift`. -/
theorem isTotalOnWeaken_fst {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH : IsTotalOnWeaken pairTerm) :
    IsTotalOnWeaken (Term.fst pairTerm) := by
  intro newType
  show (strengthenTyped? (Term.fst (Term.weaken newType pairTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstType :=
        Ty.strengthen?_weaken firstType
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some secondType := by
          have := Ty.partialStrengthen?_rename_some secondType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [secondSuccess] at secondFails
        cases secondFails
    · split
      · next pairRecurse =>
          exfalso
          have totHyp := pairIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType pairTerm))) = true :=
            pairRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.refineIntro`.  Predicate (RawTerm)
at scope+1 uses `back.lift`; baseValue and predicateProof are Term
IHs at outer scope. -/
theorem isTotalOnWeaken_refineIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (baseIH : IsTotalOnWeaken baseValue)
    (proofIH : IsTotalOnWeaken predicateProof) :
    IsTotalOnWeaken (Term.refineIntro predicate baseValue
      predicateProof) := by
  intro newType
  show (strengthenTyped? (Term.refineIntro
      (predicate.rename RawRenaming.weaken.lift)
      (Term.weaken newType baseValue)
      (Term.weaken newType predicateProof))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next predicateFails =>
      exfalso
      have predicateSuccess :
          (predicate.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some predicate := by
        have := RawTerm.partialStrengthen?_rename_some predicate
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [RawTerm.rename_identity] at this
        exact this
      rw [predicateSuccess] at predicateFails
      cases predicateFails
  · split
    · next baseRecurse =>
        exfalso
        have totHyp := baseIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType baseValue))) = true :=
          baseRecurse ▸ totHyp
        cases this
    · split
      · next proofRecurse =>
          exfalso
          have totHyp := proofIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType predicateProof))) = true :=
            proofRecurse ▸ totHyp
          cases this
      · rfl

/-- 1-IH non-binder totality: `Term.refineElim`.  One Ty (baseType) at
outer scope + one RawTerm (predicate) at scope+1 + one Term IH. -/
theorem isTotalOnWeaken_refineElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIH : IsTotalOnWeaken refinedValue) :
    IsTotalOnWeaken (Term.refineElim refinedValue) := by
  intro newType
  show (strengthenTyped? (Term.refineElim (Term.weaken newType
      refinedValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next predicateFails =>
        exfalso
        have predicateSuccess :
            (predicate.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some predicate := by
          have := RawTerm.partialStrengthen?_rename_some predicate
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [predicateSuccess] at predicateFails
        cases predicateFails
    · split
      · next refinedRecurse =>
          exfalso
          have totHyp := refinedIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType refinedValue))) = true :=
            refinedRecurse ▸ totHyp
          cases this
      · rfl

/-- 0-IH parametric atomic totality: `Term.funextReflAtId`.  Two Ty
(domainType, codomainType) at outer scope + one RawTerm (applyRaw)
at scope+1.  No Term IH. -/
theorem isTotalOnWeaken_funextReflAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextReflAtId (context := context)
      domainType codomainType applyRaw) := by
  intro newType
  show (strengthenTyped? (Term.funextReflAtId
      (context := context.cons newType)
      domainType.weaken codomainType.weaken
      (applyRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyFails =>
          exfalso
          have applySuccess :
              (applyRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyRaw := by
            have := RawTerm.partialStrengthen?_rename_some applyRaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applySuccess] at applyFails
          cases applyFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.funextIntroHet`.  Two Ty +
two RawTerm at scope+1.  No Term IH. -/
theorem isTotalOnWeaken_funextIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextIntroHet (context := context)
      domainType codomainType applyARaw applyBRaw) := by
  intro newType
  show (strengthenTyped? (Term.funextIntroHet
      (context := context.cons newType)
      domainType.weaken codomainType.weaken
      (applyARaw.rename RawRenaming.weaken.lift)
      (applyBRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyAFails =>
          exfalso
          have applyASuccess :
              (applyARaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyARaw := by
            have := RawTerm.partialStrengthen?_rename_some applyARaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applyASuccess] at applyAFails
          cases applyAFails
      · split
        · next applyBFails =>
            exfalso
            have applyBSuccess :
                (applyBRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back.lift =
                  some applyBRaw := by
              have := RawTerm.partialStrengthen?_rename_some applyBRaw
                RawRenaming.weaken.lift RawRenaming.identity
                (ContextStrengthening.dropNewest context newType).back.lift
                (fun position =>
                  PartialRawRenaming.lift_dropNewest_weaken_lift position)
              rw [RawTerm.rename_identity] at this
              exact this
            rw [applyBSuccess] at applyBFails
            cases applyBFails
        · rfl

/-- 0-IH parametric atomic totality: `Term.arrowCode` (universe-code
for `Ty.arrow`).  Two RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_arrowCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.arrowCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.arrowCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken codomainCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainCodeRaw :=
          RawTerm.strengthen?_weaken codomainCodeRaw
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.productCode` (universe-code
for `Ty.product`).  Two RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_productCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.productCode (context := context) outerLevel
      levelLe firstCodeRaw secondCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.productCode
      (context := context.cons newType) outerLevel levelLe
      firstCodeRaw.weaken secondCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstCodeRaw :=
        RawTerm.strengthen?_weaken firstCodeRaw
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            secondCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some secondCodeRaw :=
          RawTerm.strengthen?_weaken secondCodeRaw
        rw [secondSuccess] at secondFails
        cases secondFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.sumCode` (universe-code
for `Ty.sum`). -/
theorem isTotalOnWeaken_sumCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.sumCode (context := context) outerLevel
      levelLe leftCodeRaw rightCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.sumCode
      (context := context.cons newType) outerLevel levelLe
      leftCodeRaw.weaken rightCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftCodeRaw :=
        RawTerm.strengthen?_weaken leftCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightCodeRaw :=
          RawTerm.strengthen?_weaken rightCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.listCode` (universe-code
for `Ty.listType`).  One RawTerm sub-payload. -/
theorem isTotalOnWeaken_listCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.listCode (context := context) outerLevel
      levelLe elementCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.listCode
      (context := context.cons newType) outerLevel levelLe
      elementCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementCodeRaw :=
        RawTerm.strengthen?_weaken elementCodeRaw
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.optionCode` (universe-code
for `Ty.optionType`).  One RawTerm sub-payload. -/
theorem isTotalOnWeaken_optionCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.optionCode (context := context) outerLevel
      levelLe elementCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.optionCode
      (context := context.cons newType) outerLevel levelLe
      elementCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementCodeRaw :=
        RawTerm.strengthen?_weaken elementCodeRaw
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.eitherCode` (universe-code
for `Ty.eitherType`).  Two RawTerm sub-payloads. -/
theorem isTotalOnWeaken_eitherCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.eitherCode (context := context) outerLevel
      levelLe leftCodeRaw rightCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.eitherCode
      (context := context.cons newType) outerLevel levelLe
      leftCodeRaw.weaken rightCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftCodeRaw :=
        RawTerm.strengthen?_weaken leftCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightCodeRaw :=
          RawTerm.strengthen?_weaken rightCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.idCode` (universe-code
for `Ty.id`).  Three RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_idCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.idCode (context := context) outerLevel
      levelLe typeCodeRaw leftRaw rightRaw) := by
  intro newType
  show (strengthenTyped? (Term.idCode
      (context := context.cons newType) outerLevel levelLe
      typeCodeRaw.weaken leftRaw.weaken rightRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next typeFails =>
      exfalso
      have typeSuccess :
          typeCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some typeCodeRaw :=
        RawTerm.strengthen?_weaken typeCodeRaw
      rw [typeSuccess] at typeFails
      cases typeFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftRaw :=
          RawTerm.strengthen?_weaken leftRaw
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightRaw :=
            RawTerm.strengthen?_weaken rightRaw
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.equivCode` (universe-code
for `Ty.equiv`).  Two RawTerm sub-payloads. -/
theorem isTotalOnWeaken_equivCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.equivCode (context := context) outerLevel
      levelLe leftTypeCodeRaw rightTypeCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.equivCode
      (context := context.cons newType) outerLevel levelLe
      leftTypeCodeRaw.weaken rightTypeCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftTypeCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftTypeCodeRaw :=
        RawTerm.strengthen?_weaken leftTypeCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightTypeCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightTypeCodeRaw :=
          RawTerm.strengthen?_weaken rightTypeCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-! ## Wave I: Eq.mpr-blocked ctor totality.

Seven constructors have a type-equality cast in their `Term.rename` arm
(via `Ty.subst0_rename_commute.symm ▸ ...`), so `Term.weaken nt (Term.<ctor> ...)`
produces an Eq.mpr-wrapped term.  This wrapping blocks the standard
`unfold + split` template because the dispatcher's pattern-match cannot
see the constructor head through the cast.

Resolution: ship per-ctor `weaken_<ctor>_eq` rewrite lemmas that expose
the structural shape (each is `rfl`), then use `strengthenTyped?_isSome_castInvariant`
to discharge the cast and reduce to the un-cast form, which the
standard template handles.

Three ctors have OUTER casts (appPi, snd, funextRefl) — the cast wraps
the whole Term.snd/Term.appPi/Term.funextRefl head.
One ctor (boolElim) has OUTER + INNER casts.
Three ctors (pair, equivIntroHet, oeqFunext) have INNER casts on
specific subterms (secondValue / leftInv+rightInv / pointwiseProof). -/

/-- `Term.weaken` arm reshape for `Term.snd`.

The rename arm of `Term.snd` wraps the constructed `Term.snd (rename pairTerm)`
in `(Ty.subst0_rename_commute ...).symm ▸ ...` to align the result type
with the expected post-rename shape.  This lemma exposes that wrapping
explicitly for use in totality proofs.

Proved by `rfl` because `Term.weaken := Term.rename ...` is `@[reducible]`
and the rename arm's body normalises to the cast-wrapped form. -/
theorem weaken_snd_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (newType : Ty level scope)
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.weaken newType (Term.snd pairTerm) =
      ((Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd) :
       Term (context.cons newType)
         ((secondType.subst0 firstType pairRaw.fst).rename RawRenaming.weaken)
         (pairRaw.rename RawRenaming.weaken).snd) := by
  rfl

/-- 1-IH non-binder totality through Eq.mpr cast: `Term.snd`.

The Eq.mpr-blocked variant uses `weaken_snd_unfolds` + cast-invariance to
reduce to the standard `Term.snd` arm of the dispatcher.  Body shape
mirrors `isTotalOnWeaken_fst` after the cast discharge. -/
theorem isTotalOnWeaken_snd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH : IsTotalOnWeaken pairTerm) :
    IsTotalOnWeaken (Term.snd pairTerm) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd)).isSome by
    rw [weaken_snd_unfolds newType pairTerm]
    show ((Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd)).strengthenTyped?.isSome = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstType :=
        Ty.strengthen?_weaken firstType
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some secondType := by
          have := Ty.partialStrengthen?_rename_some secondType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [secondSuccess] at secondFails
        cases secondFails
    · split
      · next pairRecurse =>
          exfalso
          have totHyp := pairIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType pairTerm))) = true :=
            pairRecurse ▸ totHyp
          cases this
      · rfl

/-- `Term.weaken` arm reshape for `Term.funextRefl`.

The rename arm wraps in `(funextReflType_rename ...).symm ▸ ...` to
align the result Ty index.  Proved by `rfl`. -/
theorem weaken_funextRefl_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    Term.weaken newType
        (Term.funextRefl (context := context) domainType codomainType applyRaw) =
      ((funextReflType_rename RawRenaming.weaken domainType codomainType applyRaw).symm ▸
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift)))) :
       Term (context.cons newType)
         ((funextReflType domainType codomainType applyRaw).rename RawRenaming.weaken)
         (RawTerm.lam (RawTerm.refl applyRaw)).weaken) := by
  rfl

/-- 0-IH parametric atomic totality through Eq.mpr cast: `Term.funextRefl`.

`Term.funextRefl` carries two Ty payloads + one RawTerm at scope+1
applyRaw.  No Term IH.  The rename arm has an outer Eq.mpr wrapping the
constructor; we discharge via cast invariance + the standard atomic
template (domain success, codomain success, apply success, rfl). -/
theorem isTotalOnWeaken_funextRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextRefl (context := context)
      domainType codomainType applyRaw) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift))))).isSome by
    rw [weaken_funextRefl_unfolds newType domainType codomainType applyRaw]
    show ((funextReflType_rename RawRenaming.weaken
        domainType codomainType applyRaw).symm ▸
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift))))).strengthenTyped?.isSome = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back
            (fun position => rfl)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyFails =>
          exfalso
          have applySuccess :
              (applyRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyRaw := by
            have := RawTerm.partialStrengthen?_rename_some applyRaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applySuccess] at applyFails
          cases applyFails
      · rfl

/-- `Term.weaken` arm reshape for `Term.appPi`.

The rename arm wraps in `(Ty.subst0_rename_commute ...).symm ▸ ...` to
align the result Ty index.  Proved by `rfl`. -/
theorem weaken_appPi_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (newType : Ty level scope)
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term.weaken newType (Term.appPi functionTerm argumentTerm) =
      ((Ty.subst0_rename_commute codomainType domainType argumentRaw
          RawRenaming.weaken).symm ▸
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))) :
       Term (context.cons newType)
         ((codomainType.subst0 domainType argumentRaw).rename RawRenaming.weaken)
         (RawTerm.app functionRaw argumentRaw).weaken) := by
  rfl

/-- 2-IH non-binder totality through Eq.mpr cast: `Term.appPi`.

Dependent Π application — codomain at scope+1, two Term IH plus
domain/codomain Ty payloads.  Cast on the outer result; discharge via
weaken_appPi_unfolds + castInvariant. -/
theorem isTotalOnWeaken_appPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIH : IsTotalOnWeaken functionTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.appPi functionTerm argumentTerm) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken)))).isSome by
    rw [weaken_appPi_unfolds newType functionTerm argumentTerm]
    show ((Ty.subst0_rename_commute codomainType domainType argumentRaw
        RawRenaming.weaken).symm ▸
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken)))).strengthenTyped?.isSome
          = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next functionRecurse =>
          exfalso
          have totHyp := functionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType functionTerm))) = true :=
            functionRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- `Term.weaken` arm reshape for `Term.pair`.

The rename arm has INNER cast on `secondValue`: the head is `Term.pair`
(no outer cast), but the secondValue argument is wrapped in
`Ty.subst0_rename_commute ... ▸ ...`.  Proved by `rfl`.

Note: `Ty.weaken` is defined as `Ty.rename RawRenaming.weaken`, but
they may not be defeq in all positions; this lemma uses the
`.rename RawRenaming.weaken` form explicitly. -/
theorem weaken_pair_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (newType : Ty level scope)
    (firstValue : Term context firstType firstRaw)
    (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Term.weaken newType (Term.pair firstValue secondValue) =
      Term.pair (Term.weaken newType firstValue)
        ((Ty.subst0_rename_commute secondType firstType firstRaw
          RawRenaming.weaken) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) secondValue :
            Term (context.cons newType)
              ((secondType.subst0 firstType firstRaw).rename RawRenaming.weaken)
              (secondRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 2-IH non-binder totality through INNER Eq.mpr cast: `Term.pair`.

The cast is on the `secondValue` subterm, so the dispatcher's match on
`Term.pair` head succeeds, but the recursion on the cast term doesn't
directly hit the secondIH.  Use cast invariance to bridge the inner
cast back to the un-cast form. -/
theorem isTotalOnWeaken_pair {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIH : IsTotalOnWeaken firstValue)
    (secondIH : IsTotalOnWeaken secondValue) :
    IsTotalOnWeaken (Term.pair firstValue secondValue) := by
  intro newType
  -- Term.weaken nt (Term.pair fv sv) =
  --   Term.pair (Term.weaken nt fv) (eq ▸ Term.weaken nt sv)
  -- Rewrite via weaken_pair_unfolds to expose the inner cast explicitly,
  -- then the dispatcher's match on Term.pair head fires.
  rw [weaken_pair_unfolds newType firstValue secondValue]
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next secondTypeFails =>
      exfalso
      have secondTypeSuccess :
          (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some secondType := by
        have := Ty.partialStrengthen?_rename_some secondType
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [Ty.rename_identity] at this
        exact this
      rw [secondTypeSuccess] at secondTypeFails
      cases secondTypeFails
  · split
    · next firstRecurse =>
        exfalso
        have totHyp := firstIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType firstValue))) = true :=
          firstRecurse ▸ totHyp
        cases this
    · split
      · next secondRecurse =>
          exfalso
          -- secondRecurse : (eq ▸ Term.rename _ secondValue).partialStrengthenTyped? = none
          -- (Term.weaken newType secondValue = Term.rename (weakenStep) secondValue,
          --  definitional equality through @[reducible] Term.weaken.)
          --
          -- secondIH gives (Term.weaken nt sv).strengthenTyped?.isSome = true,
          -- castInvariant says (eq ▸ ...).strengthenTyped?.isSome = (...).strengthenTyped?.isSome,
          -- so secondRecurse's none contradicts.
          have totHyp := secondIH newType
          unfold strengthenTyped? at totHyp
          have invariance :=
            strengthenTyped?_isSome_castInvariant
              (Term.rename (TermRenaming.weakenStep context newType) secondValue)
              (Ty.subst0_rename_commute secondType firstType firstRaw
                RawRenaming.weaken)
          unfold strengthenTyped? at invariance
          -- invariance: (eq ▸ Term.rename ... sv).partialStrengthenTyped? _ .isSome
          --           = (Term.rename ... sv).partialStrengthenTyped? _ .isSome
          rw [secondRecurse] at invariance
          -- invariance: false = (Term.rename ... sv).partialStrengthenTyped? _ .isSome
          -- which is `Option.isSome none = ...`, i.e. `false = ...`
          -- After rw, invariance becomes `none.isSome = ...isSome`
          -- And totHyp says `... .isSome = true`
          rw [totHyp] at invariance
          cases invariance
      · rfl

/-- `Term.weaken` arm reshape for `Term.oeqFunext`.

Inner cast on `pointwiseProof` via `oeqFunextPointwiseType_rename`. -/
theorem weaken_oeqFunext_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof : Term context
      (oeqFunextPointwiseType domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      pointwiseRaw) :
    Term.weaken newType
        (Term.oeqFunext (context := context) domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof) =
      Term.oeqFunext (context := context.cons newType)
        (domainType.rename RawRenaming.weaken)
        (codomainType.rename RawRenaming.weaken)
        (leftFunctionRaw.rename RawRenaming.weaken)
        (rightFunctionRaw.rename RawRenaming.weaken)
        ((oeqFunextPointwiseType_rename RawRenaming.weaken
          domainType codomainType leftFunctionRaw rightFunctionRaw) ▸
          (Term.rename (TermRenaming.weakenStep context newType) pointwiseProof :
            Term (context.cons newType)
              ((oeqFunextPointwiseType domainType codomainType
                leftFunctionRaw rightFunctionRaw).rename RawRenaming.weaken)
              (pointwiseRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 1-IH non-binder totality through INNER Eq.mpr cast: `Term.oeqFunext`. -/
theorem isTotalOnWeaken_oeqFunext {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    {pointwiseProof : Term context
      (oeqFunextPointwiseType domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      pointwiseRaw}
    (pointwiseIH : IsTotalOnWeaken pointwiseProof) :
    IsTotalOnWeaken (Term.oeqFunext (context := context)
      domainType codomainType leftFunctionRaw rightFunctionRaw
      pointwiseProof) := by
  intro newType
  rw [weaken_oeqFunext_unfolds newType domainType codomainType
    leftFunctionRaw rightFunctionRaw pointwiseProof]
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back
            (fun position => rfl)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next leftFails =>
          exfalso
          have leftSuccess :
              (leftFunctionRaw.rename RawRenaming.weaken).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some leftFunctionRaw := by
            have := RawTerm.partialStrengthen?_rename_some leftFunctionRaw
              RawRenaming.weaken RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back
              (fun position => rfl)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [leftSuccess] at leftFails
          cases leftFails
      · split
        · next rightFails =>
            exfalso
            have rightSuccess :
                (rightFunctionRaw.rename RawRenaming.weaken).partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some rightFunctionRaw := by
              have := RawTerm.partialStrengthen?_rename_some rightFunctionRaw
                RawRenaming.weaken RawRenaming.identity
                (ContextStrengthening.dropNewest context newType).back
                (fun position => rfl)
              rw [RawTerm.rename_identity] at this
              exact this
            rw [rightSuccess] at rightFails
            cases rightFails
        · split
          · next pointwiseRecurse =>
              exfalso
              -- INNER CAST: pointwiseRecurse : (eq ▸ Term.rename _ pp).partialStrengthenTyped? = none
              have totHyp := pointwiseIH newType
              unfold strengthenTyped? at totHyp
              have invariance :=
                strengthenTyped?_isSome_castInvariant
                  (Term.rename
                    (TermRenaming.weakenStep context newType) pointwiseProof)
                  (oeqFunextPointwiseType_rename RawRenaming.weaken
                    domainType codomainType leftFunctionRaw rightFunctionRaw)
              unfold strengthenTyped? at invariance
              rw [pointwiseRecurse] at invariance
              rw [totHyp] at invariance
              cases invariance
          · rfl

/-- `Term.weaken` arm reshape for `Term.equivIntroHet`.

Two inner casts on `leftInv` and `rightInv`. -/
theorem weaken_equivIntroHet_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (newType : Ty level scope)
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv : Term context
      (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
      leftInvRaw)
    (rightInv : Term context
      (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
      rightInvRaw) :
    Term.weaken newType
        (Term.equivIntroHet forward backward leftInv rightInv) =
      Term.equivIntroHet
        (Term.weaken newType forward)
        (Term.weaken newType backward)
        ((equivIntroHetLeftInverseType_rename RawRenaming.weaken
          carrierA forwardRaw backwardRaw) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) leftInv :
            Term (context.cons newType)
              ((equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw).rename
                RawRenaming.weaken)
              (leftInvRaw.rename RawRenaming.weaken)))
        ((equivIntroHetRightInverseType_rename RawRenaming.weaken
          carrierB forwardRaw backwardRaw) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) rightInv :
            Term (context.cons newType)
              ((equivIntroHetRightInverseType carrierB forwardRaw backwardRaw).rename
                RawRenaming.weaken)
              (rightInvRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 4-IH non-binder totality through TWO INNER Eq.mpr casts: `Term.equivIntroHet`. -/
theorem isTotalOnWeaken_equivIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward : Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward : Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv : Term context
      (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
      leftInvRaw}
    {rightInv : Term context
      (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
      rightInvRaw}
    (forwardIH : IsTotalOnWeaken forward)
    (backwardIH : IsTotalOnWeaken backward)
    (leftInvIH : IsTotalOnWeaken leftInv)
    (rightInvIH : IsTotalOnWeaken rightInv) :
    IsTotalOnWeaken (Term.equivIntroHet forward backward leftInv rightInv) := by
  intro newType
  rw [weaken_equivIntroHet_unfolds newType forward backward leftInv rightInv]
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next forwardRecurse =>
          exfalso
          have totHyp := forwardIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType forward))) = true :=
            forwardRecurse ▸ totHyp
          cases this
      · split
        · next backwardRecurse =>
            exfalso
            have totHyp := backwardIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType backward))) = true :=
              backwardRecurse ▸ totHyp
            cases this
        · split
          · next leftInvRecurse =>
              exfalso
              -- INNER CAST on leftInv
              have totHyp := leftInvIH newType
              unfold strengthenTyped? at totHyp
              have invariance :=
                strengthenTyped?_isSome_castInvariant
                  (Term.rename (TermRenaming.weakenStep context newType) leftInv)
                  (equivIntroHetLeftInverseType_rename RawRenaming.weaken
                    carrierA forwardRaw backwardRaw)
              unfold strengthenTyped? at invariance
              rw [leftInvRecurse] at invariance
              rw [totHyp] at invariance
              cases invariance
          · split
            · next rightInvRecurse =>
                exfalso
                -- INNER CAST on rightInv
                have totHyp := rightInvIH newType
                unfold strengthenTyped? at totHyp
                have invariance :=
                  strengthenTyped?_isSome_castInvariant
                    (Term.rename (TermRenaming.weakenStep context newType) rightInv)
                    (equivIntroHetRightInverseType_rename RawRenaming.weaken
                      carrierB forwardRaw backwardRaw)
                unfold strengthenTyped? at invariance
                rw [rightInvRecurse] at invariance
                rw [totHyp] at invariance
                cases invariance
            · rfl

/-- `Term.weaken` arm reshape for `Term.boolElim`.

Combined OUTER + 2 INNER casts (thenBranch, elseBranch).  Cumulative
Eq.mpr blocking; resolved by the same castInvariant strategy applied
at all three cast sites.  Proved by `rfl`. -/
theorem weaken_boolElim_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (newType : Ty level scope)
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term.weaken newType (Term.boolElim scrutinee thenBranch elseBranch) =
      ((Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw
          RawRenaming.weaken).symm ▸
        (Term.boolElim
          (motiveType := motiveType.rename RawRenaming.weaken.lift)
          (Term.weaken newType scrutinee)
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) thenBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolTrue).rename
                  RawRenaming.weaken)
                (thenRaw.rename RawRenaming.weaken)))
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) elseBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolFalse).rename
                  RawRenaming.weaken)
                (elseRaw.rename RawRenaming.weaken))) :
          Term (context.cons newType)
            ((motiveType.rename RawRenaming.weaken.lift).subst0 Ty.bool
              (scrutineeRaw.rename RawRenaming.weaken))
            (RawTerm.boolElim
              (scrutineeRaw.rename RawRenaming.weaken)
              (thenRaw.rename RawRenaming.weaken)
              (elseRaw.rename RawRenaming.weaken))) :
       Term (context.cons newType)
         ((motiveType.subst0 Ty.bool scrutineeRaw).rename RawRenaming.weaken)
         (RawTerm.boolElim scrutineeRaw thenRaw elseRaw).weaken) := by
  rfl

/-- 3-IH non-binder totality through OUTER + 2 INNER Eq.mpr casts: `Term.boolElim`. -/
theorem isTotalOnWeaken_boolElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term context Ty.bool scrutineeRaw}
    {thenBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (thenIH : IsTotalOnWeaken thenBranch)
    (elseIH : IsTotalOnWeaken elseBranch) :
    IsTotalOnWeaken (Term.boolElim scrutinee thenBranch elseBranch) := by
  intro newType
  -- Discharge OUTER cast first via suffices + castInvariant
  suffices uncastTotality :
      (strengthenTyped?
        (Term.boolElim
          (motiveType := motiveType.rename RawRenaming.weaken.lift)
          (Term.weaken newType scrutinee)
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) thenBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolTrue).rename
                  RawRenaming.weaken)
                (thenRaw.rename RawRenaming.weaken)))
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) elseBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolFalse).rename
                  RawRenaming.weaken)
                (elseRaw.rename RawRenaming.weaken))) :
          Term (context.cons newType)
            ((motiveType.rename RawRenaming.weaken.lift).subst0 Ty.bool
              (scrutineeRaw.rename RawRenaming.weaken))
            (RawTerm.boolElim
              (scrutineeRaw.rename RawRenaming.weaken)
              (thenRaw.rename RawRenaming.weaken)
              (elseRaw.rename RawRenaming.weaken)))).isSome by
    rw [weaken_boolElim_unfolds newType scrutinee thenBranch elseBranch]
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next motiveFails =>
      exfalso
      have motiveSuccess :
          (motiveType.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some motiveType := by
        have := Ty.partialStrengthen?_rename_some motiveType
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [Ty.rename_identity] at this
        exact this
      rw [motiveSuccess] at motiveFails
      cases motiveFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next thenRecurse =>
          exfalso
          -- INNER CAST on thenBranch
          have totHyp := thenIH newType
          unfold strengthenTyped? at totHyp
          change
            (partialStrengthenTyped?
              (Term.rename
                (TermRenaming.weakenStep context newType) thenBranch)
              (ContextStrengthening.dropNewest context newType)).isSome = true at totHyp
          have invariance :=
            strengthenTyped?_isSome_castInvariant
              (Term.rename
                (TermRenaming.weakenStep context newType) thenBranch)
              (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
                RawRenaming.weaken)
          unfold strengthenTyped? at invariance
          -- invariance : isSome cast = isSome uncast
          -- totHyp : isSome uncast = true
          -- => isSome cast = true
          -- thenRecurse : cast = none
          -- => isSome cast = false (via congrArg)
          -- Combine: true = false
          have isSomeCastTrue : _ = _ := invariance.trans totHyp
          have isSomeCastFalse : _ = _ := congrArg Option.isSome thenRecurse
          have contradiction : (true : Bool) = false := isSomeCastTrue.symm.trans isSomeCastFalse
          cases contradiction
      · split
        · next elseRecurse =>
            exfalso
            have totHyp := elseIH newType
            unfold strengthenTyped? at totHyp
            change
              (partialStrengthenTyped?
                (Term.rename
                  (TermRenaming.weakenStep context newType) elseBranch)
                (ContextStrengthening.dropNewest context newType)).isSome = true at totHyp
            have invariance :=
              strengthenTyped?_isSome_castInvariant
                (Term.rename
                  (TermRenaming.weakenStep context newType) elseBranch)
                (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
                  RawRenaming.weaken)
            unfold strengthenTyped? at invariance
            have isSomeCastTrue : _ = _ := invariance.trans totHyp
            have isSomeCastFalse : _ = _ := congrArg Option.isSome elseRecurse
            have contradiction : (true : Bool) = false := isSomeCastTrue.symm.trans isSomeCastFalse
            cases contradiction
        · rfl

/-- BIG-ASS THEOREM headline — closed-atomic unweaken? recovers source.

For each of the 7 closed-atomic ctors, `Term.unweaken?` applied to
`Term.weaken newType (Term.<ctor>)` returns `some (Term.<ctor>)`.
Direct `rfl`-witnesses because the dispatcher's success and the
type/raw alignment unfolds atomically. -/
theorem unweaken?_weaken_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.unit (context := context))) = some Term.unit := by
  rfl

theorem unweaken?_weaken_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.boolTrue (context := context))) = some Term.boolTrue := by
  rfl

theorem unweaken?_weaken_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.boolFalse (context := context))) = some Term.boolFalse := by
  rfl

theorem unweaken?_weaken_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.natZero (context := context))) = some Term.natZero := by
  rfl

theorem unweaken?_weaken_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.interval0 (context := context))) = some Term.interval0 := by
  rfl

theorem unweaken?_weaken_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.interval1 (context := context))) = some Term.interval1 := by
  rfl

theorem unweaken?_weaken_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) (position : Fin scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.var (context := context) position)) =
      some (Term.var position) := by
  rfl

/-- Phase 2.A: 0-IH parametric atomic — `universeCode` equation form. -/
theorem unweaken?_weaken_universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.universeCode (context := context) innerLevel outerLevel
          cumulOk levelLe)) =
      some (Term.universeCode innerLevel outerLevel cumulOk levelLe) := by
  rfl


/-- Genuine iff (atomic-base version) — non-tautological strengthening
of `weaken_image_iff_strengthenTyped?_some`.

The original Step-3 iff is structural sugar around `Term.unweaken?`'s
definition (both witnesses succeed under identical conditions because
`unweaken?` pattern-matches on `strengthenTyped?`).  This version
adds genuine totality content: on a CLOSED ATOMIC SOURCE TERM (one of
the 7 atomics), the iff witnesses are UNCONDITIONALLY inhabited — no
side hypothesis required.

Consumers proving Step.eta-cascade subject reduction on closed atomic
source terms can invoke this directly. -/
theorem weaken_image_iff_strengthenTyped?_some_TRUE_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    (∃ originalTerm,
        Term.unweaken? (Term.weaken (context := context) newType
            (Term.unit (context := context))) = some originalTerm) ∧
      ∃ result,
        strengthenTyped? (Term.weaken (context := context) newType
            (Term.unit (context := context))) = some result :=
  ⟨⟨Term.unit, unweaken?_weaken_unit newType⟩,
   ⟨partialStrengthenTypedUnit
      (ContextStrengthening.dropNewest context newType), rfl⟩⟩

/-! ## Phase X bridge: IsAggregatorTotal (weakened term) → IsTotalOnWeaken.

`IsTotalOnWeaken sourceTerm` asserts that the dispatcher succeeds on
the WEAKENED form `Term.weaken newType sourceTerm` for any
`newType : Ty level scope`.  `IsAggregatorTotal weakenedTerm` is the
strictly stronger universal-strengthening statement on a
sourceTerm-bearing weakenedTerm.

This bridge specializes the universal statement to the canonical
`dropNewest` strengthening: when `IsAggregatorTotal (Term.weaken
newType sourceTerm)` holds for every choice of `newType`, the
`dropNewest context newType` strengthening witnesses
`IsTotalOnWeaken sourceTerm` because the source/raw indices of
`Term.weaken newType sourceTerm` are already weakened forms of
`sourceTerm`'s indices, and `Ty.strengthen?_weaken` /
`RawTerm.strengthen?_weaken` discharge the index witnesses.

This is the load-bearing path for the three binder wrappers
(`lam`, `lamPi`, `pathLam`) whose body strengthens through the
LIFTED `dropNewest`: the body's `IsAggregatorTotal` IH supplies the
universal-strengthening parameter, the binder's
`isAggregatorTotal_<binder>` derivation lifts that into
`IsAggregatorTotal (Term.<binder> ...)`, and this bridge converts
the conclusion into the consumer-facing `IsTotalOnWeaken`
predicate. -/
theorem isTotalOnWeaken_of_weaken_isAggregatorTotal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (weakenTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal (Term.weaken newType sourceTerm)) :
    IsTotalOnWeaken sourceTerm := by
  intro newType
  exact weakenTotal newType
    (ContextStrengthening.dropNewest context newType)
    (Ty.strengthen?_weaken sourceType)
    (RawTerm.strengthen?_weaken sourceRaw)

/-! ## Phase X: the three binder wrappers.

The non-binder ctors (the 75 already-shipped `isTotalOnWeaken_<ctor>`
theorems) all take `IsTotalOnWeaken child` IHs on their recursive
children — the narrow predicate suffices because the dispatcher's
recursion on a non-binder child uses `dropNewest`, matching the
predicate's `Term.weaken newType` shape directly.

The three binder ctors (`lam`, `lamPi`, `pathLam`) break this
pattern: their body's strengthening goes through `strengthening.lift`,
not `dropNewest`.  The narrow `IsTotalOnWeaken body` predicate cannot
transport through the lift; the strictly stronger
`IsAggregatorTotal body` (universal over all strengthenings of body)
must take its place as the binder IH.

Each wrapper's hypothesis is `weakenedBinderTotal`:
`∀ newType, IsAggregatorTotal (Term.weaken newType (Term.<binder> ...))`.
Downstream, this is constructed by:
1. taking `bodyTotal : IsAggregatorTotal body`,
2. transporting it under the binder's required renaming
   (`(weakenStep _).lift _` for the body of a weakened binder) — the
   typed rename-compatibility transport, ~78-case structural
   recursion, lives in the `Term.rename` cascade,
3. lifting through `isAggregatorTotal_<binder>`,
4. and arriving at the wrapper's `weakenedBinderTotal` hypothesis.

The bridge `isTotalOnWeaken_of_weaken_isAggregatorTotal` then
specializes the universal statement to `dropNewest` at each
`newType`, recovering `IsTotalOnWeaken (Term.<binder> ...)`. -/

/-- Binder totality wrapper: `Term.lam`.

Takes the per-`newType` `IsAggregatorTotal` on the weakened lam term,
which encapsulates the rename-transport of body's
`IsAggregatorTotal` through the dispatcher's lifted strengthening.
Converts to the consumer-facing `IsTotalOnWeaken` via the canonical
`dropNewest` specialization (the Phase X bridge above). -/
theorem isTotalOnWeaken_lam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {body : Term (context.cons domainType) codomainType.weaken bodyRaw}
    (weakenedLamTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.lam (context := context) (domainType := domainType)
              (codomainType := codomainType) body))) :
    IsTotalOnWeaken
      (Term.lam (context := context) (domainType := domainType)
        (codomainType := codomainType) body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedLamTotal

/-- Binder totality wrapper: `Term.lamPi`.

Dependent-Pi lambda; body lives at the lifted codomain inside the
binder.  Same structural shape as `isTotalOnWeaken_lam` modulo the
codomain's scope — proof is one application of the Phase X bridge. -/
theorem isTotalOnWeaken_lamPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {body : Term (context.cons domainType) codomainType bodyRaw}
    (weakenedLamPiTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.lamPi (context := context) (domainType := domainType)
              (codomainType := codomainType) body))) :
    IsTotalOnWeaken
      (Term.lamPi (context := context) (domainType := domainType)
        (codomainType := codomainType) body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedLamPiTotal

/-- Binder totality wrapper: `Term.pathLam`.

Cubical path lambda; body binds an interval slot with carrier
weakened.  Same Phase X bridge specialization as the other two
binders. -/
theorem isTotalOnWeaken_pathLam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {body :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (weakenedPathLamTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.pathLam (context := context) modeIsUnivalent carrierType
              leftEndpoint rightEndpoint body))) :
    IsTotalOnWeaken
      (Term.pathLam (context := context) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedPathLamTotal

end Term

end LeanFX2
