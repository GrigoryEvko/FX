import LeanFX2.Term.StrengtheningImage.TotalOnWeakenCore

/-! # Term/StrengtheningImage/TotalOnWeakenAtomicUnary

Total-on-weaken wrappers for parametric atoms and one-IH non-binder constructors.
-/

namespace LeanFX2

namespace Term

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

end Term

end LeanFX2
