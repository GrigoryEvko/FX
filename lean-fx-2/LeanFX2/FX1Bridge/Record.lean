import LeanFX2.FX1Bridge.RoundTrip
import LeanFX2.FX1.Core.HasType

/-! # FX1Bridge/Record

Root status: Bridge.

Single-field record bridge fragment.  The current rich kernel represents
records as a one-field wrapper; multi-field records are explicitly deferred to
schema elaboration.  This bridge therefore erases the wrapper to the encoded
field carrier in FX1:

* `Ty.record A` encodes as the encoding of `A`;
* `recordIntro field` encodes as the encoded field;
* `recordProj record` encodes as the encoded record payload.

This gives a real FX1 typing derivation without staging new object-level
constants.  It is Bridge evidence for the current one-field representation, not
a claim that FX1 has native records or multi-field record schemas.
-/

namespace LeanFX2
namespace FX1Bridge

/-- FX1 encoding of a single-field record type erases to its field type. -/
def encodeTy_record (encodedFieldType : FX1.Expr) : FX1.Expr :=
  encodedFieldType

/-- FX1 encoding of single-field record introduction erases the wrapper. -/
def encodeRawTerm_recordIntro (encodedField : FX1.Expr) : FX1.Expr :=
  encodedField

/-- FX1 encoding of single-field record projection erases the projection. -/
def encodeRawTerm_recordProj (encodedRecord : FX1.Expr) : FX1.Expr :=
  encodedRecord

/-- Fragment decoder for the single-field record type erasure. -/
def decodeTy_record
    {level : Nat}
    (decodeFieldType : FX1.Expr -> Option (Ty level 0)) :
    FX1.Expr -> Option (Ty level 0) :=
  fun encodedType =>
    match decodeFieldType encodedType with
    | Option.some fieldType => Option.some (Ty.record fieldType)
    | Option.none => Option.none

/-- Fragment decoder for single-field record introduction erasure. -/
def decodeRawTerm_recordIntro
    (decodeField : FX1.Expr -> Option (RawTerm 0)) :
    FX1.Expr -> Option (RawTerm 0) :=
  fun encodedField =>
    match decodeField encodedField with
    | Option.some fieldRaw => Option.some (RawTerm.recordIntro fieldRaw)
    | Option.none => Option.none

/-- Fragment decoder for single-field record projection erasure. -/
def decodeRawTerm_recordProj
    (decodeRecord : FX1.Expr -> Option (RawTerm 0)) :
    FX1.Expr -> Option (RawTerm 0) :=
  fun encodedRecord =>
    match decodeRecord encodedRecord with
    | Option.some recordRaw => Option.some (RawTerm.recordProj recordRaw)
    | Option.none => Option.none

/-- Record type encoding computes to the encoded field type. -/
theorem encodeTy_record_eq_field (encodedFieldType : FX1.Expr) :
    Eq (encodeTy_record encodedFieldType) encodedFieldType :=
  Eq.refl encodedFieldType

/-- Record introduction encoding computes to the encoded field payload. -/
theorem encodeRawTerm_recordIntro_eq_field (encodedField : FX1.Expr) :
    Eq (encodeRawTerm_recordIntro encodedField) encodedField :=
  Eq.refl encodedField

/-- Record projection encoding computes to the encoded record payload. -/
theorem encodeRawTerm_recordProj_eq_record (encodedRecord : FX1.Expr) :
    Eq (encodeRawTerm_recordProj encodedRecord) encodedRecord :=
  Eq.refl encodedRecord

/-- Single-field record type formation is inherited from its field type. -/
theorem encodedRecordType_has_sort
    {environment : FX1.Environment}
    {context : FX1.Context}
    {encodedFieldType : FX1.Expr}
    {sortLevel : FX1.Level}
    (encodedFieldTypeHasSort :
      FX1.HasType
        environment
        context
        encodedFieldType
        (FX1.Expr.sort sortLevel)) :
    FX1.HasType
      environment
      context
      (encodeTy_record encodedFieldType)
      (FX1.Expr.sort sortLevel) :=
  encodedFieldTypeHasSort

/-- Single-field record introduction inherits the child's FX1 typing. -/
theorem encodedRecordIntro_has_type
    {environment : FX1.Environment}
    {context : FX1.Context}
    {encodedFieldType encodedField : FX1.Expr}
    (encodedFieldHasType :
      FX1.HasType
        environment
        context
        encodedField
        encodedFieldType) :
    FX1.HasType
      environment
      context
      (encodeRawTerm_recordIntro encodedField)
      (encodeTy_record encodedFieldType) :=
  encodedFieldHasType

/-- Single-field record projection inherits the encoded record payload's FX1
typing. -/
theorem encodedRecordProj_has_type
    {environment : FX1.Environment}
    {context : FX1.Context}
    {encodedFieldType encodedRecord : FX1.Expr}
    (encodedRecordHasType :
      FX1.HasType
        environment
        context
        encodedRecord
        (encodeTy_record encodedFieldType)) :
    FX1.HasType
      environment
      context
      (encodeRawTerm_recordProj encodedRecord)
      encodedFieldType :=
  encodedRecordHasType

/-- Soundness of single-field record introduction over an already bridged
field. -/
theorem encodeTermSound_recordIntro
    {mode : Mode}
    {level : Nat}
    {fieldType : Ty level 0}
    {fieldRaw : RawTerm 0}
    {environment : FX1.Environment}
    {encodedFieldType encodedField : FX1.Expr}
    (_recordIntroTerm :
      Term
        (Ctx.empty mode level)
        (Ty.record fieldType)
        (RawTerm.recordIntro fieldRaw))
    (encodedFieldHasType :
      FX1.HasType
        environment
        FX1.Context.empty
        encodedField
        encodedFieldType) :
    FX1.HasType
      environment
      FX1.Context.empty
      (encodeRawTerm_recordIntro encodedField)
      (encodeTy_record encodedFieldType) :=
  encodedRecordIntro_has_type encodedFieldHasType

/-- Exact round-trip evidence for single-field record introduction, modular in
the field type and field raw decoders. -/
def encodeTermSound_recordIntro_roundTrip
    {mode : Mode}
    {level : Nat}
    {fieldType : Ty level 0}
    {fieldRaw : RawTerm 0}
    {encodedFieldType encodedField : FX1.Expr}
    {decodeFieldType : FX1.Expr -> Option (Ty level 0)}
    {decodeField : FX1.Expr -> Option (RawTerm 0)}
    (_recordIntroTerm :
      Term
        (Ctx.empty mode level)
        (Ty.record fieldType)
        (RawTerm.recordIntro fieldRaw))
    (fieldTypeRoundTrip :
      Eq (decodeFieldType encodedFieldType) (Option.some fieldType))
    (fieldRoundTrip :
      Eq (decodeField encodedField) (Option.some fieldRaw)) :
    BridgeRoundTrip
      (encodeTy_record encodedFieldType)
      (decodeTy_record decodeFieldType)
      (Ty.record fieldType)
      (encodeRawTerm_recordIntro encodedField)
      (decodeRawTerm_recordIntro decodeField)
      (RawTerm.recordIntro fieldRaw) :=
  {
    typeRoundTrip := by
      rw [
        encodeTy_record,
        decodeTy_record,
        fieldTypeRoundTrip
      ]
    rawRoundTrip := by
      rw [
        encodeRawTerm_recordIntro,
        decodeRawTerm_recordIntro,
        fieldRoundTrip
      ]
  }

/-- Soundness of single-field record projection over an already bridged record
payload. -/
theorem encodeTermSound_recordProj
    {mode : Mode}
    {level : Nat}
    {fieldType : Ty level 0}
    {recordRaw : RawTerm 0}
    {environment : FX1.Environment}
    {encodedFieldType encodedRecord : FX1.Expr}
    (_recordProjTerm :
      Term
        (Ctx.empty mode level)
        fieldType
        (RawTerm.recordProj recordRaw))
    (encodedRecordHasType :
      FX1.HasType
        environment
        FX1.Context.empty
        encodedRecord
        (encodeTy_record encodedFieldType)) :
    FX1.HasType
      environment
      FX1.Context.empty
      (encodeRawTerm_recordProj encodedRecord)
      encodedFieldType :=
  encodedRecordProj_has_type encodedRecordHasType

/-- Exact round-trip evidence for single-field record projection, modular in
the result type and record payload decoders. -/
def encodeTermSound_recordProj_roundTrip
    {mode : Mode}
    {level : Nat}
    {fieldType : Ty level 0}
    {recordRaw : RawTerm 0}
    {encodedFieldType encodedRecord : FX1.Expr}
    {decodeFieldType : FX1.Expr -> Option (Ty level 0)}
    {decodeRecord : FX1.Expr -> Option (RawTerm 0)}
    (_recordProjTerm :
      Term
        (Ctx.empty mode level)
        fieldType
        (RawTerm.recordProj recordRaw))
    (fieldTypeRoundTrip :
      Eq (decodeFieldType encodedFieldType) (Option.some fieldType))
    (recordRoundTrip :
      BridgeRoundTrip
        (encodeTy_record encodedFieldType)
        (decodeTy_record decodeFieldType)
        (Ty.record fieldType)
        encodedRecord
        decodeRecord
        recordRaw) :
    BridgeRoundTrip
      encodedFieldType
      decodeFieldType
      fieldType
      (encodeRawTerm_recordProj encodedRecord)
      (decodeRawTerm_recordProj decodeRecord)
      (RawTerm.recordProj recordRaw) :=
  {
    typeRoundTrip := fieldTypeRoundTrip
    rawRoundTrip := by
      rw [
        encodeRawTerm_recordProj,
        decodeRawTerm_recordProj,
        recordRoundTrip.rawRoundTrip
      ]
  }

end FX1Bridge
end LeanFX2
