import LeanFX2.Term
import LeanFX2.FX1.Core.Expr

/-! # FX1Bridge/RoundTrip

Root status: Bridge.

Small certificate shape for exact bridge-fragment round trips.  These
certificates are intentionally fragment-local: they prove that an already
staged encoder is recognized by the matching fragment decoder and reconstructs
the rich type/raw witness for that exact fragment.  They do not claim a global
FX1 decoder or a full faithful translation yet.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Exact round-trip certificate for one bridge fragment. -/
structure BridgeRoundTrip {richTypeValue richRawValue : Type}
    (encodedType : FX1.Expr)
    (decodeType : FX1.Expr -> Option richTypeValue)
    (expectedType : richTypeValue)
    (encodedRaw : FX1.Expr)
    (decodeRaw : FX1.Expr -> Option richRawValue)
    (expectedRaw : richRawValue) : Type where
  /-- Decoding the encoded FX1 type reconstructs the expected rich type. -/
  typeRoundTrip : Eq (decodeType encodedType) (Option.some expectedType)
  /-- Decoding the encoded FX1 raw term reconstructs the expected rich raw. -/
  rawRoundTrip : Eq (decodeRaw encodedRaw) (Option.some expectedRaw)

/-- Decode a staged anonymous-root constant by its FX1-native atom id. -/
def decodeConstByAtom {decodedValueType : Type}
    (expectedAtomId : Nat) (decodedValue : decodedValueType) :
    FX1.Expr -> Option decodedValueType
  | FX1.Expr.const (FX1.Name.str FX1.Name.anonymous actualAtomId) =>
      match FX1.NaturalNumber.eqResult actualAtomId expectedAtomId with
      | FX1.EqualityResult.equal _ => Option.some decodedValue
      | FX1.EqualityResult.notEqual => Option.none
  | FX1.Expr.const FX1.Name.anonymous => Option.none
  | FX1.Expr.const (FX1.Name.num _ _) => Option.none
  | FX1.Expr.const (FX1.Name.str (FX1.Name.str _ _) _) => Option.none
  | FX1.Expr.const (FX1.Name.str (FX1.Name.num _ _) _) => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- Proof-carrying comparison for FX1 levels, used only by bridge decoders. -/
def levelEqResult : (leftLevel rightLevel : FX1.Level) ->
    FX1.EqualityResult leftLevel rightLevel
  | FX1.Level.zero, FX1.Level.zero =>
      FX1.EqualityResult.equal (Eq.refl FX1.Level.zero)
  | FX1.Level.zero, FX1.Level.succ _ => FX1.EqualityResult.notEqual
  | FX1.Level.zero, FX1.Level.max _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.zero, FX1.Level.imax _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.zero, FX1.Level.param _ => FX1.EqualityResult.notEqual
  | FX1.Level.succ _, FX1.Level.zero => FX1.EqualityResult.notEqual
  | FX1.Level.succ leftBase, FX1.Level.succ rightBase =>
      match levelEqResult leftBase rightBase with
      | FX1.EqualityResult.equal baseEqual =>
          FX1.EqualityResult.equal (congrArg FX1.Level.succ baseEqual)
      | FX1.EqualityResult.notEqual => FX1.EqualityResult.notEqual
  | FX1.Level.succ _, FX1.Level.max _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.succ _, FX1.Level.imax _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.succ _, FX1.Level.param _ => FX1.EqualityResult.notEqual
  | FX1.Level.max _ _, FX1.Level.zero => FX1.EqualityResult.notEqual
  | FX1.Level.max _ _, FX1.Level.succ _ => FX1.EqualityResult.notEqual
  | FX1.Level.max leftLeft leftRight,
      FX1.Level.max rightLeft rightRight =>
      match levelEqResult leftLeft rightLeft with
      | FX1.EqualityResult.equal leftEqual =>
          match levelEqResult leftRight rightRight with
          | FX1.EqualityResult.equal rightEqual =>
              match leftEqual with
              | Eq.refl _ =>
                  match rightEqual with
                  | Eq.refl _ =>
                      FX1.EqualityResult.equal
                        (Eq.refl (FX1.Level.max leftLeft leftRight))
          | FX1.EqualityResult.notEqual => FX1.EqualityResult.notEqual
      | FX1.EqualityResult.notEqual => FX1.EqualityResult.notEqual
  | FX1.Level.max _ _, FX1.Level.imax _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.max _ _, FX1.Level.param _ => FX1.EqualityResult.notEqual
  | FX1.Level.imax _ _, FX1.Level.zero => FX1.EqualityResult.notEqual
  | FX1.Level.imax _ _, FX1.Level.succ _ => FX1.EqualityResult.notEqual
  | FX1.Level.imax _ _, FX1.Level.max _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.imax leftLeft leftRight,
      FX1.Level.imax rightLeft rightRight =>
      match levelEqResult leftLeft rightLeft with
      | FX1.EqualityResult.equal leftEqual =>
          match levelEqResult leftRight rightRight with
          | FX1.EqualityResult.equal rightEqual =>
              match leftEqual with
              | Eq.refl _ =>
                  match rightEqual with
                  | Eq.refl _ =>
                      FX1.EqualityResult.equal
                        (Eq.refl (FX1.Level.imax leftLeft leftRight))
          | FX1.EqualityResult.notEqual => FX1.EqualityResult.notEqual
      | FX1.EqualityResult.notEqual => FX1.EqualityResult.notEqual
  | FX1.Level.imax _ _, FX1.Level.param _ => FX1.EqualityResult.notEqual
  | FX1.Level.param _, FX1.Level.zero => FX1.EqualityResult.notEqual
  | FX1.Level.param _, FX1.Level.succ _ => FX1.EqualityResult.notEqual
  | FX1.Level.param _, FX1.Level.max _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.param _, FX1.Level.imax _ _ => FX1.EqualityResult.notEqual
  | FX1.Level.param leftName, FX1.Level.param rightName =>
      match FX1.Name.eqResult leftName rightName with
      | FX1.EqualityResult.equal namesEqual =>
          FX1.EqualityResult.equal (congrArg FX1.Level.param namesEqual)
      | FX1.EqualityResult.notEqual => FX1.EqualityResult.notEqual

end FX1Bridge
end LeanFX2
