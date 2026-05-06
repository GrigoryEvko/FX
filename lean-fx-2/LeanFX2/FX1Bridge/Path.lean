import LeanFX2.FX1Bridge.Interval

/-! # FX1Bridge/Path

Root status: Bridge.

Path-as-interval-function bridge fragment.  This encodes a rich path over a
carrier as an FX1 function from the staged interval type to the encoded carrier.
That makes `pathLam` an actual FX1 lambda and `pathApp` an actual FX1
application.

This is still Bridge evidence, not Root-FX1 path content: endpoint information
is reconstructed by the fragment decoder and is not enforced by the FX1 function
type itself.
-/

namespace LeanFX2
namespace FX1Bridge

/-- FX1 encoding of a rich path type as an interval-indexed function. -/
def encodeTy_path (encodedCarrier : FX1.Expr) : FX1.Expr :=
  FX1.Expr.pi encodeTy_interval (FX1.Expr.weaken encodedCarrier)

/-- FX1 encoding of a rich path lambda as an actual FX1 lambda. -/
def encodeRawTerm_pathLam (encodedBody : FX1.Expr) : FX1.Expr :=
  FX1.Expr.lam encodeTy_interval encodedBody

/-- FX1 encoding of rich path application as actual FX1 application. -/
def encodeRawTerm_pathApp
    (encodedPath encodedInterval : FX1.Expr) :
    FX1.Expr :=
  FX1.Expr.app encodedPath encodedInterval

/-- The staged interval type constant decodes as the rich interval type. -/
theorem decodeTy_interval_encodeTy_interval {level scope : Nat} :
    Eq
      (decodeTy_interval (level := level) (scope := scope) encodeTy_interval)
      (Option.some (Ty.interval : Ty level scope)) :=
  Eq.refl (Option.some (Ty.interval : Ty level scope))

/-- Substituting the newest binder out of a weakened expression recovers the
original expression. -/
theorem subst0_weaken (replacement expression : FX1.Expr) :
    Eq
      (FX1.Expr.subst0 replacement (FX1.Expr.weaken expression))
      expression :=
  Eq.trans
    (FX1.Expr.subst_rename_commute
      (FX1.Substitution.singleton replacement)
      FX1.Renaming.shift
      expression)
    (Eq.trans
      (FX1.Expr.subst_ext
        (fun index => Eq.refl (FX1.Expr.bvar index))
        expression)
      (FX1.Expr.subst_identity expression))

/-- Fragment decoder for path-as-interval-function types.  Endpoints are
supplied by the rich fragment because FX1's plain function type does not carry
them. -/
def decodeTy_path
    {level : Nat}
    (leftEndpoint rightEndpoint : RawTerm 0)
    (decodeCarrier : FX1.Expr -> Option (Ty level 0)) :
    FX1.Expr -> Option (Ty level 0)
  | FX1.Expr.pi domainExpr carrierExpr =>
      match decodeTy_interval (level := level) (scope := 0) domainExpr with
      | Option.some _ =>
          match decodeCarrier carrierExpr with
          | Option.some carrierType =>
              Option.some
                (Ty.path carrierType leftEndpoint rightEndpoint)
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- Fragment decoder for path lambdas over a supplied body decoder. -/
def decodeRawTerm_pathLam
    (decodeBody : FX1.Expr -> Option (RawTerm 1)) :
    FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.lam domainExpr bodyExpr =>
      match decodeTy_interval (level := 0) (scope := 0) domainExpr with
      | Option.some _ =>
          match decodeBody bodyExpr with
          | Option.some decodedBody =>
              Option.some (RawTerm.pathLam decodedBody)
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- Fragment decoder for path application over supplied child decoders. -/
def decodeRawTerm_pathApp
    (decodePath decodeInterval : FX1.Expr -> Option (RawTerm 0)) :
    FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app pathExpr intervalExpr =>
      match decodePath pathExpr with
      | Option.some decodedPath =>
          match decodeInterval intervalExpr with
          | Option.some decodedInterval =>
              Option.some (RawTerm.pathApp decodedPath decodedInterval)
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none

/-- Path type encoding computes to an FX1 function type from interval. -/
theorem encodeTy_path_eq_pi (encodedCarrier : FX1.Expr) :
    Eq
      (encodeTy_path encodedCarrier)
      (FX1.Expr.pi encodeTy_interval (FX1.Expr.weaken encodedCarrier)) :=
  Eq.refl (FX1.Expr.pi encodeTy_interval (FX1.Expr.weaken encodedCarrier))

/-- Path-lambda encoding computes to an FX1 lambda over interval. -/
theorem encodeRawTerm_pathLam_eq_lam (encodedBody : FX1.Expr) :
    Eq
      (encodeRawTerm_pathLam encodedBody)
      (FX1.Expr.lam encodeTy_interval encodedBody) :=
  Eq.refl (FX1.Expr.lam encodeTy_interval encodedBody)

/-- Path-application encoding computes to FX1 application. -/
theorem encodeRawTerm_pathApp_eq_app
    (encodedPath encodedInterval : FX1.Expr) :
    Eq
      (encodeRawTerm_pathApp encodedPath encodedInterval)
      (FX1.Expr.app encodedPath encodedInterval) :=
  Eq.refl (FX1.Expr.app encodedPath encodedInterval)

/-- Path-as-function type formation in the staged interval environment. -/
theorem encodedPathType_has_sort
    {encodedCarrier : FX1.Expr}
    (encodedCarrierHasSort :
      FX1.HasType
        intervalEnvironment
        (FX1.Context.extend FX1.Context.empty encodeTy_interval)
        (FX1.Expr.weaken encodedCarrier)
        (FX1.Expr.sort FX1.Level.zero)) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      (encodeTy_path encodedCarrier)
      (FX1.Expr.sort (FX1.Level.max FX1.Level.zero FX1.Level.zero)) :=
  FX1.HasType.pi
    intervalTypeExpr_has_sort_in_intervalEnvironment
    encodedCarrierHasSort

/-- FX1 typing derivation for a path lambda body already typed under the
interval binder. -/
theorem encodedPathLam_has_type
    {encodedCarrier encodedBody : FX1.Expr}
    (encodedBodyHasCarrier :
      FX1.HasType
        intervalEnvironment
        (FX1.Context.extend FX1.Context.empty encodeTy_interval)
        encodedBody
        (FX1.Expr.weaken encodedCarrier)) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      (encodeRawTerm_pathLam encodedBody)
      (encodeTy_path encodedCarrier) :=
  FX1.HasType.lam
    intervalTypeExpr_has_sort_in_intervalEnvironment
    encodedBodyHasCarrier

/-- FX1 typing derivation for path application as ordinary function
application. -/
theorem encodedPathApp_has_type
    {encodedCarrier encodedPath encodedInterval : FX1.Expr}
    (encodedPathHasType :
      FX1.HasType
        intervalEnvironment
        FX1.Context.empty
        encodedPath
        (encodeTy_path encodedCarrier))
    (encodedIntervalHasType :
      FX1.HasType
        intervalEnvironment
        FX1.Context.empty
        encodedInterval
        encodeTy_interval) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      (encodeRawTerm_pathApp encodedPath encodedInterval)
      encodedCarrier :=
  Eq.ndrec
    (motive := fun targetType =>
      FX1.HasType
        intervalEnvironment
        FX1.Context.empty
        (encodeRawTerm_pathApp encodedPath encodedInterval)
        targetType)
    (FX1.HasType.app
      encodedPathHasType
      encodedIntervalHasType)
    (subst0_weaken encodedInterval encodedCarrier)

/-- Soundness of path lambda over an already bridged body. -/
theorem encodeTermSound_pathLam
    {mode : Mode}
    {level : Nat}
    {carrierType : Ty level 0}
    {leftEndpoint rightEndpoint : RawTerm 0}
    {bodyRaw : RawTerm 1}
    {encodedCarrier encodedBody : FX1.Expr}
    (_pathLamTerm :
      Term
        (Ctx.empty mode level)
        (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw))
    (encodedBodyHasCarrier :
      FX1.HasType
        intervalEnvironment
        (FX1.Context.extend FX1.Context.empty encodeTy_interval)
        encodedBody
        (FX1.Expr.weaken encodedCarrier)) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      (encodeRawTerm_pathLam encodedBody)
      (encodeTy_path encodedCarrier) :=
  encodedPathLam_has_type encodedBodyHasCarrier

/-- Exact round-trip evidence for path lambda, modular in the carrier and body
decoders. -/
def encodeTermSound_pathLam_roundTrip
    {mode : Mode}
    {level : Nat}
    {carrierType : Ty level 0}
    {leftEndpoint rightEndpoint : RawTerm 0}
    {bodyRaw : RawTerm 1}
    {encodedCarrier encodedBody : FX1.Expr}
    {decodeCarrier : FX1.Expr -> Option (Ty level 0)}
    {decodeBody : FX1.Expr -> Option (RawTerm 1)}
    (_pathLamTerm :
      Term
        (Ctx.empty mode level)
        (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw))
    (carrierTypeRoundTrip :
      Eq
        (decodeCarrier (FX1.Expr.weaken encodedCarrier))
        (Option.some carrierType))
    (bodyRoundTrip :
      Eq (decodeBody encodedBody) (Option.some bodyRaw)) :
    BridgeRoundTrip
      (encodeTy_path encodedCarrier)
      (decodeTy_path leftEndpoint rightEndpoint decodeCarrier)
      (Ty.path carrierType leftEndpoint rightEndpoint)
      (encodeRawTerm_pathLam encodedBody)
      (decodeRawTerm_pathLam decodeBody)
      (RawTerm.pathLam bodyRaw) :=
  {
    typeRoundTrip := by
      rw [
        encodeTy_path,
        decodeTy_path,
        decodeTy_interval_encodeTy_interval,
        carrierTypeRoundTrip
      ]
    rawRoundTrip := by
      rw [
        encodeRawTerm_pathLam,
        decodeRawTerm_pathLam,
        decodeTy_interval_encodeTy_interval,
        bodyRoundTrip
      ]
  }

/-- Soundness of path application over already bridged path and interval
children. -/
theorem encodeTermSound_pathApp
    {mode : Mode}
    {level : Nat}
    {carrierType : Ty level 0}
    {pathRaw intervalRaw : RawTerm 0}
    {encodedCarrier encodedPath encodedInterval : FX1.Expr}
    (_pathAppTerm :
      Term
        (Ctx.empty mode level)
        carrierType
        (RawTerm.pathApp pathRaw intervalRaw))
    (encodedPathHasType :
      FX1.HasType
        intervalEnvironment
        FX1.Context.empty
        encodedPath
        (encodeTy_path encodedCarrier))
    (encodedIntervalHasType :
      FX1.HasType
        intervalEnvironment
        FX1.Context.empty
        encodedInterval
        encodeTy_interval) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      (encodeRawTerm_pathApp encodedPath encodedInterval)
      encodedCarrier :=
  encodedPathApp_has_type
    encodedPathHasType
    encodedIntervalHasType

/-- Exact round-trip evidence for path application, modular in the path,
interval, and carrier decoders. -/
def encodeTermSound_pathApp_roundTrip
    {mode : Mode}
    {level : Nat}
    {carrierType : Ty level 0}
    {leftEndpoint rightEndpoint pathRaw intervalRaw : RawTerm 0}
    {encodedCarrier encodedPath encodedInterval : FX1.Expr}
    {decodeCarrierInPathBody decodeCarrierResult :
      FX1.Expr -> Option (Ty level 0)}
    {decodePath decodeInterval : FX1.Expr -> Option (RawTerm 0)}
    (_pathAppTerm :
      Term
        (Ctx.empty mode level)
        carrierType
        (RawTerm.pathApp pathRaw intervalRaw))
    (carrierTypeRoundTrip :
      Eq (decodeCarrierResult encodedCarrier) (Option.some carrierType))
    (pathRoundTrip :
      BridgeRoundTrip
        (encodeTy_path encodedCarrier)
        (decodeTy_path leftEndpoint rightEndpoint decodeCarrierInPathBody)
        (Ty.path carrierType leftEndpoint rightEndpoint)
        encodedPath
        decodePath
        pathRaw)
    (intervalRoundTrip :
      BridgeRoundTrip
        encodeTy_interval
        (decodeTy_interval (level := level) (scope := 0))
        (Ty.interval : Ty level 0)
        encodedInterval
        decodeInterval
        intervalRaw) :
    BridgeRoundTrip
      encodedCarrier
      decodeCarrierResult
      carrierType
      (encodeRawTerm_pathApp encodedPath encodedInterval)
      (decodeRawTerm_pathApp decodePath decodeInterval)
      (RawTerm.pathApp pathRaw intervalRaw) :=
  {
    typeRoundTrip := carrierTypeRoundTrip
    rawRoundTrip := by
      rw [
        encodeRawTerm_pathApp,
        decodeRawTerm_pathApp,
        pathRoundTrip.rawRoundTrip,
        intervalRoundTrip.rawRoundTrip
      ]
  }

end FX1Bridge
end LeanFX2
