import LeanFX2.Cubical.Bridge
import LeanFX2.Bridge.IdEqType
import LeanFX2.HoTT.UnivalenceTransport

/-! # Cubical/Ua

Cubical-facing univalence facade for the fragments this kernel actually
supports.

This is not a full CCHM `ua` construction by Glue.  The sprint plan marks that
route as high-risk: arbitrary cubical `ua` needs more Glue and transport
coherence than this kernel slice currently has.  The load-bearing univalence
route is the HoTT/observational `eqType` reduction already shipped in
`HoTT/Univalence.lean`.

What this module exposes:

* cubical-facing names for the audited kernel univalence conversions;
* the canonical constant universe-path-to-equivalence fragment;
* meta-level `ua_beta` transport rules that are path-induction facts over
  Lean `Eq`.

What it deliberately does not claim:

* no arbitrary `Equiv A B -> Path Type A B` at the cubical Term layer;
* no Glue-derived computation rule for arbitrary equivalences;
* no synthesis of equivalence witnesses from arbitrary cubical paths.
-/

namespace LeanFX2
namespace Cubical

universe metaLevel

/-! ## Kernel-level univalence conversions -/

/-- Cubical-facing name for the reflexive kernel univalence conversion.

This wraps `Bridge.idEqTypeRefl`, which itself wraps the audited
`Univalence` theorem.  The result is a conversion between the canonical
type-equality witness and the identity equivalence. -/
theorem uaReflConv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Conv (Term.equivReflIdAtId (context := context)
        innerLevel innerLevelLt carrier carrierRaw)
      (Term.equivReflId (context := context) carrier) :=
  Bridge.idEqTypeRefl innerLevel innerLevelLt carrier carrierRaw

/-- Cubical-facing name for heterogeneous kernel univalence.

This is only as strong as the caller-supplied equivalence witness.  It does not
construct that witness from an arbitrary path. -/
theorem uaHetConv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness :
      Term context (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Conv (Term.uaIntroHet (context := context)
        innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness)
      equivWitness :=
  Bridge.idEqTypeHet innerLevel innerLevelLt
    carrierARaw carrierBRaw equivWitness

/-! ## Canonical cubical type-path fragment -/

/-- Canonical constant cubical universe paths produce identity equivalences.

This re-exposes the existing `Cubical.constantCubicalTypePathToEquiv` under
the `ua` module.  The path argument is restricted to the constant universe path
fragment already implemented by the bridge layer. -/
def uaConstantTypePathToEquiv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw)
    (typePath :
      Term context
        (Ty.path (Ty.universe innerLevel innerLevelLt) typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken)) :
    Term context (Ty.equiv carrier carrier)
      (Term.equivReflId (context := context) carrier).toRaw :=
  constantCubicalTypePathToEquiv
    modeIsUnivalent innerLevel innerLevelLt carrier typeCode typePath

/-- The canonical type-path `ua` fragment projects to identity equivalence. -/
theorem uaConstantTypePathToEquiv_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw)
    (typePath :
      Term context
        (Ty.path (Ty.universe innerLevel innerLevelLt) typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken)) :
    (uaConstantTypePathToEquiv modeIsUnivalent innerLevel innerLevelLt
      carrier typeCode typePath).toRaw =
      (Term.equivReflId (context := context) carrier).toRaw :=
  constantCubicalTypePathToEquiv_toRaw
    modeIsUnivalent innerLevel innerLevelLt carrier typeCode typePath

/-- Canonical specialization of the constant type-path `ua` fragment. -/
theorem uaConstantTypePathToEquiv_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw) :
    uaConstantTypePathToEquiv modeIsUnivalent innerLevel innerLevelLt carrier typeCode
      (constantTypePath modeIsUnivalent innerLevel innerLevelLt typeCode) =
      Term.equivReflId carrier :=
  constantCubicalTypePathToEquiv_onCanonical
    modeIsUnivalent innerLevel innerLevelLt carrier typeCode

/-! ## Meta-level computational rules -/

/-- Meta-level `ua_beta`: transport along a type path agrees with the forward
map of the corresponding `idToEquivMeta` equivalence. -/
theorem uaBetaMeta
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (leftValue : LeftType) :
    pathProof ▸ leftValue
      = (Univalence.idToEquivMeta pathProof).toFun leftValue :=
  Univalence.ua_beta_meta pathProof leftValue

/-- `uaBetaMeta` at reflexivity reduces definitionally. -/
theorem uaBetaMetaRefl
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Eq.refl LeftType) ▸ leftValue
      = (Univalence.idToEquivMeta (Eq.refl LeftType)).toFun leftValue :=
  Univalence.ua_beta_meta_refl LeftType leftValue

/-- Inverse meta-level `ua_beta`: transport along the inverse path agrees with
the inverse map of `idToEquivMeta`. -/
theorem uaBetaMetaSymm
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (pathProof : LeftType = RightType) (rightValue : RightType) :
    (Eq.symm pathProof) ▸ rightValue
      = (Univalence.idToEquivMeta pathProof).invFun rightValue :=
  Univalence.ua_beta_meta_symm pathProof rightValue

/-- Transport through the canonical refl-equivalence computes as identity. -/
theorem uaTransportViaReflEquiv
    (LeftType : Sort metaLevel) (leftValue : LeftType) :
    (Univalence.equivToIdMetaAtRefl LeftType (Equiv.refl LeftType)) ▸ leftValue
      = (Equiv.refl LeftType).toFun leftValue :=
  Univalence.transport_via_reflEquiv LeftType leftValue

/-- The kernel reflexive univalence fragment aligns with the meta-level
`idToEquivMeta` reflexive equivalence. -/
theorem uaKernelRflAlignsWithMeta
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta (Eq.refl LeftType)
      = Equiv.refl LeftType :=
  Univalence.kernelRflFragmentAlignsWithMeta LeftType

end Cubical
end LeanFX2
