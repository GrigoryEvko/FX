import FX1PolyAudit.FX0CrossCheckCertified
import FX1Poly.Typed.TypedChurchBooleans
import FX1Poly.Typed.TypedChurchNumerals
import FX1Poly.Typed.TypedChurchNumeralIteration

/-! Probe: FX0 cross-check corpus on the kernel's flagship CERTIFIED TYPED terms (FX0-PC.8) —
the external verifier accepts the encodings of the Church booleans + numerals, and they are SN. -/

namespace FX1Poly.FX0CrossCheck

open FX1Poly.Core (RawTerm PolyProfile)
open FX1Poly.FX0Bridge (encodeCell)
open FX1Poly.Typed (lamCell appCell variableCell HasTypeDescPi WfContextDesc churchTrueLambda
  churchFalseLambda churchTrue_hasTypeDescPi churchFalse_hasTypeDescPi churchOne_hasTypeDescPi
  churchTwo_hasTypeDescPi)
open FX1Poly.Core.StepStar (IsStronglyNormalizing)
open FX1Poly.Universe (UniverseFlag)

/-- The Church-numeral-one subject `λA.λf.λx. f x` (mirrors `churchOne_hasTypeDescPi`'s subject). -/
abbrev churchOneSubject : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

/-- The Church-numeral-two subject `λA.λf.λx. f (f x)` (mirrors `churchTwo_hasTypeDescPi`'s subject). -/
abbrev churchTwoSubject : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))

theorem externalVerify_accepts_churchTrue {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchTrueLambda)) (encodeCell churchTrueLambda).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchTrueLambda :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchTrue_hasTypeDescPi (profile := profile) UniverseFlag.standard)

theorem externalVerify_accepts_churchFalse {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchFalseLambda)) (encodeCell churchFalseLambda).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchFalseLambda :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchFalse_hasTypeDescPi (profile := profile) UniverseFlag.standard)

theorem externalVerify_accepts_churchOne {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchOneSubject)) (encodeCell churchOneSubject).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchOneSubject :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchOne_hasTypeDescPi (profile := profile) UniverseFlag.standard)

theorem externalVerify_accepts_churchTwo {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchTwoSubject)) (encodeCell churchTwoSubject).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchTwoSubject :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchTwo_hasTypeDescPi (profile := profile) UniverseFlag.standard)

end FX1Poly.FX0CrossCheck

#print axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchTrue
#print axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchFalse
#print axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchOne
#print axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_churchTwo
