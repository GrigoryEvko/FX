import FX1PolyAudit.FX0CrossCheckCertified
import FX1Poly.Typed.TypedChurchBooleans
import FX1Poly.Typed.TypedChurchNumerals
import FX1Poly.Typed.TypedChurchNumeralIteration

/-!
# FX1PolyAudit/FX0CrossCheckCorpus — the FX0 cross-check on the kernel's flagship CERTIFIED typed terms (FX0-PC.8)

`FX0CrossCheckCertified` proved `externalVerify_accepts_certified` GENERICALLY: every term carrying a
`HasTypeDescPi` derivation in a well-formed context is BOTH accepted by the independent minimal external
verifier AND strongly normalizing.  But the concrete corpus only exercised the structural smokes (var 0,
universe code) and the necessity counterexample (Ω).  This file extends the cross-check CORPUS to the
kernel's flagship CERTIFIED TYPED terms — the Church-boolean and Church-numeral encodings the typed-engine
firings (`CHURCH-BOOL` / `CHURCH-NAT` / `CHURCH-NAT-2`) constructed — connecting the typed-derivation thread
to the external-verifier soundness, an A₀-release ingredient (the `FX0 cross-check` of #464).

Each fixture instantiates the generic `externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed _`
on a closed flagship derivation, witnessing that the small, independently-auditable verifier accepts the
serialized encoding of a real `λ`-term the rich kernel certifies, and that the term genuinely terminates:

  * **`externalVerify_accepts_churchTrue` / `…churchFalse`** — the Church booleans `λA.λt.λf. t` / `…f`
    (`churchTrueLambda` / `churchFalseLambda`, from `CHURCH-BOOL`).
  * **`externalVerify_accepts_churchOne` / `…churchTwo`** — the Church numerals `λA.λf.λx. f x` /
    `λA.λf.λx. f (f x)` (subjects mirrored from `churchOne_hasTypeDescPi` / `churchTwo_hasTypeDescPi`).

The four span both data shapes the engine types (the boolean selectors and the numeral iterators), all in
the Π/λ/app fragment the typing judgment actually certifies.

## Zero-axiom verification

Each fixture is the generic cross-check applied to a shipped zero-axiom derivation; the numeral subject
abbreviations mirror the derivations' subjects exactly (the `Fin` index proofs are definitionally
irrelevant, so the local abbreviations unify with the inlined subjects).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per-declaration in
`FX1PolyAudit/AuditFX0Poly.lean`.
-/

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

/-- The external verifier accepts the certified Church-`true` encoding, and it is strongly normalizing. -/
theorem externalVerify_accepts_churchTrue {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchTrueLambda))
        (encodeCell churchTrueLambda).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchTrueLambda :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchTrue_hasTypeDescPi (profile := profile) UniverseFlag.standard)

/-- The external verifier accepts the certified Church-`false` encoding, and it is strongly normalizing. -/
theorem externalVerify_accepts_churchFalse {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchFalseLambda))
        (encodeCell churchFalseLambda).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchFalseLambda :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchFalse_hasTypeDescPi (profile := profile) UniverseFlag.standard)

/-- The external verifier accepts the certified Church-numeral-`one` encoding, and it is SN. -/
theorem externalVerify_accepts_churchOne {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchOneSubject))
        (encodeCell churchOneSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchOneSubject :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchOne_hasTypeDescPi (profile := profile) UniverseFlag.standard)

/-- The external verifier accepts the certified Church-numeral-`two` encoding, and it is SN. -/
theorem externalVerify_accepts_churchTwo {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchTwoSubject))
        (encodeCell churchTwoSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchTwoSubject :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchTwo_hasTypeDescPi (profile := profile) UniverseFlag.standard)

end FX1Poly.FX0CrossCheck
