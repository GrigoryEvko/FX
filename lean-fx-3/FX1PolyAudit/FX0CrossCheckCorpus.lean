import FX1PolyAudit.FX0CrossCheckCertified
import FX1Poly.Typed.TypedChurchBooleans
import FX1Poly.Typed.TypedChurchNumerals
import FX1Poly.Typed.TypedChurchNumeralIteration
import FX1Poly.Typed.TypedChurchNumeralTyping
import FX1Poly.Typed.TypedLambdaDerivations

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
open FX1Poly.Typed (lamCell appCell variableCell piTyCodeCell universeCodeCell HasTypeDescPi WfContextDesc
  churchTrueLambda churchFalseLambda churchTrue_hasTypeDescPi churchFalse_hasTypeDescPi
  churchOne_hasTypeDescPi churchTwo_hasTypeDescPi churchNumeralLambda churchNumeralLambda_hasTypeDescPi
  polymorphicIdentity_hasTypeDescPi churchNatType_formation)
open FX1Poly.Core.StepStar (IsStronglyNormalizing)
open FX1Poly.Universe (UniverseFlag LevelExpr)

/-- The Church-numeral-one subject `λ(A:Type@0).λ(f:A→A).λ(x:A). f x` — T2 Church-style, with the
domain annotations in the subject (mirrors `churchOne_hasTypeDescPi`'s subject at `standard`). -/
abbrev churchOneSubject : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

/-- The Church-numeral-two subject `λ(A:Type@0).λ(f:A→A).λ(x:A). f (f x)` — T2 Church-style
(mirrors `churchTwo_hasTypeDescPi`'s subject at `standard`). -/
abbrev churchTwoSubject : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
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

/-- ★ **The external verifier accepts EVERY certified Church numeral.**  For ALL `n`, the Church numeral
`churchNumeralLambda n` (typed at the Church Nat type by `churchNumeralLambda_hasTypeDescPi`) is accepted by the
independent minimal external verifier and is strongly normalizing.  This lifts the cross-check from the concrete
fixtures `churchOne`/`churchTwo` to the WHOLE infinite numeral family in one theorem — the small auditable
verifier agrees with the rich kernel on every Church numeral. -/
theorem externalVerify_accepts_churchNumeral {profile : PolyProfile} (n : Nat) :
    externalVerify (FX0Poly.Cert.encode (encodeCell (churchNumeralLambda n)))
        (encodeCell (churchNumeralLambda n)).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing (churchNumeralLambda n) :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchNumeralLambda_hasTypeDescPi (profile := profile) n)

/-- The polymorphic identity subject `λ(A:Type@0). λ(x:A). x` — T2 Church-style (mirrors
`polymorphicIdentity_hasTypeDescPi`'s subject at `standard`). -/
abbrev polymorphicIdentitySubject : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))

/-- The external verifier accepts the certified polymorphic identity `λA.λx. x` (a distinct λ-shape from the
selectors and iterators — the dependent identity), and it is strongly normalizing. -/
theorem externalVerify_accepts_polymorphicIdentity {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell polymorphicIdentitySubject))
        (encodeCell polymorphicIdentitySubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing polymorphicIdentitySubject :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (polymorphicIdentity_hasTypeDescPi (profile := profile) UniverseFlag.standard)

/-- The Church Nat TYPE-code subject `Π(A:Type@0). Π(f:A→A). Π(x:A). A` (mirrors `churchNatType_formation`). -/
abbrev churchNatTypeSubject : RawTerm 0 :=
  piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))

/-- ★ The external verifier accepts the certified Church Nat TYPE code — a `piTyCode`-headed type FORMER (typed
at a universe), not a `λ`-term.  This broadens the cross-check beyond term introductions to the type-code
encoding path: the small verifier agrees on a type the rich kernel forms, and the type code is strongly
normalizing. -/
theorem externalVerify_accepts_churchNatType {profile : PolyProfile} :
    externalVerify (FX0Poly.Cert.encode (encodeCell churchNatTypeSubject))
        (encodeCell churchNatTypeSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing churchNatTypeSubject :=
  externalVerify_accepts_certified WfContextDesc.emptyIsWellFormed
    (churchNatType_formation (profile := profile) UniverseFlag.standard)

end FX1Poly.FX0CrossCheck
