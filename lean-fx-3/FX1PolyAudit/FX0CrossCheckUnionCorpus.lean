import FX1PolyAudit.FX0CrossCheck
import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Core.ReduceOnceComplete
import FX1Poly.Core.RawTermNF

/-!
# FX1PolyAudit/FX0CrossCheckUnionCorpus — the FX0 cross-check on terms typed by the UNION judgment

`FX0CrossCheckCorpus` cross-checks the kernel's flagship terms certified by the GROWN engine
`HasTypeDescPi` (Church booleans / numerals / identity / Nat type), routing their strong
normalization through `externalVerify_accepts_certified` (which consumes a `HasTypeDescPi`
derivation).  After the NATIVE-42..45 endgame the typed layer is the single union judgment
`HasTypeNativeUnion`, whose 25 arms carry the data / former / eliminator families the deleted
standalone engines once held.  Their cross-check is NOT covered by the grown-engine corpus: the
flagship union terms (a λ whose body lives in the data family, a numeral tower built through the
recursive intro arm, the whole path-endpoint redex composed across the graded-intro and general-elim
arms) carry NO `HasTypeDescPi` derivation at all — they are exactly the terms that fall outside the
grown host.  This file extends the FX0 cross-check CORPUS to those union-typed flagship terms.

## The structural acceptance half is universal; the SN half is honest per term

`externalVerify_encodeCell` is purely structural — the independent minimal external verifier accepts
the serialized encoding of EVERY well-formed cell, union-typed or not (it re-checks arity, not
typing).  So the acceptance half of each fixture below is the universal soundness applied to the
union subject.

The strong-normalization half is honest per fixture, and here the union flagship terms are favourable
because each is a `Step`-NORMAL FORM in the bespoke core `Step` relation that
`StepStar.IsStronglyNormalizing` quantifies over:

  * the numeral tower `natSucc (natSucc natZero)` (typed by `recursiveUnaryIntro` twice, the
    NATIVE-36 union residency of the recursive data-intro family) is a value with no redex;
  * the constant-interval λ `λ(x:Bool). 0` (typed by `gradedBinderIntro` over a `dataIntroNullary`
    body, the λ-over-data composition the grown host could not state) is a λ whose body is the
    interval endpoint value;
  * ★ the WHOLE endpoint redex `pathApp (pathLam Type@0) 0` (typed by `generalElim` composing the
    `gradedBinderIntro` path and the `dataIntroNullary` argument — the flagship union eliminator
    computation) is a core-`Step` NORMAL FORM: the endpoint-β rule `pathApp (pathLam body) ε ↝
    body[i:=ε]` lives in the canonical TABLE relation (`StepTable`'s `pathBetaIotaRow`), NOT in core
    `Step` (its promotion is the recorded operational gap, see `KernelParamSubstrateSurvey`).  So
    the redex is `Step`-irreducible and therefore `Step`-strongly-normalizing — an honest, exact
    statement, not an overclaim of full βι-SN.

Each SN witness is the established normal-form accessibility idiom: `reduceOnce` halts on the subject
(`reduceOnce_complete` ⟹ `isStepNormalForm`), and a structurally normal term blocks every `Step`
(`isStepNormalForm_blocks_step`), so `Acc.intro` closes accessibility with no infinite descent.

Each fixture's docstring NAMES the union derivation that types the subject (`numeralTwoTyped…`,
`constantIntervalLambdaNativelyTyped`, `endpointRedexNativelyTypedWhole`), tying the cross-checked
byte stream to a real `HasTypeNativeUnion` certificate.

## Zero-axiom verification

Each fixture is `⟨externalVerify_encodeCell _, <Acc.intro normal-form witness>⟩`; the normal-form
witnesses are `reduceOnce`-halt `rfl`s threaded through the shipped `reduceOnce_complete` /
`isStepNormalForm_blocks_step` lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX1Poly.FX0CrossCheck

open FX1Poly.Core (RawTerm PolyProfile)
open FX1Poly.FX0Bridge (encodeCell)
open FX1Poly.Core.StepStar (IsStronglyNormalizing StepSuccessor)
open FX1Poly.Universe (UniverseFlag LevelExpr)
open FX1Poly.Typed
  (natSuccCell natZeroCell lamCell boolTypeCell intervalZeroCell pathAppCell pathLamCell
   universeCodeCell HasTypeNativeUnion TypingContext natTypeCell piTyCodeCell intervalTypeCell
   numeralTwoTypedThroughUnionRecursiveIntroTwice constantIntervalLambdaNativelyTyped
   endpointRedexNativelyTypedWhole)

/-! ## The union flagship subjects (mirroring the `HasTypeNativeUnion` fixtures' subjects) -/

/-- The numeral tower `natSucc (natSucc natZero) : Nat` — union-typed by `recursiveUnaryIntro`
applied twice (`numeralTwoTypedThroughUnionRecursiveIntroTwice`). -/
abbrev numeralTwoUnionSubject : RawTerm 0 :=
  natSuccCell (natSuccCell natZeroCell)

/-- The constant-interval λ `λ(x:Bool). 0 : Π(x:Bool).Interval` — union-typed by `gradedBinderIntro`
over a `dataIntroNullary` body (`constantIntervalLambdaNativelyTyped`), the λ-over-data composition
the grown host could not state. -/
abbrev constantIntervalLambdaUnionSubject : RawTerm 0 :=
  lamCell boolTypeCell intervalZeroCell

/-- The WHOLE endpoint redex `pathApp (pathLam Type@0) 0` — union-typed by `generalElim` composing
the graded path and the data argument (`endpointRedexNativelyTypedWhole`).  Its endpoint-β rule
lives in the canonical TABLE relation, not core `Step`, so the redex is a core-`Step` normal form. -/
abbrev endpointRedexUnionSubject : RawTerm 0 :=
  pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) intervalZeroCell

/-! ## Strong normalization of the union flagship subjects (each a core-`Step` normal form) -/

/-- The numeral tower is strongly normalizing: it is a `Step`-normal form (a value with no redex),
so accessibility closes by `Acc.intro` with the normal-form step-block. -/
theorem numeralTwoUnionSubject_stronglyNormalizing :
    IsStronglyNormalizing numeralTwoUnionSubject :=
  Acc.intro numeralTwoUnionSubject (fun _later (laterStep : StepSuccessor _later numeralTwoUnionSubject) =>
    absurd laterStep
      (RawTerm.isStepNormalForm_blocks_step
        (RawTerm.reduceOnce_complete (term := numeralTwoUnionSubject) rfl) _later))

/-- The constant-interval λ is strongly normalizing: it is a `Step`-normal form (a λ whose body is
the interval endpoint value), so accessibility closes by `Acc.intro`. -/
theorem constantIntervalLambdaUnionSubject_stronglyNormalizing :
    IsStronglyNormalizing constantIntervalLambdaUnionSubject :=
  Acc.intro constantIntervalLambdaUnionSubject
    (fun _later (laterStep : StepSuccessor _later constantIntervalLambdaUnionSubject) =>
      absurd laterStep
        (RawTerm.isStepNormalForm_blocks_step
          (RawTerm.reduceOnce_complete (term := constantIntervalLambdaUnionSubject) rfl) _later))

/-- ★ The endpoint redex is strongly normalizing IN THE BESPOKE `Step` RELATION: its endpoint-β rule
lives in the canonical TABLE relation (`StepTable`'s `pathBetaIotaRow`), not core `Step`, so the
redex is `Step`-irreducible and accessibility closes by `Acc.intro`.  This is the exact honest
statement — `Step`-SN of the union eliminator composition — not a claim of full βι-SN. -/
theorem endpointRedexUnionSubject_stronglyNormalizing :
    IsStronglyNormalizing endpointRedexUnionSubject :=
  Acc.intro endpointRedexUnionSubject
    (fun _later (laterStep : StepSuccessor _later endpointRedexUnionSubject) =>
      absurd laterStep
        (RawTerm.isStepNormalForm_blocks_step
          (RawTerm.reduceOnce_complete (term := endpointRedexUnionSubject) rfl) _later))

/-! ## The FX0 cross-check fixtures on the union-typed flagship terms -/

/-- ★ **The external verifier accepts the union-typed numeral tower, and it is strongly normalizing.**
`natSucc (natSucc natZero)` (union-typed via `recursiveUnaryIntro` twice — the numeral tower the
grown host could not state as a host premise) runs end-to-end through the independent minimal
external verifier and terminates. -/
theorem externalVerify_accepts_unionNumeralTwo :
    externalVerify (FX0Poly.Cert.encode (encodeCell numeralTwoUnionSubject))
        (encodeCell numeralTwoUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing numeralTwoUnionSubject :=
  ⟨externalVerify_encodeCell numeralTwoUnionSubject, numeralTwoUnionSubject_stronglyNormalizing⟩

/-- ★ **The external verifier accepts the union-typed λ-over-data, and it is strongly normalizing.**
`λ(x:Bool). 0` (union-typed via `gradedBinderIntro` over a `dataIntroNullary` body — the λ whose body
lives in the data family, untypable in the grown host) runs end-to-end through the external verifier
and terminates. -/
theorem externalVerify_accepts_unionConstantIntervalLambda :
    externalVerify (FX0Poly.Cert.encode (encodeCell constantIntervalLambdaUnionSubject))
        (encodeCell constantIntervalLambdaUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing constantIntervalLambdaUnionSubject :=
  ⟨externalVerify_encodeCell constantIntervalLambdaUnionSubject,
    constantIntervalLambdaUnionSubject_stronglyNormalizing⟩

/-- ★ **The external verifier accepts the WHOLE union-typed endpoint redex, and it is strongly
normalizing in core `Step`.**  `pathApp (pathLam Type@0) 0` (union-typed via `generalElim` composing
the graded path-intro and the data argument — the flagship eliminator computation no prior judgment
contained both premises of) runs end-to-end through the external verifier; its endpoint-β rule lives
in the canonical table relation, not core `Step`, so the redex is `Step`-normal and `Step`-SN. -/
theorem externalVerify_accepts_unionEndpointRedex :
    externalVerify (FX0Poly.Cert.encode (encodeCell endpointRedexUnionSubject))
        (encodeCell endpointRedexUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing endpointRedexUnionSubject :=
  ⟨externalVerify_encodeCell endpointRedexUnionSubject, endpointRedexUnionSubject_stronglyNormalizing⟩

/-! ## ★ The union cross-check coverage gate

The coverage record makes the "typed by the UNION judgment" claim MACHINE-CHECKED, not docstring-only:
each field pairs the cross-check verdict (accepted + SN) with the actual `HasTypeNativeUnion`
derivation that types the SAME subject.  An inhabitant therefore certifies that each cross-checked
byte stream is the encoding of a genuinely union-typed term. -/

/-- **The union-typed FX0 cross-check coverage record.**  Each field certifies that a flagship term
typed BY THE UNION JUDGMENT (`HasTypeNativeUnion`, not the grown host) is accepted by the independent
external verifier, is strongly normalizing, AND carries its union derivation.  An inhabitant certifies
the three flagship union shapes (recursive data-intro tower, λ-over-data, the path-endpoint
eliminator redex) are all jointly cross-checked and union-typed. -/
structure UnionCrossCheckCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The recursive data-intro numeral tower is accepted, SN, and union-typed. -/
  numeralTowerCrossChecked :
    (externalVerify (FX0Poly.Cert.encode (encodeCell numeralTwoUnionSubject))
        (encodeCell numeralTwoUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing numeralTwoUnionSubject)
    ∧ HasTypeNativeUnion profile (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        numeralTwoUnionSubject FX1Poly.Typed.natTypeCell
  /-- The λ-over-data composition is accepted, SN, and union-typed. -/
  lambdaOverDataCrossChecked :
    (externalVerify (FX0Poly.Cert.encode (encodeCell constantIntervalLambdaUnionSubject))
        (encodeCell constantIntervalLambdaUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing constantIntervalLambdaUnionSubject)
    ∧ HasTypeNativeUnion profile (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        constantIntervalLambdaUnionSubject
        (FX1Poly.Typed.piTyCodeCell FX1Poly.Typed.boolTypeCell FX1Poly.Typed.intervalTypeCell)
  /-- The path-endpoint eliminator redex is accepted, core-`Step`-SN, and union-typed. -/
  endpointRedexCrossChecked :
    (externalVerify (FX0Poly.Cert.encode (encodeCell endpointRedexUnionSubject))
        (encodeCell endpointRedexUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing endpointRedexUnionSubject)
    ∧ HasTypeNativeUnion profile (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        endpointRedexUnionSubject
        (FX1Poly.Typed.universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) UniverseFlag.standard)

/-- **★ The union cross-check coverage gate** — inhabited by the three shipped union fixtures, each
paired with its `HasTypeNativeUnion` derivation (`numeralTwoTypedThroughUnionRecursiveIntroTwice` /
`constantIntervalLambdaNativelyTyped` / `endpointRedexNativelyTypedWhole`).  The endpoint redex's
derivation forces `flag = standard` (the native interval-formation row pins `standard`); the gate is
stated at that flag. -/
theorem unionCrossCheckCoverageWitness {profile : PolyProfile} :
    UnionCrossCheckCoverage profile UniverseFlag.standard where
  numeralTowerCrossChecked :=
    ⟨externalVerify_accepts_unionNumeralTwo, numeralTwoTypedThroughUnionRecursiveIntroTwice⟩
  lambdaOverDataCrossChecked :=
    ⟨externalVerify_accepts_unionConstantIntervalLambda, constantIntervalLambdaNativelyTyped⟩
  endpointRedexCrossChecked :=
    ⟨externalVerify_accepts_unionEndpointRedex, endpointRedexNativelyTypedWhole UniverseFlag.standard⟩

/-! ## Documented exclusion — what the FX0 encoder/cross-check CANNOT yet express for the union

The cross-check above is over the bespoke core `Step` relation that `IsStronglyNormalizing`
quantifies.  The TABLE-relation reduction of the endpoint redex — `pathApp (pathLam Type@0) 0`
`pathBeta`-fires to `Type@0` in `StepTable` — is NOT cross-checked as a reduction here: the FX0
external verifier re-checks the STRUCTURE of an encoded cell (arity / tag well-formedness), it does
not execute reduction, so it cannot witness "the redex table-reduces to its contractum".  A
reduction-executing external checker (the FX0-PC.6 C/Rust re-checker, not yet built) is where that
table-step cross-check would land; recording it here as an explicit exclusion rather than silently
implying the byte channel verifies table reduction. -/

/-- The endpoint redex is a core-`Step` normal form — the FX0 acceptance above is STRUCTURAL, not a
reduction witness.  This pins the honest scope: the cross-check certifies the encoded structure is
accepted and the subject is `Step`-SN, NOT that the table relation's `pathBeta` step is executed by
the external verifier (which checks structure, not reduction). -/
theorem endpointRedexUnionSubject_isCoreStepNormalForm :
    RawTerm.reduceOnce endpointRedexUnionSubject = none := rfl

end FX1Poly.FX0CrossCheck
