import FX1PolyAudit.FX0CrossCheck
import FX1Poly.Typed.HasTypeUnion
import FX1Poly.Core.ReduceOnceComplete
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.OneStepReducts
import FX1Poly.Core.OneStepReductsComplete

/-!
# FX1PolyAudit/FX0CrossCheckUnionCorpus — the FX0 cross-check on terms typed by the UNION judgment

`FX0CrossCheckCorpus` cross-checks the kernel's flagship terms certified by the GROWN engine
`HasTypeDescPi` (Church booleans / numerals / identity / Nat type), routing their strong
normalization through `externalVerify_accepts_certified` (which consumes a `HasTypeDescPi`
derivation).  After the NATIVE-42..45 endgame the typed layer is the single union judgment
`HasTypeUnion`, whose 25 arms carry the data / former / eliminator families the deleted
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

The strong-normalization half is honest per fixture.  After TABLE-CANON-1 core `Step` is rebased onto
the canonical 21-row `iotaRuleTable`, so the endpoint-β rule is now a core-`Step` reduction (not a
table-only sibling) — and all three flagship subjects are still strongly normalizing, two as values
and one as a one-step redex collapsing to a value:

  * the numeral tower `natSucc (natSucc natZero)` (typed by `recursiveUnaryIntro` twice, the
    NATIVE-36 union residency of the recursive data-intro family) is a value with no redex;
  * the constant-interval λ `λ(x:Bool). 0` (typed by `gradedBinderIntro` over a `dataIntroNullary`
    body, the λ-over-data composition the grown host could not state) is a λ whose body is the
    interval endpoint value;
  * ★ the WHOLE endpoint redex `pathApp (pathLam Type@0) 0` (typed by `generalElim` composing the
    `gradedBinderIntro` path and the `dataIntroNullary` argument — the flagship union eliminator
    computation) now core-`Step`-reduces in ONE step to `Type@0`: the endpoint-β rule
    `pathApp (pathLam body) ε ↝ body[i:=ε]` is row `pathBetaIotaRow` of the canonical `iotaRuleTable`
    that core `Step` is now built over, and the body `Type@0` does not mention the path variable, so
    the substitution returns `Type@0` — a value with no further redex.  The whole redex is therefore
    `Step`-strongly-normalizing: its single one-step reduct is a normal form.

The value SN witnesses are the established normal-form accessibility idiom: `reduceOnce` halts on the
subject (`reduceOnce_complete` ⟹ `isStepNormalForm`), and a structurally normal term blocks every
`Step` (`isStepNormalForm_blocks_step`), so `Acc.intro` closes accessibility with no infinite
descent.  The endpoint redex uses the redex idiom from `Core/CostBound`: every one-step reduct lands
in `oneStepReducts` (`oneStepReducts_complete`), which computes to the singleton `[Type@0]`, and that
reduct is itself a normal form — so `Acc.intro` closes after one descent.

Each fixture's docstring NAMES the union derivation that types the subject (`numeralTwoTyped…`,
`constantIntervalLambdaNativelyTyped`, `endpointRedexNativelyTypedWhole`), tying the cross-checked
byte stream to a real `HasTypeUnion` certificate.

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
   universeCodeCell HasTypeUnion TypingContext natTypeCell piTyCodeCell intervalTypeCell
   numeralTwoTypedThroughUnionRecursiveIntroTwice constantIntervalLambdaNativelyTyped
   endpointRedexNativelyTypedWhole)

/-! ## The union flagship subjects (mirroring the `HasTypeUnion` fixtures' subjects) -/

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
the graded path and the data argument (`endpointRedexNativelyTypedWhole`).  After TABLE-CANON-1 its
endpoint-β rule is row `pathBetaIotaRow` of the canonical `iotaRuleTable` that core `Step` is built
over, so the redex core-`Step`-reduces in one step to `Type@0` (the body, with the path argument
substituted into a body that does not mention the path variable). -/
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

/-- The endpoint redex's one-step reducts: the singleton `[Type@0]`, the pathBeta contractum.  The
function `pathLam Type@0` and the argument `intervalZero` are both normal, so the only redex is the
root endpoint-β; the body `Type@0` does not mention the path variable, so the contractum is `Type@0`.
The enumeration computes by `rfl` (`oneStepReducts` over the canonical `iotaRuleTable`). -/
theorem endpointRedexUnionSubject_oneStepReducts :
    RawTerm.oneStepReducts endpointRedexUnionSubject
      = [(universeCodeCell LevelExpr.lzero UniverseFlag.standard : RawTerm 0)] := rfl

/-- ★ The endpoint redex is strongly normalizing.  After TABLE-CANON-1 core `Step` is the canonical
21-row `iotaRuleTable`, so the endpoint-β rule (row `pathBetaIotaRow`) fires in core `Step`: the redex
one-step-reduces to `Type@0`, a normal form.  Accessibility closes after one descent — every one-step
reduct lands in `oneStepReducts` (`oneStepReducts_complete`), which computes to the singleton
`[Type@0]`, and the reduct itself blocks every further `Step`.  This is the genuine redex idiom from
`Core/CostBound` (not the value-as-normal-form idiom the other two flagship subjects use). -/
theorem endpointRedexUnionSubject_stronglyNormalizing :
    IsStronglyNormalizing endpointRedexUnionSubject :=
  Acc.intro endpointRedexUnionSubject
    (fun later laterStep => by
      have memListed : later ∈ RawTerm.oneStepReducts endpointRedexUnionSubject :=
        RawTerm.oneStepReducts_complete laterStep
      rw [endpointRedexUnionSubject_oneStepReducts] at memListed
      cases memListed with
      | head =>
          exact Acc.intro _ (fun deeper deeperStep =>
            absurd deeperStep
              (RawTerm.isStepNormalForm_blocks_step
                (RawTerm.reduceOnce_complete
                  (term := (universeCodeCell LevelExpr.lzero UniverseFlag.standard : RawTerm 0)) rfl)
                deeper))
      | tail _ memEmpty => exact nomatch memEmpty)

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
contained both premises of) runs end-to-end through the external verifier; after TABLE-CANON-1 its
endpoint-β rule fires in core `Step` (row `pathBetaIotaRow` of the canonical `iotaRuleTable`), so the
redex core-`Step`-reduces in one step to `Type@0` — a normal form — and is therefore `Step`-SN. -/
theorem externalVerify_accepts_unionEndpointRedex :
    externalVerify (FX0Poly.Cert.encode (encodeCell endpointRedexUnionSubject))
        (encodeCell endpointRedexUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing endpointRedexUnionSubject :=
  ⟨externalVerify_encodeCell endpointRedexUnionSubject, endpointRedexUnionSubject_stronglyNormalizing⟩

/-! ## ★ The union cross-check coverage gate

The coverage record makes the "typed by the UNION judgment" claim MACHINE-CHECKED, not docstring-only:
each field pairs the cross-check verdict (accepted + SN) with the actual `HasTypeUnion`
derivation that types the SAME subject.  An inhabitant therefore certifies that each cross-checked
byte stream is the encoding of a genuinely union-typed term. -/

/-- **The union-typed FX0 cross-check coverage record.**  Each field certifies that a flagship term
typed BY THE UNION JUDGMENT (`HasTypeUnion`, not the grown host) is accepted by the independent
external verifier, is strongly normalizing, AND carries its union derivation.  An inhabitant certifies
the three flagship union shapes (recursive data-intro tower, λ-over-data, the path-endpoint
eliminator redex) are all jointly cross-checked and union-typed. -/
structure UnionCrossCheckCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The recursive data-intro numeral tower is accepted, SN, and union-typed. -/
  numeralTowerCrossChecked :
    (externalVerify (FX0Poly.Cert.encode (encodeCell numeralTwoUnionSubject))
        (encodeCell numeralTwoUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing numeralTwoUnionSubject)
    ∧ HasTypeUnion profile (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        numeralTwoUnionSubject FX1Poly.Typed.natTypeCell
  /-- The λ-over-data composition is accepted, SN, and union-typed. -/
  lambdaOverDataCrossChecked :
    (externalVerify (FX0Poly.Cert.encode (encodeCell constantIntervalLambdaUnionSubject))
        (encodeCell constantIntervalLambdaUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing constantIntervalLambdaUnionSubject)
    ∧ HasTypeUnion profile (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        constantIntervalLambdaUnionSubject
        (FX1Poly.Typed.piTyCodeCell FX1Poly.Typed.boolTypeCell FX1Poly.Typed.intervalTypeCell)
  /-- The path-endpoint eliminator redex is accepted, core-`Step`-SN, and union-typed. -/
  endpointRedexCrossChecked :
    (externalVerify (FX0Poly.Cert.encode (encodeCell endpointRedexUnionSubject))
        (encodeCell endpointRedexUnionSubject).budget = FX0Poly.CheckVerdict.accepted
      ∧ IsStronglyNormalizing endpointRedexUnionSubject)
    ∧ HasTypeUnion profile (FX1Poly.Typed.TypingContext.empty : FX1Poly.Typed.TypingContext profile 0)
        endpointRedexUnionSubject
        (FX1Poly.Typed.universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) UniverseFlag.standard)

/-- **★ The union cross-check coverage gate** — inhabited by the three shipped union fixtures, each
paired with its `HasTypeUnion` derivation (`numeralTwoTypedThroughUnionRecursiveIntroTwice` /
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

After TABLE-CANON-1 the endpoint-β reduction IS a core-`Step` step (`pathBetaIotaRow` of the
canonical `iotaRuleTable`): `pathApp (pathLam Type@0) 0 ↝ Type@0`, executed by `reduceOnce`.  But the
FX0 external verifier is STILL a STRUCTURAL re-checker — it re-checks the arity / tag well-formedness
of an encoded cell, it does NOT execute reduction.  So the cross-check above certifies the encoded
structure is accepted and the subject is `Step`-SN; it does NOT witness "the redex `Step`-reduces to
its contractum".  A reduction-executing external checker (the FX0-PC.6 C/Rust re-checker, not yet
built) is where that step cross-check would land; recording it here as an explicit exclusion rather
than silently implying the byte channel verifies reduction. -/

/-- The endpoint redex `Step`-reduces (one step, `reduceOnce`) to `Type@0` — after TABLE-CANON-1 the
endpoint-β rule fires in core `Step`.  The FX0 acceptance above is STRUCTURAL: it certifies the
encoded structure is accepted and the subject is `Step`-SN, NOT that this `pathBeta` step is executed
by the external verifier (which checks structure, not reduction). -/
theorem endpointRedexUnionSubject_coreStepReducesToType :
    RawTerm.reduceOnce endpointRedexUnionSubject
      = some (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := rfl

end FX1Poly.FX0CrossCheck
