import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateShapeValidity
import FX1Poly.Core.Metatheory.Reducibility.Candidates.FlatCodeTaitCandidate

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/FlatAndDataIntroArms
    — the flat-former validity (FTGEN-5, incl. equivCode) + the data-intro arm (FTGEN-9)

Two reachable-now FT pieces, both unconditional, wiring shipped Core lemmas to the descriptor:

  * **FTGEN-5 (flat-formation, incl. equivCode)** — `flatFormerCandidate g := flatCodeTaitCandidate g`
    (the kernel's `dataFlat`-arm candidate) is a Girard CR for every flat former (arrow/product/sum/either/
    equivCode), UNCONDITIONALLY (`flatCodeTaitCandidate_isReducibilityCandidate`).  In particular this closes
    the `equivCode` live-shape validity that FTGEN-2 left to the dependent arms — `equivCode`'s actual kernel
    candidate is valid with no premises.  (The descriptor's alternative `derivedUnfold` treatment, equiv⇒Σ,
    is the richer semantics deferred to EXT-4; this is the kernel's flat treatment.)

  * **FTGEN-9 (data-intro)** — `inductiveSaturatedIntro`: a constructor-headed normal value whose head is one
    of the shape's constructors lands in the `inductiveSaturated` candidate.  The data-introduction arm for
    the normal/nullary constructors (boolTrue/boolFalse/natZero/unit/interval0/interval1/optionNone/listNil),
    directly the kernel `dataTaitCandidate.memberOfValue`.  Constructors with reducible (non-normal) arguments
    are the recursive-intro extension (still FTGEN-9, deeper).

## Zero-axiom verification

Direct applications of the shipped, audited Core lemmas `flatCodeTaitCandidate_isReducibilityCandidate` and
`dataTaitCandidate.memberOfValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The flat former's candidate — the kernel `dataFlat`-arm candidate `flatCodeTaitCandidate` for a flat-code
former (arrow / product / sum / either / equivCode). -/
@[reducible] def flatFormerCandidate {scope : Nat} (generator : Generator) : RawTerm scope → Prop :=
  flatCodeTaitCandidate generator

/-- **★ FTGEN-5 — every flat former's candidate is valid, unconditionally.**  Instant from
`flatCodeTaitCandidate_isReducibilityCandidate`, uniform in the generator. -/
theorem flatFormerCandidate_valid {scope : Nat} (generator : Generator) :
    CandidateValidity (flatFormerCandidate (scope := scope) generator) :=
  flatCodeTaitCandidate_isReducibilityCandidate generator

/-- **★ `equivCode`'s kernel candidate is valid** — the live-shape validity FTGEN-2 deferred, closed
unconditionally via the flat-former route (`equivCode` is a flat data former). -/
theorem equivCodeCandidate_valid {scope : Nat} :
    CandidateValidity (flatFormerCandidate (scope := scope) .gen_equivCode) :=
  flatFormerCandidate_valid _

/-- **★ FTGEN-9 — the data-intro arm (normal constructors).**  A constructor-headed normal value whose head
is one of the `inductiveSaturated` shape's constructors is a member of that candidate.  Directly the kernel
`dataTaitCandidate.memberOfValue`; the introduction arm for the nullary / already-normal constructors. -/
theorem inductiveSaturatedIntro {scope : Nat}
    (constructors : List CandidateConstructorSpec) {value : RawTerm scope}
    (valueIsNormal : RawTerm.isStepNormalForm value)
    (valueHasConstructorHead : constructorHeadValue constructors value) :
    inductiveSaturatedCandidate constructors value :=
  dataTaitCandidate.memberOfValue valueIsNormal valueHasConstructorHead

end FX1Poly.Typed
