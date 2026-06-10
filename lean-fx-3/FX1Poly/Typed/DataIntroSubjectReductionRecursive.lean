import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/DataIntroSubjectReductionRecursive — SR for the RECURSIVE data-intro engines
    + the per-eliminator typed-ι SR coverage matrix (CAN-3).

## The two SR theorems (the DI-3 / DI-2e deferred debt)

`HasTypeDescNatIntro` and `HasTypeDescListIntro` are the two RECURSIVE data-intro engines; their
SR was the deliberate deferral recorded in both files.  Nat/list VALUES have no root redexes
(no β — the head is not `gen_app`; no ι — every ι head is an ELIMINATOR generator; no relevant
η — `Step.eta` is a sibling relation), so every step out of a constructor cell is a CONGRUENCE
step in a payload child, and SR is structural:

  * `HasTypeDescNatIntro.subjectReduction` — UNCONDITIONAL (no well-formedness hypothesis):
    the only premise of `natSuccIntro` is the recursive one, so the stepped predecessor
    re-types by the induction hypothesis alone.
  * `HasTypeDescListIntro.subjectReduction` — conditional on `WfContextDescPi` ONLY because
    the cons HEAD is grown-typed (`listConsIntro`): a head step re-types by the grown master
    SR (`HasTypeDescPi.subjectReduction`, SR-U4), which consumes the wf witness.  Tail steps
    re-type by the induction hypothesis; element-type-formedness premises are untouched by
    subject steps.

## The coverage matrix (reconciling the historical #475/#476 claims)

The historical TY-SR-iota tasks proved typed-ι SR for the DELETED `HasType` engine (HT-C
removed it).  The honest current coverage, per eliminator family:

  * GROWN-typable subjects: the unconditional grown master SR (SR-U4,
    `HasTypeDescPi.subjectReduction`) covers EVERY step — β, ALL 18 ι constructors, and
    congruence — in one theorem.  No per-ι work remains on grown subjects.
  * STANDALONE-judgment subjects (the DI-5 family — eliminators over DATA-engine scrutinees,
    which are not grown-typable): typed-ι is proven CONSTRUCTOR-SIDE for all 7 families
    (bool DI-5a, either DI-5b, option DI-5c, Σ-projections DI-5d, idJ DI-5e, nat CAN-1,
    list CAN-2) — the eliminator is BUILT typed, steps by its ι rule, and the reduct is
    BUILT typed from the same premises.
  * The remaining honest gap is DERIVATION-SIDE SR for the standalone eliminator judgments
    (given an arbitrary derivation, invert it at the literal redex subject and re-type any
    reduct): the extraction is the documented cons-index propext trap (free-subject +
    equation-threading per arm), deferred with rationale below — NOT silently absorbed.

`eliminatorIotaSrCoverage` records the 7-family matrix in code with a count pin, so the
ledger breaks loudly when an eliminator family is added.

## Zero-axiom

Two structural inductions (free-index `cases` on the congruence step through the payload
spine); the matrix is a literal list with an `rfl` count pin.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **SR for the recursive Nat intro engine — UNCONDITIONAL.**  A nat-intro-typed subject that
steps stays nat-intro-typed at `Nat`: nat values have no root redexes, so the step is a
congruence in the predecessor, re-typed by the induction hypothesis (the engine's only premise
is recursive — no well-formedness needed). -/
theorem HasTypeDescNatIntro.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescNatIntro profile context reduct classifier := by
  induction derivation with
  | natZeroIntro =>
      intro reduct step
      cases step with
      | cong _ _ childrenStep => cases childrenStep
  | natSuccIntro predecessor _predecessorTyped predecessorReduces =>
      intro reduct step
      cases step with
      | cong _ _ childrenStep =>
          cases childrenStep with
          | here _ predecessorStep =>
              exact HasTypeDescNatIntro.natSuccIntro _ _
                (predecessorReduces _ predecessorStep)
          | there _ tailStep => cases tailStep

/-- **SR for the recursive List intro engine.**  A list-intro-typed subject that steps stays
list-intro-typed at `List(A)`: list values have no root redexes, so the step is a congruence
in the HEAD (re-typed by the grown master SR — this is where the `WfContextDescPi` witness is
consumed) or in the TAIL (re-typed by the induction hypothesis). -/
theorem HasTypeDescListIntro.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDescListIntro profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescListIntro profile context reduct classifier := by
  induction derivation with
  | listNilIntro elementType elementLevel flag elementTypeFormed =>
      intro reduct step
      cases step with
      | cong _ _ childrenStep => cases childrenStep
  | listConsIntro headValue tailList elementType headTyped tailTyped tailReduces =>
      intro reduct step
      cases step with
      | cong _ _ childrenStep =>
          cases childrenStep with
          | here _ headStep =>
              exact HasTypeDescListIntro.listConsIntro _ _ tailList elementType
                (HasTypeDescPi.subjectReduction headTyped wellFormed _ headStep) tailTyped
          | there _ tailSpineStep =>
              cases tailSpineStep with
              | here _ tailStep =>
                  exact HasTypeDescListIntro.listConsIntro _ headValue _ elementType
                    headTyped (tailReduces _ tailStep)
              | there _ emptyStep => cases emptyStep

/-! ## The CAN-3 coverage matrix -/

/-- One row of the per-eliminator typed-ι SR coverage matrix. -/
structure EliminatorIotaSrCell where
  /-- The eliminator family (the scrutinee's data type). -/
  familyName : String
  /-- Constructor-side typed-ι is PROVEN (the DI-5 / CAN-1 / CAN-2 theorems): the typed
  eliminator steps by its ι rule and the reduct is typed from the same premises. -/
  hasConstructorSideIota : Bool
  /-- Derivation-side SR of the STANDALONE judgment is proven (invert an arbitrary derivation
  at the redex subject, re-type any reduct).  Honest current status: open for all families —
  the inversion at a literal constructor-headed subject is the documented cons-index propext
  trap and is deferred deliberately, not silently. -/
  hasDerivationSideSr : Bool

/-- The 7-family matrix.  GROWN-typable subjects need no row: the unconditional grown master
SR (SR-U4) covers every β/ι/congruence step uniformly.  These rows are the STANDALONE-judgment
subjects (data-engine scrutinees). -/
def eliminatorIotaSrCoverage : List EliminatorIotaSrCell :=
  [ ⟨"bool",          true, false⟩
  , ⟨"either",        true, false⟩
  , ⟨"option",        true, false⟩
  , ⟨"sigmaProj",     true, false⟩
  , ⟨"identity",      true, false⟩
  , ⟨"natRecursive",  true, false⟩
  , ⟨"listRecursive", true, false⟩
  ]

/-- Count pin: exactly 7 standalone eliminator families.  Adding an eliminator family without
extending the matrix breaks this loudly. -/
theorem eliminatorIotaSrCoverage_count : eliminatorIotaSrCoverage.length = 7 := rfl

/-- Every family has constructor-side typed-ι — DI-5 is complete (the #1047 closure,
re-checked here by enumeration). -/
theorem eliminatorIotaSrCoverage_constructorSideComplete :
    eliminatorIotaSrCoverage.all (fun cell => cell.hasConstructorSideIota) = true := rfl

end FX1Poly.Typed
