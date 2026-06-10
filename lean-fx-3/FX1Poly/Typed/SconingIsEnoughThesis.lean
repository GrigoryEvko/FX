import FX1Poly.Typed.GluedModelModalFragment
import FX1Poly.Typed.ClosedStronglyNormalizing

/-! # FX1Poly/Typed/SconingIsEnoughThesis
    — ★ the Leg-1 capstone: ONE sconing functor yields canonicity, normalization, AND parametricity (SN-110, #613)

The BKS thesis ("sconing is enough", FSCD 2023) as ONE theorem over the shipped substrate, closing the
O-NORM ladder's Leg-1 arc (SN-083…SN-096 + ONORM-M1):

  * ★ `GluedTypeCell.sconingIsEnough` — **the thesis theorem**: for EVERY glued type (every point of
    the glued model — the SN-091 Π/Σ/universe lifts, the ONORM-M1 modality lifts, and any future
    lift), ONE fundamental obligation yields all three metatheorems as projections: canonicity
    (strong normalization), normalization (reaches a normal form), and unary parametricity (the
    term satisfies its type's relational interpretation).  Proved by the SN-096 package — the three
    legs are the package's three fields applied to the SAME hypothesis.
  * `sconingIsEnough_atMembership` — non-vacuity: instantiating well-typedness as scone membership
    itself (`fundamental := id`) yields the real triple for every computable term — the thesis is
    not vacuous over an empty typing predicate.
  * ★ `HasTypeDescPi.closedSconingTriple` — **the DISCHARGED instance**: for the closed grown
    fragment the fundamental is a THEOREM, not a hypothesis — every closed well-typed term is
    strongly normalizing (BFT-14), reaches a normal form (the SN-112 normalizer), AND is a
    bounded-reducible member of its classifier's interpretation (BFT-13, the discharged unary
    parametricity).  Zero hypotheses: the triple holds outright.
  * `HasTypeDescPi.openSconingPair` — the OPEN discharged form: over any well-formed context,
    canonicity + normalization hold outright (the open parametricity leg — an open-term membership
    statement — is the recorded follow-on, exactly the open extension `ClosedStronglyNormalizing`
    defers).
  * `sconingIsEnough_canonicityIsTaitComposition` — **the honesty pin** (`rfl`): the thesis's
    canonicity projection IS the Tait composition `CR1 ∘ fundamental` — Leg-1 is the categorical
    ORGANIZATION of the proven Tait content (`sconingSN_eq_taitComposition`, HCAP discipline), not
    an independent second proof of SN.

## The ONORM GO/NO-GO verdict (recorded per the #463 frontier-gate obligation)

**GO** — one functor does land all three metatheorems, at two strengths: hypothesis-driven for every
glued type (the thesis theorem), and fully discharged for the closed grown fragment (the closed
triple).  Three residuals, named honestly:

  1. **Per-fragment fundamentals.**  Outside the grown/formation/flat/standalone engine fragments,
     the fundamental obligations are explicit hypotheses (the modal fragment is statically untyped
     today — `modalTermFragment_isStaticallyUntypedToday`; the data VALUE-level refinements are
     discharged per classifier by the CAN-5 syntactic route, not by one uniform engine).
  2. **STC not consumed.**  The task's anticipated STC ladder (SN-098…102) did not feed this
     capstone — the BKS/Tait route landed first; sconing-via-STC remains the independent moonshot
     cross-check, tracked separately.
  3. **Live-signature totality.**  The lifts cover the former FAMILIES (Π/Σ/universe + the six
     modality formers) and the ten data-candidate families; a per-generator coverage gate over the
     full semantically-live signature is the recorded follow-on admission gate.

## Zero-axiom verification

Direct applications of the SN-096 package, the BFT-13/14 closed corollaries, the SN-043 open form,
and the shipped normalizer — plus one `rfl` identity.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- ★ **The sconing-is-enough thesis** (SN-110, the Leg-1 capstone): for every glued type, ONE
fundamental obligation yields all three metatheorems as projections — canonicity (strong
normalization), normalization (reaches a normal form), and unary parametricity (the term satisfies
its type's relational interpretation, and is strongly normalizing).  The three legs are the SN-096
package's three fields applied to the SAME hypothesis: one functor, one obligation, three
extractions. -/
theorem GluedTypeCell.sconingIsEnough {scope : Nat} (glued : GluedTypeCell (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term) :
    (∀ term : RawTerm (scope + 1), isWellTyped term → IsStronglyNormalizing term)
      ∧ (∀ term : RawTerm (scope + 1), isWellTyped term →
          ∃ normalForm : RawTerm (scope + 1),
            StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm)
      ∧ (∀ term : RawTerm (scope + 1), isWellTyped term →
          glued.computable term ∧ IsStronglyNormalizing term) :=
  ⟨fun term typed =>
      fxBksGluedMetatheoryPackage.canonicityTransfer glued fundamental term typed,
   fun term typed =>
      fxBksGluedMetatheoryPackage.normalizationTransfer glued fundamental term typed,
   fun term typed =>
      fxBksGluedMetatheoryPackage.parametricityTransfer glued fundamental term typed⟩

/-- **Non-vacuity**: instantiating well-typedness as scone MEMBERSHIP itself (`fundamental := id`)
yields the real triple for every computable term of every glued type — the thesis does not rest on
an empty typing predicate. -/
theorem sconingIsEnough_atMembership {scope : Nat} (glued : GluedTypeCell (scope + 1)) :
    (∀ term : RawTerm (scope + 1), glued.computable term → IsStronglyNormalizing term)
      ∧ (∀ term : RawTerm (scope + 1), glued.computable term →
          ∃ normalForm : RawTerm (scope + 1),
            StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm)
      ∧ (∀ term : RawTerm (scope + 1), glued.computable term →
          glued.computable term ∧ IsStronglyNormalizing term) :=
  glued.sconingIsEnough (fun _term member => member)

/-- ★ **The discharged instance of the thesis** — the closed grown fragment, ZERO hypotheses: every
closed well-typed term is strongly normalizing (BFT-14 `closedStronglyNormalizing`), reaches a
normal form (the shipped normalizer over that SN), AND is a bounded-reducible member of its
classifier's relational interpretation (BFT-13 `closedBoundedReducibleMember` — the discharged
unary parametricity).  Here the scone's fundamental is a theorem (the budget-discharged grown
fundamental theorem), so the triple holds outright — the strongest form of "sconing is enough" the
tree supports today. -/
theorem HasTypeDescPi.closedSconingTriple {profile : PolyProfile} (env : Nat → Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      subject classifier) :
    IsStronglyNormalizing subject
      ∧ (∃ normalForm : RawTerm 0,
          StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm)
      ∧ (∃ bound : Nat,
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) classifier)
            (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject)) :=
  have subjectNormalizing := typed.closedStronglyNormalizing
  ⟨subjectNormalizing,
   ⟨RawTerm.normalize subject subjectNormalizing,
    RawTerm.normalize_reducesTo subject subjectNormalizing,
    RawTerm.normalize_isStepNormalForm subject subjectNormalizing⟩,
   HasTypeDescPi.closedBoundedReducibleMember env typed⟩

/-- **The open discharged pair**: over any well-formed context, canonicity + normalization hold
outright for the grown engine (the SN-043 open form + the normalizer).  The open parametricity leg —
an open-term membership statement under a reducible closing environment — is the recorded follow-on,
exactly the open extension `ClosedStronglyNormalizing` defers. -/
theorem HasTypeDescPi.openSconingPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    IsStronglyNormalizing subject
      ∧ ∃ normalForm : RawTerm scope,
          StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm :=
  ⟨typed.stronglyNormalizingOfWfContextDesc contextWellFormed,
   typed.normalizationTransfer contextWellFormed⟩

/-- **The honesty pin** (`rfl`): the thesis's canonicity projection IS the Tait composition
`CR1 ∘ fundamental` — Leg-1 is the categorical ORGANIZATION of the proven Tait content
(`sconingSN_eq_taitComposition`, the HCAP triangulation discipline), not an independent second
proof of strong normalization. -/
theorem sconingIsEnough_canonicityIsTaitComposition {scope : Nat}
    (glued : GluedTypeCell (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term)
    (term : RawTerm (scope + 1)) (typed : isWellTyped term) :
    (glued.sconingIsEnough fundamental).1 term typed
      = glued.isCandidate.stronglyNormalizing (fundamental term typed) :=
  rfl

end FX1Poly.Typed
