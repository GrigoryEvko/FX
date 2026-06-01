import FX1Poly.Typed.HasType
import FX1Poly.Typed.HasTypeSubjectReduction
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/HasTypeStronglyNormalizing
    — the fundamental theorem (typed SN) for the native pi/sigma-formation HasType core

`HasType.isStronglyNormalizing` is the fundamental theorem — *every
well-typed term is strongly normalizing* — for the native pi/sigma-formation `HasType` core
(`var` / `conv` / `universeFormation` / `piFormation` / `sigmaFormation`).  At
this fragment every well-typed subject is NON-STEPPING
(`HasType.subjectHasNoStep`), so SN is immediate: a term with no outgoing `Step`
is `Acc`-essible.  No reducibility predicate is needed here: the reducibility
tower (#422) is required only when genuine term-level applications (`app f a`,
which can β-reduce) become well-typed — leaf and code/constructor subjects
extend via the constructor-SN closures.

## The typed-coherence payoff

`Conv.trans_of_middle_accessible` (StepStarConfluence.lean) derives
`Conv`-transitivity through any *strongly-normalizing middle term* alone (the
source-local Newman bridge — global SN, false by Ω, is not needed).  Feeding it
`IsType.isStronglyNormalizing` gives `Conv.trans` for any well-formed middle
type — the lemma uniqueness-of-typing (#469) and inversion (#454) consume.  The
statement is permanent; a redex-bearing `app` arm routes through reducibility
instead of no-step.

## Zero-axiom verification

The no-step invariant `HasType.subjectHasNoStep` fed to
`StepStar.isStronglyNormalizing_of_noStep` + the proven
`Conv.trans_of_middle_accessible`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The fundamental theorem for the native pi/sigma-formation HasType core: every well-typed term is
strongly normalizing.  Since every well-typed subject is NON-STEPPING
(`HasType.subjectHasNoStep` — including a `piTyCodeCell` once its typed children
are normal), strong normalization is immediate: a term with no outgoing `Step`
is trivially `Acc`-essible (`StepStar.isStronglyNormalizing_of_noStep`).  The
no-step invariant absorbs the Π / Σ formers — no per-arm induction and no Π
SN-closure lemma needed.  A redex-bearing `app` arm, whose subject genuinely
steps, would route through reducibility instead of no-step. -/
theorem HasType.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject :=
  StepStar.isStronglyNormalizing_of_noStep typed.subjectHasNoStep

/-- A well-formed type is strongly normalizing — the validity-flavoured
corollary that the typed `Conv.trans` consumes.  `IsType` exposes a typing
derivation whose subject is the type itself, so this is just
`HasType.isStronglyNormalizing` on that witness. -/
theorem IsType.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsType profile context classifier) :
    StepStar.IsStronglyNormalizing classifier := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact typed.isStronglyNormalizing

/-- Typed `Conv` transitivity through a well-formed middle type.  Specializes
the source-local Newman bridge `Conv.trans_of_middle_accessible` to a middle
term whose strong normalization comes from validity
(`IsType.isStronglyNormalizing`).  This is the transitivity uniqueness-of-typing
(#469) and inversion (#454) need: conv chains collapse through any well-formed
type without a global-SN assumption. -/
theorem Conv.trans_of_typedMiddle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType middleType lastType : RawTerm scope}
    (middleIsType : IsType profile context middleType)
    (firstConv : Conv firstType middleType)
    (middleConv : Conv middleType lastType) :
    Conv firstType lastType :=
  Conv.trans_of_middle_accessible middleIsType.isStronglyNormalizing
    firstConv middleConv

end FX1Poly.Typed
