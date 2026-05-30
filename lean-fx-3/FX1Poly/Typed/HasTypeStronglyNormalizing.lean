import FX1Poly.Typed.HasType
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/HasTypeStronglyNormalizing
    — the fundamental theorem (typed SN) for the current typing fragment

`HasType.isStronglyNormalizing` is the M10 fundamental theorem — *every
well-typed term is strongly normalizing* — for the current `HasType` fragment
(`var` / `conv` / `universeFormation`).  At this fragment it is a direct 3-arm
induction, because every subject is either a leaf (`var index`,
`universeCodeCell e flag`) or is left unchanged by `conv`; no redex can appear
yet.  No reducibility predicate is needed here: the reducibility tower (#422)
is required only once genuine term-level applications (`app f a`, which can
β-reduce) become well-typed (#444) — leaf and code/constructor subjects extend
via the already-shipped constructor-SN closures.

## Why now — the typed-coherence payoff

The Newman machinery is already closed in lean-fx-3:
`Conv.trans_of_middle_accessible` (StepStarConfluence.lean) derives
`Conv`-transitivity through any *strongly-normalizing middle term* alone (the
source-local Newman bridge — global SN, false by Ω, is not needed).  Feeding it
`IsType.isStronglyNormalizing` gives `Conv.trans` for any well-formed middle
type — the lemma that unblocks uniqueness-of-typing (#469) and inversion
(#454).  So this fragment-level fundamental theorem is not a throwaway: its
statement is permanent and its leaf/code arms persist; only a future `app` arm
will route through reducibility instead of direct induction.

## Zero-axiom verification

Induction on the typing derivation + the shipped leaf-SN lemmas
(`var_isStronglyNormalizing`, `universeCode_isStronglyNormalizing`) + the
proven `Conv.trans_of_middle_accessible`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The fundamental theorem for the current fragment: every well-typed term is
strongly normalizing.  `var` and `universeFormation` subjects are leaves (SN by
the shipped leaf lemmas); `conv` leaves the subject unchanged (SN by the
premise's induction hypothesis). -/
theorem HasType.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  induction typed with
  | var index =>
      exact StepStar.var_isStronglyNormalizing index
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise _ihReclassifier =>
      exact ihTypedPremise
  | universeFormation levelExpr flag =>
      exact StepStar.universeCode_isStronglyNormalizing (levelExpr, flag)

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
