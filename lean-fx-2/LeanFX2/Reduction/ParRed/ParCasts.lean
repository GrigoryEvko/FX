import LeanFX2.Reduction.ParRed.ParInductive.Inductive

/-! # LeanFX2.Reduction.ParRed.ParCasts

Propositional-transport helpers for the six index positions of
`Step.par`: source type, target type, source raw, target raw,
source term, target term.  Each helper rewrites one index via an
equality hypothesis while preserving the `Step.par` witness.

## Root status

Zero-axiom — pure `cases` on equality. -/

namespace LeanFX2


/-! ## Cast helpers — propositional transport for indices. -/

theorem Step.par.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact parallelStep

theorem Step.par.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact parallelStep

/-- Cancellation dual of `castTargetType`: a `Step.par` whose target is a
`typeEquality ▸ targetTerm` reduces to one whose target is the bare `targetTerm`.
Needed by the `betaSndPair` rename-equivariance arms, where the constructor forces
the target into the `subst0`-distributed type `secondType.rename·.subst0 …` while the
goal wants it at the renamed-original `(secondType.subst0 …).rename ρ` — the two
agree only via `Ty.subst0_rename_commute` (a type INDEX), and the renamed argument
must be presented to the constructor pre-cast, leaving exactly one residual cast on
the output to peel.  Zero-axiom — `cases` on the type equality collapses the `▸`. -/
theorem Step.par.castTargetType_cancel
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    (targetTerm : Term context targetTypeOriginal targetRaw)
    (parallelStep : Step.par sourceTerm (typeEquality ▸ targetTerm)) :
    Step.par sourceTerm targetTerm := by
  cases typeEquality
  exact parallelStep

/-- Cancellation dual of `castSourceType`: a `Step.par` whose source is a
`typeEquality ▸ sourceTerm` reduces to one whose source is the bare `sourceTerm`.
Source-side mirror of `castTargetType_cancel`. -/
theorem Step.par.castSourceType_cancel
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    (sourceTerm : Term context sourceTypeOriginal sourceRaw)
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par (typeEquality ▸ sourceTerm) targetTerm) :
    Step.par sourceTerm targetTerm := by
  cases typeEquality
  exact parallelStep

/-- HEq-bridged target type cancel: a `Step.par` whose target lives at one type
reduces to one whose target lives at a propositionally-equal type, given a `HEq`
witnessing the two targets agree.  Unlike `castTargetType_cancel` (which forces
Lean to UNIFY a `▸`-cast against the supplied `Step.par`'s target — impossible when
the cast proof is a metavariable, the `betaFunextReflAppDeep` situation), this
takes the bridging `HEq` as DATA supplied at the call site.  Lean then only
defeq-CHECKS the supplied `HEq` against the step's target — proof-irrelevance makes
the check succeed regardless of which propositional proof built the original cast.
Proof: `cases` the type equality (homogenizing the two targets) then `cases` the
now-homogeneous `HEq`.  Zero-axiom. -/
theorem Step.par.castTargetTypeHeq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal : Term context targetTypeOriginal targetRaw}
    {targetReplacement : Term context targetTypeReplacement targetRaw}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    (targetHeq : HEq targetReplacement targetOriginal)
    (parallelStep : Step.par sourceTerm targetOriginal) :
    Step.par sourceTerm targetReplacement := by
  cases typeEquality
  cases targetHeq
  exact parallelStep

theorem Step.par.castSourceRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRawOriginal sourceRawReplacement targetRaw : RawTerm scope}
    (rawEquality : sourceRawOriginal = sourceRawReplacement)
    {sourceTerm : Term context sourceType sourceRawOriginal}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par (rawEquality ▸ sourceTerm) targetTerm := by
  cases rawEquality
  exact parallelStep

theorem Step.par.castTargetRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRawOriginal targetRawReplacement : RawTerm scope}
    (rawEquality : targetRawOriginal = targetRawReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRawOriginal}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par sourceTerm (rawEquality ▸ targetTerm) := by
  cases rawEquality
  exact parallelStep

theorem Step.par.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (parallelStep : Step.par sourceOriginal targetTerm) :
    Step.par sourceReplacement targetTerm := by
  cases sourceEquality
  exact parallelStep

theorem Step.par.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (parallelStep : Step.par sourceTerm targetOriginal) :
    Step.par sourceTerm targetReplacement := by
  cases targetEquality
  exact parallelStep


/-! ## Heterogeneous source/target casts.

The six `Eq`-based helpers above transport ONE index of a single term, or
swap a term for a propositionally-equal one at the SAME indices.  They cannot
bridge two terms that live at DIFFERENT raw indices — the situation that arises
in the typed rename-equivariance arms for eliminators carrying a `pathLam
(_.weaken)` payload (`transpReflBeta`, `hcompBeta`, …), where the goal's
naturally-renamed argument has raw `(_.weaken).rename rho.lift` while the
constructor pins it at `(_.rename rho).weaken`.  The two are equal only via
`RawTerm.weaken_rename_commute`, which sits on a type INDEX, so the terms differ
heterogeneously (`HEq`, not `Eq`).

These two helpers close that gap: given the raw-index equality AND a `HEq`
between the two terms, transport the `Step.par`.  Proof is `subst` the raw
equality (which makes the two index-types defeq) then `cases` the now-homogeneous
`HEq` — zero-axiom, no `propext` / `Quot.sound` / `Classical.choice`. -/

theorem Step.par.castSourceTermHeq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRawOriginal sourceRawReplacement targetRaw : RawTerm scope}
    (rawEquality : sourceRawOriginal = sourceRawReplacement)
    {sourceOriginal : Term context sourceType sourceRawOriginal}
    {sourceReplacement : Term context sourceType sourceRawReplacement}
    {targetTerm : Term context targetType targetRaw}
    (sourceHeq : HEq sourceOriginal sourceReplacement)
    (parallelStep : Step.par sourceOriginal targetTerm) :
    Step.par sourceReplacement targetTerm := by
  cases rawEquality
  cases sourceHeq
  exact parallelStep

theorem Step.par.castTargetTermHeq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRawOriginal targetRawReplacement : RawTerm scope}
    (rawEquality : targetRawOriginal = targetRawReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal : Term context targetType targetRawOriginal}
    {targetReplacement : Term context targetType targetRawReplacement}
    (targetHeq : HEq targetOriginal targetReplacement)
    (parallelStep : Step.par sourceTerm targetOriginal) :
    Step.par sourceTerm targetReplacement := by
  cases rawEquality
  cases targetHeq
  exact parallelStep


end LeanFX2
