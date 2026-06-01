import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves

/-! # FX1Poly/Typed/ReducibleTypeAtAllLevelsInduction
    — level-irrelevance by induction on the reducibility derivation, the Π-former arm isolated

The formation-FT cons-arm's residual obstruction (after `ReducibleTypeAtAllLevelsLeaves`) is type-level
positive level-irrelevance restricted to Π-FORMER argument types: `IsReducibleTypeAt n (Π D C) →
IsReducibleTypeAtAllLevels (Π D C)`.  This file performs the level-irrelevance INDUCTION over the whole
`ReducibleTypeStep` derivation and discharges EVERY arm except `piType` from already-shipped pieces, so the
entire obstruction is reduced to ONE explicit hypothesis (the Π-former arm), proved unconditionally for the
other four cases:

  * `whnfExpand` — a redex inherits its weak-head contractum's reducibility; the IH gives the contractum at
    all levels, then `IsReducibleTypeAtAllLevels.headExpand` lifts back across the one weak-head step.  This
    is what extends the non-Π discharge from weak-head-NORMAL arguments to ARBITRARY (redex-carrying) ones.
  * `neutral` — a weak-head-normal non-Π non-universe code is all-levels reducible unconditionally
    (`ofWeakHeadNormalNonPiNonUniverse`).
  * `universeCode` — a universe code is all-levels reducible unconditionally (`ofUniverseCode`).
  * `ofPointwiseIff` — the inner derivation is on the SAME type code, so its IH is exactly the goal.
  * `piType` — supplied by the caller as `piArm`; this is the SOLE open case (the domain-candidate
    level-mismatch — `ReducibleTypeStep.existsCongr`'s degenerate base — reappearing here as the Π-former
    arm of the induction).

So `ofReducibleTypeStep` is the inductive backbone of level-irrelevance: a proof of the Π-former case alone
(`piArm`) completes type-level level-irrelevance for every reducible type, hence the cons-arm universe
domain, hence the formation fundamental theorem.

## Zero-axiom verification

A single `induction` on `ReducibleTypeStep` with a level-independent motive (`IsReducibleTypeAtAllLevels
typeCode`); every arm is one prior lemma or the `piArm`/IH.  The full (non-partial) induction with a
level-independent motive avoids the indexed-match `propext` leak.  Verified `#print axioms` clean: no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Level-irrelevance by induction on the reducibility derivation, Π-former arm isolated.**  Every
`ReducibleTypeStep` arm but `piType` is discharged unconditionally (redex via `headExpand`, neutral / data
former via `ofWeakHeadNormalNonPiNonUniverse`, universe via `ofUniverseCode`, congruence via the IH); the
`piType` arm is the supplied `piArm` hypothesis — the sole remaining open case of type-level level-
irrelevance. -/
theorem IsReducibleTypeAtAllLevels.ofReducibleTypeStep {scope : Nat}
    {lower : RawTerm scope → (RawTerm scope → Prop) → Prop}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStep lower domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStep lower (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        IsReducibleTypeAtAllLevels domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument)) →
        IsReducibleTypeAtAllLevels
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lower typeCode candidate) :
    IsReducibleTypeAtAllLevels typeCode := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact IsReducibleTypeAtAllLevels.headExpand weakHeadStep reductInductiveHypothesis
  | neutral noWeakHeadStep notPiType notUniverse =>
      exact IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        noWeakHeadStep notPiType notUniverse
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      exact piArm codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      exact IsReducibleTypeAtAllLevels.ofUniverseCode
  | ofPointwiseIff _innerReducible _pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis

/-- **The `IsReducibleTypeAt`-level (existential) form.**  A type reducible at any single level is reducible
at all levels, given the Π-former arm at that level's lower relation — the consumer-facing shape feeding the
universe-domain reduction (`ofUniverseMemberUnderTypeLevelIrrelevance`). -/
theorem IsReducibleTypeAtAllLevels.ofReducibleAtLevel {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeAt level domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeAt level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        IsReducibleTypeAtAllLevels domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument)) →
        IsReducibleTypeAtAllLevels
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    (reducible : IsReducibleTypeAt level typeCode) :
    IsReducibleTypeAtAllLevels typeCode := by
  obtain ⟨candidate, reducibleAtLevel⟩ := reducible
  cases level with
  | zero => exact IsReducibleTypeAtAllLevels.ofReducibleTypeStep piArm reducibleAtLevel
  | succ predLevel => exact IsReducibleTypeAtAllLevels.ofReducibleTypeStep piArm reducibleAtLevel

end FX1Poly.Typed
