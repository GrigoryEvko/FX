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

## Why the `piArm` is a genuine fixpoint, not a clean lemma (frontier note)

The open `piArm` is dischargeable for a NEUTRAL / data-former domain (`piTypeOfNeutralDomain`: the domain
candidate is the level-independent `IsStronglyNormalizing`, so no mismatch).  The irreducible case is a
**universe domain** `Π (x : Type@e). C`, and it is a true fixpoint for a precise, structural reason — the
fuel model is too weak at its base, and the weakness PROPAGATES up every finite level:

  * `ReducibleTypeAt 0 = ReducibleTypeStep (fun _ _ => False)` (empty lower relation), so universe membership
    at fuel 0 is the EMPTY candidate (`IsReducibleMemberAt.universeCodeHasNoMemberAtZero` is the committed
    seed: no term inhabits `Type@e` at fuel 0).
  * Hence `Π (x : Type@e). C` is VACUOUSLY reducible at fuel 0 (empty domain ⇒ the codomain obligation is
    over an empty candidate), carrying NO information about `C` on actual members.  So
    `IsReducibleTypeAt 0 (Π Type@e C) → IsReducibleTypeAt 1 (…)` cannot be proved structurally: the level-0
    hypothesis is too weak to feed the level-1 codomain obligation.
  * The vacuity is not confined to level 0: universe membership at level `k` admits every code merely
    reducible-at-`(k-1)`, so the candidates at successive levels genuinely differ for universe codes, and the
    `existsCongr` inductive step (`StratifiedReducibleLevelCongr`) cannot bridge the `0 ↔ 1` base at ANY
    finite fuel.
  * The `piArm`'s structural IHs give `IsReducibleTypeAtAllLevels` for the domain and for the codomain under
    domain-candidate arguments — but the universe domain additionally needs the domain MEMBERS' OWN
    level-irrelevance (`piTypeOfDomainMemberExtension`'s member-extension premise), which is the whole theorem
    on codes that are NOT structurally smaller than `Π Type@e C`.  Circular ⇒ no clean induction.

CONCLUSION (recorded so this is not re-derived): the universe-domain `piArm` cannot be closed within the
external-`Nat`-fuel reducibility model.  It requires a NON-FUEL reformulation — reducibility well-founded on
the type code's structure (the members of `Type@e` are sub-codes), i.e. the Adjedj-style relation indexed by
the VALIDITY DERIVATION rather than an external fuel, threaded through the mutual term/type fundamental
theorem.  The entire reduction chain DOWN TO this one obligation is committed and gated; only the model-level
reformulation remains.

## Sharpened residual + the concrete non-fuel handle (frontier update)

The open case is even smaller than "universe-domain `piArm`": the NON-dependent universe-domain arrow
`Type@e → C` (codomain not using the bound variable) is ALREADY closed unconditionally
(`IsReducibleTypeAtAllLevels.universeDomainNonDependentArrow`, via the weaken-cancellation trick — the Π
candidate at each level reuses the codomain candidate directly, NO domain-member-extension needed).  So the
SOLE remaining obligation is the **dependent universe-domain Π** `Π (X : Type@e). C[X]` where `C` genuinely
uses `X` — impredicative dependent polymorphism (type families indexed by types).

Why no fuel/structural induction reaches it (the precise obstruction, re-confirmed): typeLevelIrrelevance is
consumed at `predLevel` possibly `0` (the member-decode of `IsReducibleMemberAt (predLevel+1) (Type@e) A`),
and `IsReducibleTypeAt 0 (Π (Type@e) C)` is VACUOUS (empty fuel-0 universe domain), carrying no information
about `C` on real members — so it cannot feed the non-vacuous level-`1+` codomain obligation.  Strong fuel
induction therefore fails at the base; structural induction on the code is circular (domain members are not
sub-codes of `Π (Type@e) C`).

The CONCRETE handle for the derivation-indexed LR (the measure to recurse on): the **universe LEVEL of the
type code**, not the external fuel.  A member `X : Type@e` is a type of universe level `≤ e`, strictly below
`Type@e`'s level `e+1 ≤ level (Π (Type@e) C)`.  So a well-founded recursion on the universe level (carried by
the validity derivation, e.g. `ValidTyping` / `HasTypeDescPi`) makes the domain members STRICTLY SMALLER —
their own level-irrelevance is then the IH, breaking the circularity that fuel and code-structure both hit.
Building that level-indexed (validity-derivation-threaded) reducibility relation is the committed next effort
(SN-006); this file's `piArm` is its single consumer.

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
