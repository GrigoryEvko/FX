import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedUniformReducible
    — the uniform-candidate-above-threshold motive: the #752 strengthening (SN-D5-piArm foundation toward SN-043)

The composite-dependent-domain piArm (#752, the lone deep residual of the denote SN-043 route) is the piType
arm of the level-irrelevance induction `IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote`.  That arm
is CIRCULAR under the all-levels motive: its codomain inductive hypothesis is gated on the SOURCE domain
candidate, but assembling the Π at a target level needs membership in the LEVEL's domain candidate, and equating
the two across levels is domain member-stability — the very content being proved.

THE FIX (this file's reason for existing): STRENGTHEN the motive from all-levels-reducibility (a per-level
candidate, varying) to `UniformlyReducibleAboveDenote` — a SINGLE candidate that is the type's candidate at
EVERY level strictly above a threshold.  Under this stronger motive the piType arm's domain IH supplies a
UNIFORM domain candidate (the same set at every level above the domain's threshold), so the codomain
domain-membership gate transfers across levels for free — breaking the circularity.  This is the standard
"strengthen the induction hypothesis" move for the impredicative Tait/Girard candidate construction; the
uniform candidate is exactly the saturated reducibility set.

This file ships the motive and the three EASY backbone arms — the leaves and head-expansion, all of which hold
at a uniform candidate without any cross-level coordination:
  * `ofNeutral` — threshold 0, candidate `IsStronglyNormalizing` (the `neutral` constructor is level-independent);
  * `ofUniverseCode` — threshold `denote levelExpr env`, candidate the level-independent decode-set
    (`universeMembership_levelIrrelevant`: above the threshold the universe candidate is the fixed
    `fun m => SN m ∧ IsReducibleTypeAtDenote env (denote levelExpr env) m`);
  * `headExpand` — a redex inherits its weak-head contractum's uniform candidate at the same threshold (rewrap
    each level through the level-independent `whnfExpand` constructor).

This file ships the motive, the three EASY backbone arms, AND the backbone INDUCTION
`ofReducibleTypeStepDenote` — a verbatim mirror of the all-levels `IsReducibleTypeAtAllDenoteLevels.\
ofReducibleTypeStepDenote`, the same 5-arm dispatch over `ReducibleTypeStepDenote` (whnfExpand→`headExpand`,
neutral→`ofNeutral`, universeCode→`ofUniverseCode`, ofPointwiseIff→IH absorbed by the motive's `∃ candidate`,
piType→the supplied `piArm`), with the uniform motive carried through.

REMAINING for #752 (next ticks): the load-bearing piType `piArm` — its obstruction is DEEPER than one
motive-swap.  The uniform DOMAIN candidate dissolves the source-vs-target candidate mismatch (determinism at the
concrete source level equates the uniform candidate with the source candidate gating the codomain IH).  But the
CODOMAIN side has a THRESHOLD-SWAP obstruction: the codomain IH gives, per argument, a threshold
`codThreshold(arg)` that VARIES with the argument, and a single Π threshold must dominate them all — an `∃∀ /
∀∃` swap with no uniform bound in general.

CORRECTION (do not re-propose): a prior note suggested the bound exists because "a type reducible at level `lvl`
contains only universe codes that decode `< lvl`".  That is FALSE — `Type@huge` is a reducible type at EVERY
level (`IsReducibleTypeAtAllDenoteLevels.ofUniverseCode`, the universe arm fires unconditionally with a possibly
degenerate candidate), so reducibility does NOT bound a type code's syntactic universe content.  The
threshold-swap is therefore genuine for DEPENDENT composite codomains and needs a different technique (the
ValidTyping-derivation-level-indexed route, or a structural-on-code recursion that handles substitution).

This file's `nonDependentArrow` discharges the slice where the obstruction VANISHES: a NON-dependent codomain
`weaken codomainBase` substitutes to the constant `codomainBase` (independent of the argument), so there is a
SINGLE codomain threshold — the Π threshold is just `domThreshold + codomainThreshold`, no per-argument swap.
So the backbone is the inductive scaffold; the non-dependent piArm is unconditional; the DEPENDENT composite
piArm remains the deep brick.

## Zero-axiom verification

A `∃`-packaged `def`, three leaf arms (two anonymous-constructor; `headExpand` rewraps via `whnfExpand`), one
`induction` on `ReducibleTypeStepDenote` with the level-independent motive `UniformlyReducibleAboveDenote env
typeCode` (avoiding the indexed-match propext leak, exactly as the all-levels backbone does), and the
non-dependent arrow piArm (`piType` + the weaken-cancellation `rw`).  No `funext`.  GOTCHA recorded: the
non-dependent arrow's Π threshold uses `domThreshold + codomainThreshold` with `Nat.le_add_left/right`, NOT
`max` with `Nat.le_max_left/right` — the `Nat.le_max_*` lemmas leak `propext` in this Init-only setting, so the
`+`-with-`Nat.le_add_*` bound is the zero-axiom route.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The uniform-candidate-above-threshold motive.**  One fixed candidate is the type code's candidate at every
ambient level strictly above a threshold.  The strengthening of `IsReducibleTypeAtAllDenoteLevels` (per-level
candidate) that breaks the piType circularity in the #752 level-irrelevance proof: above the threshold the
domain candidate is UNIFORM, so the codomain domain-membership gate transfers across levels. -/
def UniformlyReducibleAboveDenote {scope : Nat} (env : Nat → Nat) (typeCode : RawTerm scope) : Prop :=
  ∃ (threshold : Nat) (candidate : RawTerm scope → Prop),
    ∀ level : Nat, threshold < level → ReducibleTypeAtDenote env level typeCode candidate

/-- **Neutral leaf.**  A weak-head-normal non-Π non-universe code is uniformly reducible above threshold 0 with
the strong-normalization candidate — the `neutral` constructor does not reference the level family. -/
theorem UniformlyReducibleAboveDenote.ofNeutral {scope : Nat} {env : Nat → Nat}
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    UniformlyReducibleAboveDenote env typeCode :=
  ⟨0, IsStronglyNormalizing,
    fun _level _habove => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse⟩

/-- **Universe leaf.**  `Type@levelExpr` is uniformly reducible above threshold `denote levelExpr env` with the
level-independent decode-set candidate `fun m => SN m ∧ IsReducibleTypeAtDenote env (denote levelExpr env) m`
(`universeMembership_levelIrrelevant`). -/
theorem UniformlyReducibleAboveDenote.ofUniverseCode {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    UniformlyReducibleAboveDenote env
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) :=
  ⟨LevelExpr.denote levelExpr env,
    (fun member : RawTerm scope => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member),
    fun level habove => universeMembership_levelIrrelevant env level levelExpr flag habove⟩

/-- **Weak-head-expansion arm.**  A redex inherits its weak-head contractum's uniform reducibility at the SAME
threshold and candidate — rewrap each level through the level-independent `whnfExpand` constructor. -/
theorem UniformlyReducibleAboveDenote.headExpand {scope : Nat} {env : Nat → Nat}
    {typeCode reduct : RawTerm scope} (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductUniform : UniformlyReducibleAboveDenote env reduct) :
    UniformlyReducibleAboveDenote env typeCode := by
  obtain ⟨threshold, candidate, reducibleAbove⟩ := reductUniform
  exact ⟨threshold, candidate,
    fun level habove => ReducibleTypeStepDenote.whnfExpand weakHeadStep (reducibleAbove level habove)⟩

/-- **The consumable interface: uniform reducibility ⟹ is-a-reducible-type above the threshold.**  Drops the
specific uniform candidate to mere existence (`IsReducibleTypeAtDenote`), exposing the threshold so a consumer
(e.g. the A2 ambient-level bridge `universeMemberReducibleAtLevel`) can read "reducible at every level above the
threshold" without committing to a candidate.  This is the face the uniform backbone presents once the piArm
lands: a consumer that only needs reducibility at a high-enough ambient level instantiates this at that level.
Note this is the WEAKER all-levels-EXISTENCE projection valid only ABOVE the threshold — it is NOT the full
`IsReducibleTypeAtAllDenoteLevels` (which demands all levels including ≤ threshold, where a universe code's
candidate is degenerate/empty); below-threshold reducibility is leaf-specific and not provided by the motive. -/
theorem UniformlyReducibleAboveDenote.isReducibleTypeAboveThreshold {scope : Nat} {env : Nat → Nat}
    {typeCode : RawTerm scope} (uniform : UniformlyReducibleAboveDenote env typeCode) :
    ∃ threshold : Nat, ∀ level : Nat, threshold < level → IsReducibleTypeAtDenote env level typeCode := by
  obtain ⟨threshold, candidate, reducible⟩ := uniform
  exact ⟨threshold, fun level habove => ⟨candidate, reducible level habove⟩⟩

/-- **Uniform level-irrelevance by induction on the denote-keyed reducibility derivation, Π arm isolated.**
The `UniformlyReducibleAboveDenote`-motive analogue of `IsReducibleTypeAtAllDenoteLevels.\
ofReducibleTypeStepDenote`: every `ReducibleTypeStepDenote` arm but `piType` is discharged unconditionally
(redex via `headExpand`, neutral via `ofNeutral`, universe via `ofUniverseCode`, the `ofPointwiseIff`
congruence via the induction hypothesis on the SAME code — absorbed by the motive's `∃ candidate`), and the
`piType` arm is the supplied `piArm` (general over the domain).  The level-independent motive
`UniformlyReducibleAboveDenote env typeCode` makes the full (non-partial) induction propext-clean — the same
discipline the all-levels backbone uses.

This is the inductive scaffold of the #752 (composite-dependent-domain level-irrelevance) discharge under the
strengthened uniform motive: a proof of the uniform `piArm` alone completes uniform level-irrelevance for every
denote-reducible type.  The `piArm`'s domain inductive hypothesis is `UniformlyReducibleAboveDenote env
domainCode` (a SINGLE candidate above a threshold), which is exactly the strengthening that dissolves the
source-vs-target domain candidate mismatch (via determinism at the concrete source level); the residual deep
obstruction is the codomain threshold-swap, documented in the module header. -/
theorem UniformlyReducibleAboveDenote.ofReducibleTypeStepDenote {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        UniformlyReducibleAboveDenote env domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          UniformlyReducibleAboveDenote env (RawTerm.subst0 codomainCode argument)) →
        UniformlyReducibleAboveDenote env
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    UniformlyReducibleAboveDenote env typeCode := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact UniformlyReducibleAboveDenote.headExpand weakHeadStep reductInductiveHypothesis
  | neutral noWeakHeadStep notPiType notUniverse =>
      exact UniformlyReducibleAboveDenote.ofNeutral noWeakHeadStep notPiType notUniverse
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      exact piArm codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      exact UniformlyReducibleAboveDenote.ofUniverseCode env levelExpr flag
  | ofPointwiseIff _innerReducible _pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis

/-- **Uniform non-dependent-arrow `piArm` — the unconditional slice of #752 in the uniform motive.**  The simple
arrow `domainCode → codomainBase` (= `piTyCodeCell domainCode (RawTerm.weaken codomainBase)`) is uniformly
reducible above `domThreshold + codomainThreshold` from the domain and base codomain being uniformly reducible
ALONE — no member-extension, no composite-domain piArm.  The threshold-swap that blocks the general dependent
piArm VANISHES: the codomain `weaken codomainBase` substitutes to the CONSTANT `codomainBase`
(`RawTerm.weaken_subst_singleton`, independent of the argument), so there is a SINGLE codomain threshold and the
Π threshold is just the sum — no per-argument supremum.  The uniform-motive twin of the all-levels
`IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain`. -/
theorem UniformlyReducibleAboveDenote.nonDependentArrow {scope : Nat} (env : Nat → Nat)
    {domainCode codomainBase : RawTerm scope}
    (domainUniform : UniformlyReducibleAboveDenote env domainCode)
    (codomainUniform : UniformlyReducibleAboveDenote env codomainBase) :
    UniformlyReducibleAboveDenote env (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) := by
  obtain ⟨domThreshold, domainCandidate, domainReducible⟩ := domainUniform
  obtain ⟨codomainThreshold, codomainCandidate, codomainReducible⟩ := codomainUniform
  refine ⟨domThreshold + codomainThreshold,
    (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))),
    fun level habove => ?_⟩
  refine ReducibleTypeStepDenote.piType (domainCandidate := domainCandidate)
    (fun _argument => codomainCandidate)
    (domainReducible level (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) habove))
    (fun argument _argumentInDomain => ?_)
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainReducible level (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) habove)

/-- **Universe-domain non-dependent arrow (uniform motive).**  `Type@levelExpr → codomainBase` is uniformly
reducible whenever the base codomain is — the uniform-motive twin of `IsReducibleTypeAtAllDenoteLevels.\
universeDomainNonDependentArrow`, reaching past the universe-domain wall (a universe domain has no
member-extension, but the non-dependent codomain makes member-extension unnecessary). -/
theorem UniformlyReducibleAboveDenote.universeDomainNonDependentArrow {scope : Nat} (env : Nat → Nat)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {codomainBase : RawTerm scope}
    (codomainUniform : UniformlyReducibleAboveDenote env codomainBase) :
    UniformlyReducibleAboveDenote env
      (piTyCodeCell (universeCodeCell levelExpr flag) (RawTerm.weaken codomainBase)) :=
  UniformlyReducibleAboveDenote.nonDependentArrow env
    (UniformlyReducibleAboveDenote.ofUniverseCode env levelExpr flag) codomainUniform

end FX1Poly.Typed
