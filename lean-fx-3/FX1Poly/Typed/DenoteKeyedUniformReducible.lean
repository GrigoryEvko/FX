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

REMAINING for #752 (next ticks): the backbone INDUCTION over `ReducibleTypeStepDenote` assembling these arms
(the `ofPointwiseIff` arm is absorbed by the motive's `∃ candidate`), and the load-bearing piType arm — where
the uniform domain candidate transfers the codomain gate.  Then `UniformlyReducibleAboveDenote ⟹
IsReducibleTypeAtAllDenoteLevels` discharges the `ofReducibleTypeStepDenote` piArm unconditionally, closing #752.

## Zero-axiom verification

A `∃`-packaged `def` plus three arms (two anonymous-constructor leaves; `headExpand` rewraps via `whnfExpand`).
No induction here (the backbone induction is the next brick), no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
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

end FX1Poly.Typed
