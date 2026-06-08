import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch (#752 backbone foundation): the STRONGER motive for denote level-irrelevance — a SINGLE uniform
candidate works at every level ABOVE a threshold. This is the strengthening that breaks the piType circularity:
the all-levels motive `IsReducibleTypeAtAllDenoteLevels` gives a per-level candidate (varies), but the piType
gate-transfer needs the domain candidate to be the SAME across levels — which `UniformlyReducibleAboveDenote`
provides. Leaf arms: neutral (candidate = SN, threshold 0, level-independent ctor) and universe Type@e
(candidate = the level-independent decode-set, threshold = denote e, via universeMembership_levelIrrelevant). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- A type code is uniformly denote-reducible above a threshold: one fixed candidate is its candidate at every
ambient level strictly above the threshold. The stronger member-stability motive for #752. -/
def UniformlyReducibleAboveDenote {scope : Nat} (env : Nat → Nat) (typeCode : RawTerm scope) : Prop :=
  ∃ (threshold : Nat) (candidate : RawTerm scope → Prop),
    ∀ level : Nat, threshold < level → ReducibleTypeAtDenote env level typeCode candidate

/-- **Neutral leaf.** A weak-head-normal non-Π non-universe code is uniformly reducible above threshold 0 with
the strong-normalization candidate — the `neutral` constructor is level-independent. -/
theorem UniformlyReducibleAboveDenote.ofNeutral {scope : Nat} {env : Nat → Nat}
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    UniformlyReducibleAboveDenote env typeCode :=
  ⟨0, IsStronglyNormalizing,
    fun _level _ => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse⟩

/-- **Universe leaf.** `Type@levelExpr` is uniformly reducible above threshold `denote levelExpr env` with the
level-independent decode-set candidate (`universeMembership_levelIrrelevant`). -/
theorem UniformlyReducibleAboveDenote.ofUniverseCode {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    UniformlyReducibleAboveDenote env
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) :=
  ⟨LevelExpr.denote levelExpr env,
    (fun member : RawTerm scope => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member),
    fun level habove => universeMembership_levelIrrelevant env level levelExpr flag habove⟩

/-- **Weak-head-expansion arm.** A redex inherits its weak-head contractum's uniform reducibility at the SAME
threshold and candidate — rewrap each level through the level-independent `whnfExpand` constructor. -/
theorem UniformlyReducibleAboveDenote.headExpand {scope : Nat} {env : Nat → Nat}
    {typeCode reduct : RawTerm scope} (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductUniform : UniformlyReducibleAboveDenote env reduct) :
    UniformlyReducibleAboveDenote env typeCode := by
  obtain ⟨threshold, candidate, reducibleAbove⟩ := reductUniform
  exact ⟨threshold, candidate,
    fun level habove => ReducibleTypeStepDenote.whnfExpand weakHeadStep (reducibleAbove level habove)⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofNeutral
#print axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofUniverseCode
#print axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.headExpand
