import FX1Poly.Typed.Metatheory.Denote.Core.DenoteKeyedUniformReducible

/-! # FX1Poly/Typed/DenoteKeyedCanonicalThreshold
    — the canonical-threshold reducibility motive: pin the threshold to the type's classifying level, dissolving
      the dependent-Π threshold-swap (#752 / SN-043)

`UniformlyReducibleAboveDenote` (the #752 strengthening) reduces the composite-dependent piArm to ONE residual
the module header of `DenoteKeyedUniformReducible` names precisely: the codomain inductive hypothesis gives, per
argument, an EXISTENTIAL threshold `codThreshold(arg)` that varies with the argument, and a single Π threshold
must dominate them all — an `∀arg ∃threshold → ∃threshold ∀arg` swap with no uniform bound from the bare IH.

THE FIX (this file): replace the existential threshold with a PINNED one.  `CandidateReducibleAboveDenote env
canonicalLevel typeCode candidate` says `candidate` is the type's reducibility candidate at every ambient level
strictly above the PARAMETER `canonicalLevel` — the threshold is supplied, not existentially chosen.  Once the
codomain reducibility is in this canonical form at a FIXED `codomainLevel`, the swap evaporates: the threshold is
already arg-independent, so the Π threshold is just `domainLevel + codomainLevel`, with no per-argument supremum.

Why the codomain's canonical level IS arg-independent (the #1674 finding): the codomain code's classifying
universe code is `universeCodeCell codomainLevel flag`, and `subst_universeCodeCell` (`rfl`) shows substitution
leaves it untouched — so `subst0 codomainCode arg` is classified at the SAME `codomainLevel` for every `arg`,
hence reducible above the SAME `denote codomainLevel env`.  This file proves the swap is resolvable; supplying
the codomain IH in canonical form from the validity derivation (where `codomainLevel` is read off
`piFormation`'s `codomainTyped`) is the next rung.

## What this file ships

  * `CandidateReducibleAboveDenote` — the threshold-pinned motive (candidate explicit).
  * `raiseThreshold` — monotone in the canonical level (raise to a common bound); `toUniform` — canonical ⟹
    the existential `UniformlyReducibleAboveDenote`.
  * the five leaf/structural arms in canonical form (`ofNeutral` / `ofDataEmpty` / `ofDataFlat` / `ofUniverseCode`
    / `headExpand`) — the canonical-motive analogues of the `UniformlyReducibleAboveDenote` leaves.
  * `piTyCode` ★ — the canonical dependent-Π arm: from the domain reducible above `domainLevel` and the codomain
    reducible above a FIXED `codomainLevel` (uniformly in the argument), the Π is reducible above
    `domainLevel + codomainLevel`.  No existential, no per-argument supremum — the threshold-swap RESOLVED.

This is unconditional on the codomain IH being canonical; it does NOT yet re-derive the backbone induction in
canonical form (that supplies the canonical codomain IH from typing — the next rung).  No overclaim: the deep
content here is that a PINNED codomain threshold makes the dependent-Π arm a one-line `piType` assembly.

## Zero-axiom verification

A threshold-pinned `def`; `raiseThreshold`/`toUniform` are direct; the leaf arms are the `ReducibleTypeStep
Denote` constructors at a fixed threshold (mirroring the `UniformlyReducibleAboveDenote` leaves); `piTyCode` is
one `ReducibleTypeStepDenote.piType` with the two component thresholds bounded by `Nat.le_add_right` /
`Nat.le_add_left` (NOT `Nat.le_max_*`, which leak `propext` in Init-only).  No `induction`, no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The canonical-threshold reducibility motive.**  `candidate` is the type code's reducibility candidate at
EVERY ambient level strictly above the PINNED `canonicalLevel` — the threshold is a parameter, NOT existentially
chosen as in `UniformlyReducibleAboveDenote`.  Killing the existential is what dissolves the dependent-Π
threshold-swap: a codomain reducible above a FIXED `canonicalLevel` (arg-independent, since its classifying
universe code is substitution-invariant — `subst_universeCodeCell`) contributes a single threshold to the Π. -/
def CandidateReducibleAboveDenote {scope : Nat} (env : Nat → Nat) (canonicalLevel : Nat)
    (typeCode : RawTerm scope) (candidate : RawTerm scope → Prop) : Prop :=
  ∀ level : Nat, canonicalLevel < level → ReducibleTypeAtDenote env level typeCode candidate

/-- **Raise the canonical threshold (monotone).**  Reducibility above a canonical level persists above any higher
level — fewer levels to cover.  The move that combines the domain and codomain canonical levels into a single
common bound for the Π. -/
theorem CandidateReducibleAboveDenote.raiseThreshold {scope : Nat} {env : Nat → Nat}
    {lowerLevel higherLevel : Nat} {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : CandidateReducibleAboveDenote env lowerLevel typeCode candidate)
    (levelLe : lowerLevel ≤ higherLevel) :
    CandidateReducibleAboveDenote env higherLevel typeCode candidate :=
  fun level habove => reducible level (Nat.lt_of_le_of_lt levelLe habove)

/-- **Forget the canonical level (canonical ⟹ uniform).**  A canonical-threshold witness is in particular
`UniformlyReducibleAboveDenote` — instantiate the existential threshold with the pinned canonical level. -/
theorem CandidateReducibleAboveDenote.toUniform {scope : Nat} {env : Nat → Nat}
    {canonicalLevel : Nat} {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : CandidateReducibleAboveDenote env canonicalLevel typeCode candidate) :
    UniformlyReducibleAboveDenote env typeCode :=
  ⟨canonicalLevel, candidate, reducible⟩

/-- **Neutral leaf (canonical at 0).**  A weak-head-normal non-Π non-universe non-empty non-flat code is reducible
above threshold 0 with the strong-normalization candidate — the level-independent `neutral` constructor. -/
theorem CandidateReducibleAboveDenote.ofNeutral {scope : Nat} {env : Nat → Nat}
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : typeCode.rootGenerator ≠ Generator.gen_emptyCode)
    (notFlat : typeCode.rootGenerator.isFlatDataCode = false) :
    CandidateReducibleAboveDenote env 0 typeCode IsStronglyNormalizing :=
  fun _level _habove =>
    ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty notFlat

/-- **Empty-code leaf (canonical at 0).**  `emptyTypeCell` is reducible above threshold 0 with the
head-expansion-closed empty Tait candidate. -/
theorem CandidateReducibleAboveDenote.ofDataEmpty {scope : Nat} {env : Nat → Nat} :
    CandidateReducibleAboveDenote env 0 (emptyTypeCell (scope := scope)) emptyTaitCandidate :=
  fun _level _habove => ReducibleTypeStepDenote.dataEmpty

/-- **Flat-code leaf (canonical at 0).**  A flat-data-code-rooted type cell is reducible above threshold 0 with
the pinned flat Tait candidate. -/
theorem CandidateReducibleAboveDenote.ofDataFlat {scope : Nat} {env : Nat → Nat}
    {typeCode : RawTerm scope} (flatPinned : typeCode.rootGenerator.isFlatDataCode = true) :
    CandidateReducibleAboveDenote env 0 typeCode
      (dataTaitCandidate (flatCodeValuePredicate typeCode.rootGenerator)) :=
  fun _level _habove => ReducibleTypeStepDenote.dataFlat flatPinned

/-- **Universe leaf (canonical at `denote levelExpr env`).**  `Type@levelExpr` is reducible above its OWN decoded
level with the level-independent decode-set candidate `fun m => SN m ∧ IsReducibleTypeAtDenote env (denote
levelExpr env) m`.  The pinned threshold here is genuinely the type's classifying level (not 0). -/
theorem CandidateReducibleAboveDenote.ofUniverseCode {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    CandidateReducibleAboveDenote env (LevelExpr.denote levelExpr env)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope)
      (fun member : RawTerm scope => IsStronglyNormalizing member ∧
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member) :=
  fun level habove => universeMembership_levelIrrelevant env level levelExpr flag habove

/-- **Weak-head-expansion arm (canonical, same threshold).**  A redex inherits its weak-head contractum's
canonical reducibility at the SAME canonical level — rewrap each level through `whnfExpand`. -/
theorem CandidateReducibleAboveDenote.headExpand {scope : Nat} {env : Nat → Nat}
    {typeCode reduct : RawTerm scope} {canonicalLevel : Nat} {candidate : RawTerm scope → Prop}
    (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductReducible : CandidateReducibleAboveDenote env canonicalLevel reduct candidate) :
    CandidateReducibleAboveDenote env canonicalLevel typeCode candidate :=
  fun level habove => ReducibleTypeStepDenote.whnfExpand weakHeadStep (reductReducible level habove)

/-- **★ The canonical-threshold dependent-Π arm — the threshold-swap RESOLVED.**  From the domain reducible above
`domainLevel` (candidate `domainCandidate`) and the codomain reducible above a FIXED `codomainLevel` UNIFORMLY in
the argument (candidate family `codomainCandidate`), the dependent function type
`Π domainCode codomainCode` is reducible above `domainLevel + codomainLevel` with the function-space candidate
`fun f => ∀ arg, domainCandidate arg → codomainCandidate arg (f arg)`.

Because `codomainLevel` is a single fixed `Nat` (NOT an existential chosen per argument), there is no
`∀arg ∃ → ∃ ∀arg` swap: each component's threshold is bounded by the sum (`Nat.le_add_right` for the domain,
`Nat.le_add_left` for the codomain), and the Π is assembled by one `ReducibleTypeStepDenote.piType`.  This is the
deep content of #752 reduced to its essence — the arg-independence of `codomainLevel` (free via
`subst_universeCodeCell`) is exactly what makes the canonical form available. -/
theorem CandidateReducibleAboveDenote.piTyCode {scope : Nat} (env : Nat → Nat)
    (domainLevel codomainLevel : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (domainReducible : CandidateReducibleAboveDenote env domainLevel domainCode domainCandidate)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        CandidateReducibleAboveDenote env codomainLevel (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) :
    CandidateReducibleAboveDenote env (domainLevel + codomainLevel)
      (piTyCodeCell domainCode codomainCode)
      (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument
          (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  fun level habove =>
    ReducibleTypeStepDenote.piType (domainCandidate := domainCandidate) codomainCandidate
      (domainReducible level (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) habove))
      (fun argument argumentInDomain =>
        codomainReducible argument argumentInDomain level
          (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) habove))

end FX1Poly.Typed
