import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StratifiedReducibleMemberNonDependent
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Core/StratifiedReducibleSmoke
    — concrete end-to-end smoke tests of the stratified reducibility → strong-normalization pipeline

These witnesses exercise the choice-free dependent-reducibility stack (the `ofPointwiseIff` congruence
closure, the canonical member-predicate, and the choice-free Π formation/introduction) end to end on CLOSED,
genuinely-well-typed cells, producing strong normalization via CR1 (`IsReducibleMemberAt.stronglyNormalizing`).
They are baby cases of the SN-for-well-typed fundamental-theorem corollary (#426): "a well-typed term is a
reducible member of its type, hence strongly normalizing", instantiated at concrete closed terms so the whole
pipeline is exercised before the general fundamental-theorem induction lands.

## Zero-axiom verification

Each smoke composes shipped pieces (`IsReducibleMemberAt.universeFormation`,
`IsReducibleMemberAt.stronglyNormalizing`, the universe-code reducibility) — no new proof obligation, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- **SN of a closed universe code, via the reducibility → SN pipeline.**  `Type@levelExpr` is a reducible
member of `Type@(lsucc levelExpr)` (`universeFormation`), and reducible members are strongly normalizing
(CR1, `IsReducibleMemberAt.stronglyNormalizing`) — so the universe code is strongly normalizing.  A concrete
instance of "a well-typed term is strongly normalizing" routed through the stratified reducibility model
rather than the direct leaf-normality argument: `Type@e : Type@(lsucc e)` ⟹ `SN (Type@e)`. -/
theorem universeCode_stronglyNormalizing_viaReducibility {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm (scope + 1)) :=
  (IsReducibleMemberAt.universeFormation predLevel levelExpr flag).stronglyNormalizing

/-- **SN of the closed simply-typed identity λ, via the choice-free reducibility stack.**  `λ. var0` is a
reducible member of the simple arrow `Type@levelExpr → Type@levelExpr` (`abstractionNonDependent` — the
no-large-elimination `piIntro` arm), hence strongly normalizing by CR1.  The domain `Type@levelExpr` is a
reducible type at the `universeCode` arm (candidate the Tarski-universe predicate `SN ∧ is-a-reducible-type`),
every domain-member is strongly normalizing (its SN conjunct), and the body `var0` β-substitutes to its
argument (`subst0_var_zero`, `rfl`), which already inhabits the identical codomain candidate.  A concrete
end-to-end exercise of the Π-introduction pipeline on a well-typed closed identity. -/
theorem identityLambda_stronglyNormalizing_viaReducibility {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_lam ()
        (.childCons (.mkGen .gen_var ⟨0, Nat.succ_pos (scope + 1)⟩ .childNil) .childNil)
        : RawTerm (scope + 1)) := by
  have universeReducible :
      ReducibleTypeAt (predLevel + 1)
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm (scope + 1))
        (universeReducibilityPredicate (ReducibleTypeAt predLevel)) :=
    ReducibleTypeStep.universeCode levelExpr flag
  exact (IsReducibleMemberAt.abstractionNonDependent
    (body := .mkGen .gen_var ⟨0, Nat.succ_pos (scope + 1)⟩ .childNil)
    universeReducible
    (fun _argument argumentInDomain => argumentInDomain.1)
    universeReducible
    (fun _argument argumentInDomain => argumentInDomain)).stronglyNormalizing

/-- **The closed simply-typed arrow `Type@levelExpr → Type@levelExpr` is a reducible type, via the
choice-free type-former machinery.**  `ReducibleTypeAt.arrowType` (the non-dependent specialization of the
choice-free dependent Π-formation) from a reducible domain and codomain — both the `universeCode` arm.  The
type-FORMATION counterpart to `identityLambda_…` (the introduction side) and
`universeCode_…` (the membership side): together the three witness that type formation, membership, and
introduction all compose through the stratified reducibility model on concrete well-typed cells. -/
theorem closedSimpleArrow_isReducibleType {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAt (predLevel + 1)
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons (RawTerm.weaken (.mkGen .gen_universeCode (levelExpr, flag) .childNil))
            .childNil))
        : RawTerm (scope + 1)) :=
  have universeReducible :
      ReducibleTypeAt (predLevel + 1)
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm (scope + 1))
        (universeReducibilityPredicate (ReducibleTypeAt predLevel)) :=
    ReducibleTypeStep.universeCode levelExpr flag
  ⟨_, ReducibleTypeAt.arrowType universeReducible universeReducible⟩

/-- **A Σ-type former over strongly-normalizing components is a reducible member of its universe, via the
data-former arm of the fundamental theorem.**  `Σ domain codomain` (a genuine 2-child data former, distinct
from the Π/universe codes) is a reducible member of `Type@levelExpr` at `predLevel + 1` whenever its domain
and under-binder codomain are strongly normalizing: the former is strongly normalizing
(`sigmaTyCode_isStronglyNormalizing_of_domain_codomain` — two-child congruence SN from the children's SN),
weak-head-normal (no weak-head step is Σ-rooted — only `rootIota` could unify, and no ι-redex is a type
former), and root-distinct from both Π and universe.  `dataFormerInUniverse` then classifies it by strong
normalization in the Tarski universe.  This validates the `genFormationPi` data-former dispatch on a concrete
2-child former: with the per-former SN lemma supplied, membership-in-universe is automatic — no per-former
reducibility-candidate development, exactly as the general fundamental-theorem arm will dispatch. -/
theorem sigmaFormer_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainNormalizing : IsStronglyNormalizing domain)
    (codomainNormalizing : IsStronglyNormalizing codomain) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_sigmaTyCode ()
        (.childCons domain (.childCons codomain .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core
