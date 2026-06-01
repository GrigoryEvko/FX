import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StratifiedReducibleMemberNonDependent

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

end FX1Poly.Core
