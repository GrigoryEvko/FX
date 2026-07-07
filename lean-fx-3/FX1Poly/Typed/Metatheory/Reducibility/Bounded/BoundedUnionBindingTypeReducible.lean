import FX1Poly.Typed.Metatheory.Reducibility.Fundamental.ClosedNativeStronglyNormalizing
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedBindingTypeReducible

/-! # FX1Poly/Typed/BoundedUnionBindingTypeReducible
    — the NATIVE-union discharged fundamental theorem + the native binding-type reducibility leaf

The native-union analogues of the two grown pieces the open-SN cone consumes.  Both are exact mirrors of the
grown wire (`BoundedGrownFundamental` / `BoundedBindingTypeReducible`), swapping only the ENGINE-specific
fundamental call — everything downstream (`subst_universeCodeCell`, the below-bound gate, the decode, member
cumulativity) reads members, never derivations, and reuses verbatim.

## The two bricks

  * `HasTypeUnion.fundamentalAtBoundedSucc` — the DISCHARGED native fundamental theorem at the kernel bundle
    (`fxTypingBundle`).  `HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms` is conditional on the three
    table-arm FT premises; here they are supplied by the shipped per-role row dispatchers
    (`fundamentalFormationRowAtBoundedSucc` / `fundamentalIntroRowAtBoundedSucc` /
    `fundamentalElimRowAtBoundedSucc`), exactly as `HasTypeUnionOver.closedStronglyNormalizing` threads them —
    so a single `(env, bound)`-fixed call produces `FundamentalConclusionAtBoundedSucc` with NO open premises.
    The native analogue of `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c).
  * `HasTypeUnion.subjectReducibleAsTypeUnderEnv` — a universe-typed subject is bound-reducible-as-type under a
    reducible env.  Verbatim mirror of `HasTypeDescPi.subjectReducibleAsTypeUnderEnv`, swapping its first line
    (the grown FT) for the discharged native FT above; the five-step assembly (FT → `subst_universeCodeCell` →
    below-bound gate → decode → cumulativity) is production-agnostic and copies unchanged.

## Zero-axiom verification

A linear composition of shipped zero-axiom results.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`funext`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The DISCHARGED native union fundamental theorem at the kernel bundle.**  Under a `BoundExceedsUnion env
bound d` budget, every kernel-union derivation (`HasTypeUnion = HasTypeUnionOver fxTypingBundle`) satisfies the
`+1`-closing bound-reducible conclusion `FundamentalConclusionAtBoundedSucc`.  The three table-arm FT premises of
`fundamentalAtBoundedSuccFromTableArms` are discharged at the kernel bundle by the shipped per-role row
dispatchers (their gates match `fxTypingBundle.{formationRule,intro,elim}` definitionally), so this is an
open-premise-free native fundamental — the union twin of `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c). -/
theorem HasTypeUnion.fundamentalAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (d : HasTypeUnion profile context subject classifier)
    (budget : BoundExceedsUnion env bound d) :
    FundamentalConclusionAtBoundedSucc env bound context subject classifier :=
  HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms env bound
    (fundamentalFormationRowAtBoundedSucc env bound)
    (fundamentalIntroRowAtBoundedSucc env bound)
    (fundamentalElimRowAtBoundedSucc env bound) d budget

/-- **A universe-typed subject is bound-reducible-as-type under a reducible env (native union).**  Given a
kernel-union derivation typing `bindingType` at `Type@levelExpr`, a `BoundExceedsUnion` budget for it at
`bound`, and a bound-reducible closing environment for the context at `bound`, the substituted `bindingType` is
bound-reducible-as-type at `bound`.  Verbatim mirror of `HasTypeDescPi.subjectReducibleAsTypeUnderEnv` over the
discharged native FT: FT → `subst_universeCodeCell` → below-bound gate → decode → cumulativity.  The type-side
leaf the native reducible-closing-environment builder (`reducibleEnvOfWfContextUnion`) cons-feeds. -/
theorem HasTypeUnion.subjectReducibleAsTypeUnderEnv {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} {restContext : TypingContext profile scope}
    {bindingType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (unionDeriv : HasTypeUnion profile restContext bindingType (universeCodeCell levelExpr flag))
    (budget : BoundExceedsUnion env bound unionDeriv)
    {substitution : RawTermSubst scope (targetScope + 1)}
    (envReducible : ReducibleEnvAtBounded env bound restContext substitution) :
    IsReducibleTypeAtBounded env bound (RawTerm.subst substitution bindingType) := by
  have member := HasTypeUnion.fundamentalAtBoundedSucc env bound unionDeriv budget substitution envReducible
  rw [subst_universeCodeCell] at member
  obtain ⟨candidate, candidateReducible, candidateMember⟩ := member
  have belowBound := belowBound_of_reducibleUniverse candidateReducible
  exact isReducibleBounded_cumulative
    (universeMemberReducibleAsTypeAtDecodedLevelBounded
      ⟨candidate, candidateReducible, candidateMember⟩ belowBound)
    (Nat.le_of_lt belowBound)

end FX1Poly.Typed
