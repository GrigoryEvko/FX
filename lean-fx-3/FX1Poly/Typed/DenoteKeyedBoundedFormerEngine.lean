import FX1Poly.Typed.DenoteKeyedBoundedFundamentalMotive

/-! # FX1Poly/Typed/DenoteKeyedBoundedFormerEngine
    — the bound-carrying universe-membership INTRODUCTION + type-former engine (#753 → SN-043)

The bound-carrying analogue of `DenoteKeyedUniverseMembershipIntro` (the introduction step (b) that the denote
`universeFormation` / `piFormation` / `genFormationPi` arms share): a type code that is strongly normalizing and a
bound-reducible type *at its decoded level* is a bound-reducible MEMBER of its universe code `Type@levelExpr` *at
any higher bound*.  Plus the universe-member SN projection the genFormation arms consume.

## Built entirely on the already-shipped bounded universe machinery

Every proof routes through `universeMembershipBounded_levelIrrelevant` (shipped in the motive tick) — whose
decode-set candidate is exactly `SN ∧ bound-reducible-type-at-decoded-level` — and `ReducibleTypeAtBounded.
deterministic` (shipped via the forget bridge).  No new induction; the universe candidate's level-irrelevance IS
the introduction rule, and its SN conjunct IS the member-SN projection.

## The three declarations

  * `universeMembershipIntroAtBounded` — the relation-internal intro: `denote levelExpr env < bound`, SN of the
    type code, and its bound-reducibility at the decoded level ⟹ membership of `Type@levelExpr` at `bound`.
  * `fundamentalTypeFormerAtBounded` — the FT-shaped consumer: a former that, under every closing substitution +
    bound-reducible environment, is an SN bound-reducible type at its decoded level satisfies
    `FundamentalConclusionAtBounded` at its universe classifier `Type@levelExpr`.  Isolates the former's
    type-reducibility (route A) as the single premise — for the bounded relation this is the residual that CLOSES
    via free cumulativity (`stepBounded_cumulative`) where the denote relation was model-obstructed.  The shared
    packaging the bounded `universeFormation` / `genFormationPi` arms route through.
  * `stronglyNormalizing_of_universeMemberAtBounded` — the universe-member SN projection: a bound-reducible member
    of `Type@levelExpr` is strongly normalizing (align its candidate with the universe candidate via
    `deterministic`, project the SN conjunct).  The genFormation arms' domain/codomain CR1.

## Zero-axiom verification

`universeMembershipIntroAtBounded` is one anonymous-constructor term over `universeMembershipBounded_levelIrrelevant`;
`fundamentalTypeFormerAtBounded` destructures the route-A premise and applies the intro under the closed-universe
`subst` reduction (`rfl`); the SN projection is `deterministic` + `.1`.  No induction, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The universe-membership INTRODUCTION (bound-carrying).**  A type code that is strongly normalizing and a
bound-reducible type at the decoded level `denote levelExpr env` is a bound-reducible MEMBER of its universe code
`Type@levelExpr` at any `bound` strictly above the decoded level.  The witnessing candidate is the level-irrelevant
bounded universe candidate (`universeMembershipBounded_levelIrrelevant`), whose decode-set is exactly
`SN ∧ bound-reducible-type-at-decoded-level` — so the two member obligations ARE the supplied hypotheses. -/
theorem universeMembershipIntroAtBounded {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (bound : Nat) (typeCode : RawTerm scope)
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (typeCodeSN : IsStronglyNormalizing typeCode)
    (typeCodeReducible : IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) typeCode) :
    IsReducibleMemberAtBounded env bound
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      typeCode :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) member,
    universeMembershipBounded_levelIrrelevant env bound levelExpr flag belowBound,
    typeCodeSN,
    typeCodeReducible⟩

/-- **The bound-carrying type-former fundamental-theorem arm MODULO route-A reducibility.**  A former that, under
every closing substitution and bound-reducible environment, is a strongly-normalizing bound-reducible type at its
decoded level satisfies the fundamental-theorem conclusion at its universe classifier `Type@levelExpr`.  The
classifier is closed, so the closing substitution leaves it fixed and the goal reduces to
`universeMembershipIntroAtBounded` on the substituted former.  Isolates the former's TYPE-reducibility (route A) as
the single explicit premise — the residual that, in the BOUNDED relation, closes via free cumulativity
(`stepBounded_cumulative`) where the denote relation is model-obstructed (`DenoteKeyedCumulativityObstruction`). -/
theorem fundamentalTypeFormerAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope) (typeFormer : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (formerReducible : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution typeFormer) ∧
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution typeFormer)) :
    FundamentalConclusionAtBounded env bound context typeFormer (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution envReducible
  obtain ⟨formerSN, formerRed⟩ := formerReducible substitution envReducible
  show IsReducibleMemberAtBounded env bound
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil) (RawTerm.subst substitution typeFormer)
  exact universeMembershipIntroAtBounded env levelExpr flag bound
    (RawTerm.subst substitution typeFormer) belowBound formerSN formerRed

/-- **Universe-member SN projection (bound-carrying).**  A bound-reducible member of `Type@levelExpr` is strongly
normalizing — align the member's candidate with the level-irrelevant bounded universe candidate via
`ReducibleTypeAtBounded.deterministic` and project the SN conjunct.  The genFormation arms' domain/codomain CR1. -/
theorem stronglyNormalizing_of_universeMemberAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (term : RawTerm scope)
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (member : IsReducibleMemberAtBounded env bound (universeCodeCell levelExpr flag) term) :
    IsStronglyNormalizing term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have universeCandidateReducible :
      ReducibleTypeAtBounded env bound (universeCodeCell levelExpr flag)
        (fun member : RawTerm scope => IsStronglyNormalizing member ∧
          IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) member) :=
    universeMembershipBounded_levelIrrelevant env bound levelExpr flag belowBound
  have pointwise := ReducibleTypeAtBounded.deterministic candidateReducible universeCandidateReducible
  exact ((pointwise term).mp termInCandidate).1

end FX1Poly.Typed
