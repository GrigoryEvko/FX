import FX1Poly.Typed.DenoteKeyedUniverseFormationMember
import FX1Poly.Typed.DenoteKeyedFundamentalMotive

/-! # FX1Poly/Typed/DenoteKeyedUniverseMembershipIntro
    — the universe-membership INTRODUCTION over the denote relation (genFormationPi arm step (b); toward SN-043)

The denote fundamental theorem's type-former arms (`universeFormation`, `piFormation`, `genFormationPi`) all
conclude that a TYPE is a denote-reducible MEMBER of its universe code `Type@levelExpr`.  Their common
final step is the universe-membership INTRODUCTION proved here: a denote-reducible SN type *at its decoded
level* is a denote-reducible member of its universe code *at any higher ambient level*.  This is the exact
CONVERSE of the shipped A2 bridge (#751, `universe membership → ambient-level reducibility`, the DECODE
direction): there the membership is consumed; here it is INTRODUCED.

## Why it is exactly the headline candidate, repackaged

`universeMembership_levelIrrelevant` (`DenoteKeyedReducibility.lean`) gives the candidate of `Type@levelExpr`
at any ambient `level > denote levelExpr env` as the level-irrelevant decode set
`fun member => IsStronglyNormalizing member ∧ IsReducibleTypeAtDenote env (denote levelExpr env) member`.
So to exhibit a type code as a member it suffices to land in that set — i.e. to be SN and reducible at the
decoded level.  No new induction; the level-irrelevance of the universe candidate IS the introduction rule.

`universeFormationMemberAtDenote` (`DenoteKeyedUniverseFormationMember.lean`) is precisely the special case
where the member type code is itself a closed universe code `Type@e` (verified in scratch as
`universeFormationMemberAtDenote_viaIntro`); this file abstracts that to an ARBITRARY denote-reducible type
code, which is what the generic former arm needs (a Π/Σ/arrow former is not a universe code).

## The two declarations

  * `universeMembershipIntroAtDenote` — the relation-internal intro: `denote levelExpr env < level`, SN of
    the type code, and its reducibility at the decoded level ⟹ membership of `Type@levelExpr` at `level`.
  * `fundamentalTypeFormerAtDenote` — the FT-shaped consumer: a former that, under every closing
    substitution + denote-reducible environment, is an SN denote-reducible type at its decoded level (the
    route-A reducibility premise) satisfies `FundamentalConclusionAtDenote` at its universe classifier.  This
    is the type-former fundamental-theorem arm MODULO route-A reducibility — the universe-classifier `Type@…`
    is closed (`childNil`), so the closing substitution leaves it fixed and the conclusion lands on
    `universeMembershipIntroAtDenote`.  It isolates route-A (the former's type-reducibility, ultimately the
    A2 composite-domain piArm #752) as the single premise — the same isolation discipline the `conv` arm
    (`fundamentalConvAtDenote`) uses for its ambient-level reducibility premise.

## Zero-axiom verification

`universeMembershipIntroAtDenote` is one anonymous-constructor term over `universeMembership_levelIrrelevant`.
`fundamentalTypeFormerAtDenote` introduces the substitution, destructures the route-A premise, and applies the
intro under the closed-universe-code `subst` reduction (`rfl`).  No induction, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The universe-membership INTRODUCTION (denote-keyed).**  A type code that is strongly normalizing and a
denote-reducible type at the decoded level `denote levelExpr env` is a denote-reducible MEMBER of its universe
code `Type@levelExpr` at any ambient `level` strictly above the decoded level.  The witnessing candidate is the
level-irrelevant universe candidate (`universeMembership_levelIrrelevant`), whose decode-set is exactly
`SN ∧ reducible-type-at-decoded-level` — so the two member obligations ARE the supplied hypotheses.  The
converse of the shipped A2 decode bridge (#751); the generic former arm's final packaging step. -/
theorem universeMembershipIntroAtDenote {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat) (typeCode : RawTerm scope)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (typeCodeSN : IsStronglyNormalizing typeCode)
    (typeCodeReducible : IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) typeCode) :
    IsReducibleMemberAtDenote env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      typeCode :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member,
    universeMembership_levelIrrelevant env level levelExpr flag levelAbove,
    typeCodeSN,
    typeCodeReducible⟩

/-- **The type-former fundamental-theorem arm MODULO route-A reducibility.**  A former `typeFormer` that, under
every closing substitution and denote-reducible environment, is a strongly-normalizing denote-reducible type at
its decoded level `denote levelExpr env` satisfies the fundamental-theorem conclusion
`FundamentalConclusionAtDenote` at its universe classifier `Type@levelExpr`.  The classifier is closed, so the
closing substitution leaves it fixed and the goal reduces to `universeMembershipIntroAtDenote` on the
substituted former.  This isolates the former's TYPE-reducibility (route A / the A2 composite-domain piArm
#752) as the single explicit premise — mirroring the conv arm's isolation of its ambient-level reducibility
premise — and discharges the universe-membership packaging the `universeFormation` / `piFormation` /
`genFormationPi` arms share. -/
theorem fundamentalTypeFormerAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope) (typeFormer : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (formerReducible : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution typeFormer) ∧
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution typeFormer)) :
    FundamentalConclusionAtDenote env level context typeFormer (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution envReducible
  obtain ⟨formerSN, formerRed⟩ := formerReducible substitution envReducible
  show IsReducibleMemberAtDenote env level
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil) (RawTerm.subst substitution typeFormer)
  exact universeMembershipIntroAtDenote env levelExpr flag level
    (RawTerm.subst substitution typeFormer) levelAbove formerSN formerRed

end FX1Poly.Typed
