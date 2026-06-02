import FX1Poly.Typed.FundamentalLevelIndexed

/-! # FX1Poly/Typed/TypeFundamentalLevelIndexed
    — the TYPE half of the mutual fundamental theorem (level-indexed), for the formation type-subjects

The recursor-assembly motive for the level-indexed fundamental theorem (`FundamentalLevelIndexed.lean`) is a
MUTUAL term + type fundamental theorem (the Abel/Adjedj validity logical relation, arXiv:2310.06376): the
term FT's `conv` arm needs the classifier as a reducible TYPE at the member's level (`IsReducibleMemberAt`'s
`castAlongConv` consumes a `ReducibleTypeAt` target), and that reducibility comes from the classifier's OWN
type validity, NOT from Conv-transport (`ReducibleTypeAt.convInvariant` needs both endpoints).

This file carries the TYPE-FT conclusions for the formation type-subjects — the type codes a `conv`
reclassifier (or a former child) can be — derived from the already-shipped TERM-FT arms by `tarskiDecode`
(a reducible member of a universe at `L+1` is a reducible type at `L`).  The `var`/type-variable case and the
context-validity threading remain for the full mutual relation; these are the choice-free, derivation-free
pieces available now.

## Zero-axiom verification

Each lemma is one application of a shipped term-FT arm (`fundamentalUniverseFormationLevelIndexed` /
`fundamentalPiFormationLevelIndexed` / `fundamentalSigmaFormationLevelIndexed`) followed by
`subst_universeCodeCell` (normalising the substituted universe classifier) and `IsReducibleMemberAt.tarskiDecode`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The type-level fundamental conclusion** (decoupled-`typeLevel`).  A type code is a reducible TYPE at
`typeLevel` under every per-variable-level closing environment — the `ReducibleTypeAt`-valued analogue of
`FundamentalConclusionLevelIndexed`.  The conclusion shape of the TYPE half of the mutual fundamental
theorem; the term FT's `conv` arm consumes exactly this for its classifier (`castAlongConv`'s
`targetReducible`). -/
def IsTypeFundamentalLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (typeLevel : Nat)
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
    ReducibleEnvVec contextLevels context substitution →
    IsReducibleTypeAt typeLevel (RawTerm.subst substitution typeCode)

/-- **A universe code is a reducible TYPE at every level** (the type-FT for the `universeFormation` subject).
`fundamentalUniverseFormationLevelIndexed` makes `universeCodeCell levelExpr flag` a reducible MEMBER of its
parent universe at `predLevel+1`; `tarskiDecode` drops that to a reducible TYPE at `predLevel`.  Polymorphic
in `predLevel` — a universe code is a valid type at every level (the membership level is fuel, free). -/
theorem universeCodeIsTypeFundamentalLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsTypeFundamentalLevelIndexed contextLevels predLevel context
      (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution env
  have member :=
    fundamentalUniverseFormationLevelIndexed contextLevels predLevel context levelExpr flag
      substitution env
  rw [subst_universeCodeCell] at member
  exact member.tarskiDecode

/-- **A Π type-code is a reducible TYPE at `predLevel`** (the type-FT for the Π former), from the domain and
codomain fundamentals — `fundamentalPiFormationLevelIndexed` makes the Π code a member of its universe at
`predLevel+1`, then `tarskiDecode` drops to a reducible type at `predLevel`.  `formerLevel` is the syntactic
output universe level (immaterial to the type-membership, since `tarskiDecode` discards the universe code). -/
theorem piFormerIsTypeFundamentalLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental : ∀ aboveLevel : Nat,
      FundamentalConclusionLevelIndexed contextLevels (aboveLevel + 1) context domainCode
        (universeCodeCell domainLevel flag))
    (codomainFundamental : ∀ headLevel : Nat,
      FundamentalConclusionLevelIndexed (levelCons headLevel contextLevels) (predLevel + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    IsTypeFundamentalLevelIndexed contextLevels predLevel context
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution env
  have member :=
    fundamentalPiFormationLevelIndexed contextLevels predLevel
      (formerLevel := formerLevel) domainFundamental codomainFundamental substitution env
  rw [subst_universeCodeCell] at member
  exact member.tarskiDecode

/-- **A Σ type-code is a reducible TYPE at `predLevel`** (the type-FT for the Σ former), the data-former twin
of `piFormerIsTypeFundamentalLevelIndexed`. -/
theorem sigmaFormerIsTypeFundamentalLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental : ∀ aboveLevel : Nat,
      FundamentalConclusionLevelIndexed contextLevels (aboveLevel + 1) context domainCode
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionLevelIndexed (levelCons (predLevel + 1) contextLevels) (predLevel + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    IsTypeFundamentalLevelIndexed contextLevels predLevel context
      (sigmaTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution env
  have member :=
    fundamentalSigmaFormationLevelIndexed contextLevels predLevel
      (formerLevel := formerLevel) domainFundamental codomainFundamental substitution env
  rw [subst_universeCodeCell] at member
  exact member.tarskiDecode

/-- **A type variable is a reducible TYPE at its env level** (the type-FT for the type-`var` subject).
When the variable's looked-up type is a universe code `universeCodeCell levelExpr flag` and its env level is
positive (`contextLevels index = predLevel + 1`), the environment gives the variable as a reducible MEMBER of
that universe at `predLevel+1`, and `tarskiDecode` drops it to a reducible TYPE at `predLevel`.  Unlike the
universe-code/former subjects (polymorphic in the level — the membership level is free fuel), the variable's
type-level is FIXED by the env, so the `levelMatches` hypothesis pins it; the eventual context-consistency
supplies exactly this (each type entry's env level is one above its universe's decoded level).  With this,
the type-FT covers every formation type-subject — universe code, Π former, Σ former, type variable —
modulo the `conv` case (which is mutual with the term FT: `ReducibleTypeAt.convInvariant` needs both
endpoints reducible, so the source type's reducibility comes from its own term-FT validity). -/
theorem varIsTypeFundamentalLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope} (index : Fin scope)
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (lookupIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (levelMatches : contextLevels index = predLevel + 1) :
    IsTypeFundamentalLevelIndexed contextLevels predLevel context (variableCell index) := by
  intro _targetScope substitution env
  have member := env.lookupReducible index
  rw [levelMatches, lookupIsUniverse, subst_universeCodeCell] at member
  exact member.tarskiDecode

end FX1Poly.Typed
