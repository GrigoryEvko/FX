import FX1Poly.Typed.UniverseFormationStrictness

/-! # FX1Poly/Typed/FormerFormationStrictness
    — the dependent-former rules are LEVEL-TIGHT (the 0-FP soundness corpus for Π/Σ)

The Π/Σ analog of `UniverseFormationStrictness`.  `HasType.piFormation` /
`sigmaFormation` land a Π/Σ-type code at `Type@(lmax (level domain) (level codomain))`.  This file proves that
classifier is the ONLY one (up to conversion): a Π/Σ-type code, given its component levels, is typed at EXACTLY
the iterated-`lmax` level, so the engine rejects every level mismatch on a dependent type code — the
formation-family completion of the universe level-tightness (universe + Π + Σ all level-tight).

  * `HasType.piTyCodeClassifierConv` / `HasType.sigmaTyCodeClassifierConv` — the inversion: any classifier of a
    Π/Σ-type code (given its domain/codomain typings) is `Conv` to `Type@(lmax domainLevel codomainLevel)`.
    One line: `HasType.uniqueness` against the canonical `piFormation` / `sigmaFormation` derivation.
  * `closedPi_notTypedAtZero` / `closedSigma_notTypedAtZero` — a concrete closed rejection per former: the
    closed `Π(Type@0).Type@0` / `Σ(Type@0).Type@0` sits at `Type@(lmax 1 1)`, NOT at `Type@0`.  Demonstrates the
    engine rejects a mislevelled dependent type code (the 0-FP corpus instance for the dependent formers).

Like the universe strictness, this holds because the engine has NO universe cumulativity / subsumption rule yet
(`@[cumulUpMarker]`, M43, unimplemented): `conv` uses symmetric `Conv`, not a `≤`-subtyping, so a Π/Σ-type code
neither climbs nor descends.  When cumulativity lands, the mismatch rejection becomes a `≤`-bounded statement.

## Zero-axiom verification

The inversions are `HasType.uniqueness` (validity-backed) against the canonical formation derivations; the
concrete rejections compose them with `universeCodeCell_inj_of_conv` (confluence + cell injectivity) + a
`decide` on closed `LevelExpr` equality (propext-free `DecidableEq`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Π-formation inversion: a Π-type code is classified by EXACTLY its iterated-`lmax` level.**  Given the
domain typed at `Type@domainLevel` and the codomain typed at `Type@codomainLevel` (the formation premises), any
classifier of `piTyCodeCell domainCode codomainCode` is `Conv` to `Type@(lmax domainLevel codomainLevel)` — by
typing uniqueness against the canonical `piFormation` derivation.  The reusable Π-level-strictness lemma. -/
theorem HasType.piTyCodeClassifierConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (contextWellFormed : WfContext context)
    (domainTyped : HasType profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasType profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (typed : HasType profile context (piTyCodeCell domainCode codomainCode) classifier) :
    Conv classifier (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasType.uniqueness contextWellFormed typed
    (HasType.piFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped)

/-- **Σ-formation inversion: a Σ-type code is classified by EXACTLY its iterated-`lmax` level** (the Σ dual of
`HasType.piTyCodeClassifierConv`). -/
theorem HasType.sigmaTyCodeClassifierConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (contextWellFormed : WfContext context)
    (domainTyped : HasType profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasType profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (typed : HasType profile context (sigmaTyCodeCell domainCode codomainCode) classifier) :
    Conv classifier (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasType.uniqueness contextWellFormed typed
    (HasType.sigmaFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped)

/-- **0-FP: a closed Π-type code is rejected at the wrong level.**  `Π(Type@0).Type@0` (its domain and codomain
both `Type@0 : Type@1`) sits at `Type@(lmax 1 1)`, so it is NOT typed at `Type@0` — the engine rejects a
mislevelled dependent type code.  The dependent-former instance of the level-strictness corpus: instantiates
`piTyCodeClassifierConv` at `Type@0` components and reads off the level mismatch with `universeCodeCell_inj_of_conv`
+ `decide`. -/
theorem closedPi_notTypedAtZero {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  have conv := HasType.piTyCodeClassifierConv
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc flag
    WfContext.emptyIsWellFormed
    (HasType.universeFormation TypingContext.empty LevelExpr.lzero flag)
    (HasType.universeFormation (TypingContext.empty.cons _) LevelExpr.lzero flag)
    typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (by decide)

/-- **0-FP: a closed Σ-type code is rejected at the wrong level** (the Σ dual of `closedPi_notTypedAtZero`). -/
theorem closedSigma_notTypedAtZero {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (sigmaTyCodeCell (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  have conv := HasType.sigmaTyCodeClassifierConv
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc flag
    WfContext.emptyIsWellFormed
    (HasType.universeFormation TypingContext.empty LevelExpr.lzero flag)
    (HasType.universeFormation (TypingContext.empty.cons _) LevelExpr.lzero flag)
    typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (by decide)

end FX1Poly.Typed
