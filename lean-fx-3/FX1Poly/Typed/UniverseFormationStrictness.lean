import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.WfContext

/-! # FX1Poly/Typed/UniverseFormationStrictness
    — the universe-formation rule is LEVEL-TIGHT (a 0-FP soundness corpus)

The universe rule (`HasType.universeFormation`) gives `Type@e : Type@(e+1)`.  This file proves it is the ONLY
classifier (up to conversion): a universe code is typed at EXACTLY its successor level, so the engine rejects
every level mismatch — no spurious inflation (`Type@e : Type@(e+2)`), no deflation, and no Type-in-Type
(`Type@e : Type@e`).  Together with the no-Type-in-Type probe of `M35-T1` and the subject-side honesty corpus
(`HasTypeHonesty`), this pins the universe level exactly and strengthens the 0-false-positive defense layer.

  * `HasType.universeCodeClassifierConvToSuccessor` — the inversion: any classifier of `Type@e` is `Conv` to
    `Type@(e+1)`.  One line: `HasType.uniqueness` against the canonical `universeFormation` derivation.
  * the three concrete rejections instantiate it at `Type@0` and read off the level mismatch with
    `universeCodeCell_inj_of_conv` (convertible universe codes have syntactically equal levels) + `decide`.

This holds because the engine has NO universe cumulativity / subsumption rule yet (`@[cumulUpMarker]`, M43, is
unimplemented): the `conv` rule uses symmetric `Conv`, not a `≤`-subtyping, so a universe code does not climb to
higher universes.  When cumulativity lands, the over-shoot rejection becomes a `≤`-bounded statement.

## Zero-axiom verification

The inversion is `HasType.uniqueness` (validity-backed, zero-axiom) applied to the `universeFormation` rule; the
rejections compose it with `universeCodeCell_inj_of_conv` (confluence + cell injectivity) and a `decide` on
closed `LevelExpr` equality (the `LevelExpr` `DecidableEq` is propext-free).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Universe-formation inversion: a universe code is classified by EXACTLY its successor level.**  Any
classifier of `universeCodeCell e flag` in a well-formed context is `Conv` to `universeCodeCell e.lsucc flag` —
by typing uniqueness against the canonical `universeFormation` derivation.  The reusable level-strictness lemma:
every level-mismatch rejection below is an instance. -/
theorem HasType.universeCodeClassifierConvToSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (contextWellFormed : WfContext context)
    (typed : HasType profile context (universeCodeCell levelExpr flag) classifier) :
    Conv classifier (universeCodeCell levelExpr.lsucc flag) :=
  HasType.uniqueness contextWellFormed typed
    (HasType.universeFormation context levelExpr flag)

/-- **0-FP: no level inflation.**  `Type@0` is NOT typed at `Type@2` — only at `Type@1`. -/
theorem universeCode_notTypedAboveSuccessor {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag) := by
  intro typed
  have conv : Conv (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag : RawTerm 0)
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor LevelExpr.lzero flag
      WfContext.emptyIsWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (by decide)

/-- **0-FP: no level deflation.**  `Type@1` is NOT typed at `Type@0` — only at `Type@2`. -/
theorem universeCode_notTypedBelowSuccessor {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (universeCodeCell LevelExpr.lzero.lsucc flag)
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  have conv : Conv (universeCodeCell LevelExpr.lzero flag : RawTerm 0)
      (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor LevelExpr.lzero.lsucc flag
      WfContext.emptyIsWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (by decide)

/-- **0-FP: no Type-in-Type.**  `Type@0` is NOT typed at `Type@0` — the universe sits strictly above itself. -/
theorem universeCode_notTypedAtSelf {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  have conv : Conv (universeCodeCell LevelExpr.lzero flag : RawTerm 0)
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor LevelExpr.lzero flag
      WfContext.emptyIsWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (by decide)

/-! ## The general (all-level, all-WfContext) level-strictness corpus.

The three rejections above are pinned at `Type@0` in the EMPTY context (closed by `decide` on closed levels).
These two generalize the load-bearing ones to EVERY level and EVERY well-formed context, refuting the closed
`decide` against the structural predicativity guard `LevelExpr.ne_lsucc_self` (`levelExpr ≠ lsucc levelExpr`,
size-free).  `universeCode_notTypedAtSelf_general` is the §1.4 "Type:Type / Girard's paradox structurally
impossible" claim in FULL generality — the headline §27.2 dependent-type known-unsoundness rejection, the
five-layer-defense L1 anchor for the universe axis. -/

/-- **0-FP: no Type-in-Type, in FULL generality (SN-140 L1).**  `Type@e` is NOT typed at `Type@e` at ANY level
`e` in ANY well-formed context — the universe sits strictly above itself everywhere.  This is the §1.4
"Type:Type / Girard's-paradox structurally impossible" claim in full generality (the closed-`Type@0` probe
`universeCode_notTypedAtSelf` is its empty-context instance): a self-classified universe forces `e = lsucc e`,
refuted by the predicativity guard `LevelExpr.ne_lsucc_self`. -/
theorem universeCode_notTypedAtSelf_general {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor levelExpr flag contextWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr)

/-- **0-FP: no level inflation, in full generality.**  `Type@e` is NOT typed at `Type@(e+2)` at ANY level in
ANY well-formed context — only at `Type@(e+1)`.  The inversion forces `lsucc (lsucc e) = lsucc e`, i.e.
`lsucc e = lsucc (lsucc e)`, refuted by `LevelExpr.ne_lsucc_self` at `lsucc e`. -/
theorem universeCode_notTypedAboveSuccessor_general {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc.lsucc flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr.lsucc.lsucc flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasType.universeCodeClassifierConvToSuccessor levelExpr flag contextWellFormed typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr.lsucc).symm

end FX1Poly.Typed
