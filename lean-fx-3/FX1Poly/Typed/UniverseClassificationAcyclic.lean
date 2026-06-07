import FX1Poly.Typed.KnownUnsoundnessCorpus
import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Typed/UniverseClassificationAcyclic
    — universe classification is irreflexive at EVERY length (no Girard cycle of any length, §27.2 / §1.4)

The §27.3 Layer-1 known-unsoundness corpus (`KnownUnsoundnessCorpus`) ships the Type:Type / Girard entry
as two finite obstructions: the length-1 cycle `corpusRejectsTypeInType` (`Type@e` never classifies itself)
and the length-2 cycle `grownUniverseTypingHasNoTwoCycle` (no pair of universes each classifies the other).
Its docstring promises "the honest 'no Girard cycle of any length'" — but a length-1 + length-2 refutation
is NOT that promise: a length-3 (or length-`n`) cycle `Type@a₀ : Type@a₁ : ⋯ : Type@a_{n-1} : Type@a₀` is a
genuinely distinct configuration.  This file delivers the general statement: the TRANSITIVE CLOSURE of grown
universe classification is irreflexive, so there is no Girard cycle of any length whatsoever.

## The argument — a strictly-increasing size measure along the chain

`grownUniverseTypingForcesSuccessor` (the §27.2 corpus's functional characterization) pins every classification
edge: `Type@a : Type@b` forces `b = a.lsucc`.  So each edge adds exactly one `lsucc`, and `LevelExpr.size`
(`size (lsucc a) = a.size + 1`) strictly increases by one across it.  Composing edges, `subjectLevel.size`
is STRICTLY below `classifierLevel.size` along any non-empty chain (`subjectSizeLtClassifier`).  A cycle is a
chain whose endpoints coincide, forcing `level.size < level.size` — refuted by `Nat.lt_irrefl`.  No iterate
function, no `e ≠ lsucc^[n] e` lemma family: the size measure collapses every length to one `Nat.lt`
irreflexivity.

  * `UniverseClassificationChain` — the transitive closure of `Type@a : Type@b` as a two-constructor `Prop`
    inductive (`single` edge + `step` left-extension).  Genuinely transitively closed (`trans`), so "cycle of
    any length" is a meaningful predicate, not a stand-in for the 2-cycle.
  * `UniverseClassificationChain.subjectSizeLtClassifier` — the load-bearing measure: `subjectLevel.size <
    classifierLevel.size` along any chain, by induction (`single` edge ⇒ `Nat.lt_succ_self`; `step` ⇒
    `Nat.lt_trans`).
  * **`grownUniverseTypingHasNoCycleOfAnyLength`** — the headline: no `UniverseClassificationChain` returns to
    its start, in ANY context, at ANY length.  `Nat.lt_irrefl` on the strictly-increasing size.
  * `grownUniverseTypingHasNoTwoCycleViaChain` — the shipped corpus 2-cycle (`grownUniverseTypingHasNoTwoCycle`)
    re-derived as the length-2 instance (`step edge₁ (single edge₂)`), demonstrating the general theorem
    subsumes the finite obstructions.
  * `universeClassificationChain_nonVacuous` / `universeClassificationChain_twoStep_nonVacuous` — non-vacuity:
    `Type@0 : Type@1` and `Type@0 : Type@1 : Type@2` are REAL chains (via `HasTypeDescPi.ofFormation` on
    `HasTypeDesc.universeFormation`), so the irreflexivity is over an inhabited relation, not a vacuous one.

## Zero-axiom verification

The inductive's indices are general `LevelExpr` / `UniverseFlag` variables (no successor/cons index patterns),
so `induction` over it generates no `propext`-leaking equation lemmas.  The size lemma is
`grownUniverseTypingForcesSuccessor` (corpus inversion, already zero-axiom) + `subst` + the structural Nat-order
facts `Nat.lt_succ_self` / `Nat.lt_trans` / `Nat.lt_irrefl` (Init, propext-free).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The transitive closure of grown universe classification.**  `UniverseClassificationChain profile context
subjectLevel subjectFlag classifierLevel classifierFlag` holds when `Type@(subjectLevel, subjectFlag)` is
grown-classified by `Type@(classifierLevel, classifierFlag)` through a chain of ≥1 single-step classifications
`Type@a : Type@b`.  Two constructors: a `single` edge, and a `step` that prepends an edge to a chain (a left
extension — the standard transitive-closure shape).  Indexed by the level/flag pairs only; the profile/context
are fixed parameters.  Genuinely composable (`trans`), so a CYCLE (`subjectLevel = classifierLevel ∧
subjectFlag = classifierFlag`) captures a Girard loop of arbitrary length. -/
inductive UniverseClassificationChain (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) :
    LevelExpr → UniverseFlag → LevelExpr → UniverseFlag → Prop where
  | single {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag}
      {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
      (edge : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag)
        (universeCodeCell classifierLevel classifierFlag)) :
      UniverseClassificationChain profile context subjectLevel subjectFlag
        classifierLevel classifierFlag
  | step {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag}
      {middleLevel : LevelExpr} {middleFlag : UniverseFlag}
      {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
      (edge : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag)
        (universeCodeCell middleLevel middleFlag))
      (rest : UniverseClassificationChain profile context middleLevel middleFlag
        classifierLevel classifierFlag) :
      UniverseClassificationChain profile context subjectLevel subjectFlag
        classifierLevel classifierFlag

/-- **The classification chain strictly increases level SIZE.**  Along any chain `Type@subjectLevel ⤳
Type@classifierLevel`, `subjectLevel.size < classifierLevel.size`.  The load-bearing measure for acyclicity:
each edge forces `classifier = subject.lsucc` (`grownUniverseTypingForcesSuccessor`), and `size (lsucc a) =
a.size + 1`, so a single edge bumps the size by exactly one (`Nat.lt_succ_self`) and a `step` composes via
`Nat.lt_trans`.  Induction on the chain; no per-length lemma needed. -/
theorem UniverseClassificationChain.subjectSizeLtClassifier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag}
    {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
    (chain : UniverseClassificationChain profile context subjectLevel subjectFlag
      classifierLevel classifierFlag) :
    subjectLevel.size < classifierLevel.size := by
  induction chain with
  | single edge =>
      obtain ⟨classifierEq, _flagEq⟩ := grownUniverseTypingForcesSuccessor edge
      subst classifierEq
      show LevelExpr.size _ < LevelExpr.size (LevelExpr.lsucc _)
      exact Nat.lt_succ_self _
  | step edge _rest ih =>
      obtain ⟨middleEq, _flagEq⟩ := grownUniverseTypingForcesSuccessor edge
      subst middleEq
      exact Nat.lt_trans (Nat.lt_succ_self _) ih

/-- **The classification chain is transitively closed (composition).**  Appending a chain
`Type@levelB ⤳ Type@levelC` after `Type@levelA ⤳ Type@levelB` yields `Type@levelA ⤳ Type@levelC`.  This
confirms `UniverseClassificationChain` is genuinely the transitive closure (not merely a 2-step relation), so
the cycle predicate in the headline below ranges over loops of EVERY length.  Induction on the first chain;
the `single` edge prepends to the second, the `step` recurses. -/
theorem UniverseClassificationChain.trans {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelA : LevelExpr} {flagA : UniverseFlag} {levelB : LevelExpr} {flagB : UniverseFlag}
    {levelC : LevelExpr} {flagC : UniverseFlag}
    (chainAB : UniverseClassificationChain profile context levelA flagA levelB flagB)
    (chainBC : UniverseClassificationChain profile context levelB flagB levelC flagC) :
    UniverseClassificationChain profile context levelA flagA levelC flagC := by
  induction chainAB with
  | single edge => exact .step edge chainBC
  | step edge _rest ih => exact .step edge (ih chainBC)

/-- **No Girard cycle of ANY length (§27.2 / §1.4).**  No grown universe `Type@(level, flag)` classifies
itself through a chain of classification steps, in ANY context — for every length, not just 1 (the shipped
`corpusRejectsTypeInType`) or 2 (`grownUniverseTypingHasNoTwoCycle`).  A cyclic chain makes `level.size`
strictly less than itself (`subjectSizeLtClassifier`), refuted by `Nat.lt_irrefl`.  The honest realization of
the corpus docstring's "no Girard cycle of any length" — the universe-classification relation is well-founded:
the predicative successor structure (`Type@e : Type@(e+1)`) admits no loops. -/
theorem grownUniverseTypingHasNoCycleOfAnyLength {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (cycle : UniverseClassificationChain profile context level flag level flag) :
    False :=
  Nat.lt_irrefl level.size cycle.subjectSizeLtClassifier

/-- **The shipped 2-cycle rejection, re-derived as a chain instance.**  `grownUniverseTypingHasNoTwoCycle`
(no pair `Type@a : Type@b` and `Type@b : Type@a`) is the length-2 specialization of the general theorem:
the two edges form the cyclic chain `step typedUp (single typedDown)` from `levelA` back to `levelA`.
Demonstrates that `grownUniverseTypingHasNoCycleOfAnyLength` SUBSUMES the corpus's finite obstructions
rather than merely sitting beside them. -/
theorem grownUniverseTypingHasNoTwoCycleViaChain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelA : LevelExpr} {flagA : UniverseFlag} {levelB : LevelExpr} {flagB : UniverseFlag}
    (typedUp : HasTypeDescPi profile context (universeCodeCell levelA flagA)
        (universeCodeCell levelB flagB))
    (typedDown : HasTypeDescPi profile context (universeCodeCell levelB flagB)
        (universeCodeCell levelA flagA)) :
    False :=
  grownUniverseTypingHasNoCycleOfAnyLength (.step typedUp (.single typedDown))

/-- **Non-vacuity (length 1): a real classification edge exists.**  `Type@0 : Type@1` is a genuine
single-step chain in every context (the universe-formation rule `Type@e : Type@(e+1)` embedded into the grown
engine via `ofFormation`).  The acyclicity headline is over an INHABITED relation, not vacuously true. -/
theorem universeClassificationChain_nonVacuous {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    UniverseClassificationChain profile context LevelExpr.lzero flag LevelExpr.lzero.lsucc flag :=
  .single (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context LevelExpr.lzero flag))

/-- **Non-vacuity (length 2): a genuinely multi-step chain exists.**  `Type@0 : Type@1 : Type@2` is a real
2-edge chain, so `UniverseClassificationChain` captures loops longer than the shipped 2-cycle obstruction —
the irreflexivity guarantee is over chains of unbounded length, not just direct edges. -/
theorem universeClassificationChain_twoStep_nonVacuous {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    UniverseClassificationChain profile context LevelExpr.lzero flag
      LevelExpr.lzero.lsucc.lsucc flag :=
  .step (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context LevelExpr.lzero flag))
    (.single (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation context LevelExpr.lzero.lsucc flag)))

end FX1Poly.Typed
