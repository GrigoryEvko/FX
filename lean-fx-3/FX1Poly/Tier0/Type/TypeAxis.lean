import FX1Poly.Tier0.Type.Level.LevelExprSimplify
import FX1Poly.Tier0.Type.Universe.UniverseFlagStrength

/-! # type-0 — the Tier0 type ω-category, design-lock: the universe as a standalone Tarski structure

The fourth Tier0 ω-category axis (context · mode · term · TYPE), the foundational discharge dimension
(fx_design.md §6.3: "Dimension 1: Type … determines which grade elements are valid for the other
dimensions").  This is the `type-0` DESIGN-LOCK: it fixes the standalone Tarski-universe DATA MODEL the whole
type ladder (`type-1` … `type-21` + extended) builds on, ships it zero-axiom with one inhabited witness, and
records every later/cross-axis theorem as a `:= false` honesty marker naming WHERE it lands.  Mirrors the
`mode-0` (`Tier0/Mode/Mode.lean`) and `context-0` (`Tier0/Context/Context.lean`) sibling design-locks.

## What is locked here (the standalone Tarski data model), and what is deferred

LOCKED — the universe-as-a-Tarski-structure, standalone (no term/context/mode dependency):

  * **`UniverseCode`** — a universe CODE is a `LevelExpr × UniverseFlag`: a level expression paired with a
    structural-reflection flag.  This is exactly the shipped `gen_universeCode` payload (the "foundation
    stone": the level lives IN the payload, so the universe rule `Type@e : Type@(succ e)` is even statable —
    a bare/`Unit` level would re-open Girard's paradox).
  * **`StandaloneTarskiUniverse`** — the data model: a code carrier with a `level` / `flag` projection and a
    `successor` operation, locked PREDICATIVE — `successor` raises the level by exactly one and a code never
    classifies itself (`predicative : level (successor c) ≠ level c`).  This is the Tarski (code/decode)
    discipline, NOT Russell (`Type : Type`); no universe collapse, no top universe.
  * **`TypeAxis`** + the witness **`fxTypeAxis`** — bundles the Tarski universe with the LEVEL NORMALIZER
    (`LevelExpr.simplify`), proven SOUND (preserves denotation) and IDEMPOTENT (reaches the structural normal
    form in one pass — the predicative Phase-A normalizer).  The "design-lock teeth": `fxTypeAxis` is a value
    the whole `type-*` track must satisfy, pinned definitionally.
  * Three backed flips (`= true`, each conjoined with a named shipped theorem): predicative level
    normalization (`fxType_hasLevelNormalization`), the predicative successor / no-self-classification guard
    (`fxType_hasPredicativeUniverse`), and the Setzer-Rathjen flag ladder as a decidable TOTAL ORDER
    (`fxType_hasUniverseFlagLadder`).

DEFERRED (recorded as `:= false` markers naming the destination rung / cross-axis Core gluing):

  * `type-1` inductive/Σ (LEFT/initial) · `type-3` M-types (RIGHT/terminal coalgebra) — the dual adjoints.
  * `type-2` display+Π classifier — the decidable-fibration TYPE WRAPPER; lives in `Core/` (polycell §11.8.5),
    glued cross-axis `×type` / `fib-1`.
  * `type-7` definitional univalence `Id_U ↝ Equiv` / `type-8` SIP — ship in `Core/`, cross-axis `×type`.
  * The Tarski DECODE / `El` + the no-Type-in-Type metatheory (`grownUniverseCode_notTypedAtSelf`,
    `universeHierarchyHasNoTop`, the stratified-reducibility `tarskiDecode` / membership-iff) are ALREADY
    shipped in `Core/` and `Typed/` — referenced here as cross-axis, glued at `fib-2` / `type-2` (a Tier0
    design-lock must not import up into `Typed/`/`Core/`).
  * `type-18` cumulative subtyping — the shipped engine is intentionally NON-cumulative (classification IS the
    successor); definitional cumulativity via explicit lift markers is deferred.
  * `type-14` large-cardinal universes — `UniverseFlag`'s ladder + total order are shipped, but the
    set-theoretic ADMISSION strengths are enum-only / unproven.
  * `type-21` CAPSTONE — the standalone type ω-category record (full adjoint string + univalence + joint
    canonicity), the `fib-*`-consumable deliverable (cf. `mode-21`'s `ModeOmega`).

## Zero-axiom verification

Three `Bool` markers `:= true` (each with an `_isBacked` conjunction closed by `rfl` + named shipped
theorems: `simplify_denote_eq` / `simplify_idempotent`, `ne_lsucc_self`, the `UniverseFlag` order family) and
seven `:= false` deferral markers.  The data model + witnesses are `rfl`-pinned.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTier0TypeAxis.lean`.  Imports only Tier0/Type substrate — Init + `FX1Poly.Universe`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Universe

/-! ## The standalone Tarski data model -/

/-- A **universe code** in the standalone Tarski structure: a level expression paired with a
structural-reflection flag — exactly the shipped `gen_universeCode` payload (`LevelExpr × UniverseFlag`) seen
standalone, with no term/context/mode dependency. -/
structure UniverseCode where
  /-- The universe's level expression. -/
  level : LevelExpr
  /-- The structural-reflection flag (the Setzer-Rathjen ladder degree). -/
  flag : UniverseFlag

/-- A **standalone Tarski universe**: a code carrier with `level` / `flag` projections and a `successor`
operation, locked PREDICATIVE.  `successor` raises the level by exactly one (`successor_level`), keeps the
flag (`successor_flag`), and no code classifies itself (`predicative` — the no-Type-in-Type guard at the code
level).  Tarski-style (code/decode), never Russell (`Type : Type`). -/
structure StandaloneTarskiUniverse where
  /-- The carrier of universe codes. -/
  Code : Type
  /-- Each code's level. -/
  level : Code → LevelExpr
  /-- Each code's reflection flag. -/
  flag : Code → UniverseFlag
  /-- The next universe up (`Type@e ↝ Type@(succ e)`). -/
  successor : Code → Code
  /-- The successor raises the level by exactly one. -/
  successor_level : ∀ code : Code, level (successor code) = (level code).lsucc
  /-- The successor keeps the reflection flag. -/
  successor_flag : ∀ code : Code, flag (successor code) = flag code
  /-- PREDICATIVITY: a code never classifies itself — its successor's level differs from its own. -/
  predicative : ∀ code : Code, level (successor code) ≠ level code

/-- The canonical FX standalone Tarski universe: codes are `UniverseCode`, the successor bumps the level via
`LevelExpr.lsucc`, and predicativity is `LevelExpr.ne_lsucc_self`. -/
def fxTarskiUniverse : StandaloneTarskiUniverse where
  Code := UniverseCode
  level := UniverseCode.level
  flag := UniverseCode.flag
  successor := fun code => { level := code.level.lsucc, flag := code.flag }
  successor_level := fun _ => rfl
  successor_flag := fun _ => rfl
  predicative := fun code => (LevelExpr.ne_lsucc_self code.level).symm

/-! ## The type-axis bundle + witness -/

/-- The **type-axis datum**: a standalone Tarski universe together with the LEVEL NORMALIZER, proven sound
(denotation-preserving) and idempotent (reaches the structural normal form).  The bundle the whole `type-*`
track must satisfy. -/
structure TypeAxis where
  /-- The standalone Tarski universe. -/
  tarskiUniverse : StandaloneTarskiUniverse
  /-- The level-expression normalizer. -/
  normalizeLevel : LevelExpr → LevelExpr
  /-- The normalizer is SOUND: it preserves the denotation of every level expression. -/
  normalize_sound : ∀ (levelExpr : LevelExpr) (env : Nat → Nat),
    (normalizeLevel levelExpr).denote env = levelExpr.denote env
  /-- The normalizer is IDEMPOTENT: its output is a fixed point (the structural normal form). -/
  normalize_idempotent : ∀ levelExpr : LevelExpr,
    normalizeLevel (normalizeLevel levelExpr) = normalizeLevel levelExpr

/-- The canonical FX type-axis datum: the FX Tarski universe wired to the shipped `LevelExpr.simplify`
predicative normalizer. -/
def fxTypeAxis : TypeAxis where
  tarskiUniverse := fxTarskiUniverse
  normalizeLevel := LevelExpr.simplify
  normalize_sound := LevelExpr.simplify_denote_eq
  normalize_idempotent := LevelExpr.simplify_idempotent

/-- Design-lock tooth: the FX type-axis universe is the canonical Tarski universe, pinned definitionally. -/
theorem fxTypeAxis_universe_isTarski : fxTypeAxis.tarskiUniverse = fxTarskiUniverse := rfl

/-- Design-lock tooth: the FX type-axis normalizer is the shipped predicative `LevelExpr.simplify`. -/
theorem fxTypeAxis_normalizer_isSimplify : fxTypeAxis.normalizeLevel = LevelExpr.simplify := rfl

/-- Design-lock tooth: the canonical Tarski universe's codes are `UniverseCode`. -/
theorem fxTarskiUniverse_code_isUniverseCode : fxTarskiUniverse.Code = UniverseCode := rfl

/-! ## The backed flips (the metatheory the standalone type layer genuinely earns) -/

/-- **Honesty marker** — `type-0` (predicative level normalization).  The level theory `LevelExpr` has the
predicative Phase-A normalizer `simplify`, proven SOUND and IDEMPOTENT (structural normal form in one pass).
Backed in `fxType_levelNormalization_isBacked`.  `= true`.  Phase-B (lmax canonical ordering, lsucc
distributivity, open-term `denoteEquiv`) is deferred. -/
def fxType_hasLevelNormalization : Bool := true

/-- ★ **Backed flip (level normalization).**  The marker is `true` AND `LevelExpr.simplify` is SOUND
(`simplify_denote_eq`) and IDEMPOTENT (`simplify_idempotent`). -/
theorem fxType_levelNormalization_isBacked :
    fxType_hasLevelNormalization = true
      ∧ (∀ (levelExpr : LevelExpr) (env : Nat → Nat),
          levelExpr.simplify.denote env = levelExpr.denote env)
      ∧ (∀ levelExpr : LevelExpr, levelExpr.simplify.simplify = levelExpr.simplify) :=
  ⟨rfl, LevelExpr.simplify_denote_eq, LevelExpr.simplify_idempotent⟩

/-- **Honesty marker** — `type-0` (predicative universe successor).  The universe is predicative: a level is
never its own successor (`ne_lsucc_self`), so in the standalone Tarski universe no code classifies itself —
the syntactic no-Type-in-Type guard.  Backed in `fxType_predicativeUniverse_isBacked`.  `= true`. -/
def fxType_hasPredicativeUniverse : Bool := true

/-- ★ **Backed flip (predicative universe).**  The marker is `true` AND (i) no level equals its own successor
(`LevelExpr.ne_lsucc_self`); (ii) in the canonical Tarski universe no code classifies itself
(`fxTarskiUniverse.predicative`). -/
theorem fxType_predicativeUniverse_isBacked :
    fxType_hasPredicativeUniverse = true
      ∧ (∀ levelExpr : LevelExpr, levelExpr ≠ levelExpr.lsucc)
      ∧ (∀ code : UniverseCode,
          fxTarskiUniverse.level (fxTarskiUniverse.successor code) ≠ fxTarskiUniverse.level code) :=
  ⟨rfl, LevelExpr.ne_lsucc_self, fxTarskiUniverse.predicative⟩

/-- **Honesty marker** — `type-0` (the universe flag ladder).  The Setzer-Rathjen large-cardinal flag ladder
`UniverseFlag` (standard … Vopěnka) carries a DECIDABLE TOTAL ORDER on structural-reflection strength.  Backed
in `fxType_universeFlagLadder_isBacked`.  `= true`.  The set-theoretic ADMISSION strengths of the
large-cardinal flags are deferred (`type-14`, enum-only). -/
def fxType_hasUniverseFlagLadder : Bool := true

/-- ★ **Backed flip (universe flag ladder).**  The marker is `true` AND the flag strength order is reflexive
(`le_refl`), transitive (`le_trans`), antisymmetric (`le_antisymm`), and total (`le_total`). -/
theorem fxType_universeFlagLadder_isBacked :
    fxType_hasUniverseFlagLadder = true
      ∧ (∀ flag : UniverseFlag, flag ≤ flag)
      ∧ (∀ {leftFlag midFlag rightFlag : UniverseFlag},
          leftFlag ≤ midFlag → midFlag ≤ rightFlag → leftFlag ≤ rightFlag)
      ∧ (∀ {leftFlag rightFlag : UniverseFlag},
          leftFlag ≤ rightFlag → rightFlag ≤ leftFlag → leftFlag = rightFlag)
      ∧ (∀ leftFlag rightFlag : UniverseFlag, leftFlag ≤ rightFlag ∨ rightFlag ≤ leftFlag) :=
  ⟨rfl, UniverseFlag.le_refl, UniverseFlag.le_trans, UniverseFlag.le_antisymm, UniverseFlag.le_total⟩

/-! ## Honesty markers (deferred to later type rungs / cross-axis Core gluing) -/

/-- **Honesty marker.**  Dependent SUM + INDUCTIVE types as left adjoints / initial algebras — `type-1`,
deferred.  `= false`. -/
def fxType_hasInductiveTypes : Bool := false

/-- **Honesty marker.**  The DISPLAY + Π CLASSIFIER (the decidable-fibration type wrapper) — `type-2`, ships
in `Core/` (the dim-0 soundness stratum), cross-axis `×type` / `fib-1`, deferred.  `= false`. -/
def fxType_hasDisplayClassifier : Bool := false

/-- **Honesty marker.**  The Tarski DECODE / `El` + the no-Type-in-Type metatheory
(`grownUniverseCode_notTypedAtSelf`, `universeHierarchyHasNoTop`, stratified-reducibility `tarskiDecode`) are
shipped in `Core/`/`Typed/`, glued at `fib-2` / `type-2`, deferred from this Tier0 axis.  `= false`. -/
def fxType_hasTarskiDecodeGluing : Bool := false

/-- **Honesty marker.**  DEFINITIONAL UNIVALENCE `Id_U ↝ Equiv` + the structure-identity principle —
`type-7`/`type-8`, ship in `Core/`, cross-axis `×type`, deferred.  `= false`. -/
def fxType_hasDefinitionalUnivalence : Bool := false

/-- **Honesty marker.**  CUMULATIVE SUBTYPING `Type@u <: Type@v` — `type-18`; the shipped engine is
intentionally NON-cumulative (classification IS the successor), cumulativity via explicit lift markers,
deferred.  `= false`. -/
def fxType_hasCumulativeSubtyping : Bool := false

/-- **Honesty marker.**  The set-theoretic large-cardinal ADMISSION strengths of the `UniverseFlag` ladder —
`type-14`; the ladder + order are shipped, the consistency-strength content is enum-only / unproven,
deferred.  `= false`. -/
def fxType_hasLargeCardinalAdmission : Bool := false

/-- **Honesty marker.**  The standalone type ω-category CAPSTONE (full adjoint string + univalence + joint
canonicity, the `fib-*`-consumable record) — `type-21`, deferred.  `= false`. -/
def fxType_hasTypeOmegaCategory : Bool := false

end FX1Poly.Tier0
