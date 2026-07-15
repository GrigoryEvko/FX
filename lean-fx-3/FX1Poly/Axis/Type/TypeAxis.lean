import FX1Poly.Axis.Type.Level.LevelExprSimplify
import FX1Poly.Axis.Type.Level.LevelExprTower
import FX1Poly.Axis.Type.Universe.UniverseFlagStrength

/-! # type-0 — the Axis type ω-category, design-lock: the universe as a standalone Tarski structure

The fourth Axis ω-category axis (context · mode · term · TYPE), the foundational discharge dimension
(fx_design.md §6.3: "Dimension 1: Type … determines which grade elements are valid for the other
dimensions").  This is the `type-0` DESIGN-LOCK: it fixes the standalone Tarski-universe DATA MODEL the whole
type ladder (`type-1` … `type-21` + extended) builds on and ships it zero-axiom with one inhabited witness.
Mirrors the `mode-0` (`Axis/Mode/Mode.lean`) and `context-0` (`Axis/Context/Context.lean`) sibling
design-locks.

## What is locked here (the standalone Tarski data model)

LOCKED — the universe-as-a-Tarski-structure, standalone (no term/context/mode dependency):

  * **`UniverseCode`** — a universe CODE is a `LevelExpr × UniverseFlag`: a level expression paired with a
    large-cardinal-strength flag (the Setzer-Rathjen ladder — `standard` / `inaccessible` / `mahlo` / … /
    `reflecting` / `vopenka`; here "reflecting" is the SET-THEORETIC Σ²ₙ-reflection rung, NOT a Kan/cubical
    structure class).  This flag is the large-cardinal axis κ; it does NOT classify universe FIBRANCY — that
    is a SEPARATE, not-yet-built axis φ, orthogonal to κ.  This is exactly the shipped `gen_universeCode`
    payload (the "foundation stone": the level lives IN the payload, so the universe rule
    `Type@e : Type@(succ e)` is even statable — a bare/`Unit` level would re-open Girard's paradox).
  * **`StandaloneTarskiUniverse`** — the data model: a code carrier with a `level` / `flag` projection and a
    `successor` operation, locked PREDICATIVE — `successor` raises the level by exactly one and a code never
    classifies itself (`predicative : level (successor c) ≠ level c`).  This is the Tarski (code/decode)
    discipline, NOT Russell (`Type : Type`); no universe collapse, no top universe.
  * **`TypeAxis`** + the witness **`fxTypeAxis`** — bundles the Tarski universe with the LEVEL NORMALIZER
    (`LevelExpr.simplify`).  The witness DISCHARGES the model's proof-obligation fields with the real,
    home-module-proven lemmas: `predicative` ← `LevelExpr.ne_lsucc_self`, `normalize_sound` ←
    `LevelExpr.simplify_denote_eq`, `normalize_idempotent` ← `LevelExpr.simplify_idempotent`.  The witness
    fields ARE the honest carrier of those facts — there are no self-assigned "backed" flags; `fxTypeAxis`
    being well-typed IS the claim that the predicative Tarski model with a sound, idempotent (predicative
    Phase-A) level normalizer is inhabited.  `fxTypeAxis` is the value the whole `type-*` track must satisfy.

This file does NOT re-prove the substrate facts it bundles — they live, and are zero-axiom-gated, in their
home modules: predicativity / level normalization in `Axis/Type/Level/LevelExprSimplify.lean`, and the
Setzer-Rathjen flag ladder's decidable TOTAL ORDER (`UniverseFlag.le_refl` / `le_trans` / `le_antisymm` /
`le_total`) in `Axis/Type/Universe/UniverseFlagStrength.lean`.

## What is deferred (NOT shipped here)

The later/cross-axis type theory is genuinely open and is named only for navigation — none of it is shipped
by this design-lock:

  * `type-1` inductive / Σ (LEFT/initial) and `type-3` M-types (RIGHT/terminal coalgebra) — the dual adjoints.
  * `type-2` display + Π classifier — the decidable-fibration TYPE WRAPPER; lives in `Core/` (polycell
    §11.8.5), glued cross-axis `×type` / `fib-1`.
  * `type-7` definitional univalence `Id_U ↝ Equiv` and `type-8` SIP — ship in `Core/`, cross-axis `×type`.
  * The Tarski DECODE / `El` + the no-Type-in-Type metatheory (`grownUniverseCode_notTypedAtSelf`,
    `universeHierarchyHasNoTop`, the stratified-reducibility `tarskiDecode` / membership-iff) are ALREADY
    shipped in `Core/` and `Typed/` — referenced cross-axis, glued at `fib-2` / `type-2` (a Axis design-lock
    must not import up into `Typed/` / `Core/`).
  * `type-18` cumulative subtyping — the shipped engine is intentionally NON-cumulative (classification IS the
    successor); definitional cumulativity via explicit lift markers is deferred.
  * `type-14` large-cardinal universes — the `UniverseFlag` ladder + total order are shipped, but the
    set-theoretic ADMISSION strengths are enum-only / unproven.
  * `type-21` CAPSTONE — the standalone type ω-category record (full adjoint string + univalence + joint
    canonicity), the `fib-*`-consumable deliverable (cf. `mode-21`'s `ModeOmega`).

## Zero-axiom verification

The data model + witnesses are `rfl`-pinned, the proof-obligation fields are discharged by home-module lemmas.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditAxisTypeAxis.lean`.  Imports only Axis/Type substrate — Init + `FX1Poly.Universe`.
-/

namespace FX1Poly.Axis

open FX1Poly.Universe

/-! ## The standalone Tarski data model -/

/-- A **universe code** in the standalone Tarski structure: a level expression paired with a
large-cardinal-strength flag — exactly the shipped `gen_universeCode` payload (`LevelExpr × UniverseFlag`)
seen standalone, with no term/context/mode dependency. -/
structure UniverseCode where
  /-- The universe's level expression. -/
  level : LevelExpr
  /-- The large-cardinal-strength flag (the Setzer-Rathjen ladder degree — the consistency-strength axis κ).
  NOT a fibrancy classifier: universe FIBRANCY (Kan/cubical structure) is a separate axis φ, orthogonal to
  this one and not yet built. -/
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
  /-- Each code's large-cardinal-strength flag (the κ axis; not a fibrancy classifier). -/
  flag : Code → UniverseFlag
  /-- The next universe up (`Type@e ↝ Type@(succ e)`). -/
  successor : Code → Code
  /-- The successor raises the level by exactly one. -/
  successor_level : ∀ code : Code, level (successor code) = (level code).lsucc
  /-- The successor keeps the large-cardinal-strength flag (the successor moves only the level, not κ). -/
  successor_flag : ∀ code : Code, flag (successor code) = flag code
  /-- PREDICATIVITY: a code never classifies itself — its successor's level differs from its own. -/
  predicative : ∀ code : Code, level (successor code) ≠ level code
  /-- NO DEFLATION: a code's DOUBLE successor never returns to its own level — the deflation twin of
  `predicative` (`Type@(e+2) ≠ Type@e` at the code level). -/
  noDeflation : ∀ code : Code, level (successor (successor code)) ≠ level code
  /-- The level algebra carries an ℕ-indexed TOWER: `levelTower n` is the `n`-th universe's level, and the
  family injects ℕ into the levels — the infinite, non-collapsing hierarchy made explicit at the code level
  (the no-top witness the Typed universe tower delegates to). -/
  levelTower : Nat → LevelExpr
  /-- The tower has no collapse and no top: distinct naturals name distinct levels. -/
  levelTower_injective : ∀ towerIndexLeft towerIndexRight : Nat,
    levelTower towerIndexLeft = levelTower towerIndexRight → towerIndexLeft = towerIndexRight

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
  noDeflation := fun code => (LevelExpr.ne_lsuccLsucc_self code.level).symm
  levelTower := universeLevelOfNat
  levelTower_injective := fun _ _ levelsEqual => universeLevelOfNat_injective levelsEqual

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
predicative normalizer.  The proof-obligation fields are discharged by the home-module lemmas
`LevelExpr.simplify_denote_eq` (soundness) and `LevelExpr.simplify_idempotent`. -/
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

/-- Design-lock tooth: the canonical Tarski universe's level tower IS the relocated Axis
`universeLevelOfNat` — the axis OWNS the ℕ ↪ levels injection the Typed universe tower
(`universeHierarchy_isInfiniteNonCollapsingTower`) delegates to, pinned definitionally. -/
theorem fxTarskiUniverse_levelTower_isUniverseLevelOfNat :
    fxTarskiUniverse.levelTower = universeLevelOfNat := rfl

end FX1Poly.Axis
