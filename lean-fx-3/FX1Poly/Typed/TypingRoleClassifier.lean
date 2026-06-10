import FX1Poly.Typed.IntroRuleDesc
import FX1Poly.Typed.ElimRuleDesc

/-! # FX1Poly/Typed/TypingRoleClassifier — the unified typing-role dispatch over the three rule tables (GTL-19)

`HasTypeDesc.lean` (`typingRuleDescOf`), `IntroRuleDesc.lean` (`introRuleDescOf`, GTL-15) and
`ElimRuleDesc.lean` (`elimRuleDescOf`, GTL-17) each describe ONE typing-rule family as a pure-syntax
`Option`-valued table: FORMATION (output a universe code from the children's levels), INTRODUCTION (output
the introduced type from the rule's type-parameters) and ELIMINATION (output children-dependent — the motive
applied to the scrutinee).  Each table has cascade-death metadata lemmas and a non-vacuous reconstruction
(`hasTypeDesc_piFormation_viaGenArm` / `hasTypeDescPi_piIntro_viaIntroDesc` / `hasTypeDescPi_piElim_via
ElimDesc`).

This file unifies the three into ONE dispatch — the substrate a single fundamental-metatheory bundle over the
rule tables (GTL-20) and the subject-reduction master dispatcher (SN-055) route over.  It answers, for any
generator, "which typing-rule family (if any) does it belong to?", and proves the answer is WELL-DEFINED: the
three tables are PAIRWISE DISJOINT, so a generator carries AT MOST ONE typing rule — its typing ROLE is unique.

  * `TypingRole` (formation / intro / elim) + `typingRoleOf` — the unified classifier (consult the three
    tables in order; the disjointness below makes the order immaterial).
  * **`typingRuleDescOf_excludesIntro` / `_excludesElim` / `introRuleDescOf_excludesElim`** (+ symmetric) —
    the ROLE-UNIQUENESS core: the three tables are pairwise disjoint.  Each is the established
    `enumeration-lemma + rfl-reduction` pattern: a generator with an introduction rule IS `gen_lam`
    (`introRuleDescOf_isLam`), and `typingRuleDescOf gen_lam = none` (`gen_lam` is not a formation former),
    so no generator carries both.  Adding a new former extends the relevant enumeration lemma by one disjunct,
    never a per-consumer cascade (P13 cascade-freedom, now spanning all three families).
  * `typingRoleOf_formation_of` / `_intro_of` / `_elim_of` — COMPLETENESS: every table-member is classified
    with its role (the intro/elim directions consume the disjointness, since the classifier checks formation
    first).  `typingRoleOf_isNone_iff` — a generator has NO typing role iff it is in NONE of the three tables.
    NOTE: roleless does NOT mean untyped — the engine also types two BESPOKE non-table heads, `gen_var` (the
    `var` arm) and `gen_universeCode` (the `universeFormation` arm), both roleless yet typed; `typingRoleOf`
    covers only the table-driven heads (see `TypingRoleEngineBridge` for the engine-coherence bridge).
  * `typingRoleOf_*_smoke` — concrete witnesses: `gen_piTyCode ↦ formation`, `gen_lam ↦ intro`,
    `gen_app ↦ elim`, `gen_boolTrue ↦ none`.

## Zero-axiom

`typingRoleOf` is a pure-syntax `Option`-valued classifier; the disjointness lemmas are `enumeration-lemma`
(`introRuleDescOf_isLam` / `elimRuleDescOf_isApp`) + `subst` + `rfl` (the excluded table reduces to `none` on
the now-concrete generator); completeness is `unfold` + `if_pos`/`if_neg` over the `Option.isSome` guards;
the none-characterization is `by_cases` over the three guards; the smokes are `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-! ## Pairwise table disjointness — the role-uniqueness core

A generator carries at most one of the three typing rules.  Each direction routes through the relevant
table's enumeration lemma (the generator IS the table's sole former) and the `rfl`-reduction of the OTHER
table to `none` on that concrete former. -/

/-- A generator carrying an INTRODUCTION rule carries NO formation rule (`gen_lam` is not a formation
former).  Routes through `introRuleDescOf_isLam` + `typingRuleDescOf gen_lam = none`. -/
theorem typingRuleDescOf_excludesIntro {generator : Generator} {rule : IntroRuleDesc}
    (isIntro : introRuleDescOf generator = some rule) :
    typingRuleDescOf generator = none := by
  have hLam : generator = Generator.gen_lam := introRuleDescOf_isLam isIntro
  subst hLam
  rfl

/-- A generator carrying an ELIMINATION rule carries NO formation rule (`gen_app` is not a formation
former). -/
theorem typingRuleDescOf_excludesElim {generator : Generator} {rule : ElimRuleDesc}
    (isElim : elimRuleDescOf generator = some rule) :
    typingRuleDescOf generator = none := by
  have hApp : generator = Generator.gen_app := elimRuleDescOf_isApp isElim
  subst hApp
  rfl

/-- A generator carrying an INTRODUCTION rule carries NO elimination rule (`gen_lam ≠ gen_app`). -/
theorem introRuleDescOf_excludesElim {generator : Generator} {rule : IntroRuleDesc}
    (isIntro : introRuleDescOf generator = some rule) :
    elimRuleDescOf generator = none := by
  have hLam : generator = Generator.gen_lam := introRuleDescOf_isLam isIntro
  subst hLam
  rfl

/-- A generator carrying an ELIMINATION rule carries NO introduction rule (`gen_app ≠ gen_lam`) — the
symmetric companion of `introRuleDescOf_excludesElim`. -/
theorem elimRuleDescOf_excludesIntro {generator : Generator} {rule : ElimRuleDesc}
    (isElim : elimRuleDescOf generator = some rule) :
    introRuleDescOf generator = none := by
  have hApp : generator = Generator.gen_app := elimRuleDescOf_isApp isElim
  subst hApp
  rfl

/-! ## The unified typing-role classifier -/

/-- The typing ROLE of a generator: which of the three typing-rule families (formation / introduction /
elimination) it belongs to.  A future ground-data former is absorbed by extending the relevant table, never
this enum. -/
inductive TypingRole where
  | formation
  | intro
  | elim
  deriving DecidableEq

/-- The unified typing-role classifier: consult `typingRuleDescOf`, then `introRuleDescOf`, then
`elimRuleDescOf`.  The pairwise disjointness above makes the consultation order immaterial (a generator is in
at most one table), so the role it returns is the generator's UNIQUE typing role — or `none` if the engine
leaves it untyped (the data constructors / eliminators). -/
def typingRoleOf (generator : Generator) : Option TypingRole :=
  if (typingRuleDescOf generator).isSome then some .formation
  else if (introRuleDescOf generator).isSome then some .intro
  else if (elimRuleDescOf generator).isSome then some .elim
  else none

/-! ## Completeness — every table-member is classified with its role

The formation direction is immediate (formation is consulted first); the introduction and elimination
directions CONSUME the disjointness (their tables are reached only after the earlier guards fail, which the
disjointness guarantees). -/

/-- A formation former is classified as `formation`. -/
theorem typingRoleOf_formation_of {generator : Generator}
    (isFormation : (typingRuleDescOf generator).isSome = true) :
    typingRoleOf generator = some TypingRole.formation := by
  dsimp only [typingRoleOf]
  rw [if_pos isFormation]

/-- An introduction former is classified as `intro` — consumes `typingRuleDescOf_excludesIntro` (the
formation guard must fail first). -/
theorem typingRoleOf_intro_of {generator : Generator} {rule : IntroRuleDesc}
    (isIntro : introRuleDescOf generator = some rule) :
    typingRoleOf generator = some TypingRole.intro := by
  have formationNone : typingRuleDescOf generator = none := typingRuleDescOf_excludesIntro isIntro
  dsimp only [typingRoleOf]
  rw [formationNone, Option.isSome_none, if_neg (by decide), isIntro, Option.isSome_some, if_pos rfl]

/-- An elimination former is classified as `elim` — consumes `typingRuleDescOf_excludesElim` and
`elimRuleDescOf_excludesIntro` (both earlier guards must fail). -/
theorem typingRoleOf_elim_of {generator : Generator} {rule : ElimRuleDesc}
    (isElim : elimRuleDescOf generator = some rule) :
    typingRoleOf generator = some TypingRole.elim := by
  have formationNone : typingRuleDescOf generator = none := typingRuleDescOf_excludesElim isElim
  have introNone : introRuleDescOf generator = none := elimRuleDescOf_excludesIntro isElim
  dsimp only [typingRoleOf]
  rw [formationNone, Option.isSome_none, if_neg (by decide), introNone, Option.isSome_none,
    if_neg (by decide), isElim, Option.isSome_some, if_pos rfl]

/-- **A generator has NO typing role iff it is in NONE of the three tables.**  The roleless generators split
into two kinds: the genuinely-UNTYPED data constructors / eliminators (`HasTypeDescPiDataHeadUntyped`), AND the
two BESPOKE typed heads `gen_var` / `gen_universeCode` (typed by the `var` / `universeFormation` arms, which are
not table rows).  So `typingRoleOf = none` means "not a table-driven typed head", NOT "untyped";
`TypingRoleEngineBridge.cellUntypedWhenRolelessAndNonBespoke` recovers untyping by additionally excluding the
two bespoke heads. -/
theorem typingRoleOf_isNone_iff (generator : Generator) :
    typingRoleOf generator = none ↔
      typingRuleDescOf generator = none ∧ introRuleDescOf generator = none ∧
        elimRuleDescOf generator = none := by
  constructor
  · intro roleNone
    dsimp only [typingRoleOf] at roleNone
    cases hFormation : typingRuleDescOf generator with
    | some rule =>
        rw [hFormation, Option.isSome_some, if_pos rfl] at roleNone
        exact absurd roleNone (by decide)
    | none =>
        cases hIntro : introRuleDescOf generator with
        | some rule =>
            rw [hFormation, hIntro, Option.isSome_none, if_neg (by decide), Option.isSome_some,
              if_pos rfl] at roleNone
            exact absurd roleNone (by decide)
        | none =>
            cases hElim : elimRuleDescOf generator with
            | some rule =>
                rw [hFormation, hIntro, hElim, Option.isSome_none, if_neg (by decide),
                  Option.isSome_none, if_neg (by decide), Option.isSome_some, if_pos rfl] at roleNone
                exact absurd roleNone (by decide)
            | none => exact ⟨rfl, rfl, rfl⟩
  · intro ⟨formationNone, introNone, elimNone⟩
    dsimp only [typingRoleOf]
    rw [formationNone, Option.isSome_none, if_neg (by decide), introNone, Option.isSome_none,
      if_neg (by decide), elimNone, Option.isSome_none, if_neg (by decide)]

/-! ## Concrete classification witnesses -/

/-- `gen_piTyCode` (a Π-FORMATION former) is classified as `formation`. -/
theorem typingRoleOf_piTyCode_smoke : typingRoleOf .gen_piTyCode = some TypingRole.formation := rfl

/-- `gen_lam` (Π-INTRODUCTION / λ) is classified as `intro`. -/
theorem typingRoleOf_lam_smoke : typingRoleOf .gen_lam = some TypingRole.intro := rfl

/-- `gen_app` (Π-ELIMINATION / application) is classified as `elim`. -/
theorem typingRoleOf_app_smoke : typingRoleOf .gen_app = some TypingRole.elim := rfl

/-- `gen_boolTrue` (a ground-data constructor — proven untyped by the formation-only engine) has NO typing
role. -/
theorem typingRoleOf_boolTrue_smoke : typingRoleOf .gen_boolTrue = none := rfl

end FX1Poly.Typed
