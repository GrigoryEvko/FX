import FX1Poly.Typed.TypingRoleClassifier
import FX1Poly.Typed.HasTypeDescPiRootGeneric

/-! # FX1Poly/Typed/TypingRoleEngineBridge — the classifier ↔ engine coherence (GTL-19 follow-up)

`TypingRoleClassifier.lean` (GTL-ROLE, #985) defined the SYNTACTIC classifier `typingRoleOf` over the three
rule tables (formation / introduction / elimination).  `HasTypeDescPiRootGeneric.lean` proved the SEMANTIC
head classification `HasTypeDescPi.subjectRootGeneratorGeneric`: a grown-typed subject is rooted at one of the
four non-former heads (`gen_var` / `gen_universeCode` / `gen_lam` / `gen_app`) OR carries a formation rule.

This file bridges the two — the coherence of the classifier with the engine, and the honest correction of a
`typingRoleOf` subtlety.  `typingRoleOf` classifies the table-driven heads (the formation FORMERS, `gen_lam`,
`gen_app`); but the engine ALSO types two BESPOKE non-table heads via dedicated arms: `gen_var` (the `var`
rule) and `gen_universeCode` (the `ofFormation ∘ universeFormation` rule).  Both have `typingRoleOf = none` —
they are roleless yet TYPED.  So `typingRoleOf g = none` does NOT mean "g is untyped"; it means "g is not a
table-driven typed head" (g is a bespoke head OR genuinely untyped data).

  * **`HasTypeDescPi.subjectHeadHasRoleOrBespoke`** — THE BRIDGE: every grown-typed subject's head either
    carries a `typingRoleOf` role (`some`) or is one of the two bespoke heads (`gen_var` / `gen_universeCode`).
    The COMPLETENESS of `typingRoleOf` with respect to the engine: the role-classification covers every
    table-driven typed head; only the two bespoke arms escape it.  Maps each disjunct of
    `subjectRootGeneratorGeneric` through the `typingRoleOf_*_of` completeness lemmas (#985).
  * `HasTypeDescPi.closedSubjectHeadHasRoleOrIsUniverseCode` — the CLOSED corollary: in the empty context the
    `gen_var` disjunct vanishes (the `var` payload is `Fin 0`), so a closed typed subject is role-bearing OR
    `gen_universeCode`-rooted.
  * **`HasTypeDescPi.cellUntypedWhenRolelessAndNonBespoke`** — the contrapositive, the HONEST untyping
    criterion: a cell whose head is roleless (`typingRoleOf = none`) AND neither bespoke head (`≠ gen_var`,
    `≠ gen_universeCode`) has no grown typing.  This is `cellHasNoTypingWhenRootGenericallyExcluded` rephrased
    through `typingRoleOf` (consuming `typingRoleOf_isNone_iff` to recover the three `*RuleDescOf = none`
    facts), with the two bespoke heads made EXPLICIT — the precise statement of which roleless generators are
    untyped (the genuine data constructors / eliminators) versus typed (`gen_var` / `gen_universeCode`).
  * `HasTypeDescPi.boolTrueCellUntypedViaRole` — a smoke: `gen_boolTrue` (roleless, non-bespoke) is untyped,
    rederived through the `typingRoleOf` route (`typingRoleOf gen_boolTrue = none` by `rfl`).

## Zero-axiom

The bridge is an `rcases` on `subjectRootGeneratorGeneric` mapping each head to its role (`typingRoleOf_lam_
smoke` / `_app_smoke` / `typingRoleOf_formation_of`) or bespoke disjunct; the contrapositive destructs
`typingRoleOf_isNone_iff` and applies the table-generic refutation; the head-distinctness helpers are
`subst` + table-`rfl` + `cases` on `some = none`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A generator carrying NO introduction rule is not `gen_lam` (`introRuleDescOf gen_lam = some`). -/
theorem notGenLam_ofIntroRuleDescNone {generator : Generator}
    (introNone : introRuleDescOf generator = none) : generator ≠ Generator.gen_lam := by
  intro isLam
  subst isLam
  rw [introRuleDescOf_lam] at introNone
  cases introNone

/-- A generator carrying NO elimination rule is not `gen_app` (`elimRuleDescOf gen_app = some`). -/
theorem notGenApp_ofElimRuleDescNone {generator : Generator}
    (elimNone : elimRuleDescOf generator = none) : generator ≠ Generator.gen_app := by
  intro isApp
  subst isApp
  rw [elimRuleDescOf_app] at elimNone
  cases elimNone

/-- ★ **The classifier ↔ engine bridge.**  Every grown-typed subject's head either carries a `typingRoleOf`
role (a formation former / `gen_lam` / `gen_app`) or is one of the two BESPOKE non-table heads (`gen_var`,
typed by the `var` arm; `gen_universeCode`, typed by `ofFormation ∘ universeFormation`).  The COMPLETENESS of
`typingRoleOf` with respect to the engine: the table-driven role classification covers every typed head except
the two bespoke arms.  Each disjunct of `subjectRootGeneratorGeneric` maps to its role via the #985
completeness lemmas (`typingRoleOf_lam_smoke` / `_app_smoke` / `typingRoleOf_formation_of`) or to a bespoke
disjunct. -/
theorem HasTypeDescPi.subjectHeadHasRoleOrBespoke {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    (∃ role : TypingRole, typingRoleOf subject.rootGenerator = some role) ∨
      subject.rootGenerator = Generator.gen_var ∨
      subject.rootGenerator = Generator.gen_universeCode := by
  rcases typed.subjectRootGeneratorGeneric with isVar | isUniverse | isLam | isApp | ⟨rule, isFormer⟩
  · exact Or.inr (Or.inl isVar)
  · exact Or.inr (Or.inr isUniverse)
  · exact Or.inl ⟨TypingRole.intro, by rw [isLam]; exact typingRoleOf_lam_smoke⟩
  · exact Or.inl ⟨TypingRole.elim, by rw [isApp]; exact typingRoleOf_app_smoke⟩
  · exact Or.inl ⟨TypingRole.formation, typingRoleOf_formation_of (by rw [isFormer, Option.isSome_some])⟩

/-- **The CLOSED classifier ↔ engine bridge.**  In the empty context the `gen_var` disjunct vanishes (the
`var` payload is `Fin 0`, uninhabited), so a closed grown-typed subject is role-bearing or `gen_universeCode`-
rooted — exactly the closed-canonical-forms shape the consistency argument turns on (only `gen_app` of the
remaining role/bespoke heads classifies at a non-universe/non-Π type). -/
theorem HasTypeDescPi.closedSubjectHeadHasRoleOrIsUniverseCode {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    (∃ role : TypingRole, typingRoleOf subject.rootGenerator = some role) ∨
      subject.rootGenerator = Generator.gen_universeCode := by
  rcases typed.closedSubjectRootGeneratorGeneric with isUniverse | isLam | isApp | ⟨rule, isFormer⟩
  · exact Or.inr isUniverse
  · exact Or.inl ⟨TypingRole.intro, by rw [isLam]; exact typingRoleOf_lam_smoke⟩
  · exact Or.inl ⟨TypingRole.elim, by rw [isApp]; exact typingRoleOf_app_smoke⟩
  · exact Or.inl ⟨TypingRole.formation, typingRoleOf_formation_of (by rw [isFormer, Option.isSome_some])⟩

/-- ★ **The honest untyping criterion.**  A cell whose head is ROLELESS (`typingRoleOf = none`) AND neither
bespoke head (`≠ gen_var`, `≠ gen_universeCode`) has no grown typing.  The contrapositive of the bridge:
`typingRoleOf = none` alone does NOT force untyped (`gen_var` / `gen_universeCode` are roleless yet typed);
excluding those two bespoke heads recovers untyping.  Routes `typingRoleOf_isNone_iff` (#985) — which yields
all three `*RuleDescOf = none` — into the table-generic `cellHasNoTypingWhenRootGenericallyExcluded`.  This is
the precise `typingRoleOf`-phrasing of the canonical-forms boundary: the genuinely-untyped roleless heads are
exactly the data constructors / eliminators (everything roleless except the two bespoke arms). -/
theorem HasTypeDescPi.cellUntypedWhenRolelessAndNonBespoke {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (roleless : typingRoleOf generator = none)
    (notVar : generator ≠ Generator.gen_var)
    (notUniverse : generator ≠ Generator.gen_universeCode)
    (typed : HasTypeDescPi profile context (.mkGen generator payload children) classifier) :
    False := by
  obtain ⟨formationNone, introNone, elimNone⟩ := (typingRoleOf_isNone_iff generator).mp roleless
  exact typed.cellHasNoTypingWhenRootGenericallyExcluded notVar notUniverse
    (notGenLam_ofIntroRuleDescNone introNone) (notGenApp_ofElimRuleDescNone elimNone) formationNone

/-- **Smoke: `gen_boolTrue` is untyped, via the `typingRoleOf` route.**  `gen_boolTrue` is roleless
(`typingRoleOf gen_boolTrue = none` by `rfl`) and neither bespoke head, so the criterion fires — a data
constructor has no grown typing, rederived through the unified classifier rather than the bespoke
`cellHasNoTypingWhenRootGenericallyExcluded` inequalities. -/
theorem HasTypeDescPi.boolTrueCellUntypedViaRole {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_boolTrue.payload scope}
    {children : RawTermChildren Generator.gen_boolTrue.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_boolTrue payload children) classifier) :
    False :=
  typed.cellUntypedWhenRolelessAndNonBespoke rfl
    (by intro contra; cases contra) (by intro contra; cases contra)

end FX1Poly.Typed
