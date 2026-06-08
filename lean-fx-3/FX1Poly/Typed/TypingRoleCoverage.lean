import FX1Poly.Typed.TypingRoleEngineBridge

/-! # FX1Poly/Typed/TypingRoleCoverage — the GTL-19 coverage capstone: exhaustive head-classification of typed
    cells.

GTL-ROLE (#985-988) shipped the unified `typingRoleOf` classifier over the three rule tables, its
role-uniqueness (pairwise table disjointness), completeness (`typingRoleOf_*_of`), and the engine bridge
(`HasTypeDescPi.subjectHeadHasRoleOrBespoke`: every grown-typed head carries a `typingRoleOf` role or is one of
the two bespoke arms `gen_var` / `gen_universeCode`).

This file closes the GTL-19 substrate with the COVERAGE CAPSTONE: the exhaustive FIVE-class partition of
grown-typed CELL heads.  A `mkGen`-rooted grown-typed cell's head generator is exactly one of: a FORMATION
former (`typingRoleOf = some formation`), an INTRODUCTION former (`= some intro`, i.e. `gen_lam`), an
ELIMINATION former (`= some elim`, i.e. `gen_app`), or one of the two BESPOKE typed heads (`gen_var`,
`gen_universeCode`).  This is the explicit "the three rule tables plus the two bespoke arms EXHAUSTIVELY cover
every typed head" statement — the coherence headline the cascade-free extensibility gate (FRAME-2) turns on: a
NEW data/type former is admitted by extending ONE rule table (a new role-bearing head), never by touching the
two bespoke arms or this partition.  It is the realization-side complement to the role classifier: where
`subjectHeadHasRoleOrBespoke` phrases coverage existentially (`∃ role`), this resolves the existential into the
three concrete role constructors, giving a fully decided five-way head taxonomy over the head GENERATOR (the
`mkGen` index), not the `rootGenerator` projection.

  * `HasTypeDescPi.headClassificationExhaustive` — the five-way partition (open context).
  * `HasTypeDescPi.closedHeadClassificationExhaustive` — the closed corollary: in the empty context the
    `gen_var` class vanishes (the `var` payload is `Fin 0`-indexed, uninhabited), so a closed typed cell head
    is a formation / intro / elim former or `gen_universeCode` — the four-way closed taxonomy the
    canonical-forms / consistency arguments turn on.

## Zero-axiom

`subjectHeadHasRoleOrBespoke` / `closedSubjectHeadHasRoleOrIsUniverseCode` (#986) + the definitional
`(mkGen generator payload children).rootGenerator = generator` head reduction + a `TypingRole` three-way
case-split.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The GTL-19 coverage capstone: exhaustive head-classification of typed cells.**  Every grown-typed
`mkGen`-rooted cell's head generator falls into exactly one of five classes — a FORMATION former
(`typingRoleOf = some formation`), an INTRODUCTION former (`= some intro`), an ELIMINATION former (`= some
elim`), or one of the two BESPOKE typed heads (`gen_var`, `gen_universeCode`).  Resolves the existential role of
`subjectHeadHasRoleOrBespoke` into its three concrete constructors and reads the head off the `mkGen` index
(`rootGenerator = generator` by `rfl`).  The exhaustive-partition coherence headline: the three rule tables
plus the two bespoke arms cover EVERY typed head, so a new former is one new table row, never a partition
change. -/
theorem HasTypeDescPi.headClassificationExhaustive {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen generator payload children) classifier) :
    typingRoleOf generator = some TypingRole.formation ∨
    typingRoleOf generator = some TypingRole.intro ∨
    typingRoleOf generator = some TypingRole.elim ∨
    generator = Generator.gen_var ∨
    generator = Generator.gen_universeCode := by
  rcases typed.subjectHeadHasRoleOrBespoke with ⟨role, roleEq⟩ | isVar | isUniverse
  · cases role with
    | formation => exact Or.inl roleEq
    | intro => exact Or.inr (Or.inl roleEq)
    | elim => exact Or.inr (Or.inr (Or.inl roleEq))
  · exact Or.inr (Or.inr (Or.inr (Or.inl isVar)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr isUniverse)))

/-- **★ The closed coverage capstone.**  In the empty context the `gen_var` class vanishes (the `var` payload
is `Fin 0`-indexed, uninhabited — `closedSubjectHeadHasRoleOrIsUniverseCode`), so a closed grown-typed
`mkGen`-rooted cell's head generator is a FORMATION / INTRODUCTION / ELIMINATION former or the bespoke
`gen_universeCode` — the four-way closed head taxonomy the canonical-forms and consistency arguments consume
(only `gen_app`, the elimination class, classifies at a non-universe/non-Π type among the remaining heads). -/
theorem HasTypeDescPi.closedHeadClassificationExhaustive {profile : PolyProfile}
    {generator : Generator} {payload : generator.payload 0}
    {children : RawTermChildren generator.binderShifts 0} {classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty (.mkGen generator payload children) classifier) :
    typingRoleOf generator = some TypingRole.formation ∨
    typingRoleOf generator = some TypingRole.intro ∨
    typingRoleOf generator = some TypingRole.elim ∨
    generator = Generator.gen_universeCode := by
  rcases typed.closedSubjectHeadHasRoleOrIsUniverseCode with ⟨role, roleEq⟩ | isUniverse
  · cases role with
    | formation => exact Or.inl roleEq
    | intro => exact Or.inr (Or.inl roleEq)
    | elim => exact Or.inr (Or.inr (Or.inl roleEq))
  · exact Or.inr (Or.inr (Or.inr isUniverse))

end FX1Poly.Typed
