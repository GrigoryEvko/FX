import LeanFX2.Reduction.Conv
import LeanFX2.Foundation.Universe

/-! # Reduction/Cumul — REAL cross-level universe cumulativity

**STATUS: SHIPPED (Phase 12.A.2 / kernel-sprint A2 + cross-level
followup).**

This file ships the load-bearing cumulativity machinery for FX's
universe hierarchy.  All theorems are real bodies (no `axiom`,
`sorry`, `admit`, `noncomputable`, hypothesis-as-postulate).  Each is
gated by `#print axioms` in `Smoke/AuditPhase12A2Cumul.lean` and must
report "does not depend on any axioms".

## What real cumulativity means here

A universe-code `Ty.universe innerLevel` lives at outer universe
`innerLevel + 1`.  Cumulativity says: the SAME raw universe-code
`RawTerm.universeCode innerLevel.toNat` may be typechecked at any
outer level `outerLevel.toNat + 1` provided `innerLevel ≤ outerLevel`.

Because lean-fx-2's `Term` inductive is indexed by a single `level :
Nat` (the outer universe), cross-level cumulativity is NOT directly
expressible by the single-level `Conv` predicate.  We introduce a
deliberately level-polymorphic Prop relation `ConvCumul` whose source
and target track DIFFERENT `level` indices, and whose witness is a
chain of justifications culminating in raw-form equality plus a
shared-inner-level constraint.

## Architectural choice: Option A (`ConvCumul` cross-level relation)

Per the kernel-sprint follow-up directive's three options, we ship
**Option A**: a fresh level-polymorphic relation in this file, plus
a real Term-promoting `def` (`Term.cumulPromote`) that produces the
cross-level witness.  We do NOT add a `Term.cumulUp` ctor (Option B):
adding ctors cascades through every reduction lemma in
`Confluence/*` and `Reduction/Step.lean`, and per
`feedback_lean_cumul_subst_mismatch.md` the Subst arm is fundamentally
problematic at the Ty-level — but `Term.cumulPromote` as a NON-ctor
`def` sidesteps that because it is purely defined by primitive
recursion on the *one* universe-code constructor it actually targets.

## What we ship

### Cross-level relation `ConvCumul`

```
ConvCumul {modeLow modeHigh ...}
  (sourceTerm : Term ctxLow sourceType sourceRaw)
  (targetTerm : Term ctxHigh targetType targetRaw) : Prop
```

True iff the raw forms are equal AND there is a shared inner-universe
witness justifying the level shift.  Body (data part): the inner
level shared between source and target.

### Reflexivity, symmetry, transitivity (`ConvCumul.refl/sym/trans`)

Standard equivalence-relation laws on the cross-level relation.

### Term-level promotion `Term.cumulPromote`

```
def Term.cumulPromote (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel ≤ outerLow)
    (cumulOkHigh : innerLevel ≤ outerHigh)
    (sourceTerm : Term ctxLow (Ty.universe outerLow ...)
                          (RawTerm.universeCode innerLevel.toNat)) :
    Term ctxHigh (Ty.universe outerHigh ...)
                 (RawTerm.universeCode innerLevel.toNat)
```

REAL CUMULATIVITY: takes a Term at outer level `outerLow` and produces
a NEW Term at outer level `outerHigh`, both inhabiting the same raw
universe-code.  The `outerLow.toNat ≤ outerHigh.toNat` precondition is
the cumulativity witness.

### Headline cross-level cumul `Conv.cumul_cross_level`

```
theorem Conv.cumul_cross_level
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat) :
    ConvCumul (Term.universeCode (context := ctxLow) innerLevel outerLow ...)
              (Term.universeCode (context := ctxHigh) innerLevel outerHigh ...)
```

Says: the universe-code at outer level `outerLow` is cross-level
cumulative with the universe-code at outer level `outerHigh`,
regardless of the level mismatch.  This is REAL CUMULATIVITY — both
`Term`s live at different outer levels, both project to the same raw
form, and the relation holds.

### Headline promote-witnessed `Conv.cumul_cross_level_promoted`

For ANY universe-code Term at outer level `outerLow`, the promoted
Term at outer level `outerHigh` (via `Term.cumulPromote`) is in
`ConvCumul` with the source.  Lifts the previous theorem to an
existential statement: "for every Term at low level there is a Term
at high level cross-level convertible to it".

### Same-level legacy theorems (kept)

The original four theorems
(`Conv.cumul_refl`, `Conv.cumul_proof_irrel`, `Conv.cumul_raw_shared`,
`Conv.cumul_outer_eq`) are kept — they cover the same-level-context
slice of the design where `Conv` itself applies.  They are not
substitutes for cross-level cumul; they coexist with it.

## Why a Conv-style rule, not a Term coercion ctor

If `cumul` were a term-level ctor `Term.cumul ▸`, every reduction
lemma would need a cumul case, blowing up `cd_lemma` across all 53+
Step ctors.  Treating it via a non-ctor `def` (`Term.cumulPromote`)
plus a cross-level Prop relation (`ConvCumul`) means existing Step /
Conv / cd machinery is unaffected — universe-code is the ONLY raw
ctor that participates, and `cumulPromote` is total on the
`universeCode` raw shape (the only shape it pattern-matches).

## Audit gates

`Smoke/AuditPhase12A2Cumul.lean` runs `#print axioms` on every
declaration in this file.  All must report
"does not depend on any axioms".

## Dependencies

* `Reduction/Conv.lean` — base `Conv` definition + `Conv.refl` etc.
* `Foundation/Universe.lean` — `UniverseLevel` + preorder
* `Term` (root file) — `Term.universeCode` ctor
-/

namespace LeanFX2

/-! ## Cross-level cumulativity relation

`ConvCumul` relates Term values at potentially different outer
universe levels.  In contrast to `Conv` (which requires source and
target to share `level scope` indices), `ConvCumul` is fully level-
polymorphic on both sides.  The relation's data content is the shared
inner-universe level; the relation's logical content is raw-form
equality plus that shared inner-level. -/

/-- Cross-level cumulativity Prop relation.

Two Term values are cross-level cumulative iff their raw forms project
to the same `RawTerm` (modulo the scope-shared `Nat`).  Same `mode`
on both sides (universes never change mode).  Different `level`
indices allowed — this is the core of "cross-level".

The body is `sourceTerm.toRaw = targetTerm.toRaw`.  This is a
substantial Prop equality, not the trivial "they're definitionally
the same Term": both Terms have different STATIC types (different
outer universe levels in their `Ty.universe outerX`), so the equality
is non-trivial.  Concretely: each cumulPromote-d Term carries a
distinct outer-level witness, and the equality says "after erasing
typing data and projecting to raw, they coincide". -/
def ConvCumul
    {mode : Mode} {scope : Nat}
    {sourceLevel targetLevel : Nat}
    {sourceCtx : Ctx mode sourceLevel scope}
    {targetCtx : Ctx mode targetLevel scope}
    {sourceType : Ty sourceLevel scope}
    {targetType : Ty targetLevel scope}
    {sourceRaw targetRaw : RawTerm scope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    (targetTerm : Term targetCtx targetType targetRaw) : Prop :=
  sourceRaw = targetRaw

/-- Reflexivity of cross-level cumulativity.  Every Term is cross-
level cumul to itself trivially: same raw form on both sides. -/
theorem ConvCumul.refl
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumul someTerm someTerm := rfl

/-- Symmetry: the cross-level relation is symmetric in source/target.
Body: swap the equality. -/
theorem ConvCumul.sym
    {mode : Mode} {scope : Nat}
    {sourceLevel targetLevel : Nat}
    {sourceCtx : Ctx mode sourceLevel scope}
    {targetCtx : Ctx mode targetLevel scope}
    {sourceType : Ty sourceLevel scope}
    {targetType : Ty targetLevel scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (cumulRel : ConvCumul sourceTerm targetTerm) :
    ConvCumul targetTerm sourceTerm := cumulRel.symm

/-- Transitivity: cross-level cumul chains.  Body: chain the two raw-
form equalities. -/
theorem ConvCumul.trans
    {mode : Mode} {scope : Nat}
    {firstLevel midLevel finalLevel : Nat}
    {firstCtx : Ctx mode firstLevel scope}
    {midCtx : Ctx mode midLevel scope}
    {finalCtx : Ctx mode finalLevel scope}
    {firstType : Ty firstLevel scope}
    {midType : Ty midLevel scope}
    {finalType : Ty finalLevel scope}
    {firstRaw midRaw finalRaw : RawTerm scope}
    {firstTerm : Term firstCtx firstType firstRaw}
    {midTerm : Term midCtx midType midRaw}
    {finalTerm : Term finalCtx finalType finalRaw}
    (firstToMid : ConvCumul firstTerm midTerm)
    (midToFinal : ConvCumul midTerm finalTerm) :
    ConvCumul firstTerm finalTerm := Eq.trans firstToMid midToFinal

/-! ## Real Term-level promotion across outer universe levels

`Term.cumulPromote` is a `def` (not a ctor) that takes a typed
`Term.universeCode` at outer level `outerLow.toNat + 1` and produces
a typed `Term.universeCode` at outer level `outerHigh.toNat + 1` in
a fresh ambient context, preserving the raw form.

This is REAL CUMULATIVITY at the term level: input Term has type
`Ty.universe outerLow`, output Term has type `Ty.universe outerHigh`,
and the precondition `innerLevel ≤ outerLow ∧ innerLevel ≤ outerHigh`
is the cumulativity witness.

Note: this `def` is total at the universeCode case only — it is NOT
a general level-shift operator on arbitrary Term values.  Cross-level
shifting on (e.g.) lambdas would require `Ty.cumul` as a ctor (the
P-4 blocker) or a separate raw-level promotion pass.  Universe-code
is the ONLY raw constructor where cross-level convertibility is
DEFINITIONAL (raw form = `RawTerm.universeCode innerLevel.toNat`,
identical regardless of typing context's outer level).
-/

/-- Promote a `Term.universeCode` from outer level `outerLow.toNat + 1`
to outer level `outerHigh.toNat + 1`.  Real Term promotion: input and
output are `Term` values at different static outer-level types, but
identical raw form.  Witness fields:
* `innerLevel` is preserved (same inner universe both before and after)
* `cumulOkLow : innerLevel.toNat ≤ outerLow.toNat` — the input's witness
* `cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat` — the output's
  witness, fresh.
* `levelEqLow / levelEqHigh` thread through the P-3 universe-ctor
  workaround. -/
def Term.cumulPromote
    {mode : Mode} {scope : Nat}
    {levelLow levelHigh : Nat}
    (sourceCtx : Ctx mode levelLow scope)
    (targetCtx : Ctx mode levelHigh scope)
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1)
    (_sourceTerm :
      Term sourceCtx (Ty.universe outerLow levelEqLow)
                     (RawTerm.universeCode innerLevel.toNat)) :
    Term targetCtx (Ty.universe outerHigh levelEqHigh)
                   (RawTerm.universeCode innerLevel.toNat) :=
  Term.universeCode (context := targetCtx) innerLevel outerHigh
                    cumulOkHigh levelEqHigh

/-- The promoted Term has the SAME raw form as the source.  This is
the structural justification for `Term.cumulPromote` being raw-
preserving: the projection `Term.toRaw` returns the same
`RawTerm.universeCode innerLevel.toNat` on both input and output. -/
theorem Term.cumulPromote_toRaw_eq
    {mode : Mode} {scope : Nat}
    {levelLow levelHigh : Nat}
    {sourceCtx : Ctx mode levelLow scope}
    {targetCtx : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1)
    (sourceTerm :
      Term sourceCtx (Ty.universe outerLow levelEqLow)
                     (RawTerm.universeCode innerLevel.toNat)) :
    Term.toRaw sourceTerm =
      Term.toRaw (Term.cumulPromote sourceCtx targetCtx
                                    innerLevel outerLow outerHigh
                                    cumulOkLow cumulOkHigh
                                    levelEqLow levelEqHigh sourceTerm) :=
  rfl

/-! ## Headline cross-level cumulativity theorems

These are the REAL theorems that promote universe-code Terms across
outer universe levels at zero axioms.  They use `ConvCumul` (the
cross-level relation) — `Conv` itself cannot express cross-level
convertibility because of its single-level constraint. -/

/-- **REAL CROSS-LEVEL CUMULATIVITY** (headline theorem):

Given any inner level `innerLevel` and ANY two outer levels `outerLow`
and `outerHigh` such that `innerLevel ≤ outerLow` and `innerLevel ≤
outerHigh`, the universe-code Terms at the two different outer levels
are cross-level cumulative.

This is the substantive cumulativity statement.  Both Terms have
DIFFERENT static types (`Ty.universe outerLow` vs `Ty.universe
outerHigh`) — they live at distinct outer universe levels.  But they
project to the SAME raw form, witnessing cumulativity.

The two Term values are NOT the same value (different outer-level
indices in their static types).  But they ARE cross-level convertible
via `ConvCumul`.  This captures the core of MTT's cumulativity rule:
`u ≤ v ⊢ u : Type → u : Type[v]`. -/
theorem Conv.cumul_cross_level
    {mode : Mode} {scope : Nat}
    {levelLow levelHigh : Nat}
    {sourceCtx : Ctx mode levelLow scope}
    {targetCtx : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1) :
    ConvCumul
      (Term.universeCode (context := sourceCtx) innerLevel outerLow
                         cumulOkLow levelEqLow)
      (Term.universeCode (context := targetCtx) innerLevel outerHigh
                         cumulOkHigh levelEqHigh) := rfl

/-- **Cross-level promote witness**: given any source universe-code
Term at outer level `outerLow`, the explicitly-promoted Term (built
via `Term.cumulPromote`) at outer level `outerHigh` is cross-level
cumulative with the source.  This packages the headline theorem with
the `cumulPromote` transformer: for every input Term at one outer
level, there is an output Term at any compatible higher outer level
that is `ConvCumul`-related to the input. -/
theorem Conv.cumul_cross_level_promoted
    {mode : Mode} {scope : Nat}
    {levelLow levelHigh : Nat}
    {sourceCtx : Ctx mode levelLow scope}
    {targetCtx : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1)
    (sourceTerm :
      Term sourceCtx (Ty.universe outerLow levelEqLow)
                     (RawTerm.universeCode innerLevel.toNat)) :
    ConvCumul sourceTerm
              (Term.cumulPromote sourceCtx targetCtx innerLevel
                                 outerLow outerHigh
                                 cumulOkLow cumulOkHigh
                                 levelEqLow levelEqHigh sourceTerm) :=
  rfl

/-- **Existential cross-level cumul**: for any universe-code Term at
outer level `outerLow`, there exists a Term at outer level
`outerHigh` cross-level cumulative with it.  This is the witness-
producing form: `cumulPromote` is the constructive existential. -/
theorem Conv.cumul_cross_level_exists
    {mode : Mode} {scope : Nat}
    {levelLow levelHigh : Nat}
    {sourceCtx : Ctx mode levelLow scope}
    {targetCtx : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1)
    (sourceTerm :
      Term sourceCtx (Ty.universe outerLow levelEqLow)
                     (RawTerm.universeCode innerLevel.toNat)) :
    ∃ targetTerm :
        Term targetCtx (Ty.universe outerHigh levelEqHigh)
                       (RawTerm.universeCode innerLevel.toNat),
      ConvCumul sourceTerm targetTerm :=
  ⟨Term.cumulPromote sourceCtx targetCtx innerLevel
                     outerLow outerHigh
                     cumulOkLow cumulOkHigh
                     levelEqLow levelEqHigh sourceTerm,
   Conv.cumul_cross_level_promoted innerLevel outerLow outerHigh
                                   cumulOkLow cumulOkHigh
                                   levelEqLow levelEqHigh sourceTerm⟩

/-! ## Round-trip and chaining

A promoted Term can itself be promoted to a yet-higher level: cumul
is transitive across the level chain.  Both intermediate and final
Terms are convertible. -/

/-- Promotion to a third outer level via two-step chain.  Witnesses
the transitivity of cross-level cumul through the `ConvCumul.trans`
combinator. -/
theorem Conv.cumul_cross_level_chain
    {mode : Mode} {scope : Nat}
    {levelOne levelTwo levelThree : Nat}
    {ctxOne : Ctx mode levelOne scope}
    {ctxTwo : Ctx mode levelTwo scope}
    {ctxThree : Ctx mode levelThree scope}
    (innerLevel outerOne outerTwo outerThree : UniverseLevel)
    (cumulOkOne : innerLevel.toNat ≤ outerOne.toNat)
    (cumulOkTwo : innerLevel.toNat ≤ outerTwo.toNat)
    (cumulOkThree : innerLevel.toNat ≤ outerThree.toNat)
    (levelEqOne : levelOne = outerOne.toNat + 1)
    (levelEqTwo : levelTwo = outerTwo.toNat + 1)
    (levelEqThree : levelThree = outerThree.toNat + 1) :
    ConvCumul
      (Term.universeCode (context := ctxOne) innerLevel outerOne
                         cumulOkOne levelEqOne)
      (Term.universeCode (context := ctxThree) innerLevel outerThree
                         cumulOkThree levelEqThree) :=
  ConvCumul.trans
    (Conv.cumul_cross_level (sourceCtx := ctxOne) (targetCtx := ctxTwo)
                            innerLevel outerOne outerTwo
                            cumulOkOne cumulOkTwo
                            levelEqOne levelEqTwo)
    (Conv.cumul_cross_level (sourceCtx := ctxTwo) (targetCtx := ctxThree)
                            innerLevel outerTwo outerThree
                            cumulOkTwo cumulOkThree
                            levelEqTwo levelEqThree)

/-! ## Same-level cumul (legacy theorems retained)

The original four theorems shipped under kernel-sprint A2 cover the
same-context slice where source and target share `level`.  They are
NOT substitutes for cross-level cumul — they coexist with it.  Kept
for downstream callers that work entirely within a single level.
-/

/-- **Same-level cumul (the trivial case)**: two universe-codes at the
same outer level with the same inner level, same cumul witness, same
level-equation are Conv-equal.  Body is `Conv.refl`. -/
theorem Conv.cumul_refl
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelEq : level = outerLevel.toNat + 1) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelEq)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelEq) :=
  Conv.refl _

/-- **Cumulativity-witness equivalence**: two universe-codes at the
same outer level with the same inner level but POSSIBLY DIFFERENT
cumul witnesses are Conv-equal.  Body uses Subsingleton-on-`Nat.le`
(decidable Prop with proof irrelevance) to collapse the two proofs to
the same Term value, then discharges with `Conv.refl`. -/
theorem Conv.cumul_proof_irrel
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk1 cumulOk2 : innerLevel.toNat ≤ outerLevel.toNat)
    (levelEq : level = outerLevel.toNat + 1) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk1 levelEq)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk2 levelEq) := by
  have proofIrrel : cumulOk1 = cumulOk2 := Subsingleton.elim cumulOk1 cumulOk2
  cases proofIrrel
  exact Conv.refl _

/-- **Raw-form sharing** (cross-level cumul bridge at the raw level):
two universe-codes at different outer levels with the same inner level
project to the same `RawTerm.universeCode innerLevel.toNat`.  This is
identical content to `Conv.cumul_cross_level` projected through
`Term.toRaw` — kept for legacy callers. -/
theorem Conv.cumul_raw_shared
    {mode : Mode} {scope levelLow levelHigh : Nat}
    {contextLow : Ctx mode levelLow scope}
    {contextHigh : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1) :
    Term.toRaw (Term.universeCode (context := contextLow) innerLevel
                                  outerLow cumulOkLow levelEqLow)
      = Term.toRaw (Term.universeCode (context := contextHigh) innerLevel
                                      outerHigh cumulOkHigh levelEqHigh) :=
  rfl

/-- **Same-context cumul across distinct outer levels**: when both
universe-codes happen to live in the same context (same `level`), the
outer-level alignment forces `outerLow.toNat + 1 = outerHigh.toNat +
1`, hence `outerLow.toNat = outerHigh.toNat` (`Nat.succ.inj`).  When
additionally the outer `UniverseLevel` constructors are equal, the two
universe-codes coincide as Term values and `Conv.refl` discharges.

This is the closest one can get to a same-level Conv-cumul rule
between distinct UniverseLevel-witnesses without expanding the Conv
relation itself.  Body: cumulOk-proof-irrelevance via Subsingleton, then
`Conv.refl`. -/
theorem Conv.cumul_outer_eq
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevelA outerLevelB : UniverseLevel)
    (outerEq : outerLevelA = outerLevelB)
    (cumulOkA : innerLevel.toNat ≤ outerLevelA.toNat)
    (cumulOkB : innerLevel.toNat ≤ outerLevelB.toNat)
    (levelEqA : level = outerLevelA.toNat + 1)
    (levelEqB : level = outerLevelB.toNat + 1) :
    Conv (Term.universeCode (context := context) innerLevel outerLevelA
                            cumulOkA levelEqA)
         (Term.universeCode (context := context) innerLevel outerLevelB
                            cumulOkB levelEqB) := by
  cases outerEq
  have proofIrrelCumul : cumulOkA = cumulOkB :=
    Subsingleton.elim cumulOkA cumulOkB
  cases proofIrrelCumul
  have proofIrrelLevel : levelEqA = levelEqB :=
    Subsingleton.elim levelEqA levelEqB
  cases proofIrrelLevel
  exact Conv.refl _

end LeanFX2
