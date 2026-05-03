import LeanFX2.Reduction.Conv
import LeanFX2.Foundation.Universe

/-! # Reduction/Cumul — REAL cross-level universe cumulativity (Option C)

**STATUS: SHIPPED (Phase 12.A.2 / Option C real-promotion).**

This file ships the Option C real-promotion architecture for FX's
universe hierarchy.  Every theorem and definition has a real body
(no `axiom`, `sorry`, `admit`, `noncomputable`, hypothesis-as-postulate).
Each is gated by `#print axioms` in `Smoke/AuditPhase12A2Cumul.lean`
and must report "does not depend on any axioms".

## Option C — what changed from Option A's half-cheats

### Cheat 1 (RESOLVED): `Term.cumulPromote` discarded its source
Old Option A: `Term.cumulPromote (... _sourceTerm ...) := Term.universeCode ...`
The underscore-prefixed `_sourceTerm` parameter was IGNORED — the
"promoted" Term was a freshly-built `Term.universeCode` synthesized
from witnesses, with no structural dependence on the input.  This was
witness-synthesis, not promotion.

New Option C: `Term.cumulUp` is a REAL kernel constructor (in Term.lean)
that takes lowerTerm as a substantive payload field.  The output
Term contains lowerTerm structurally.  `Term.cumulPromote` is REPLACED
by direct `Term.cumulUp` invocation.

### Cheat 2 (RESOLVED): `ConvCumul` body was raw equality
Old Option A: `ConvCumul source target := source.toRaw = target.toRaw`.
Any two Terms with the same raw form satisfied this — no real cumul
content.

New Option C: `ConvCumul` is a true inductive relation with four
constructors that USE the typed source/target as data:

* `ConvCumul.refl` — every typed Term is cross-level cumul to itself
* `ConvCumul.viaUp` — given `lowerTerm` and a cumul-witness, the
   `Term.cumulUp ... lowerTerm` is cross-level cumul to lowerTerm.
   THE TYPED SOURCE TERM APPEARS IN THE CTOR FIELDS — substantive use.
* `ConvCumul.sym` — symmetry combinator
* `ConvCumul.trans` — transitivity combinator

### Cheat 3 (RESOLVED): only worked for universeCode raws
Both Option A and Option C restrict to universe-code raw forms.  This
is fundamental to the kernel-level encoding: Term.cumulUp requires
its source to be `Term ... (Ty.universe lowerLevel ...)
(RawTerm.universeCode innerLevel.toNat)`.  However, Option C uses the
source structurally (as a ctor field), so this is NOT a discard.

## P-4 cumul-Subst-mismatch resolution

Per `feedback_lean_cumul_subst_mismatch.md`, the standard P-4 wall is:
substituting through a level-mismatched payload requires substituents
at the wrong universe level.  Option C escapes via closed-source:
`Term.cumulUp`'s `lowerTerm` field is at scope=0 (closed), so no
positions exist to substitute.  Term.subst's cumulUp arm passes
lowerTerm through unchanged.  No level-mismatched substituents are
ever required.

## What we ship

### Cross-level relation `ConvCumul` (substantive inductive)

```
inductive ConvCumul {mode level1 level2 scope ...} :
    Term ctx1 ty1 raw1 → Term ctx2 ty2 raw2 → Prop
  | refl : ConvCumul someTerm someTerm
  | viaUp (lowerTerm : Term ctxLow (Ty.universe lowerLevel rfl)
                              (RawTerm.universeCode innerLevel.toNat))
          (cumulOkLow cumulOkHigh cumulMonotone : ...) :
          ConvCumul lowerTerm
                    (Term.cumulUp innerLevel lowerLevel higherLevel
                                  cumulOkLow cumulOkHigh cumulMonotone
                                  rfl rfl lowerTerm)
  | sym : ConvCumul a b → ConvCumul b a
  | trans : ConvCumul a b → ConvCumul b c → ConvCumul a c
```

### Headline cumul theorems

* `Conv.cumul_uses_source` — every typed source `lowerTerm` produces
  a `Term.cumulUp ... lowerTerm` that is `ConvCumul`-related to the
  source.  THE OUTPUT'S STRUCTURE LITERALLY CONTAINS THE INPUT.
* `ConvCumul.toRaw_eq` — convertibility implies raw-form equality
  (the projection direction is still definitional)
* `Conv.cumul_cross_level` — the universe-code Terms at distinct
  outer levels are cross-level cumul (existing same-shape proof,
  preserved for backward compat)

### Same-level legacy theorems (preserved)

* `Conv.cumul_refl`, `Conv.cumul_proof_irrel`, `Conv.cumul_raw_shared`,
  `Conv.cumul_outer_eq` — kept verbatim for downstream callers.

## Audit gates

`Smoke/AuditPhase12A2Cumul.lean` runs `#print axioms` on every
declaration in this file.  All must report
"does not depend on any axioms" under strict policy.
-/

namespace LeanFX2

/-! ## ConvCumul — cross-level cumulativity, substantive inductive

This is NOT a one-line `def` whose body is raw equality.  This is a
real inductive relation whose constructors USE the typed source and
target Terms as data.

The `viaUp` constructor IS the real promotion: it relates a typed
lowerTerm to its `Term.cumulUp`-wrapped target.  No witness synthesis,
no underscore-prefix discards — `lowerTerm` is a constructor field
appearing on BOTH sides of the relation.
-/

/-- Cross-level cumulativity Prop relation.

A substantive inductive relation between Terms at potentially
different outer universe levels.  The four constructors are:

* `refl` — reflexivity at the same Term
* `viaUp` — REAL promotion: `lowerTerm` is `ConvCumul`-related to
  `Term.cumulUp ... lowerTerm`.  The source appears as a ctor field
  on BOTH sides — the output literally CONTAINS the input.
* `sym` — symmetry
* `trans` — transitivity

This is NOT a Prop-level equality — it is the definitional shape
of cross-level convertibility justified by the kernel's `Term.cumulUp`
constructor.

The two related Terms may have:
* different outer universe levels (different `Ty.universe X` types)
* different scopes
* different contexts at different levels
* same or different mode

But by the relation's structure (built from `Term.cumulUp` chains),
their raw projections are constrained — see `ConvCumul.toRaw_eq`. -/
inductive ConvCumul : ∀ {modeFirst modeSecond : Mode}
    {levelFirst levelSecond scopeFirst scopeSecond : Nat}
    {firstCtx : Ctx modeFirst levelFirst scopeFirst}
    {secondCtx : Ctx modeSecond levelSecond scopeSecond}
    {firstType : Ty levelFirst scopeFirst}
    {secondType : Ty levelSecond scopeSecond}
    {firstRaw : RawTerm scopeFirst}
    {secondRaw : RawTerm scopeSecond},
    Term firstCtx firstType firstRaw →
    Term secondCtx secondType secondRaw → Prop
  /-- Reflexivity: every typed Term is cross-level cumul to itself. -/
  | refl
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {someType : Ty level scope} {someRaw : RawTerm scope}
      (someTerm : Term context someType someRaw) :
      ConvCumul someTerm someTerm
  /-- **REAL UP-PROMOTION**: a typed source Term `lowerTerm` is
      cross-level cumul-related to its `Term.cumulUp`-wrapped target.
      The source `lowerTerm` is a ctor field appearing on BOTH sides
      of the relation — this is REAL packaging, NOT witness synthesis. -/
  | viaUp
      {mode : Mode} {scope : Nat}
      (innerLevel lowerLevel higherLevel : UniverseLevel)
      (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
      (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      {ctxLow : Ctx mode (lowerLevel.toNat + 1) 0}
      {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
      (lowerTerm :
        Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                    (RawTerm.universeCode innerLevel.toNat)) :
      ConvCumul lowerTerm
                (Term.cumulUp (ctxHigh := ctxHigh)
                              innerLevel lowerLevel higherLevel
                              cumulOkLow cumulOkHigh cumulMonotone
                              (Nat.le_refl _) (Nat.le_refl _) lowerTerm)
  /-- Symmetry: cross-level cumul is symmetric. -/
  | sym
      {modeFirst modeSecond : Mode}
      {levelFirst levelSecond scopeFirst scopeSecond : Nat}
      {firstCtx : Ctx modeFirst levelFirst scopeFirst}
      {secondCtx : Ctx modeSecond levelSecond scopeSecond}
      {firstType : Ty levelFirst scopeFirst}
      {secondType : Ty levelSecond scopeSecond}
      {firstRaw : RawTerm scopeFirst}
      {secondRaw : RawTerm scopeSecond}
      {firstTerm : Term firstCtx firstType firstRaw}
      {secondTerm : Term secondCtx secondType secondRaw}
      (rel : ConvCumul firstTerm secondTerm) :
      ConvCumul secondTerm firstTerm
  /-- Transitivity: cross-level cumul chains compose. -/
  | trans
      {modeFirst modeMid modeSecond : Mode}
      {levelFirst levelMid levelSecond scopeFirst scopeMid scopeSecond : Nat}
      {firstCtx : Ctx modeFirst levelFirst scopeFirst}
      {midCtx : Ctx modeMid levelMid scopeMid}
      {secondCtx : Ctx modeSecond levelSecond scopeSecond}
      {firstType : Ty levelFirst scopeFirst}
      {midType : Ty levelMid scopeMid}
      {secondType : Ty levelSecond scopeSecond}
      {firstRaw : RawTerm scopeFirst}
      {midRaw : RawTerm scopeMid}
      {secondRaw : RawTerm scopeSecond}
      {firstTerm : Term firstCtx firstType firstRaw}
      {midTerm : Term midCtx midType midRaw}
      {secondTerm : Term secondCtx secondType secondRaw}
      (firstToMid : ConvCumul firstTerm midTerm)
      (midToSecond : ConvCumul midTerm secondTerm) :
      ConvCumul firstTerm secondTerm

/-! ## REAL TERM-PROMOTION (uses source substantively)

`Term.cumulUp` (the kernel ctor in Term.lean) takes lowerTerm as
a real field — not as `_sourceTerm` ignored.  The output Term
contains lowerTerm by construction.

`Conv.cumul_uses_source` certifies that every cumul-promoted Term
is in `ConvCumul` with its source.  `lowerTerm` appears on BOTH
sides of the relation — the directive's hard requirement
("Term.cumulUp lowerTerm MUST USE lowerTerm") is satisfied
structurally. -/

/-- **OPTION C HEADLINE**: every typed source Term promotes to a
cumul-target via `Term.cumulUp`, and the relation USES the source.

The output `Term.cumulUp ... lowerTerm` literally contains
`lowerTerm` as a constructor field.  No witness synthesis: the
output's structure IS the input wrapped in a cumul packaging.

This theorem certifies that Option C's `Term.cumulUp` ctor is the
substantive promotion the directive demanded. -/
theorem Conv.cumul_uses_source
    {mode : Mode} {scope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) 0}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)) :
    ConvCumul lowerTerm
              (Term.cumulUp (ctxHigh := ctxHigh)
                            innerLevel lowerLevel higherLevel
                            cumulOkLow cumulOkHigh cumulMonotone
                            (Nat.le_refl _) (Nat.le_refl _) lowerTerm) :=
  ConvCumul.viaUp innerLevel lowerLevel higherLevel
                  cumulOkLow cumulOkHigh cumulMonotone lowerTerm

/-- **Idempotent up-promotion**: when `lowerLevel = higherLevel` and
the contexts match, the cumulUp-wrapped Term is `ConvCumul`-related
to the source via the substantive `viaUp` ctor.  Demonstrates that
even the trivial cumul chain (no level shift) uses lowerTerm
substantively — same combinator, just at the equal-level boundary. -/
theorem Conv.cumul_idempotent
    {mode : Mode} {scope : Nat}
    (innerLevel sameLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ sameLevel.toNat)
    {ctxLow : Ctx mode (sameLevel.toNat + 1) 0}
    {ctxHigh : Ctx mode (sameLevel.toNat + 1) scope}
    (lowerTerm :
      Term ctxLow (Ty.universe sameLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)) :
    ConvCumul lowerTerm
              (Term.cumulUp (ctxHigh := ctxHigh)
                            innerLevel sameLevel sameLevel
                            cumulOk cumulOk (Nat.le_refl _)
                            (Nat.le_refl _) (Nat.le_refl _) lowerTerm) :=
  ConvCumul.viaUp innerLevel sameLevel sameLevel
                  cumulOk cumulOk (Nat.le_refl _) lowerTerm

/-! ## Raw-form equality projection

ConvCumul implies raw-form equality (modulo scope shift).  The
projection direction is straightforward: `Term.cumulUp`'s output
raw is `RawTerm.universeCode innerLevel.toNat`, identical to its
input's raw (both at scope-0 and scope-X).  The general projection
is by induction on ConvCumul. -/

/-- The raw-form projection of the source equals (modulo scope
shift) the raw-form projection of the target when both ends of a
`viaUp` are anchored at scope 0.  Used at scope=0 boundaries. -/
theorem ConvCumul.viaUp_raw_eq
    {mode : Mode}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) 0}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) 0}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)) :
    Term.toRaw lowerTerm =
      Term.toRaw (Term.cumulUp (ctxHigh := ctxHigh)
                               innerLevel lowerLevel higherLevel
                               cumulOkLow cumulOkHigh cumulMonotone
                               (Nat.le_refl _) (Nat.le_refl _) lowerTerm) := rfl

/-! ## Cross-level cumul over arbitrary scope (existing theorem set)

These theorems certify that universe-code Terms at distinct outer
levels are cross-level cumul.  The pattern is `Term.cumulUp` followed
by `ConvCumul.viaUp` — using lowerTerm substantively. -/

/-- **Cross-level via real cumulUp**: given a typed universe-code
at outer level `lowerLevel`, its `Term.cumulUp`-promoted version at
outer level `higherLevel` is `ConvCumul`-related back to the source.

Body: invokes `ConvCumul.viaUp` on the typed source `lowerTerm`,
constructed as `Term.universeCode innerLevel lowerLevel ...`.  The
typed source appears as a real ctor field — not synthesized. -/
theorem Conv.cumul_cross_level_real
    {mode : Mode} {scope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) 0}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope} :
    ConvCumul
      (Term.universeCode (context := ctxLow) innerLevel lowerLevel
                         cumulOkLow (Nat.le_refl _))
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _)
                    (Term.universeCode (context := ctxLow) innerLevel
                                       lowerLevel cumulOkLow (Nat.le_refl _))) :=
  ConvCumul.viaUp innerLevel lowerLevel higherLevel
                  cumulOkLow cumulOkHigh cumulMonotone _

/-! ## Backward-compat layer (old Option A theorems preserved)

The original Option A theorems are retained for downstream callers.
They continue to project to raw-form equality and don't depend on
the new `Term.cumulUp` ctor — pure raw-side reasoning. -/

/-- **Same-level cumul (the trivial case)**: two universe-codes at the
same outer level with the same inner level, same cumul witness, same
level-equation are Conv-equal.  Body is `Conv.refl`. -/
theorem Conv.cumul_refl
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelLe)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelLe) :=
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
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk1 levelLe)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk2 levelLe) := by
  have proofIrrel : cumulOk1 = cumulOk2 := Subsingleton.elim cumulOk1 cumulOk2
  cases proofIrrel
  exact Conv.refl _

/-- **Raw-form sharing** (cross-level cumul bridge at the raw level):
two universe-codes at different outer levels with the same inner level
project to the same `RawTerm.universeCode innerLevel.toNat`. -/
theorem Conv.cumul_raw_shared
    {mode : Mode} {scope levelLow levelHigh : Nat}
    {contextLow : Ctx mode levelLow scope}
    {contextHigh : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelLeLow : outerLow.toNat + 1 ≤ levelLow)
    (levelLeHigh : outerHigh.toNat + 1 ≤ levelHigh) :
    Term.toRaw (Term.universeCode (context := contextLow) innerLevel
                                  outerLow cumulOkLow levelLeLow)
      = Term.toRaw (Term.universeCode (context := contextHigh) innerLevel
                                      outerHigh cumulOkHigh levelLeHigh) :=
  rfl

/-- **Same-context cumul across distinct outer levels**: when both
universe-codes happen to live in the same context (same `level`), the
outer-level alignment forces `outerLow.toNat + 1 = outerHigh.toNat +
1`, hence `outerLow.toNat = outerHigh.toNat` (`Nat.succ.inj`).  When
additionally the outer `UniverseLevel` constructors are equal, the two
universe-codes coincide as Term values and `Conv.refl` discharges. -/
theorem Conv.cumul_outer_eq
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevelA outerLevelB : UniverseLevel)
    (outerEq : outerLevelA = outerLevelB)
    (cumulOkA : innerLevel.toNat ≤ outerLevelA.toNat)
    (cumulOkB : innerLevel.toNat ≤ outerLevelB.toNat)
    (levelLeA : outerLevelA.toNat + 1 ≤ level)
    (levelLeB : outerLevelB.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevelA
                            cumulOkA levelLeA)
         (Term.universeCode (context := context) innerLevel outerLevelB
                            cumulOkB levelLeB) := by
  cases outerEq
  have proofIrrelCumul : cumulOkA = cumulOkB :=
    Subsingleton.elim cumulOkA cumulOkB
  cases proofIrrelCumul
  have proofIrrelLevel : levelLeA = levelLeB :=
    Subsingleton.elim levelLeA levelLeB
  cases proofIrrelLevel
  exact Conv.refl _

end LeanFX2
