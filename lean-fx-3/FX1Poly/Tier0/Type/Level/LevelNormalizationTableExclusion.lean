import FX1Poly.Tier0.Type.Level.LevelExprSimplify

/-! # LevelNormalizationTableExclusion — LEVEL-TAB: levels are a PINNED MOON-LEDGER exclusion

The MOON-LEDGER program (#1385) makes "every semantic fact a row" in a
first-order ORTHOGONAL rule table (`IotaRuleDesc` / `EtaRuleDesc` /
`DeltaRuleDesc` over `StepOver`): head-keyed, orientation-terminating,
orthogonal-confluent.  LEVEL-TAB asks whether the universe-level normalizer
(`LevelExpr.simplify` / `canonicalize`: lmax sort + dedup + lsucc-distrib)
should join that program as a `LevelRuleDesc` table, or be PINNED as an
honest exclusion.

**DECISION: pinned exclusion** (`levelNormalizationStatus = .pinnedExclusion`).
Two independent reasons, one machine-checked here, one structural:

1. **`lmax` is associative-commutative — its commutativity admits NO
   terminating oriented rule.**  The sound denotational equation
   `lmax e1 e2 ~ lmax e2 e1` (`lmax_comm_denoteEquiv`), oriented either way
   as a rewrite rule `lmax e1 e2 ↝ lmax e2 e1`, is a **2-cycle**:
   `lmaxOrient (lmaxOrient (lmax e1 e2)) = lmax e1 e2` definitionally, while
   the single step is non-trivial on distinct arguments
   (`lmaxOrient w ≠ w`).  A 2-cycle is a non-terminating reduction, so AC
   commutativity cannot be an orientation-terminating row in the rule-table
   program.  LevelExpr normalization is therefore an **AC-normalizer**
   (sort-and-dedup), categorically NOT an orthogonal first-order rewrite
   table.  This is the same obstruction that forces partialClass on raw β
   (HCAP-NOGO-rpoSN): a sound equation with no terminating orientation.

2. **Different carrier, already-complete normalizer (structural).**  The
   rule tables key on `Generator` heads over `RawTerm`; `LevelExpr` is a
   SEPARATE inductive (`lzero`/`lsucc`/`lmax`/`limax`/`lvar`) with no
   `Generator` head, and its normalizer is ALREADY a complete convergent
   system — `simplify` reaches structural normal form in one pass
   (`simplify_produces_isStructurallyNormalForm`) and is idempotent
   (`simplify_idempotent`), with the M22-A11 O(n·log n) complexity witness.
   There is no extension pressure (no new universe-level constructors land
   as rows), so table-izing it would add machinery without making any new
   fact a row.

The deliverable (per the task) is this pinned exclusion lemma bundle + the
ledger value, closing the LevelExpr seam in MOON-LEDGER (#1385) honestly.

## Zero-axiom

The cycle facts are `rfl` (`lmaxOrient` is a one-arm structural function);
non-triviality is structural `injection`; the soundness equation reuses the
audited `lmax_comm_denoteEquiv`; the completeness citations reuse the
audited M22 normalizer theorems.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Universe

/-! ## The candidate orientation of lmax-commutativity -/

/-- The orientation a `LevelRuleDesc` row WOULD give lmax-commutativity:
swap the two arguments of an `lmax` head, identity elsewhere.  Used only to
exhibit that this orientation is a 2-cycle — the witness that levels resist
the orthogonal rule-table program. -/
def LevelExpr.lmaxOrient : LevelExpr → LevelExpr
  | .lmax leftExpr rightExpr => .lmax rightExpr leftExpr
  | .lzero => .lzero
  | .lsucc inner => .lsucc inner
  | .limax leftExpr rightExpr => .limax leftExpr rightExpr
  | .lvar index => .lvar index

/-- **The oriented commutativity rule is a 2-cycle.**  Applying the lmax
swap twice returns the original term — so the rewrite rule
`lmax e1 e2 ↝ lmax e2 e1` never terminates: `w ↝ orient w ↝ w ↝ …`.  This
is the core obstruction: a non-terminating oriented rule cannot be an
orientation-terminating row. -/
theorem LevelExpr.lmaxOrient_cycles (leftExpr rightExpr : LevelExpr) :
    LevelExpr.lmaxOrient (LevelExpr.lmaxOrient (LevelExpr.lmax leftExpr rightExpr))
      = LevelExpr.lmax leftExpr rightExpr := rfl

/-- The lmax swap is SOUND as a denotational equation — exactly
`lmax_comm_denoteEquiv` read through `lmaxOrient`.  So the rule IS a real
(semantically valid) equation; it is the ORIENTATION that fails, not the
equation.  Together with `lmaxOrient_cycles` this is the precise "sound but
non-orientable" diagnosis. -/
theorem LevelExpr.lmaxOrient_denoteEquiv (leftExpr rightExpr : LevelExpr) :
    LevelExpr.denoteEquiv (LevelExpr.lmax leftExpr rightExpr)
      (LevelExpr.lmaxOrient (LevelExpr.lmax leftExpr rightExpr)) :=
  LevelExpr.lmax_comm_denoteEquiv leftExpr rightExpr

/-- The swap step is non-trivial on distinct arguments: the two orientations
of `lmax (lvar 0) (lvar 1)` are structurally distinct LevelExprs.  This makes
`lmaxOrient_cycles` a GENUINE 2-cycle (the term actually changes each step),
not a fixpoint — so the non-termination is real. -/
theorem LevelExpr.lmaxOrient_nontrivial_witness :
    LevelExpr.lmaxOrient (LevelExpr.lmax (LevelExpr.lvar 0) (LevelExpr.lvar 1))
      ≠ LevelExpr.lmax (LevelExpr.lvar 0) (LevelExpr.lvar 1) := by
  intro orientEq
  -- `lmaxOrient (lmax (lvar 0) (lvar 1)) = lmax (lvar 1) (lvar 0)` by rfl,
  -- so the hypothesis is `lmax (lvar 1) (lvar 0) = lmax (lvar 0) (lvar 1)`.
  injection orientEq with leftEq _
  injection leftEq with indexEq
  cases indexEq

/-- The two orientations are denote-EQUAL yet structurally DISTINCT — the
single fact that simultaneously forces an AC-identification (so a normalizer
must merge them) AND forbids a confluent oriented rule from doing it. -/
theorem LevelExpr.lmaxOrientations_denoteEquiv_but_distinct :
    LevelExpr.denoteEquiv (LevelExpr.lmax (LevelExpr.lvar 0) (LevelExpr.lvar 1))
        (LevelExpr.lmax (LevelExpr.lvar 1) (LevelExpr.lvar 0))
    ∧ LevelExpr.lmax (LevelExpr.lvar 0) (LevelExpr.lvar 1)
        ≠ LevelExpr.lmax (LevelExpr.lvar 1) (LevelExpr.lvar 0) :=
  ⟨LevelExpr.lmax_comm_denoteEquiv (LevelExpr.lvar 0) (LevelExpr.lvar 1),
   by intro structEq; injection structEq with leftEq _; injection leftEq with indexEq; cases indexEq⟩

/-! ## The pinned ledger entry -/

/-- Where the universe-level normalizer sits relative to the rule-table
program.  A two-state honest ledger: either it is `tableized` (would be a
`LevelRuleDesc` table with the generic confluence/termination), or it is a
`pinnedExclusion` (a separate convergent normalizer, justified). -/
inductive LevelNormalizationStatus where
  /-- LevelExpr normalization is a first-order rule table in the program. -/
  | tableized : LevelNormalizationStatus
  /-- LevelExpr normalization stays a bespoke convergent AC-normalizer,
  excluded from the rule-table program with a machine-checked reason. -/
  | pinnedExclusion : LevelNormalizationStatus
deriving DecidableEq, Repr

/-- **THE LEVEL-TAB DECISION: pinned exclusion.**  Levels are NOT a rule
table — see the module docstring + `levelNormalization_exclusion_justified`. -/
def levelNormalizationStatus : LevelNormalizationStatus :=
  .pinnedExclusion

/-- **The exclusion is justified** — the machine-checked bundle behind the
ledger value.  Three facts pin the decision:

* the lmax-commutativity rule is SOUND (`lmaxOrient_denoteEquiv`) yet its
  orientation CYCLES (`lmaxOrient_cycles`) and the step is NON-TRIVIAL
  (`lmaxOrient_nontrivial_witness`) — so it is not an orientation-terminating
  row (reason 1);
* `simplify` already reaches structural normal form
  (`simplify_produces_isStructurallyNormalForm`) and is idempotent
  (`simplify_idempotent`) — the normalizer is already complete and
  convergent, no extension pressure (reason 2).

The conjunction is the honest MOON-LEDGER exclusion certificate for the
level seam. -/
theorem levelNormalization_exclusion_justified :
    levelNormalizationStatus = .pinnedExclusion
    ∧ (∀ (leftExpr rightExpr : LevelExpr),
        LevelExpr.denoteEquiv (LevelExpr.lmax leftExpr rightExpr)
            (LevelExpr.lmaxOrient (LevelExpr.lmax leftExpr rightExpr))
        ∧ LevelExpr.lmaxOrient (LevelExpr.lmaxOrient (LevelExpr.lmax leftExpr rightExpr))
            = LevelExpr.lmax leftExpr rightExpr)
    ∧ (∀ (expr : LevelExpr), LevelExpr.IsStructurallyNormalForm expr.simplify)
    ∧ (∀ (expr : LevelExpr), expr.simplify.simplify = expr.simplify) :=
  ⟨rfl,
   fun leftExpr rightExpr =>
     ⟨LevelExpr.lmaxOrient_denoteEquiv leftExpr rightExpr,
      LevelExpr.lmaxOrient_cycles leftExpr rightExpr⟩,
   LevelExpr.simplify_produces_isStructurallyNormalForm,
   fun expr => LevelExpr.simplify_idempotent expr⟩

end FX1Poly.Universe
