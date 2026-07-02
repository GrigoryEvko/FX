import FX1Poly.Typed.Engine.Classifier.TypedByTableUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.RuleTables.TermIndexedFormer

/-! # FX1Poly/Typed/TableTypingUnionDivergence — the union classifier now AGREES with the honesty classifier

This file once pinned a genuine DIVERGENCE: the honesty classifier `hasSomeTypingRule` (and its faithful table
twin `hasTableTypingRule`) deliberately excluded three rule tables that DO drive `HasTypeUnion`, so four heads —
`idCode` / `natElim` / `natRec` / `listElim` — were union-typable yet honesty-RESERVED.  TAB-CLS closed that gap:
`hasSomeTypingRule` and `hasTableTypingRule` were both promoted to consult the same three tables —

  * `termIndexedFormerDescOf` (the `idCode` formation row, landed by the Id retrofit NATIVE-17),
  * `nativeRecursiveElimRuleOf` (the `natElim` / `natRec` recursive-eliminator rows, NATIVE-32), and
  * `listElimNativeRuleOf` (the `listElim` row).

So the honesty classifier now AGREES with the full union on all four heads; the former divergence is CLOSED.  The
file is retained (no-delete) and restated as the AGREEMENT certificate: the full-union classifier
`hasUnionEliminatorTypingRule` coincides with `hasTableTypingRule` (hence with `hasSomeTypingRule`), and each of the
four formerly-divergent heads is now live across ALL three classifiers.

  * **`hasUnionEliminatorTypingRule`** — the full-union extension: `hasTableTypingRule` ∨ the three tables.  Retained
    as the canonical name `UnionStaticTypingSoundness` consults; its three extra disjuncts are now subsumed by
    `hasTableTypingRule`, so it is provably equal to the twin.
  * **`hasTableTypingRule_le_hasUnionEliminatorTypingRule`** — the extension refines the table classifier (pointwise).
  * **`hasUnionEliminatorTypingRule_eq_hasTableTypingRule`** (★) — the agreement: the full-union classifier and the
    table twin compute the SAME `Bool` on every generator (`cases g <;> rfl`).
  * **`…LiveAcrossClassifiers`** + **`unionEliminatorClassifierAgreesWithHonestyClassifier`** (★) — the four heads
    `idCode` / `natElim` / `natRec` / `listElim` are now live across honesty / table / full-union classifiers, and the
    bundle records the agreement.

## Zero-axiom

Every agreement fact is `rfl` (the tables and all three classifiers compute on a concrete generator); the universal
equality is `cases generator <;> rfl`; the refinement is `rw` + `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The full-union eliminator-aware classifier.**  `hasTableTypingRule` extended with the three union tables —
the term-indexed former table (`idCode`), the recursive-eliminator table (`natElim` / `natRec`), and the listElim
table.  Post-TAB-CLS `hasTableTypingRule` ALREADY folds those three tables in, so the extra disjuncts are redundant
and this classifier is provably equal to the twin (`hasUnionEliminatorTypingRule_eq_hasTableTypingRule`).  The name
is retained as the canonical full-union classifier `UnionStaticTypingSoundness` keys its peel on. -/
def hasUnionEliminatorTypingRule (generator : Generator) : Bool :=
  hasTableTypingRule generator || (termIndexedFormerDescOf generator).isSome
  || (nativeRecursiveElimRuleOf generator).isSome || (listElimNativeRuleOf generator).isSome

/-- **The full-union classifier refines the table classifier (pointwise).**  Anything the table classifier types,
the eliminator-aware extension types too — a true leading disjunct makes the `||` true. -/
theorem hasTableTypingRule_le_hasUnionEliminatorTypingRule (generator : Generator)
    (live : hasTableTypingRule generator = true) : hasUnionEliminatorTypingRule generator = true := by
  unfold hasUnionEliminatorTypingRule
  rw [live]
  rfl

/-- **★ The full-union classifier AGREES with the table classifier on every generator.**  Post-TAB-CLS
`hasTableTypingRule` already folds in the three extension tables, so the three extra disjuncts of
`hasUnionEliminatorTypingRule` are subsumed — both classifiers compute the same `Bool` on every one of the 205
generators.  Combined with the shipped `hasSomeTypingRule_eq_hasTableTypingRule`, all THREE static classifiers
coincide. -/
theorem hasUnionEliminatorTypingRule_eq_hasTableTypingRule (generator : Generator) :
    hasUnionEliminatorTypingRule generator = hasTableTypingRule generator := by
  cases generator <;> rfl

/-! ## ★ The four formerly-divergent heads are now live across all classifiers -/

/-- **`idCode` — live across honesty / table / full-union classifiers.**  The Id retrofit (NATIVE-17) put the
`idCode` formation row in `termIndexedFormerDescOf`; TAB-CLS folded that table into both `hasSomeTypingRule` and
`hasTableTypingRule`, so the formerly-honesty-reserved Id former is now statically typed everywhere. -/
theorem idCodeLiveAcrossClassifiers :
    (termIndexedFormerDescOf .gen_idCode).isSome = true ∧
    hasSomeTypingRule .gen_idCode = true ∧
    hasTableTypingRule .gen_idCode = true ∧
    hasUnionEliminatorTypingRule .gen_idCode = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`natElim` — live across all classifiers** via `nativeRecursiveElimRuleOf` (NATIVE-32), now folded into the
honesty classifier by TAB-CLS. -/
theorem natElimLiveAcrossClassifiers :
    (nativeRecursiveElimRuleOf .gen_natElim).isSome = true ∧
    hasSomeTypingRule .gen_natElim = true ∧
    hasTableTypingRule .gen_natElim = true ∧
    hasUnionEliminatorTypingRule .gen_natElim = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`natRec` — the dependent-recursor twin of `natElim`, live across all classifiers.** -/
theorem natRecLiveAcrossClassifiers :
    (nativeRecursiveElimRuleOf .gen_natRec).isSome = true ∧
    hasSomeTypingRule .gen_natRec = true ∧
    hasTableTypingRule .gen_natRec = true ∧
    hasUnionEliminatorTypingRule .gen_natRec = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`listElim` — live across all classifiers** via `listElimNativeRuleOf`, now folded in by TAB-CLS. -/
theorem listElimLiveAcrossClassifiers :
    (listElimNativeRuleOf .gen_listElim).isSome = true ∧
    hasSomeTypingRule .gen_listElim = true ∧
    hasTableTypingRule .gen_listElim = true ∧
    hasUnionEliminatorTypingRule .gen_listElim = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **★ The full-union classifier AGREES with the honesty classifier — the former divergence is closed.**  The
universal agreement (everything the full-union classifier types, the table twin types, and vice versa) plus four
witnesses (`idCode` / `natElim` / `natRec` / `listElim` are now honesty-live AND union-live).  This is the precise
honest statement that TAB-CLS made the honesty ledger CURRENT with the union: the recursive-eliminator arms and the
Id retrofit type exactly the four heads the honesty classifier was once written (pre-union) to call reserved, and
the honesty classifier now reports them live. -/
theorem unionEliminatorClassifierAgreesWithHonestyClassifier :
    (∀ generator : Generator,
      hasUnionEliminatorTypingRule generator = hasTableTypingRule generator) ∧
    (hasSomeTypingRule .gen_idCode = true ∧ hasUnionEliminatorTypingRule .gen_idCode = true) ∧
    (hasSomeTypingRule .gen_natElim = true ∧ hasUnionEliminatorTypingRule .gen_natElim = true) ∧
    (hasSomeTypingRule .gen_natRec = true ∧ hasUnionEliminatorTypingRule .gen_natRec = true) ∧
    (hasSomeTypingRule .gen_listElim = true ∧ hasUnionEliminatorTypingRule .gen_listElim = true) :=
  ⟨hasUnionEliminatorTypingRule_eq_hasTableTypingRule,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end FX1Poly.Typed
