import FX1Poly.Typed.TypedByTableUnion
import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Typed.HasTypeDescTermIndexedFormer

/-! # FX1Poly/Typed/TableTypingUnionDivergence — where the union types strictly more than the honesty classifier

`hasTableTypingRule` (`TypedByTableUnion`) is the faithful table-driven twin of the honesty classifier
`hasSomeTypingRule`: exactly equal, by `hasSomeTypingRule_eq_hasTableTypingRule`.  To stay faithful it
DELIBERATELY excludes three rule tables that DO drive `HasTypeNativeUnion`:

  * `termIndexedFormerDescOf` (carries the `idCode` formation row, landed by the Id retrofit),
  * `nativeRecursiveElimRuleOf` (carries the `natElim` / `natRec` recursive-eliminator rows), and
  * `listElimNativeRuleOf` (carries the `listElim` row).

Including any of them would flip the classifier on the four heads `idCode` / `natElim` / `natRec` / `listElim`,
which the honesty classifier still brands RESERVED (`hasSomeTypingRule … = false`) — a verdict that PREDATES the
recursive-eliminator union arms (NATIVE-32) and the Id retrofit (NATIVE-17).  This file pins that genuine
divergence as machine-checked findings: the four heads are union-typable through their tables yet honesty-reserved.
It is the precise input to the canonicity-collapse decision — whether to promote those four to statically live.

  * **`hasUnionEliminatorTypingRule`** — the full-union extension: `hasTableTypingRule` ∨ the three excluded tables.
  * **`hasTableTypingRule_le_hasUnionEliminatorTypingRule`** — the extension refines the table classifier (pointwise).
  * **`unionEliminatorClassifierStrictlyExtends…`** (★) — the four strict witnesses + the bundle: each head is
    honesty-reserved (`hasSomeTypingRule = false`, hence `hasTableTypingRule = false`) yet flips to live under the
    full-union classifier.  The containment is PROPER on exactly these four heads.

## Zero-axiom

Every divergence fact is `rfl` (the tables and both classifiers compute on a concrete generator); the refinement is
`cases` on the chain Bool.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The full-union eliminator-aware classifier.**  `hasTableTypingRule` extended with the three union tables the
faithful twin excludes — the term-indexed former table (`idCode`), the recursive-eliminator table (`natElim` /
`natRec`), and the listElim table.  This is what a classifier tracking the WHOLE union (not just the
honesty-classifier's set) reports. -/
def hasUnionEliminatorTypingRule (generator : Generator) : Bool :=
  hasTableTypingRule generator || (termIndexedFormerDescOf generator).isSome
  || (nativeRecursiveElimRuleOf generator).isSome || (listElimNativeRuleOf generator).isSome

/-- **The full-union classifier refines the table classifier (pointwise).**  Anything the faithful table classifier
types, the eliminator-aware extension types too — a true leading disjunct makes the `||` true. -/
theorem hasTableTypingRule_le_hasUnionEliminatorTypingRule (generator : Generator)
    (live : hasTableTypingRule generator = true) : hasUnionEliminatorTypingRule generator = true := by
  unfold hasUnionEliminatorTypingRule
  rw [live]
  rfl

/-! ## ★ The four strict-divergence witnesses -/

/-- **`idCode` — union-typable through `termIndexedFormerDescOf`, honesty-reserved.**  The Id retrofit (NATIVE-17)
made `idCode` formable, so the term-indexed former table carries its row; but the honesty classifier still reports
it reserved (it was only ever a classifier of `refl`, never a formed subject, when the classifier was written). -/
theorem idCodeUnionTypableButHonestyReserved :
    (termIndexedFormerDescOf .gen_idCode).isSome = true ∧
    hasSomeTypingRule .gen_idCode = false ∧
    hasTableTypingRule .gen_idCode = false ∧
    hasUnionEliminatorTypingRule .gen_idCode = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`natElim` — union-typable through `nativeRecursiveElimRuleOf`, honesty-reserved.**  The recursive-eliminator
union arm (NATIVE-32) types `natElim`; the honesty classifier brands the recursive eliminators reserved. -/
theorem natElimUnionTypableButHonestyReserved :
    (nativeRecursiveElimRuleOf .gen_natElim).isSome = true ∧
    hasSomeTypingRule .gen_natElim = false ∧
    hasTableTypingRule .gen_natElim = false ∧
    hasUnionEliminatorTypingRule .gen_natElim = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`natRec` — the dependent-recursor twin of `natElim`.** -/
theorem natRecUnionTypableButHonestyReserved :
    (nativeRecursiveElimRuleOf .gen_natRec).isSome = true ∧
    hasSomeTypingRule .gen_natRec = false ∧
    hasTableTypingRule .gen_natRec = false ∧
    hasUnionEliminatorTypingRule .gen_natRec = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`listElim` — union-typable through `listElimNativeRuleOf`, honesty-reserved.** -/
theorem listElimUnionTypableButHonestyReserved :
    (listElimNativeRuleOf .gen_listElim).isSome = true ∧
    hasSomeTypingRule .gen_listElim = false ∧
    hasTableTypingRule .gen_listElim = false ∧
    hasUnionEliminatorTypingRule .gen_listElim = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **★ The full-union classifier STRICTLY extends the honesty classifier on exactly the recursive-eliminator and
Id-former heads.**  The refinement (everything table-live is union-live) plus four strict witnesses
(`idCode` / `natElim` / `natRec` / `listElim` are honesty-reserved yet union-live).  This is the precise honest
statement that the honesty ledger is STALE relative to the union: the union's recursive-eliminator arms and the Id
retrofit type four heads the honesty classifier was written (pre-union) to call reserved — the input to whether to
promote them to statically live. -/
theorem unionEliminatorClassifierStrictlyExtendsHonestyClassifier :
    (∀ generator : Generator,
      hasTableTypingRule generator = true → hasUnionEliminatorTypingRule generator = true) ∧
    (hasSomeTypingRule .gen_idCode = false ∧ hasUnionEliminatorTypingRule .gen_idCode = true) ∧
    (hasSomeTypingRule .gen_natElim = false ∧ hasUnionEliminatorTypingRule .gen_natElim = true) ∧
    (hasSomeTypingRule .gen_natRec = false ∧ hasUnionEliminatorTypingRule .gen_natRec = true) ∧
    (hasSomeTypingRule .gen_listElim = false ∧ hasUnionEliminatorTypingRule .gen_listElim = true) :=
  ⟨fun generator live => hasTableTypingRule_le_hasUnionEliminatorTypingRule generator live,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end FX1Poly.Typed
