/-! # Polygraph/Omega/PsContext — CaTT pasting-scheme contexts as flat rows + the decidable ps-checker
    (OMEGA-6 r1, B1)

★ **The weak/directed rung's context layer — the Finster–Mimram CaTT ps-judgment shipped as DATA + a `Bool`
checker.**  A context is a *pasting scheme* iff it is derivable in CaTT's ps-judgment `Γ ⊢ps x : A` by four
rules (Finster–Mimram, *A type-theoretical definition of weak ω-categories*, LICS 2017):

  * **pss (start):** `(x : *) ⊢ps x : *` — the focus is a single object at dimension 0.
  * **pse (extend):** `Γ ⊢ps x : A  ⟹  Γ, (y : A), (f : x →_A y) ⊢ps f : x →_A y` — push a fresh target `y`
    and a fresh arrow `f`; the focus moves UP one dimension.
  * **psd (drop):** `Γ ⊢ps f : x →_A y  ⟹  Γ ⊢ps y : A` — the focus moves DOWN one dimension to the target.
  * **ps (final):** `Γ ⊢ps x : *  ⟹  Γ ⊢ps` — a completed ps-context has the focus back at dimension 0.

Under the canonical bijection ps-contexts ≅ Batanin trees ≅ Dyck words, the ps-judgment is a **decidable stack
walk**: the focus dimension goes UP on `pse`, DOWN on `psd`, must never go below the base, and must return to 0.

## The honest minimal encoding (DATA + a Bool checker — NOT a typed telescope)

The Omega carrier (`Carrier.lean`) has no variables, no context, no substitution.  Building a genuine typed
telescope drags weakening / substitution, which is explicitly **OMEGA-7** ("substitution = pasting").  So r1
ships the ps-judgment exactly the way `StrictAxiomRel` / `CriticalPairRow` ship laws as data and `cellBeq`
decides by a flat fold:

  * **`PsContextRow`** — a FLAT (non-`Nat`-indexed) inductive recording the pasting-scheme construction as the
    move sequence `start` / `extend` (pse) / `drop` (psd).  A plain inductive with no `Nat` type-index, so the
    checker is a structural fold — dodging the indexed-partial-match `propext` trap the Carrier boundary hit
    (`Carrier.lean` documents that exact trap).
  * **`psFocus`** — the focus-dimension stack machine: `some 0` at `start`, `+1` on `extend`, `-1` on `drop`,
    and `none` on an underflowing `drop` (dropping below the base is not a ps-move).  A full-enumeration match
    into the constant motive `Option Nat` — propext-free, like `cellSize`.
  * **`psContextCheck`** — the decidable ps-judgment: `true` iff the walk ends with the focus at dimension 0
    with no underflow (the completed `ps` rule).  A full `Option Nat` enumeration — no wildcard, so
    propext-clean, like `skeletonBeq`.

## Genuine discrimination (the non-vacuity brick)

The checker is genuinely discriminating, not trivially `true`:

  * the **single-2-cell disk** `(x)(y)(f)(g)(a : f⇒g)` (`twoGlobePsContext`) CHECKS `true`;
  * the **horizontal-composite** pasting scheme `(x)(y)(z)(f,g,a)(h,k,b)` (`horizontalCompositePsContext`)
    — the Godement / interchange source — CHECKS `true`;
  * a **dangling** context whose focus never returns to the base (`danglingPsContext`) CHECKS `false`;
  * an **underflowing** context that drops below the base (`underflowPsContext`) CHECKS `false`.

## What r1 does NOT do (named honestly, deferred to OMEGA-7)

r1 ships the ps-context SHAPE and its decision only.  It does NOT introduce typed variables, a telescope, or
substitution (that is OMEGA-7, "substitution = pasting"); and the `CohSeed` `CohRow` that consumes a checked
ps-context does NOT type its boundary OVER the ps-context (the fullness side-condition + the typed link are the
OMEGA-7 pasting engine).  The carrier already supplies everything the coherence rule's boundary side needs
(`IsParallelPair`, total boundaries); the ps-layer and the carrier meet only at the witness level in r1.

Raw Lean 4 + Init, STRUCTURAL only, ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The pasting-scheme row -/

/-- A **pasting-scheme context** recorded as the CaTT construction move sequence, a FLAT inductive (no `Nat`
type-index, so the checker is a structural fold that dodges the indexed-partial-match propext trap):

  * `start`  — the `pss` rule: the singleton object context `(x : *)`, focus at dimension 0.
  * `extend` — the `pse` rule: push a fresh target and arrow, focus UP one dimension.
  * `drop`   — the `psd` rule: move the focus DOWN one dimension to the target.

A `PsContextRow` is a valid (completed) ps-context exactly when `psContextCheck` returns `true`. -/
inductive PsContextRow where
  /-- `pss`: the singleton object context `(x : *)`, focus at dimension 0. -/
  | start : PsContextRow
  /-- `pse`: push a fresh target `y : A` and arrow `f : x →_A y`, focus UP one dimension. -/
  | extend : PsContextRow → PsContextRow
  /-- `psd`: move the focus DOWN one dimension to the target of the current arrow. -/
  | drop : PsContextRow → PsContextRow

/-! ## The decidable ps-judgment as a focus-dimension stack walk -/

/-- The **focus dimension** after walking the ps-context moves: `some 0` at `start`, `some (depth+1)` on
`extend`, `some depth` on a legal `drop`, and `none` on an underflowing `drop` (dropping below the base
dimension is not a ps-move).  A full-enumeration structural fold into the constant motive `Option Nat`, so
propext-free.  Structural recursion on the prior row. -/
def psFocus : PsContextRow → Option Nat
  | .start => some 0
  | .extend prior =>
      match psFocus prior with
      | some depth => some (depth + 1)
      | none => none
  | .drop prior =>
      match psFocus prior with
      | some (depth + 1) => some depth
      | some 0 => none
      | none => none

/-- ★ The **decidable ps-judgment**: `psContextCheck row = true` iff the ps-context is well formed and complete
— the focus walk ends at dimension 0 with no underflow (the CaTT `ps` final rule).  A full `Option Nat`
enumeration (no wildcard), so propext-clean; this is the decidable ps-checker the coherence rule gates on. -/
def psContextCheck (row : PsContextRow) : Bool :=
  match psFocus row with
  | some 0 => true
  | some (_ + 1) => false
  | none => false

/-! ## Non-vacuity — genuine discrimination between pasting and non-pasting contexts -/

/-- The **single-2-cell disk** `(x)(y)(f)(g)(a : f⇒g)`: `pss`, then two `pse`'s (focus up to dimension 2, the
2-cell `a`), then two `psd`'s (focus back to 0).  The canonical ps-context a 2-cell coherence fills. -/
def twoGlobePsContext : PsContextRow :=
  .drop (.drop (.extend (.extend .start)))

/-- The **horizontal-composite** pasting scheme `(x)(y)(z)(f,g,a : f⇒g)(h,k,b : h⇒k)`: two 2-cells side by
side sharing the middle object `y` — the Godement / interchange source.  Two nested up-down excursions, focus
returning to 0. -/
def horizontalCompositePsContext : PsContextRow :=
  .drop (.drop (.extend (.extend (.drop (.drop (.extend (.extend .start)))))))

/-- A **dangling** context: `pss` then `pse`, leaving the focus at dimension 1 (the in-progress judgment
`(x)(y)(f) ⊢ps f`, NOT the completed `ps` — the focus never returns to the base). -/
def danglingPsContext : PsContextRow :=
  .extend .start

/-- An **underflowing** context: `psd` applied at the base dimension — dropping below dimension 0 is not a
ps-move, so the walk fails. -/
def underflowPsContext : PsContextRow :=
  .drop .start

#eval psContextCheck twoGlobePsContext
#eval psContextCheck horizontalCompositePsContext
#eval psContextCheck danglingPsContext
#eval psContextCheck underflowPsContext

/-- The single-2-cell disk CHECKS as a valid ps-context. -/
theorem twoGlobePsContext_checks : psContextCheck twoGlobePsContext = true := rfl

/-- The horizontal-composite pasting scheme CHECKS as a valid ps-context. -/
theorem horizontalCompositePsContext_checks : psContextCheck horizontalCompositePsContext = true := rfl

/-- A dangling context (focus never returns to the base) CHECKS as NOT a ps-context. -/
theorem danglingPsContext_checksFalse : psContextCheck danglingPsContext = false := rfl

/-- An underflowing context (drops below the base) CHECKS as NOT a ps-context. -/
theorem underflowPsContext_checksFalse : psContextCheck underflowPsContext = false := rfl

end FX1Poly.Polygraph.Omega
