/-! # Foundation/PolyCell/NbE/DesignDecision
   — committed NbE design choice for the M11-M17 pipeline

M11-pre (#372, 2026-05-28).  Resolves the contradiction Agent 3 +
Agent 4 of the 5-agent gap audit surfaced between:

* **M11 #260 task wording** ("ValueTerm semantic domain with HOAS
  closures") — Design A: a SEPARATE inductive `ValueTerm` with
  Lean-level functions for HOAS λ closures, `eval : RawTerm →
  ValueTerm`, `quote : ValueTerm → RawTerm`.

* **polycell.md §3 Phase 3 table (lines 5704-5707)** — Design B:
  no new inductive; values are NF PREDICATES on `RawTerm`,
  `eval` is the polygraph fold, `quote` is the inverse of fold
  (i.e. identity once eval lands at NF).

The two designs lead to different M11-M17 implementations and
different downstream Decidable-Conv paths.

## The decision: HYBRID

After careful analysis, neither pure Design A nor pure Design B is
optimal.  The committed design is:

* **Raw layer** (M11-M14, M16-M18): follow polycell vision —
  `eval : RawTerm → RawTerm` returns a `RawTerm` in β-NF via the
  fold engine, `RawTerm.isNF` (M-substrate-3 #367) is the NF
  predicate, `quote` is the IDENTITY at the raw layer (the eval
  output already IS in NF, no readback needed).
* **Typed layer with η** (M15a-e via #359-#363, M55a #364):
  add a SEPARATE type-directed η-long readback pass
  `etaLongReadback : RawTerm → Ty → RawTerm` that inserts
  η-expansions per the target type (Π → `lam (app f (var 0))`,
  Σ → `pair (fst p) (snd p)`, Unit → `()`, etc.).

The hybrid splits raw and typed concerns:
* Raw β-NF: handled by eval-as-fold.
* Typed β-η-NF: handled by post-eval etaLongReadback at the type.

## Why this hybrid wins

**Versus pure Design A (HOAS ValueTerm)**:
* HOAS in Lean requires meta-level functions inside Value ctors,
  which complicates audit-gating and DecidableEq.
* The polycell uniformity thesis is REAL: one inductive (RawTerm),
  one fold (parameterized by GenAlgebra), one set of metatheory
  cascades.  A separate ValueTerm inductive doubles the substrate.
* The HOAS closure design's main motivation is η-long readback
  at function types — which the hybrid handles via a separate
  typed pass, not by changing the semantic domain.

**Versus pure Design B (everything as RawTerm predicates)**:
* Design B can't directly express typed-η (e.g. Unit-η: every
  Unit-typed term ≡ ()) because that requires KNOWING the type.
* M55a typed β+η Decidable Conv needs type-directed readback;
  pure Design B has no place to insert it.

**Versus hybrid**:
* Raw layer stays clean and spec-aligned (one inductive, one
  fold, NF predicate).
* Typed layer adds exactly the type-directed pass needed for η,
  no more.
* M11-M17 simplifies: M13 quote becomes the identity at raw,
  collapsing one substrate concern.
* M15a-e remains as planned but is now an after-the-fact typed
  post-processing pass, not a redesign of the semantic domain.

## Concrete consequences for M11-M17 task descriptions

* **M11 #260 retitle**: "NbE substrate — `RawTerm.isNF` predicate
  + canonical normalizer signature."  Drops "ValueTerm semantic
  domain with HOAS closures."
* **M12 #261 retitle**: "NbE eval — `RawTerm → RawTerm` in β-NF
  via fold + NbE GenAlgebra."  No `ValueTerm` target type.
* **M13 #262 retitle**: "NbE quote — identity at raw layer (eval
  output is already in NF)."  Cheapest deliverable in M11-M17.
* **M14 #263 stays**: β-NF smoke corpus.  Now checks eval outputs
  directly against expected RawTerm NFs.
* **M15a-e #359-#363 stay**: type-directed η-long readback pass
  applied AFTER eval at typed layer.
* **M16 #265 NbE soundness**: `Conv a b ↔ eval a = eval b` at
  raw layer (RawTerm equality on NFs).
* **M17 #266 NbE completeness**: every closed certified term has
  a unique RawTerm NF.
* **M18 #267 ★ Decidable raw Conv**: `decide (Conv a b) :=
  RawTerm.decEq (eval a) (eval b)` — single line at raw layer.

## Consequences for typed pipeline

* **M55 #304 ★ Decidable typed Conv**: at type T, computes
  `etaLongReadback (eval a) T` and `etaLongReadback (eval b) T`,
  then compares via `RawTerm.decEq`.
* **M55a #364 typed β+η Decidable Conv**: directly extends M55
  with the η-cascade's `Step.eta` confluence.

## Why this is committed today

* It dissolves the spec/task contradiction.
* It preserves the polycell uniformity thesis at the raw layer.
* It satisfies the typed-η design requirement at the typed layer.
* It minimizes the substrate surface (one inductive, one fold).
* It commits to a coherent vision before M11+ implementation
  starts — avoids per-implementer drift.

## What's NOT decided here

Two follow-up decisions are GATED on this commitment:

* **M12-pre #373**: reduction strategy choice (CBN vs CBV vs lazy).
  Hybrid is strategy-agnostic; M12-pre commits separately.
* **M-WHNF-migration #374**: whether to retire `Algo/RawWHNF/` or
  keep it as the algorithmic procedure.  Hybrid makes either
  direction viable; M-WHNF-migration commits separately.

## Audit-gated marker

This file ships a marker inductive `NbEDesignChoice` and a committed
value `NbEDesign.committed : NbEDesignChoice := .hybrid`.  The marker
is queryable by downstream code (e.g. M11's implementation files can
match on it).  Audit-gated to ensure the choice does not silently
change without re-elaborating this decision file.

## Zero-axiom verification

Three declarations, all closing by `rfl` or direct value construction.
No `axiom`, no `sorry`, no Classical.  Audit-gated. -/

namespace LeanFX2.Foundation.PolyCell.NbE

/-- Marker tracking the NbE design choice committed to by M11-pre
`#372`.

* `rawTermNFPredicate` — Design B (polycell-vision): values are NF
  predicates on RawTerm, eval = fold, quote = identity.
* `hoasClosures` — Design A (modern NbE): separate ValueTerm
  inductive with HOAS λ closures.
* `hybrid` — committed: Design B at raw layer + type-directed
  η-long readback at typed layer.
* `undecided` — placeholder marker for tasks not yet committed. -/
inductive NbEDesignChoice
  | rawTermNFPredicate
  | hoasClosures
  | hybrid
  | undecided
deriving DecidableEq, BEq, Repr

/-- The committed NbE design for M11-M17.  The hybrid choice
preserves polycell uniformity at the raw layer (one inductive, one
fold) while adding a separate typed η-long readback pass for the
typed-η requirement.

See file docstring for full rationale. -/
def NbEDesign.committed : NbEDesignChoice := .hybrid

/-- Pinned theorem witnessing that the committed design is the
hybrid.  Future code that matches on `NbEDesign.committed` can rely
on this `rfl` to specialize. -/
theorem NbEDesign.committed_is_hybrid :
    NbEDesign.committed = .hybrid := rfl

/-- Decidability instance for the committed-choice marker.  Useful
in audit checks that confirm `NbEDesign.committed` has not silently
regressed to `.undecided` during a refactor. -/
instance : Decidable (NbEDesign.committed = .hybrid) :=
  decEq NbEDesign.committed .hybrid

end LeanFX2.Foundation.PolyCell.NbE
