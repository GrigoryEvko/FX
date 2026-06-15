/-! # Foundation/PolyCell/NbE/DesignDecision
   — NbE design-choice marker

The NbE design choice as a queryable marker.  The committed choice
is HYBRID, which splits the raw and typed concerns:

* **Raw layer**: `eval : RawTerm → RawTerm` returns a `RawTerm` in
  β-NF via the fold engine, `RawTerm.isNF` is the NF predicate, and
  `quote` is the IDENTITY at the raw layer (the eval output already
  IS in NF, no readback needed).
* **Typed layer with η**: a SEPARATE type-directed η-long readback
  pass `etaLongReadback : RawTerm → Ty → RawTerm` inserts
  η-expansions per the target type (Π → `lam (app f (var 0))`,
  Σ → `pair (fst p) (snd p)`, Unit → `()`, etc.).

So raw β-NF is handled by eval-as-fold, and typed β-η-NF by post-eval
`etaLongReadback` at the type.

## Why hybrid

* The raw layer keeps the polycell uniformity thesis: one inductive
  (RawTerm), one fold (parameterized by GenAlgebra), one set of
  metatheory cascades.  A separate HOAS `ValueTerm` inductive would
  double the substrate and complicate audit-gating and DecidableEq.
* The typed layer adds exactly the type-directed pass needed for η,
  no more.  Type-directed readback is where typed-η (e.g. Unit-η:
  every Unit-typed term ≡ ()) lives, since it requires KNOWING the
  type.

## Audit-gated marker

This file defines a marker inductive `NbEDesignChoice` and the
committed value `NbEDesign.committed : NbEDesignChoice := .hybrid`,
queryable by downstream code.  Audit-gated to ensure the choice does
not silently change.

## Zero-axiom verification

Three declarations, all closing by `rfl` or direct value construction.
No `axiom`, no `sorry`, no Classical.  Audit-gated. -/

namespace FX1Poly.NbE

/-- Marker tracking the NbE design choice.

* `rawTermNFPredicate` — values are NF predicates on RawTerm,
  eval = fold, quote = identity.
* `hoasClosures` — a separate ValueTerm inductive with HOAS λ
  closures.
* `hybrid` — `rawTermNFPredicate` at the raw layer + type-directed
  η-long readback at the typed layer.
* `undecided` — placeholder marker for an uncommitted choice. -/
inductive NbEDesignChoice
  | rawTermNFPredicate
  | hoasClosures
  | hybrid
  | undecided
deriving DecidableEq, BEq, Repr

/-- The committed NbE design.  The hybrid choice preserves polycell
uniformity at the raw layer (one inductive, one fold) while adding a
separate typed η-long readback pass for the typed-η requirement.

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

end FX1Poly.NbE
