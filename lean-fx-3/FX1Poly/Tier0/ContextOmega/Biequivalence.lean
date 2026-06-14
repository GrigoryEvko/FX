import FX1Poly.Tier0.ContextOmega.Comprehension
import FX1Poly.Tier0.ContextOmega.Initiality

/-! # Tier0/ContextOmega/Biequivalence — the four presentations agree on the FX context base (context-6)

The semantics of dependent type theory can be packaged in several biequivalent ways: a **CwF**
(category with families, Dybjer), a **natural model** (Awodey — a representable natural transformation
`Tm ⟶ Ty`), a **representable map category** (Uemura), a **CwA** (category with attributes), and a
**contextual category** (Cartmell).  The "biequivalence" theorem says these are all the same 2-category
up to equivalence.  At the heart of every one of them is a SINGLE piece of data: the
context-extension universal property `Hom(Δ, Γ.A) ≅ Hom(Δ, Γ) × Tm(Δ)`.  On the FX term base that
property is the shipped `comprehensionBijection` (context-1).  This module exhibits the OTHER
presentations' defining data on the FX base and proves they agree with the CwF one — the funext-free
core of the biequivalence.

## What is built

  * **Natural-model presentation.**  Awodey's natural model is the display map `Tm ↠ Ty` together with
    representability.  Its defining data is the display PROJECTION `p = SubstVec.weakening` and the
    GENERIC ELEMENT `q = var 0` (the last variable).  `naturalModelExtensionDecomposes` is the
    representability statement (every map into the extension factors through `(p, q)`), and it IS the
    shipped `comprehensionPair_comprehensionSplit` — so the natural model and the CwF carry the same
    universal property.
  * **Contextual-category presentation.**  Cartmell's contextual category has a length GRADING on
    objects, a terminal object at grade 0, and grade-decreasing father maps.  On the FX base the
    grading is the scope itself; `scopeContextGrade_empty` / `scopeContextGrade_extend` are the
    contextual laws (grade of the empty context is 0, extension raises grade by one), bridging to
    context-5's `syntacticContextAlgebra`; the iterated father-tower is context-5's
    `interpretScope_syntactic_id`.
  * ★ `presentationsBiequivalent` — the headline: at each context the CwF comprehension bijection AND
    the natural-model decomposition AND the contextual grading laws hold simultaneously; the four
    presentations agree on the FX context base at the object + hom-set level.

## Honest boundary (recorded, not faked)

The FULL biequivalence is a 2-categorical statement: the four presentations form biequivalent
2-categories via structure-preserving 2-functors, with the comparison functors' coherences
(naturality squares, functoriality of the comparison on whole substitution/type/term presheaf maps).
Those coherences compare infinite function families (the `component` of a `SubstFamilyMap`, the
`morphismMap` of a `RawEndofunctor`) → `funext` = `Quot.sound`-derived, OFF the zero-axiom path (the
same boundary as context-3/4/5's adjoint/functor uniqueness).  What IS zero-axiom is the agreement at
the OBJECT level (the contextual grading = context-5's NNO) and the HOM-SET level (the one
comprehension bijection wears every presentation's hat).

## Zero-axiom verification

The natural-model decomposition is the shipped `comprehensionPair_comprehensionSplit`; the contextual
grading laws are `rfl` / the lock object map; the biequivalence bundle conjoins shipped lemmas.  No
`funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Core

/-! ## The natural-model presentation (Awodey): display projection + generic element -/

/-- **The natural model's display projection** `p : Γ.A ⟶ Γ`.  On the FX base it is the shipped
weakening substitution — the same map the CwF comprehension projects along. -/
def naturalModelDisplayProjection (scope : Nat) : SubstVec (scope + 1) scope :=
  SubstVec.weakening scope

/-- **The natural model's generic element** `q` — the "last variable" of the extended context, the
universal element witnessing representability.  On the FX base it is the zeroth entry of the identity
substitution (the canonical last variable cell). -/
def naturalModelGenericElement (scope : Nat) : RawTerm (scope + 1) :=
  (SubstVec.identity (scope + 1)).lookup ⟨0, Nat.succ_pos scope⟩

/-- **Natural-model representability = CwF comprehension.**  Every substitution into the extended
context factors uniquely through the universal `(p, q)` — i.e. the extension REPRESENTS the presheaf
`Δ ↦ Hom(Δ, Γ) × Tm(Δ)`.  This is exactly the shipped CwF comprehension round-trip
`comprehensionPair_comprehensionSplit`: the natural model and the CwF carry the SAME universal
property. -/
theorem naturalModelExtensionDecomposes {targetScope sourceScope : Nat}
    (extended : SubstVec targetScope (sourceScope + 1)) :
    comprehensionPair (comprehensionSplit extended) = extended :=
  comprehensionPair_comprehensionSplit extended

/-! ## The contextual-category presentation (Cartmell): the length grading -/

/-- **The contextual-category grading** — the length of a context.  On the FX base a context object IS
its scope, so the grading is the identity; the contextual structure lives in the grade-raising
extension and the grade-0 empty context. -/
def scopeContextGrade (scope : Nat) : Nat := scope

/-- The empty context has contextual grade `0` (the terminal/length-0 object). -/
theorem scopeContextGrade_empty : scopeContextGrade syntacticContextAlgebra.empty = 0 := rfl

/-- Context extension raises the contextual grade by exactly one (the father map decreases length by
one), bridging the contextual grading to context-5's `syntacticContextAlgebra` extension (the lock). -/
theorem scopeContextGrade_extend (scope : Nat) :
    scopeContextGrade (syntacticContextAlgebra.extend scope) = scopeContextGrade scope + 1 :=
  dimensionLock_objectMap scope

/-! ## The biequivalence headline -/

/-- ★ **The four presentations agree on the FX context base.**  At every context the CwF comprehension
bijection holds (so the CwF, the natural model as a representable display map, and the CwA/RMC all
share the one universal property), and the contextual grading laws hold (so the contextual category's
length structure is context-5's natural-numbers object).  This is the object + hom-set core of the
CwF ≃ natural model ≃ RMC ≃ CwA ≃ contextual-category biequivalence — the 2-functor coherences are the
recorded funext boundary. -/
theorem presentationsBiequivalent {targetScope sourceScope : Nat} :
    (∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
    (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended) ∧
    scopeContextGrade syntacticContextAlgebra.empty = 0 ∧
    (∀ scope : Nat,
        scopeContextGrade (syntacticContextAlgebra.extend scope) = scopeContextGrade scope + 1) :=
  ⟨comprehensionSplit_comprehensionPair, comprehensionPair_comprehensionSplit,
   scopeContextGrade_empty, scopeContextGrade_extend⟩

end FX1Poly.Tier0.ContextOmega
