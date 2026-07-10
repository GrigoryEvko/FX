import FX1Poly.Tier0.Term.Subst.RawTermSubstAction
import FX1Poly.Polygraph.Omega.Steiner.DecideFreeConv

/-! # Polygraph/Omega/SubstPasting — substitution composition IS pasting arithmetic (OMEGA-7 r1, B1)

★ **THE IDENTIFICATION, the OMEGA-5 App-anchor play one layer down.**  OMEGA-5 identified the kernel App
rule's grade slot with the sequential graded composite `gradeCompose` by defeq (`GradedAppAnchor.lean`).
OMEGA-7 r1 does the SAME move for substitution: it recognises the kernel's most-used primitive law
`RawTerm.subst_compose` — the polynomial-monad multiplication `(t.subst s1).subst s2 = t.subst (s1.compose
s2)` (`Tier0/Term/Subst/RawTermSubstCompose.lean`, the file's own thesis "μ_X ∘ μ_X = μ_X ∘ T_μ_X") — as the
TERM-side instance of the same associative-composition arithmetic whose Steiner PASTING shadow is
`addCoordinates_assoc` (`Steiner/CoordinateArithmetic.lean`).  The bridge is the ALREADY-SHIPPED `linearize`
homomorphism, whose `.vcomp` arm is literally `addCoordinates` of the two legs (`Steiner/Linearize.lean`,
`linearize_vcomp`) — "composition IS addition" (Steiner, arXiv:math/0403237).

This is the PICKED r1 form (recon Form B — the arithmetic shadow): the substitution-composition LAW and the
pasting-composition LAW are the same associative operation, byte-for-byte where possible.  It defers Form A
(a total `termToCell` model homomorphism) to the Makkai wall — arbitrary lambda-terms are not strong-Steiner,
so no total homomorphism into the integer-arithmetic fragment exists in general (memo pin OMEGA-7(c); see the
r1 ledger `DesignLockOmega7.lean`).

## What ships here (each machine-checked zero-axiom)

  * **`substCompose_assoc`** — THE genuine kernel-lemma anchor.  `RawTermSubst.compose` is ASSOCIATIVE
    (pointwise, no `funext` so no `Quot.sound`): at every position the two bracketings agree, and the proof
    IS `RawTerm.subst_compose` applied at `firstSubstitution position` — no re-proof, no lookalike, the
    genuine kernel workhorse anchored to the composition.  The two unit laws (`substCompose_identity_left`
    by `rfl`, `substCompose_identity_right` by `subst_identity_apply`) complete the substitution MONOID.
  * **`IsAssociativeComposition`** — the generic shape both sides instantiate: `∀ a b c, op (op a b) c =
    op a (op b c)`.
  * **`steinerPasting_isAssociativeComposition`** — the STEINER shadow, byte-for-byte:
    `IsAssociativeComposition addCoordinates := addCoordinates_assoc`.  The pasting composition is exactly
    the associative coordinate addition.
  * **`linearize_vcomp_eq_pasting`** — the homomorphism leg (`rfl`): `linearize` sends the polygraph pasting
    composite `vcomp` to `addCoordinates` of the two linearized legs.
  * **`linearize_vcomp_assoc`** — the pasting associativity carried through the homomorphism: on the
    strong-Steiner fragment (relative to a `ComputadValuation`), re-bracketing a triple `vcomp` is invisible
    to `linearize`, its proof `addCoordinates_assoc` on the linearized legs.
  * **`substLemma_is_pastingAssoc`** — ★ THE ANCHOR.  The two faces packaged: the substitution monoid's
    action law (LEFT conjunct, = kernel `subst_compose`) and its Steiner pasting shadow (RIGHT conjunct, =
    `addCoordinates_assoc` under `linearize`) are the SAME associative-composition law.

## Non-vacuity (recon B1 discipline — two concrete witnesses)

  * **`substPasting_linearizeVcomp_nonVacuity`** / **`substPasting_vcompAssoc_nonVacuity`** — a concrete
    dim-3 `vcomp` over the demo computad linearises to a concrete coordinate SUM (`[1,1,0] = [1,0,0] +
    [0,1,0]`), and a concrete triple `vcomp` re-brackets identically.
  * **`substFusion_nonVacuity`** / **`substFusion_computes`** — a concrete two-substitution fusion on REAL
    kernel substitutions (`subst s2 (subst s1 t) = subst (s1.compose s2) t`), both sides computing to a
    concrete unit term.

## The honest scoping (recon risk #1)

The `linearize` identification is RELATIVE to a `ComputadValuation` (the free-fragment Steiner realization),
matching OMEGA-2's scoping.  `substCompose_assoc` is the term-level ACTION law; `RawTermSubst.compose`
associativity is its 1-line pointwise corollary — the two are not conflated (recon risk #2).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Core
open FX1Poly.Polygraph.Steiner

/-! ## The term side — the substitution monoid (the genuine kernel-lemma anchor) -/

/-- ★ **THE SUBSTITUTION-COMPOSITION ANCHOR.**  `RawTermSubst.compose` is ASSOCIATIVE: at every position,
composing three substitutions is the same however bracketed.  The proof IS the kernel workhorse
`RawTerm.subst_compose` (the polynomial-monad multiplication) applied at `firstSubstitution position` — both
bracketings reduce, by the reducible `compose`, to `subst last (subst middle (first pos))` on the left and
`subst (compose middle last) (first pos)` on the right, which `subst_compose` identifies.  Stated POINTWISE
(no `funext`, so no `Quot.sound`) — the substitution monoid's associativity is the term-side face of the
same associative-composition law whose Steiner shadow is `addCoordinates_assoc`. -/
theorem substCompose_assoc
    {scopeA scopeB scopeC scopeD : Nat}
    (firstSubstitution : RawTermSubst scopeA scopeB)
    (middleSubstitution : RawTermSubst scopeB scopeC)
    (lastSubstitution : RawTermSubst scopeC scopeD)
    (position : Fin scopeA) :
    RawTermSubst.compose (RawTermSubst.compose firstSubstitution middleSubstitution)
        lastSubstitution position
      = RawTermSubst.compose firstSubstitution
          (RawTermSubst.compose middleSubstitution lastSubstitution) position :=
  RawTerm.subst_compose middleSubstitution lastSubstitution (firstSubstitution position)

/-- **The substitution monoid's LEFT unit** (pointwise, `rfl`): `identity . s ~ s`.  `compose identity s`
at a position reduces `subst s (identity position)` — the identity substituent is `mkGen .gen_var position
.childNil` and the fold's variable arm returns `s position` directly. -/
theorem substCompose_identity_left
    {scope targetScope : Nat} (someSubstitution : RawTermSubst scope targetScope)
    (position : Fin scope) :
    RawTermSubst.compose RawTermSubst.identity someSubstitution position = someSubstitution position :=
  rfl

/-- **The substitution monoid's RIGHT unit** (pointwise): `s . identity ~ s`.  `compose s identity` at a
position reduces to `subst identity (s position)`, which is `RawTerm.subst_identity_apply` at `s position`
(substituting by the identity returns the term unchanged). -/
theorem substCompose_identity_right
    {scope targetScope : Nat} (someSubstitution : RawTermSubst scope targetScope)
    (position : Fin scope) :
    RawTermSubst.compose someSubstitution RawTermSubst.identity position = someSubstitution position :=
  RawTerm.subst_identity_apply (someSubstitution position)

/-! ## The shared shape and the Steiner (pasting) side -/

/-- The **associative-composition shape** shared by substitution composition and coordinate addition — a
binary operation on one carrier whose two triple-bracketings agree.  The identification target: both the
substitution monoid and the Steiner pasting monoid instantiate this predicate. -/
def IsAssociativeComposition {carrier : Type} (composeOp : carrier → carrier → carrier) : Prop :=
  ∀ leftValue middleValue rightValue,
    composeOp (composeOp leftValue middleValue) rightValue
      = composeOp leftValue (composeOp middleValue rightValue)

/-- ★ **The STEINER pasting shadow, byte-for-byte.**  The Steiner pasting composition — coordinate addition
`addCoordinates` — is an associative composition, and the proof IS the shipped `addCoordinates_assoc`.  This
is the arithmetic face of the same law `substCompose_assoc` expresses at the term level. -/
theorem steinerPasting_isAssociativeComposition :
    IsAssociativeComposition addCoordinates :=
  addCoordinates_assoc

/-- **The homomorphism leg** (`rfl`): `linearize` sends the polygraph pasting composite `vcomp` to
`addCoordinates` of the two linearized legs — composition IS addition (Steiner). -/
theorem linearize_vcomp_eq_pasting {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (leftCell rightCell : CellExpr computad (dim + 1)) :
    (linearize valuation (CellExpr.vcomp leftCell rightCell)).coordinates
      = addCoordinates (linearize valuation leftCell).coordinates
          (linearize valuation rightCell).coordinates :=
  rfl

/-- ★ **The pasting associativity carried through the homomorphism.**  On the strong-Steiner fragment
(relative to a valuation), re-bracketing a triple pasting composite `vcomp` is INVISIBLE to `linearize`:
`linearize (vcomp (vcomp a b) c) = linearize (vcomp a (vcomp b c))`, its proof `addCoordinates_assoc` on the
linearized legs (via `congrArg SteinerCell.mk`).  This is the Steiner shadow of the substitution law
`substCompose_assoc`. -/
theorem linearize_vcomp_assoc {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellA cellB cellC : CellExpr computad (dim + 1)) :
    linearize valuation (CellExpr.vcomp (CellExpr.vcomp cellA cellB) cellC)
      = linearize valuation (CellExpr.vcomp cellA (CellExpr.vcomp cellB cellC)) :=
  congrArg SteinerCell.mk
    (addCoordinates_assoc (linearize valuation cellA).coordinates
      (linearize valuation cellB).coordinates (linearize valuation cellC).coordinates)

/-! ## THE ANCHOR — the two faces of one associative-composition law -/

/-- ★ **THE OMEGA-7 r1 ANCHOR — substitution law IS pasting arithmetic.**  The substitution monoid's action
law and the Steiner pasting arithmetic are the SAME associative-composition law, exhibited as a pair: the
LEFT conjunct is the kernel `subst_compose` (the substitution monoid associativity, `substCompose_assoc`),
the RIGHT conjunct is `addCoordinates_assoc` carried through the `linearize` homomorphism
(`linearize_vcomp_assoc`).  The genuine kernel workhorse `RawTerm.subst_compose` is the term-side instance;
its polygraph pasting shadow is `addCoordinates_assoc`; `linearize` is the composition homomorphism that
connects them.  (Form A — a total `termToCell` model homomorphism — is the deferred Makkai wall; see
`DesignLockOmega7.lean`.) -/
theorem substLemma_is_pastingAssoc
    {scopeA scopeB scopeC scopeD : Nat}
    (firstSubstitution : RawTermSubst scopeA scopeB)
    (middleSubstitution : RawTermSubst scopeB scopeC)
    (lastSubstitution : RawTermSubst scopeC scopeD)
    (position : Fin scopeA)
    {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellA cellB cellC : CellExpr computad (dim + 1)) :
    (RawTermSubst.compose (RawTermSubst.compose firstSubstitution middleSubstitution)
          lastSubstitution position
        = RawTermSubst.compose firstSubstitution
            (RawTermSubst.compose middleSubstitution lastSubstitution) position)
      ∧ (linearize valuation (CellExpr.vcomp (CellExpr.vcomp cellA cellB) cellC)
          = linearize valuation (CellExpr.vcomp cellA (CellExpr.vcomp cellB cellC))) :=
  ⟨substCompose_assoc firstSubstitution middleSubstitution lastSubstitution position,
   linearize_vcomp_assoc valuation cellA cellB cellC⟩

/-! ## Non-vacuity — concrete witnesses on real kernel data -/

/-- Non-vacuity (pasting side): a concrete dim-3 `vcomp` over the demo computad linearises to a concrete
coordinate SUM — `[1,1,0] = addCoordinates [1,0,0] [0,1,0]` — "composition IS addition" computing on real
cells. -/
theorem substPasting_linearizeVcomp_nonVacuity :
    (linearize demoValuation (CellExpr.vcomp cellThreeA cellThreeB)).coordinates = [1, 1, 0] := rfl

/-- Non-vacuity (pasting associativity): a concrete triple `vcomp` re-brackets identically under
`linearize`, via the shipped `linearize_vcomp_assoc`. -/
theorem substPasting_vcompAssoc_nonVacuity :
    linearize demoValuation (CellExpr.vcomp (CellExpr.vcomp cellThreeA cellThreeB) cellThreeA)
      = linearize demoValuation (CellExpr.vcomp cellThreeA (CellExpr.vcomp cellThreeB cellThreeA)) :=
  linearize_vcomp_assoc demoValuation cellThreeA cellThreeB cellThreeA

/-- A concrete source term (variable 0 at scope 1) for the substitution-fusion non-vacuity. -/
def sampleFusionTerm : RawTerm 1 :=
  .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil

/-- A concrete first substitution (the identity on scope 1). -/
def sampleFusionFirst : RawTermSubst 1 1 := RawTermSubst.identity

/-- A concrete second substitution (scope 1 -> scope 1) mapping variable 0 to a unit term. -/
def sampleFusionSecond : RawTermSubst 1 1 :=
  fun _ => .mkGen .gen_unit () .childNil

/-- ★ Non-vacuity (term side): the two-substitution FUSION on REAL kernel substitutions — substituting
sequentially equals substituting by the composite, `subst s2 (subst s1 t) = subst (s1.compose s2) t` — is
the kernel `subst_compose` on the concrete sample data.  The identity is not vacuous on real substitutions. -/
theorem substFusion_nonVacuity :
    RawTerm.subst sampleFusionSecond (RawTerm.subst sampleFusionFirst sampleFusionTerm)
      = RawTerm.subst (RawTermSubst.compose sampleFusionFirst sampleFusionSecond) sampleFusionTerm :=
  RawTerm.subst_compose sampleFusionFirst sampleFusionSecond sampleFusionTerm

/-- Non-vacuity (term side, computation): both fusion legs COMPUTE to the concrete unit term (`rfl`),
witnessing the substitution actually fires (variable 0 replaced by unit). -/
theorem substFusion_computes :
    RawTerm.subst sampleFusionSecond (RawTerm.subst sampleFusionFirst sampleFusionTerm)
      = (.mkGen .gen_unit () .childNil : RawTerm 1) := rfl

end FX1Poly.Polygraph.Omega
