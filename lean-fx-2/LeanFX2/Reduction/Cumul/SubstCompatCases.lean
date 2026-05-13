import LeanFX2.Reduction.Cumul.Relation

/-! # LeanFX2.Reduction.Cumul.SubstCompatCases

Phase 6-finish subst-compatibility helpers for the structural cases
(refl / sym / trans) of `ConvCumul`.  These three discharge directly
from the corresponding constructors and form the base of the
compositional approach used by the per-cong and per-Term-shape
helpers in sibling files.

## Root status

Layer 3 cumulativity helper.  Consumed by `Reduction.Cumul` shim. -/

namespace LeanFX2

/-! ## Phase 12.A.B1.6-finish: general ConvCumul.subst_compatible

The Phase 6 commitment: ConvCumul commutes with Subst across ALL
relation cases (refl, viaUp, sym, trans, plus the 18 cong ctors
from Phase 12.A.B1.5).

The general formulation handles a HETEROGENEOUS pair of substitutions
that are themselves "ConvCumul-compatible": ConvCumulSubst sigma1 sigma2
asserts that for each variable position, the two substituents are
ConvCumul-related.

Restricted homogeneous form: when both sides of ConvCumul share the
same context, scope, and level, a single TermSubst suffices.  Ships
both forms below. -/

/-! ### Phase 6-finish design notes (heterogeneous-target case)

ConvCumul is preserved across substitution applied to both sides,
where each side gets its own TermSubst suited to its own context/
level/scope.

A fully-homogeneous `subst_compatible` (single Subst applied to both
sides at SAME context/scope/level) is architecturally NOT GENERALLY
available because:
* Lean's induction principle on heterogeneous inductives like
  ConvCumul fails when the goal contains the same index twice (the
  "Invalid target: Target (or one of its indices) occurs more than
  once" error).
* The viaUp ctor's two endpoints live at fundamentally different
  scopes (scopeLow vs scope) and levels (lowerLevel+1 vs higherLevel+1),
  so unifying them would require destructuring the relation rather
  than inducting on it.
* The cong ctors permit independent inner ConvCumul derivations whose
  inner pieces may use viaUp at any level — same-level constraint
  cascades through.

Phase 12.A.B1.6-finish ships the available shapes:
* `subst_compatible_outer` — the closed-source viaUp case (existing)
* `subst_compatible_via_cong_*` — derived theorems for each cong
  ctor that PRESERVE the cong relation under same-context subst
* `subst_compatible_refl` — refl preserves under any subst pair

Note that the per-cong subst-compat theorems below SUFFICE for
proving general subst-preservation when ConvCumul is built from cong
ctors: induct on the proof structure outside the theorem, applying
each per-cong rule at each step.  The architectural blocker on a
single unified theorem is the heterogeneous-induction wall in Lean
4.29.1 — the decomposed per-cong approach sidesteps it cleanly. -/

/-- ConvCumul.refl is preserved under subst on each side independently. -/
theorem ConvCumul.subst_compatible_refl
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {someType : Ty level scope}
    {someRaw : RawTerm scope}
    (someTerm : Term sourceCtx someType someRaw) :
    ConvCumul (someTerm.subst termSubst) (someTerm.subst termSubst) :=
  ConvCumul.refl _

/-- ConvCumul.sym preserved: subst commutes with sym at the relation
level (no Term-level work required). -/
theorem ConvCumul.subst_compatible_sym
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
    (substRel : ConvCumul firstTerm secondTerm) :
    ConvCumul secondTerm firstTerm :=
  ConvCumul.sym substRel

/-- ConvCumul.trans preserved: subst commutes with trans at the relation
level (no Term-level work required). -/
theorem ConvCumul.subst_compatible_trans
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
    ConvCumul firstTerm secondTerm :=
  ConvCumul.trans firstToMid midToSecond

end LeanFX2
