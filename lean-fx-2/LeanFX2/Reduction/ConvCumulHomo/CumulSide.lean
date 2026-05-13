import LeanFX2.Reduction.ConvCumulHomo.BentonHeadlines

/-! # LeanFX2.Reduction.ConvCumulHomo.CumulSide

ConvCumul-output Pattern 2 BHKM headlines (compose `ConvCumulHomo`'s
recursive headlines with `toCumul`) PLUS the complementary `viaUp`
case treated separately at outer-side-only substitution / renaming.

* `fromCumul_refl` — refl-built `ConvCumul` lifts to `ConvCumulHomo`.
* `ConvCumul.{rename,subst}_compatible_homo_benton` — homogeneous-ctx
  ConvCumulHomo lifts via `toCumul`.
* `ConvCumul.{rename,subst}_compatible_viaUp` — cross-context cumul
  promotion under outer-side-only substitution / renaming (general
  arbitrary `scopeLow` per Phase 12.A.B1.5).

A unified `ConvCumul a b → ConvCumul (a.subst σ) (b.subst σ)` is
ill-typed for viaUp; the two complementary theorems above cover all
cases at the correct typing.

## Root status

Layer 3 conv-cumul homogeneous helper. -/

namespace LeanFX2


/-! # Bridge: ConvCumul → ConvCumulHomo for the homogeneous fragment

While `ConvCumul → ConvCumulHomo` is NOT generally derivable (the
viaUp ctor on ConvCumul has no analog in ConvCumulHomo), we CAN
derive it for the per-ctor cong cases by structural inversion.

The viaUp case is genuinely separate: it's the cross-context
cumul-promotion ctor, handled by per-arm helpers in
`CumulSubstCompat.lean` (`subst_compatible_outer` etc.).

For homogeneous-context input (firstCtx = secondCtx, firstType =
secondType, etc.), every ConvCumul ctor — INCLUDING viaUp — can
be analyzed.  The viaUp case becomes degenerate: when `firstCtx =
ctxLow` AND `firstCtx = ctxHigh` AND `lowerLevel = higherLevel`,
viaUp's source and target coincide; then the relation collapses
to `ConvCumulHomo.refl`.

Below we provide the per-shape cong inversions that return
`ConvCumulHomo` results — these compose with the recursive
headlines `rename_compatible_benton` and `subst_compatible_benton`
to give callers a direct path from any ConvCumul-derived cong
witness to the headline output.
-/

/-- Lift: every refl-built `ConvCumul` is `ConvCumulHomo.refl`. -/
theorem ConvCumulHomo.fromCumul_refl
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumulHomo someTerm someTerm :=
  ConvCumulHomo.refl someTerm

/-! # ConvCumul-side BHKM headlines (rename + subst)

These compose `ConvCumulHomo`'s recursive headlines with `toCumul`
to give a `ConvCumul`-output theorem.  Callers operating on
`ConvCumul` (full relation, including viaUp) can use these when
their input is a `ConvCumulHomo`-derivable shape — i.e., any
homogeneous-ctx cong-built relation.

The viaUp case (cross-context cumul promotion) is genuinely not in
the homogeneous fragment; it's handled separately by the per-arm
`subst_compatible_outer` / `rename_compatible_outer` helpers in
`CumulSubstCompat.lean`, which produce `ConvCumul` directly via
`Conv.cumul_subst_outer`. -/

/-- **Pattern 2 rename headline at ConvCumul output**: any
homogeneous-ctx ConvCumulHomo input lifts via toCumul. -/
theorem ConvCumul.rename_compatible_homo_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumul (firstTerm.rename termRenaming) (secondTerm.rename termRenaming) :=
  (cumulRel.rename_compatible_benton termRenaming).toCumul

/-- **Pattern 2 subst headline at ConvCumul output**: any
homogeneous-ctx ConvCumulHomo input lifts via toCumul. -/
theorem ConvCumul.subst_compatible_homo_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumul (firstTerm.subst termSubst) (secondTerm.subst termSubst) :=
  (cumulRel.subst_compatible_benton termSubst).toCumul

/-! # The viaUp case — cross-context cumul promotion

`ConvCumul.viaUp` is the cross-context ctor that defeats homogeneous
induction.  Its two endpoints live at INDEPENDENT scopes (`scopeLow`
vs outer `scope`) and INDEPENDENT levels (`lowerLevel + 1` vs
`higherLevel + 1`).  A "`ConvCumul a b → ConvCumul (a.subst σ)
(b.subst σ)`" theorem is genuinely ill-typed for viaUp because a
single σ at outer scope cannot apply to lowerTerm at scopeLow.

The CORRECT framing for viaUp under substitution: applying σ only
to the OUTER side preserves the relation, because:
1. `(Term.cumulUp ... lowerTerm).subst σ = Term.cumulUp ... lowerTerm`
   reconstructed at the new target scope (lowerTerm preserved verbatim
   per `Term/Subst.lean`'s cumulUp arm).
2. `ConvCumul.viaUp` reapplies on the substituted shape.

Below: the GENERAL version (arbitrary scopeLow per Phase 12.A.B1.5)
of subst preservation for viaUp.  Existing `Conv.cumul_subst_outer`
in `Reduction/Cumul.lean` covers the closed-source `scopeLow = 0`
case; this generalizes to arbitrary `scopeLow`.

Same shape applies to `Term.rename`: the cumulUp arm preserves
`lowerTerm` verbatim, and `ConvCumul.viaUp` witnesses. -/

/-- **Subst preservation through viaUp at arbitrary scopeLow**.
Phase 12.A.B1.5 decoupled `scopeLow` from outer `scope`; this is
the general statement.  Substituting the outer side of a `viaUp`
witness produces a new `viaUp` at the substituted target. -/
theorem ConvCumul.subst_compatible_viaUp
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma) :
    ConvCumul (Term.subst termSubst typeCode)
              (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  -- Phase CUMUL-2.6 Design D: Term.subst's cumulUp arm recurses on
  -- typeCode.  The output is `Term.cumulUp ... (Term.subst typeCode)`,
  -- so ConvCumul.viaUp witnesses on the substituted typeCode directly.
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh (Term.subst termSubst typeCode)

/-- **Rename preservation through viaUp at arbitrary scopeLow**.
Mirror of `subst_compatible_viaUp` for the rename direction.
Renaming the outer side preserves the relation. -/
theorem ConvCumul.rename_compatible_viaUp
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (rho : RawRenaming scope targetScope)
    (termRenaming : TermRenaming context targetContext rho) :
    ConvCumul (Term.rename termRenaming typeCode)
              (Term.rename termRenaming
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  -- Phase CUMUL-2.6 Design D: Term.rename's cumulUp arm recurses on
  -- typeCode.  Same shape as subst case.
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh (Term.rename termRenaming typeCode)

end LeanFX2
