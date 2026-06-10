import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Core.CertifiedToPolyCell

/-! # FX1Poly/Typed/TypedCertificationStackingRefuted
    — O-STACK REFUTED: grown typing does NOT factor through the sort-disciplined certifier

The §5.2 tower's p₂ arrow (O-STACK) conjectured `HasTypeDescPi Γ t T → HasCertifiedCellDim0 t`:
every grown-typed subject admits a structural dim-0 certificate, so the typed layer sits ABOVE
the certified layer.  The expected argument — "every typed cell is built from real generators at
table arity/payload/shifts, so `certifyRawCellExact?` accepts" — is TRUE for arity, payload, and
shifts, and FALSE for the table's fourth check: the per-child SORT discipline.

## The root cause: sort-stratified specs vs the unified-syntax engines

`Generator.childSpecs` assigns each child slot a `CellSort` (`.term` or `.type`), and the
certifier's spine walker rejects a child whose ROOT generator's `cellSort` differs from the
slot's (`.wrongChildShape`).  But the typing engines live in UNIFIED syntax where type codes are
first-class terms, so well-typed cells mix the sorts in BOTH directions:

  * `gen_lam`'s domain-annotation slot demands `.term` — yet a typed λ's annotation is usually a
    TYPE CODE: `λ(A : Type@e). A` (the shipped `identityOnUniverse_hasTypeDescPi`) puts the
    `.type`-rooted `universeCodeCell` there.  REJECTED.
  * `gen_piTyCode`'s domain slot demands `.type` — yet a typed Π code over a context variable,
    `Π (x : X). X` with `X` a binder, puts the `.term`-rooted `gen_var` there.  REJECTED
    (probe-verified; not theorem-ized here since it needs an open-context derivation — the λ
    counterexample below already kills the arrow).

Because the mismatch is BIDIRECTIONAL, no one-sided relabeling of the `childSpecs` table fixes
it: a sort-faithful repair needs either sort-JOIN slots ("term-or-type") or a sort-assignment
pass that classifies by TYPING ROLE rather than root generator.  Until then the typed layer sits
BESIDE the sort-disciplined certified layer, not above it.

## What survives (the seam is NOT dead)

The FX0 external-verifier seam is unaffected: `externalVerify_accepts_certified` routes through
`encodeCell` + the sort-AGNOSTIC structural re-checker, which accepts every well-scoped encoding
(even Ω — see `externalVerify_accepts_omega_but_omega_notStronglyNormalizing`).  So the
typed → FX0-cross-checkable arrow HOLDS; it is precisely the typed → `certifyRawCellExact?`
arrow that fails.  All-`.term` typed cells (Church-style λ-terms with VARIABLE annotations,
data values, eliminator spines) also certify fine — the obstruction is exactly sort-mixing.

## What this file ships

  * `identityOnUniverse_notCertified` — the procedural counterexample: the certifier REJECTS
    `λ(A : Type@e). A` (`.wrongChildShape`), for EVERY level and flag, by computation.
  * `identityOnUniverse_noCertifiedCellDim0` — the structural counterexample: no `PolyCell`
    exists over that cell either (the spine's first slot demands sort `.term`; the `gen`
    constructor pins any cell over `universeCodeCell` to sort `.type`).
  * ★ `typedDoesNotFactorThroughCertification` — O-STACK in its exact stated shape, REFUTED:
    the witness is the SHIPPED grown typing `identityOnUniverse_hasTypeDescPi`.

## Zero-axiom verification

The procedural refutation is a `rfl`-computation of the certifier on the concrete cell; the
structural one is `cases` on `HasCertifiedCellDim0`/`PolyCell`/`CertifiedTermSpine` (the
established propext-clean pattern from the `HasCertifiedCellDim0.preservedByIota*` SR arms),
with the head-cell case closed by constructor-sort mismatch.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The certifier REJECTS the typed universe-annotated identity** `λ(A : Type@e). A`, for every
level and flag: the λ's domain-annotation slot demands sort `.term`, but the annotation
`universeCodeCell` is `.type`-rooted — `.wrongChildShape` by computation. -/
theorem identityOnUniverse_notCertified (levelExpr : LevelExpr) (flag : UniverseFlag)
    (certified : Certified (profile := fxProfile)
      (lamCell (universeCodeCell levelExpr flag)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) :
    False := by
  obtain ⟨result, accepted⟩ := certified
  have computed :
      inferRawCellGeneral? (profile := fxProfile) 0
          (RawCell.termBase
            (lamCell (universeCodeCell levelExpr flag)
              (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))
        = Except.error CellCheckRejection.wrongChildShape := rfl
  rw [computed] at accepted
  cases accepted

/-- **A `PolyCell` over a `.termBase` generator cell pins the SORT index to the root generator's
`cellSort`** — the only constructor producing a `.termBase`-shaped raw cell is `gen`, whose
output sort is `generator.cellSort`.  Stated with the sort FREE so dependent elimination
solves the index equations (the equation-motive recipe). -/
theorem _root_.FX1Poly.Core.PolyCell.sortPinnedAtTermBaseGen {profile : PolyProfile}
    {sort : CellSort} {scope : Nat}
    {boundary : CellBoundary profile sort 0 scope}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (cell : PolyCell profile sort 0 scope boundary
      (.termBase (.mkGen generator payload children))) :
    sort = generator.cellSort := by
  cases cell with
  | gen admission payloadEvidence spine => rfl

/-- **No structural dim-0 certificate exists over the typed universe-annotated identity either**:
a `PolyCell` over the λ cell forces (via its spine's first slot) a `PolyCell` of sort `.term`
over `universeCodeCell levelExpr flag`, but the only constructor producing a `.termBase` cell
pins the sort to the root generator's `gen_universeCode.cellSort = .type`. -/
theorem identityOnUniverse_noCertifiedCellDim0 (levelExpr : LevelExpr) (flag : UniverseFlag)
    (certified : HasCertifiedCellDim0 (profile := fxProfile)
      (lamCell (universeCodeCell levelExpr flag)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) :
    False := by
  obtain ⟨sort, cell⟩ := certified
  cases cell with
  | gen admission payloadEvidence spine =>
      cases spine with
      | cons annotationCell restSpine =>
          exact CellSort.noConfusion annotationCell.sortPinnedAtTermBaseGen

/-- **★ O-STACK REFUTED: grown typing does NOT factor through the sort-disciplined structural
certification.**  The polycell.md §5.2 p₂ arrow `HasTypeDescPi Γ t T → HasCertifiedCellDim0 t`
is FALSE — witnessed by the SHIPPED typed derivation `identityOnUniverse_hasTypeDescPi` of
`λ(A : Type@0). A`, whose subject the certifier rejects (`.wrongChildShape`: a `.type`-rooted
annotation in `gen_lam`'s `.term` slot).  The typed layer sits BESIDE the sort-disciplined
certified layer; the surviving seam is the sort-agnostic FX0 external re-checker
(`externalVerify_accepts_certified`). -/
theorem typedDoesNotFactorThroughCertification :
    ¬ (∀ {scope : Nat} (context : TypingContext fxProfile scope)
         (subject classifier : RawTerm scope),
         HasTypeDescPi fxProfile context subject classifier →
         HasCertifiedCellDim0 (profile := fxProfile) subject) :=
  fun stacking =>
    identityOnUniverse_noCertifiedCellDim0 LevelExpr.lzero UniverseFlag.standard
      (stacking TypingContext.empty _ _
        (identityOnUniverse_hasTypeDescPi LevelExpr.lzero UniverseFlag.standard))

/-- Non-vacuity of the CONTRAST: the all-`.term` λ twin with a VARIABLE annotation,
`λ(x : X). x` under one binder, IS certified — the obstruction is exactly sort-mixing, not λ
itself. -/
theorem lamWithVariableAnnotation_certified :
    Certified (profile := fxProfile)
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))) := by
  exact ⟨_, rfl⟩

end FX1Poly.Typed
