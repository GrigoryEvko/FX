import FX1Poly.Core.Equality.Eta.EtaStrengthenEquivariance

/-! # TranspensionAffineContractionEquivariance — the TRANSP-DSL (#1414) make-or-break, machine-checked

#1414 posed the gating question for syntactic transpension: can the
AFFINE / FRESH substitution behaviour of the transpension contraction
`unmer(u. mer[u] a) ↝ a` be carried WITHOUT breaking the generic
iota-template equivariance IOTA-T2 (`interpretTarget` commutes with
subst/rename, `IotaTableEquivariance`)?

**Verdict: GO — and the equivariance ingredient is ALREADY SHIPPED.**

The transpension gel-β contraction drops one FRESH shape binder `u` and
returns the body `a` (which is fresh for `u`).  Structurally this is
`RawTerm.strengthenBy? 1` — the same shape as η-contraction
(`λx. f x ↝ f`).  Three consequences:

  * the reduct needs NO new `ReductTemplate` constructor that could
    break IOTA-T2 — it is a strengthening contraction, living in the
    ETA / strengthening lane, whose equivariance is separate;
  * its PARTIAL-SUBSTITUTION equivariance is the shipped ETA-T2 pair
    `RawTerm.strengthenBy?_subst` / `RawTerm.strengthenBy?_rename`
    (`EtaStrengthenEquivariance`), specialised here to the single shape
    binder (`depth = 1`); the general multi-shape `∮` over `k` shape
    variables is the SAME lemma at `depth = k`;
  * the FRESHNESS FIRING GUARD is exactly the partiality of
    `strengthenBy?` — it returns `none` when `u` genuinely occurs — and
    a successful firing is sound: the contractum re-weakens to the body
    (`weakenBy_strengthenBy?`).

This matches Ceulemans–Nuyts–Devriese SFMTT (arXiv:2406.13622)
precisely: term substitution stays STRUCTURAL and commutes (the
`strengthen` lift/lock discipline), and the modal/shape behaviour is
confined to the firing layer (here the `strengthenBy?` partiality), NOT
to the term-substitution equivariance.  The transpension non-commutation
(Nuyts–Devriese arXiv:2008.08533 §2.1.7) lives in the SHAPE-substitution
layer — a different operation from the term substitution governed here.

So #1414's decision is resolved GO; the build-out (a `gen_transpension`
generator + the gel-β contraction as an eta-style row + per-instance SN)
is TRANSP-1 (#1418).

Zero-axiom; audit-gated in
`FX1PolyAudit/AuditTranspensionAffineContractionEquivariance.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Axis.Syntax (RawRenaming)

/-- ★ **TRANSP-DSL GO (subst half)** — the transpension/gel-β affine
contraction (`strengthenBy? 1`, drop one fresh shape binder) commutes
with term substitution: a single specialisation of the shipped ETA-T2
`strengthenBy?_subst` at `depth = 1`.  IOTA-T2 is untouched — the affine
contraction rides the strengthening lane's own equivariance. -/
theorem transpensionAffineContraction_subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (shapeBinderBody : RawTerm (sourceScope + 1))
    (contractum : RawTerm sourceScope)
    (fires : RawTerm.strengthenBy? 1 shapeBinderBody = some contractum) :
    RawTerm.strengthenBy? 1
        (RawTerm.subst (iterateLiftRaw someSubstitution 1) shapeBinderBody)
      = some (RawTerm.subst someSubstitution contractum) :=
  RawTerm.strengthenBy?_subst someSubstitution 1 shapeBinderBody contractum fires

/-- ★ **TRANSP-DSL GO (rename half)** — the affine contraction commutes
with renaming, via the shipped ETA-T2 `strengthenBy?_rename`. -/
theorem transpensionAffineContraction_rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (shapeBinderBody : RawTerm (sourceScope + 1))
    (contractum : RawTerm sourceScope)
    (fires : RawTerm.strengthenBy? 1 shapeBinderBody = some contractum) :
    RawTerm.strengthenBy? 1
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) shapeBinderBody)
      = some (RawTerm.rename rawRenaming contractum) :=
  RawTerm.strengthenBy?_rename rawRenaming 1 shapeBinderBody contractum fires

/-- The FRESHNESS FIRING GUARD is sound: when the affine contraction
fires, the shape binder genuinely did not use its variable — the
contractum re-weakens to the body.  So the decidable `strengthenBy?`
partiality IS the (sound) freshness side-condition SFMTT prescribes. -/
theorem transpensionAffineContraction_firingGuardSound {scope : Nat}
    (shapeBinderBody : RawTerm (scope + 1)) (contractum : RawTerm scope)
    (fires : RawTerm.strengthenBy? 1 shapeBinderBody = some contractum) :
    RawTerm.weakenBy 1 contractum = shapeBinderBody :=
  RawTerm.weakenBy_strengthenBy? 1 shapeBinderBody contractum fires

end FX1Poly.Core
