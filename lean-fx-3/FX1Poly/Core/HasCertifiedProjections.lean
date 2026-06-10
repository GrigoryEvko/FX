import FX1Poly.Core.HasCertifiedComposition
import FX1Poly.Core.CertifiedTermSpineProjections

/-! # Foundation/PolyCell/Core/HasCertifiedProjections
   — child-cell projections from compound certifications

Sibling to the compositional intros (`HasCertifiedComposition.lean`)
and the preservations (`CompoundRenamePreservation` /
`CompoundSubstPreservation` / `BetaRedexLeafPreservation` /
`BetaRedexCompoundPreservation`): the EXTRACTION half — given a
`HasCertifiedCellDim0` of a compound shape, project to
certifications of its children.

## Contents

For each compound generator, projections to its children's certs:

  * Binary (app / pair / listCons): two projections each
    (function/argument, first/second, head/tail).
  * Unary, no binders (natSucc / optionSome / eitherInl /
    eitherInr / refl): one projection each.
  * Unary, 1 binder (lam): one projection to the body's cert at
    `scope + 1`.

Total: **12 projections**, mirroring the 9 compositional intros.

## Why these matter for SR-beta

Beta redex `app (lam body) arg → subst0 body arg`.  Reading the
chain from a cert of the source:

  1. `cert : HasCertifiedCellDim0 (app (lam body) arg)`
  2. `cert.app_argument_projection` →
     `HasCertifiedCellDim0 arg`
  3. `cert.app_function_projection` →
     `HasCertifiedCellDim0 (lam body)`
  4. `(3).lam_body_projection` →
     `HasCertifiedCellDim0 body` (at scope + 1)
  5. Combine via the compositional rebuild from
     `BetaRedexCompoundPreservation` to produce
     `HasCertifiedCellDim0 (subst0 body arg)` for body shapes
     where the structural induction lands.

This file provides steps 2-4 (the EXTRACTION chain); step 5 is
the compositional rebuild in `BetaRedexCompoundPreservation`.

## Proof pattern

Each projection follows the same template (zero-axiom):

  ```
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩  -- or spine.tail.headAtDim0 rfl
  ```

Key insight: with FREE sort (from the existential destructure),
`cases` on the cell at dim 0 cleanly inverts to the `.gen` arm.
Index unification on the raw `.termBase (.mkGen .gen_X () ...)`
constrains `generator = .gen_X` and exposes the spine over the
specific child shape.

## Zero-axiom verification

Each projection in this file is propext-free under the same recipe
and is audit-gated.
-/

namespace FX1Poly.Core

/-! ## Section 1 — Binary compound projections (app / pair / listCons) -/

/-- **Projection: `gen_app` → function child's cert.**

From `HasCertifiedCellDim0 (.gen_app () [func, arg])`, extract
`HasCertifiedCellDim0 func`. -/
theorem HasCertifiedCellDim0.app_function_projection
    {profile : PolyProfile} {scope : Nat}
    (functionTerm argumentTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_app ()
                (.childCons functionTerm
                  (.childCons argumentTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) functionTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_app` → argument child's cert.**

From `HasCertifiedCellDim0 (.gen_app () [func, arg])`, extract
`HasCertifiedCellDim0 arg` via spine tail. -/
theorem HasCertifiedCellDim0.app_argument_projection
    {profile : PolyProfile} {scope : Nat}
    (functionTerm argumentTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_app ()
                (.childCons functionTerm
                  (.childCons argumentTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) argumentTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_pair` → first child's cert.** -/
theorem HasCertifiedCellDim0.pair_first_projection
    {profile : PolyProfile} {scope : Nat}
    (firstTerm secondTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_pair ()
                (.childCons firstTerm
                  (.childCons secondTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) firstTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_pair` → second child's cert.** -/
theorem HasCertifiedCellDim0.pair_second_projection
    {profile : PolyProfile} {scope : Nat}
    (firstTerm secondTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_pair ()
                (.childCons firstTerm
                  (.childCons secondTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) secondTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_listCons` → head child's cert.** -/
theorem HasCertifiedCellDim0.listCons_head_projection
    {profile : PolyProfile} {scope : Nat}
    (headTerm tailTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_listCons ()
                (.childCons headTerm
                  (.childCons tailTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) headTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_listCons` → tail child's cert.** -/
theorem HasCertifiedCellDim0.listCons_tail_projection
    {profile : PolyProfile} {scope : Nat}
    (headTerm tailTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_listCons ()
                (.childCons headTerm
                  (.childCons tailTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) tailTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-! ## Section 2 — Unary compound projections (no binders) -/

/-- **Projection: `gen_natSucc` → predecessor child's cert.** -/
theorem HasCertifiedCellDim0.natSucc_predecessor_projection
    {profile : PolyProfile} {scope : Nat}
    (predecessorTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natSucc ()
                (.childCons predecessorTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) predecessorTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_optionSome` → wrapped child's cert.** -/
theorem HasCertifiedCellDim0.optionSome_wrapped_projection
    {profile : PolyProfile} {scope : Nat}
    (wrappedTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_optionSome ()
                (.childCons wrappedTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) wrappedTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_eitherInl` → wrapped child's cert.** -/
theorem HasCertifiedCellDim0.eitherInl_wrapped_projection
    {profile : PolyProfile} {scope : Nat}
    (wrappedTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_eitherInl ()
                (.childCons wrappedTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) wrappedTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_eitherInr` → wrapped child's cert.** -/
theorem HasCertifiedCellDim0.eitherInr_wrapped_projection
    {profile : PolyProfile} {scope : Nat}
    (wrappedTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_eitherInr ()
                (.childCons wrappedTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) wrappedTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_refl` → witness child's cert.** -/
theorem HasCertifiedCellDim0.refl_witness_projection
    {profile : PolyProfile} {scope : Nat}
    (witnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_refl ()
                (.childCons witnessTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) witnessTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-! ## Section 3 — Binder projection (lam) -/

/-- **Projection: `gen_lam` → body child's cert at scope + 1.**

BINDER CASE.  `gen_lam` now carries two children (binderShifts
`[0,1]`): a domain annotation at the parent scope followed by
the body under one binder.  The body lives at `scope + 1`
because lam's body child has scopeShift = 1.  After peeling the
domain head with `tail`, the spine's `headAtDim0` returns a
`PolyCell ... 0 (parentScope + 1) ... (.termBase body)`, which
wraps as `HasCertifiedCellDim0 body` at scope+1. -/
theorem HasCertifiedCellDim0.lam_body_projection
    {profile : PolyProfile} {scope : Nat}
    (domainAnn : RawTerm scope)
    (bodyTerm : RawTerm (scope + 1))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_lam ()
                (.childCons domainAnn
                  (.childCons bodyTerm .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) bodyTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

end FX1Poly.Core
