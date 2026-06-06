import FX1Poly.Core.RedexExtraction

/-! # FX1Poly/Core/RootStepDispatch
    — the root-redex dispatch: `hasRootStepSource source = true → ∃ target, Step source target`

`RedexExtraction` ships one productive brick per root-redex shape (`hasXxxRoot children = true → ∃ target,
Step (mkGen gen_Xxx () children) target`).  This file assembles them into the single dispatch: whenever the
boolean root-redex detector `RawTerm.hasRootStepSource` fires, the term genuinely takes a `Step`, and the proof
PRODUCES the reduct.  This is the converse of `RawTerm.isStepNormalForm`'s root half and the missing ingredient
for weak normalization (the `Acc StepSuccessor` descent extracts an actual reduct at a non-normal term),
feeding raw decidable conversion and the WHNF migration.

The proof mirrors `hasRootStepSource`'s own definition: a chain of `dite generator = gen_Xxx`.  After reducing
the definition (`dsimp only [hasRootStepSource]`) the dependent-if chain is peeled one generator at a time
(`split at rootSource`); each true branch `subst`s the generator equality (so `castToGenerator children rfl`
reduces to `children` by the `Eq.rec` iota rule) and applies that generator's brick; the final else is the
`false = true` contradiction.

The eleven-deep dependent case split is elaboration-heavy (the `subst` rewrites the payload/children dependent
types at each level), so this single declaration carries a raised `maxHeartbeats`.  It is isolated in its own
file so the rest of the kernel build does not pay that cost.

## Zero-axiom verification

A `dsimp`-reduced `split`/`subst`/brick chain over the eleven redex generators plus a `by decide` on the
`false = true` else.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

set_option maxHeartbeats 1000000 in
/-- **Root-redex dispatch.**  If `RawTerm.hasRootStepSource` recognizes `source` as a root redex, `source`
takes a `Step` — produced by dispatching to the matching per-redex brick (beta / pair-projection / the
inductive-eliminator iotas).  The productive companion of the root half of structural normality. -/
theorem hasRootStepSource_exists_step {scope : Nat} {source : RawTerm scope}
    (rootSource : RawTerm.hasRootStepSource source = true) :
    ∃ target : RawTerm scope, Step source target := by
  match source with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.hasRootStepSource] at rootSource
      split at rootSource
      · next h => subst h; exact hasAppBetaRoot_exists_step _ rootSource
      · split at rootSource
        · next h => subst h; exact hasBoolElimIotaRoot_exists_step _ rootSource
        · split at rootSource
          · next h => subst h; exact hasPairProjectionIotaRoot_exists_step_fst _ rootSource
          · split at rootSource
            · next h => subst h; exact hasPairProjectionIotaRoot_exists_step_snd _ rootSource
            · split at rootSource
              · next h => subst h; exact hasNatElimIotaRoot_exists_step_natElim _ rootSource
              · split at rootSource
                · next h => subst h; exact hasNatElimIotaRoot_exists_step_natRec _ rootSource
                · split at rootSource
                  · next h => subst h; exact hasListElimIotaRoot_exists_step _ rootSource
                  · split at rootSource
                    · next h => subst h; exact hasOptionMatchIotaRoot_exists_step _ rootSource
                    · split at rootSource
                      · next h => subst h; exact hasEitherMatchIotaRoot_exists_step _ rootSource
                      · split at rootSource
                        · next h => subst h; exact hasIdElimIotaRoot_exists_step_idJ _ rootSource
                        · split at rootSource
                          · next h =>
                              subst h
                              exact hasIdElimIotaRoot_exists_step_idStrictRec _ rootSource
                          · exact absurd rootSource (by decide)

end FX1Poly.Core
