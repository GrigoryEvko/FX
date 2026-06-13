import FX1Poly.Core.GeneratorRedexHead
import FX1Poly.Core.RawTermNF

/-! # FX1Poly/Core/GeneratorRedexHeadSoundness — operational-inertness soundness (HON-6)

The SOUNDNESS of the operational-liveness classifier `Generator.hasRedexHead` (HON-2,
`GeneratorRedexHead.lean`): a generator the classifier rejects (`hasRedexHead g = false`) yields NO root redex
for ANY cell built on it — universally, not just on smoke witnesses.  This is the honest "reserved ⟹
operationally inert" statement in the kernel's OWN no-root-redex vocabulary: the root-redex detector
`hasRootStepSource` (the `!`-half of `isStepNormalFormBool`) returns `false`.

  * `hasRedexHead_false_imp_no_root_redex` — **the soundness statement, direct.**  `hasRedexHead g = false →
    hasRootStepSource (mkGen g _ _) = false`.  Both `hasRedexHead` and `hasRootStepSource` are parallel
    `DecidableEq Generator` `dite`-chains over the SAME eleven eliminator heads (β: `gen_app`;
    ι: boolElim/fst/snd/natElim/natRec/listElim/optionMatch/eitherMatch/idJ/idStrictRec);
    `hasRedexHead g = false` says `g` is none of them, so `hasRootStepSource`'s chain takes all eleven
    `else` branches to `false`.  (Before the IOTA-T11 reducer retirement this was derived through the
    bespoke `fireRootRedex` firing function; the per-iota firing left the kernel, so the proof now
    targets the detector directly — same eleven disequalities, same `dif_neg` dispatch.)
  * `hilbertSpace_no_root_redex` / `lam_no_root_redex` — concrete instances: a genuinely RESERVED head
    (`gen_hilbertSpace`) and a canonical VALUE head (`gen_lam`, operationally live via the static axis, not a
    redex head) both have no root redex.

This is the operational half of the semanticTier soundness (HON-7: `reserved ⟹ untyped AND inert`); the static
half is HON-5 (`reserved ⟹ untyped by all engines`).  Reserved ⟹ `hasRedexHead = false` (since `reserved`
means neither typed nor a redex head), so this theorem applies to every reserved generator.

η-extension heads (`gen_pathLam`/`gen_modIntro`/`gen_glueIntro` and their unwraps) are NOT covered here:
`hasRootStepSource` is β+ι only by design (the table eta tier fires η separately), so those heads have
`hasRedexHead = false` AND no β/ι root redex — consistent with this theorem.  Their η-root operational
liveness is the separate HON-15 axis.

## Zero-axiom

The disequality extraction is `rw [h] at notRedexHead; Bool.noConfusion` (the `gen_X.hasRedexHead = true` facts
are `rfl`-computable, so `Bool.noConfusion` closes `true = false` after the rewrite); the dispatch is
`dsimp only [RawTerm.hasRootStepSource]` + eleven `dif_neg`.  No wildcard match, no `Bool.or_eq_false_iff` (which
pulls `propext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- Every canonical-table row's eliminator head is a redex head — the
row-by-row `rfl` certificate aligning the table with the honesty
classifier. -/
theorem canonicalRowElimHead_hasRedexHead {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable) :
    rule.elimGenerator.hasRedexHead = true := by
  cases isRow with
  | head => rfl
  | tail _ isRow => cases isRow with
    | head => rfl
    | tail _ isRow => cases isRow with
      | head => rfl
      | tail _ isRow => cases isRow with
        | head => rfl
        | tail _ isRow => cases isRow with
          | head => rfl
          | tail _ isRow => cases isRow with
            | head => rfl
            | tail _ isRow => cases isRow with
              | head => rfl
              | tail _ isRow => cases isRow with
                | head => rfl
                | tail _ isRow => cases isRow with
                  | head => rfl
                  | tail _ isRow => cases isRow with
                    | head => rfl
                    | tail _ isRow => cases isRow with
                      | head => rfl
                      | tail _ isRow => cases isRow with
                        | head => rfl
                        | tail _ isRow => cases isRow with
                          | head => rfl
                          | tail _ isRow => cases isRow with
                            | head => rfl
                            | tail _ isRow => cases isRow with
                              | head => rfl
                              | tail _ isRow => cases isRow with
                                | head => rfl
                                | tail _ isRow => cases isRow with
                                  | head => rfl
                                  | tail _ isRow => cases isRow with
                                    | head => rfl
                                    | tail _ isRow => cases isRow with
                                      | head => rfl
                                      | tail _ isRow => cases isRow with
                                        | head => rfl
                                        | tail _ isRow => cases isRow with
                                          | head => rfl
                                          | tail _ isRow => cases isRow

/-- **★ Operational-inertness soundness.**  A redex-head-rejected generator is no root redex source:
`hasRootStepSource (mkGen g _ _) = false` — exactly the `!`-half of `isStepNormalFormBool`.
`hasRedexHead g = false` rejects every eliminator head of the canonical table, so the generic table
walk (`fireTableRedexOver`) misses at every row and returns `none`. -/
theorem hasRedexHead_false_imp_no_root_redex {scope : Nat} {g : Generator}
    (notRedexHead : g.hasRedexHead = false)
    (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope) :
    RawTerm.hasRootStepSource (.mkGen g payload children) = false := by
  have neHead : ∀ headGenerator : Generator,
      g.hasRedexHead = false → g = headGenerator →
      headGenerator.hasRedexHead = true → False := by
    intro headGenerator notHead headEq isHead
    rw [headEq, isHead] at notHead
    exact Bool.noConfusion notHead
  have walkMisses : ∀ rows : List IotaRuleDesc,
      (∀ rule, rule ∈ rows → rule ∈ iotaRuleTable) →
      fireTableRedexOver rows g payload children = none := by
    intro rows
    induction rows with
    | nil => intro _; rfl
    | cons rule restRows restMisses =>
        intro rowsAreCanonical
        dsimp only [fireTableRedexOver]
        have headFireMisses : rule.fireAtRoot? g payload children = none := by
          dsimp only [IotaRuleDesc.fireAtRoot?]
          have notElimHead : g ≠ rule.elimGenerator := by
            intro headEq
            have isCanonical : rule ∈ iotaRuleTable :=
              rowsAreCanonical rule (.head _)
            have elimHeadIsRedexHead : rule.elimGenerator.hasRedexHead = true :=
              canonicalRowElimHead_hasRedexHead isCanonical
            exact neHead rule.elimGenerator notRedexHead headEq
              elimHeadIsRedexHead
          rw [dif_neg notElimHead]
        rw [headFireMisses]
        exact restMisses
          (fun innerRule isInner => rowsAreCanonical innerRule (.tail _ isInner))
  dsimp only [RawTerm.hasRootStepSource]
  rw [walkMisses iotaRuleTable (fun _ isRow => isRow)]
  rfl

/-- A genuinely RESERVED head has no root redex (`gen_hilbertSpace`: neither typed nor a redex head). -/
theorem hilbertSpace_no_root_redex {scope : Nat}
    (payload : Generator.gen_hilbertSpace.payload scope)
    (children : RawTermChildren Generator.gen_hilbertSpace.binderShifts scope) :
    RawTerm.hasRootStepSource (.mkGen .gen_hilbertSpace payload children) = false :=
  hasRedexHead_false_imp_no_root_redex rfl payload children

/-- A canonical VALUE head has no root redex (`gen_lam`: operationally live as a value via the static axis, but
not itself a redex head — `app(lam, _)` reduces, headed by `gen_app`, not `lam`). -/
theorem lam_no_root_redex {scope : Nat}
    (payload : Generator.gen_lam.payload scope)
    (children : RawTermChildren Generator.gen_lam.binderShifts scope) :
    RawTerm.hasRootStepSource (.mkGen .gen_lam payload children) = false :=
  hasRedexHead_false_imp_no_root_redex rfl payload children

end FX1Poly.Core
