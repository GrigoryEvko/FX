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

/-- **★ Operational-inertness soundness.**  A redex-head-rejected generator is no root redex source:
`hasRootStepSource (mkGen g _ _) = false` — exactly the `!`-half of `isStepNormalFormBool`.  Both
`hasRedexHead` and `hasRootStepSource` dispatch over the same eleven eliminator heads, so
`hasRedexHead g = false` (i.e. `g` is none of them) sends `hasRootStepSource`'s `dite`-chain to its
final `false`. -/
theorem hasRedexHead_false_imp_no_root_redex {scope : Nat} {g : Generator}
    (notRedexHead : g.hasRedexHead = false)
    (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope) :
    RawTerm.hasRootStepSource (.mkGen g payload children) = false := by
  have neApp : g ≠ .gen_app := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neBoolElim : g ≠ .gen_boolElim := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neFst : g ≠ .gen_fst := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neSnd : g ≠ .gen_snd := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neNatElim : g ≠ .gen_natElim := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neNatRec : g ≠ .gen_natRec := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neListElim : g ≠ .gen_listElim := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neOptionMatch : g ≠ .gen_optionMatch := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neEitherMatch : g ≠ .gen_eitherMatch := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neIdJ : g ≠ .gen_idJ := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  have neIdStrictRec : g ≠ .gen_idStrictRec := by
    intro h; rw [h] at notRedexHead; exact Bool.noConfusion notRedexHead
  dsimp only [RawTerm.hasRootStepSource]
  rw [dif_neg neApp, dif_neg neBoolElim, dif_neg neFst, dif_neg neSnd, dif_neg neNatElim,
    dif_neg neNatRec, dif_neg neListElim, dif_neg neOptionMatch, dif_neg neEitherMatch,
    dif_neg neIdJ, dif_neg neIdStrictRec]

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
