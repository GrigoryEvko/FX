import FX1Poly.Core.GeneratorRedexHead
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.FireRootRedexComplete

/-! # FX1Poly/Core/GeneratorRedexHeadSoundness — operational-inertness soundness (HON-6)

The SOUNDNESS of the operational-liveness classifier `Generator.hasRedexHead` (HON-2,
`GeneratorRedexHead.lean`): a generator the classifier rejects (`hasRedexHead g = false`) yields NO root redex
for ANY cell built on it — universally, not just on smoke witnesses.  This is the honest "reserved ⟹
operationally inert" statement in the kernel's OWN no-root-redex vocabulary: `fireRootRedex` (the computable
root-redex firing used by `reduceOnce`/`normalize`) returns `none`, and the root-redex detector
`hasRootStepSource` (the `!`-half of `isStepNormalFormBool`) returns `false`.

  * `hasRedexHead_false_imp_fireRootRedex_none` — **primary, computational.**  `hasRedexHead g = false →
    fireRootRedex g _ _ = none`.  Both `hasRedexHead` and `fireRootRedex` are parallel `DecidableEq Generator`
    `dite`-chains over the SAME eleven eliminator heads (β: `gen_app`; ι: boolElim/fst/snd/natElim/natRec/
    listElim/optionMatch/eitherMatch/idJ/idStrictRec); `hasRedexHead g = false` says `g` is none of them, so
    `fireRootRedex`'s chain takes all eleven `else` branches to `none`.
  * `hasRedexHead_false_imp_no_root_redex` — **derived, normal-form.**  `hasRootStepSource (mkGen g _ _) =
    false`, obtained from the computational result via the shipped `fireRootRedex_eq_none_imp_hasRootStepSource_false`
    — no re-extraction of the eleven disequalities.
  * `hilbertSpace_no_root_redex` / `lam_no_root_redex` — concrete instances: a genuinely RESERVED head
    (`gen_hilbertSpace`) and a canonical VALUE head (`gen_lam`, operationally live via the static axis, not a
    redex head) both have no root redex.

This is the operational half of the semanticTier soundness (HON-7: `reserved ⟹ untyped AND inert`); the static
half is HON-5 (`reserved ⟹ untyped by all engines`).  Reserved ⟹ `hasRedexHead = false` (since `reserved`
means neither typed nor a redex head), so this theorem applies to every reserved generator.

η-extension heads (`gen_pathLam`/`gen_modIntro`/`gen_glueIntro` and their unwraps) are NOT covered here:
`hasRootStepSource`/`fireRootRedex` are β+ι only by design (the `Step.eta` sibling inductive fires η separately),
so those heads have `hasRedexHead = false` AND no β/ι root redex — consistent with this theorem.  Their η-root
operational liveness is the separate HON-15 axis.

## Zero-axiom

The disequality extraction is `rw [h] at notRedexHead; Bool.noConfusion` (the `gen_X.hasRedexHead = true` facts
are `rfl`-computable, so `Bool.noConfusion` closes `true = false` after the rewrite); the dispatch is
`dsimp only [RawTerm.fireRootRedex]` + eleven `dif_neg`.  No wildcard match, no `Bool.or_eq_false_iff` (which
pulls `propext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **★ Operational-inertness soundness (computational).**  A generator the redex-head classifier rejects fires
no root redex: `fireRootRedex` returns `none` for every cell built on it.  Both `hasRedexHead` and
`fireRootRedex` dispatch over the same eleven eliminator heads, so `hasRedexHead g = false` (i.e. `g` is none of
them) sends `fireRootRedex`'s `dite`-chain to its final `none`. -/
theorem hasRedexHead_false_imp_fireRootRedex_none {scope : Nat} {g : Generator}
    (notRedexHead : g.hasRedexHead = false)
    (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope) :
    RawTerm.fireRootRedex g payload children = none := by
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
  dsimp only [RawTerm.fireRootRedex]
  rw [dif_neg neApp, dif_neg neBoolElim, dif_neg neFst, dif_neg neSnd, dif_neg neNatElim,
    dif_neg neNatRec, dif_neg neListElim, dif_neg neOptionMatch, dif_neg neEitherMatch,
    dif_neg neIdJ, dif_neg neIdStrictRec]

/-- **★ Operational-inertness soundness (normal-form vocabulary).**  A redex-head-rejected generator is no root
redex source: `hasRootStepSource (mkGen g _ _) = false` — exactly the `!`-half of `isStepNormalFormBool`.
Derived from the computational result via the shipped `fireRootRedex_eq_none_imp_hasRootStepSource_false`, so the
eleven disequalities are extracted once. -/
theorem hasRedexHead_false_imp_no_root_redex {scope : Nat} {g : Generator}
    (notRedexHead : g.hasRedexHead = false)
    (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope) :
    RawTerm.hasRootStepSource (.mkGen g payload children) = false :=
  RawTerm.fireRootRedex_eq_none_imp_hasRootStepSource_false
    (hasRedexHead_false_imp_fireRootRedex_none notRedexHead payload children)

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
