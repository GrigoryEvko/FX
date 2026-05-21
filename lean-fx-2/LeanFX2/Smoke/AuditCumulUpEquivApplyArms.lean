import LeanFX2.Term.RenameInjective.InductiveArms

/-!
# Reviewer log: rename-injectivity arms zero-axiom audit.

This file is the running log of `Term.rename_injective_arm_*` arms
shipped on strength-T2 (#1953).  All `#print axioms` below report
"does not depend on any axioms".

## Arms shipped 2026-05-21 (this session, 9 new arms)

J-family (suffices+cases+injection, no cast):
* `idJ` (commit a2747945) — HoTT identity J eliminator.
* `oeqJ` (commit a2747945) — observational equality J.
* `idStrictRec` (commit a2747945) — strict identity recursor.
* `oeqFunext` (commit a975b638) — observational funext intro
  (with `oeqFunextPointwiseType_rename` cast stripping).

Cubical (suffices+cases+injection):
* `pathApp` (commit 2db6ffd1) — path application at carrierType.
* `glueElim` (commit e763f744) — glue elimination at baseType.
* `hcomp` (commit e763f744) — homogeneous cubical composition;
  collides with hcompPath at raw `RawTerm.hcomp`, refutes
  sibling via `Term.noConfusion` on bare ctors.
* `hcompPath` (commit e763f744) — path-shaped hcomp; reverse
  cross-refutation via `Term.noConfusion`.

Equivalence (suffices+cases+injection):
* `equivApp` (commit 2db6ffd1) — equivalence application at
  carrierB.  carrierA existential recovered via
  `Ty.rename_injective`.

## Arms shipped earlier (referenced for completeness)

* `cumulUp` (commit 4e95a608)
* `equivApply` (commit 598fea15)
* `uaToEquiv` (commit ec5291fe)
* `transp` (commit 286f3cdb)
* `appPi` (refuted in `app` arm body via Term.noConfusion
  HEq-aware breakthrough — see `feedback_lean_noconfusion_heq_aware`)

Plus 53 closed/structural arms shipped previously.

## Deferred — concrete Lean blockers

### Cast-on-result wall (3 arms)

`appPi` (as standalone arm), `snd`, `boolElim` — result type is
`subst0 ...` which is NOT structurally injective.  `cases typeEq`
fails with:
```
Dependent elimination failed: Failed to solve equation
  innerCodomain.subst (Subst.singleton ...) =
    codomainType.subst (Subst.singleton ...)
```
Requires HEq-aware Σ-Ty / Π-Ty / boolElim-motive inversion lemma.
The suffices+free-genericType pattern lets `cases genericTerm`
succeed, but the resulting typeEq slot cannot be `cases`'d.

### toNat non-injectivity wall (1 arm)

`universeCode` — `RawTerm.universeCode innerLevel.toNat` forgets
the universe expression structure.  `cases genericTerm` fails:
```
Dependent elimination failed: Failed to solve equation
  innerLevel.toNat = innerLevel✝.toNat
```
See `Foundation/Universe.lean:toNat_not_injective` for proof that
`UniverseLevel.toNat` cannot be reversed.

### Effects.CanPerform Prop wall (1 arm)

`effectPerform` — injection on
`Term.rename effectPerform = Term.rename effectPerform`
produces a heterogeneous Prop equation
`Effects.CanPerform.map _ canPerformA = Effects.CanPerform.map _ canPerformB`
that cannot be discharged without proof irrelevance (propext-free).

### η-family 4-way collision (7 arms)

`equivReflId / funextRefl / equivReflIdAtId / funextReflAtId /
equivIntroHet / uaIntroHet / funextIntroHet` — collide on raw
shapes `RawTerm.equivIntro id id` (4-way) and `RawTerm.lam
(RawTerm.refl _)` (3-way).  Existing `_of_inner` helpers in
`EquivIntro.lean` take HEq-style `childInjective`; the arm
signature has childA-fixed IHs.  Bridging requires either
strengthening the rename_injective driver to thread HEq-style IHs
or per-arm direct-cases proofs (~200-400 LoC each).

## Status: 66 of 78 arms shipped zero-axiom

12 arms deferred due to fundamental dep-elim walls or HEq-style-IH
gaps documented above.
-/

#print axioms LeanFX2.Term.rename_injective_arm_cumulUp
#print axioms LeanFX2.Term.rename_injective_arm_equivApply
#print axioms LeanFX2.Term.rename_injective_arm_uaToEquiv
#print axioms LeanFX2.Term.rename_injective_arm_transp
#print axioms LeanFX2.Term.rename_injective_arm_idJ
#print axioms LeanFX2.Term.rename_injective_arm_oeqJ
#print axioms LeanFX2.Term.rename_injective_arm_idStrictRec
#print axioms LeanFX2.Term.rename_injective_arm_oeqFunext
#print axioms LeanFX2.Term.rename_injective_arm_pathApp
#print axioms LeanFX2.Term.rename_injective_arm_glueElim
#print axioms LeanFX2.Term.rename_injective_arm_hcomp
#print axioms LeanFX2.Term.rename_injective_arm_hcompPath
#print axioms LeanFX2.Term.rename_injective_arm_equivApp
