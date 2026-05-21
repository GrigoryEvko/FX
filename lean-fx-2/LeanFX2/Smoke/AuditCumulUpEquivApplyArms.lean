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

## Arms shipped 2026-05-21 (cast-on-result wall cracked, 3 new arms)

The cast-on-result wall (subst0 on output type, non-injective
structurally) is broken via `Term.noConfusion`'s HEq-aware
decomposition: it provides existential Ty HEqs (renamed) +
child HEqs directly from `HEq (Term.X args) (Term.X args')` at
potentially-different outer types, given the outer-type HEq as
input (= `congrArg (Ty.rename · rho) typeEqB` after
`Ty.subst0_rename_commute` reduction).

* `snd` — Σ-second-projection at `secondType.subst0 firstType
  (RawTerm.fst pairRaw)`.  Uses `Term.snd_raw_inv` +
  `Term.rename_heq_of_eq` + cast-stripping via
  `termRenameInjectiveCastHEq` + `Term.noConfusion`
  HEq-extraction.
* `boolElim` — bool eliminator at `motiveType.subst0 Ty.bool
  scrutineeRaw`.  Same pattern as `snd` plus per-child cast
  stripping for thenA/elseA at boolTrue/boolFalse subst0.
* `appPi` — dependent-Π application at `codomainType.subst0
  domainType argumentRaw`.  Sibling `app`-raw branch refutes
  via `Term.noConfusion` (Term.appPi ≠ Term.app), main branch
  uses HEq-aware decomposition.

## Arms shipped earlier (referenced for completeness)

* `cumulUp` (commit 4e95a608)
* `equivApply` (commit 598fea15)
* `uaToEquiv` (commit ec5291fe)
* `transp` (commit 286f3cdb)
* `appPi` (refuted in `app` arm body via Term.noConfusion
  HEq-aware breakthrough — see `feedback_lean_noconfusion_heq_aware`)

Plus 53 closed/structural arms shipped previously.

## Walled (verified by counterexample) — `Smoke/AuditRenameInjectivityWalls`

The remaining 9 of 78 arms are KERNEL-DESIGN walls, not proof-
technique gaps.  Constructive counterexamples in
`Smoke/AuditRenameInjectivityWalls.lean` show the strict
propositional equality form of `rename_injective_arm_*` is FALSE
on these ctors — distinct typed `Term` inhabitants exist at the
same outer `Ty` and same raw, and Lean 4's freely-generated
inductives make distinct ctors propositionally distinct.

### toNat-collapse wall (1 arm)

`universeCode` — `UniverseLevel.toNat` is non-injective
(`Foundation/Universe.lean:toNat_not_injective`); the raw
`RawTerm.universeCode innerLevel.toNat` stores ONLY the
collapsed Nat, so `Term.universeCode (max 0 0) ...` and
`Term.universeCode (imax 0 0) ...` inhabit the same outer
type `Ty.universe outerLevel _` and same raw
`RawTerm.universeCode 0`, distinct typed terms.

### Effect-row free-parameter wall (1 arm)

`effectPerform` — `effectRow` appears in neither the outer
type `Ty.effect resultCarrier effectTag` nor the raw
`RawTerm.effectPerform op arg`.  A read operation is permitted
by `[read]` (via `CanPerform.direct`) AND by `[write]` (via
`CanPerform.readViaWrite`), yielding two distinct typed
`Term.effectPerform` inhabitants at the same outer type + raw.

### η-family multi-inhabitancy wall (7 arms)

`equivReflId / funextRefl / equivReflIdAtId / funextReflAtId /
equivIntroHet / uaIntroHet / funextIntroHet` — kernel admits
distinct typed inhabitants at the same outer-Ty + raw shape.
`Smoke/AuditRenameInjectivityWalls.lean` constructs
`Term.equivReflId carrier` and `Term.equivIntroHet (lam (var 0))
(lam (var 0)) leftInv rightInv` BOTH at the same outer type
`Ty.equiv carrier carrier` and same raw
`RawTerm.equivIntro (lam (var 0)) (lam (var 0))`.

## Status: 69 of 78 arms shipped zero-axiom

This is the MAXIMUM achievable under the current kernel; 78/78
is impossible without one of: (a) restating T2 with HEq + Conv,
(b) refactoring the kernel to fold specialized ctors into
definitions over heterogeneous ones, or (c) routing the 9
walled ctors through a separate multi-inhabitancy-aware lemma.
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
#print axioms LeanFX2.Term.rename_injective_arm_snd
#print axioms LeanFX2.Term.rename_injective_arm_boolElim
#print axioms LeanFX2.Term.rename_injective_arm_appPi
