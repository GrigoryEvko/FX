import LeanFX2.Term.RenameInjective.InductiveArms

/-!
# Reviewer log: 4 Tier-A unique-raw rename-injectivity arms zero-axiom.

Four Tier-A unique-raw arms shipped 2026-05-21:

* `cumulUp` (commit 4e95a608) — cumulativity wrapper, ~85 LoC.
* `equivApply` (commit 598fea15) — univalence-β application, ~73 LoC.
* `uaToEquiv` (commit ec5291fe) — ua intro at distinct RawTerm shape,
  ~90 LoC.
* `transp` (commit 286f3cdb) — cubical transport across a `Ty.path` of
  universes; 5 raw existentials (mode prop + universe + universeLt HEq +
  sourceType + 2 raw payloads) + 2 typed subterms (typePath, sourceValue)
  with their respective IHs, ~129 LoC.

All four ship via the standard suffices+cases+injection recipe:

1.  Σ' chain captures each ctor's raw existentials including any prop
    equations (`mode = Mode.univalent`).
2.  `cases genericTerm` absorbs outer pinning index into `genericType`
    when the result type is a parametric Ty (e.g. transp's targetType).
3.  `injection renameEq with …` discharges the Σ' chain; the slot
    ordering is empirically per-ctor (implicit args interleave with
    trivial raw equations).
4.  `Ty.rename_injective_under_injective_renaming` and
    `RawTerm.rename_injective_under_injective_renaming` discharge raw
    existential equalities; typed IHs discharge subterm equalities via
    `eq_of_heq`.

57 of 78 arms shipped on strength-T2 (#1953).  Remaining 21 ctors
(appPi/snd/boolElim/idJ/oeqJ/oeqFunext/idStrictRec/pathApp/glueElim/
hcomp/hcompPath/effectPerform/universeCode/equivReflId/funextRefl/
equivReflIdAtId/funextReflAtId/equivIntroHet/equivApp/uaIntroHet/
funextIntroHet) involve cast-on-result walls, dependent-eliminator
existentials, 4-way η collisions, or the toNat non-injectivity wall —
deferred to future sessions using the noConfusion HEq-aware
breakthrough (see `feedback_lean_noconfusion_heq_aware`).
-/

#print axioms LeanFX2.Term.rename_injective_arm_cumulUp
#print axioms LeanFX2.Term.rename_injective_arm_equivApply
#print axioms LeanFX2.Term.rename_injective_arm_uaToEquiv
#print axioms LeanFX2.Term.rename_injective_arm_transp
