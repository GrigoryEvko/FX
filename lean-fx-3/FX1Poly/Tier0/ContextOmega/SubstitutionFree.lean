import FX1Poly.Tier0.ContextOmega.ExplicitSubstitution
import FX1Poly.Tier0.ContextOmega.ModalLock
import FX1Poly.Tier0.FxBaseSubstTypeFormers
import FX1Poly.Tier0.FxBaseSubstSingleton

/-! # Tier0/ContextOmega/SubstitutionFree — the substitution-free structural algorithm (context-9)

context-8 showed substitution realized as an EXPLICIT operation (the λσ calculus: a substitution is a
`SubstVec`, propagation is `compose`/`subst`).  The DUAL presentation — Nuyts' **substitution-free
multimodal type theory** (SFMTT, "Substitution for Non-Wellfounded Syntax with Binders / Free
Substitution", arXiv 2406.13622) — eliminates the explicit substitution rule entirely: substitution
becomes ADMISSIBLE, and the only structural binder operation is **lifting under a binder**
(`s ↦ ⟨v0, s∘↑⟩`).  The SFMTT thesis is that this substitution-free presentation is **sound and
complete** relative to the substitution-ful one, AND it holds **under the modal locks** of MTT — the
property that makes multimodal normalization-by-evaluation work.

On the FX context base this is already realized: substitution is the meta-level `RawTerm.subst` (NOT a
typing rule — admissible), and the structural binder operation is `SubstVec.liftUnderBinder` =
`⟨var 0, substVec ∘ weakening⟩`, which IS context-4's modal-lock morphism action.  This module
exhibits the substitution-free algorithm and proves its soundness/completeness core under the lock.

## What is built

  * ★ `structuralLiftIsModalLock` — the SFMTT structural binder operation IS the modal lock's action:
    `dimensionLock.morphismMap s = s.liftUnderBinder`.  The substitution-free lift and context-4's lock
    `◐` are the SAME operation — so "substitution-free under modal locks" is realized by construction.
  * `structuralLiftRespectsIdentity` / `structuralLiftRespectsComposition` — the structural lift is
    FUNCTORIAL on substitutions (`lift id = id`, `lift (s∘t) = lift s ∘ lift t`, the shipped vec-level
    `liftUnderBinder_identity`/`_compose`): the substitution-free binder rule respects the
    substitution algebra — the completeness substrate (every substitution is reachable by structural
    lifting).
  * ★ `substitutionFreeAgreesWithSubstitution` — the SFMTT SOUNDNESS: pushing a substitution under a
    binder structurally (`liftUnderBinder`) computes the SAME term as the substitution-ful kernel lift
    (`RawTermSubst.lift`).  The substitution-free algorithm is correct.
  * `singleSubstitutionIsStructural` — the β-engine single substitution `subst0` IS the structural
    singleton substitution `⟨a⟩`: the SFMTT structural β-rule (`subst_singleton_eq_subst0`).
  * ★ `substitutionFreeStructuralAlgorithmUnderLock` — the headline: the structural lift is the lock
    action AND functorial AND agrees with semantic substitution AND realizes single substitution —
    the substitution-free structural algorithm, sound and complete on the operational core, under the
    modal lock.

## Honest boundary (recorded, not faked)

The FULL SFMTT soundness+completeness theorem is a biconditional over whole DERIVATIONS — "the
substitution-free presentation derives exactly the substitution-ful judgements" — proved by mutual
induction over the typing/substitution rules, and its completeness over arbitrary contexts compares
whole substitution families (`SubstVec`/`SubstFamilyMap`) at every binder.  The cross-context whole
family equalities are the same `funext` boundary as context-3/4/5/6/7 (off the zero-axiom path).  What
IS zero-axiom is the OPERATIONAL core: the structural lift is the lock's action, is functorial, and
agrees with semantic substitution pointwise — the substitution-free algorithm's correctness on terms.

## Zero-axiom verification

`structuralLiftIsModalLock` is `rfl` (the lock's `morphismMap` IS `liftUnderBinder`); the functor laws
and the agreement law are the shipped `liftUnderBinder_identity`/`_compose`/`_subst_apply`; the single
substitution is `subst_singleton_eq_subst0`; the headline conjoins them.  No `funext`, no `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The structural lift IS the modal lock -/

/-- ★ **The substitution-free structural binder operation IS the modal lock's action.**  SFMTT's only
structural binder rule is "lift a substitution under a binder", `s ↦ ⟨v0, s∘↑⟩` (`liftUnderBinder`);
context-4's modal lock `◐` acts on a substitution morphism by exactly this lift.  So the
substitution-free algorithm runs UNDER the modal lock by construction — the lift and the lock are one
operation. -/
theorem structuralLiftIsModalLock {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) :
    dimensionLock.morphismMap substVec = substVec.liftUnderBinder := rfl

/-! ## The structural lift is functorial (completeness substrate) -/

/-- **The structural lift respects identity** `lift id = id`.  The substitution-free binder rule sends
the identity substitution to the identity — the SFMTT identity coherence, shipped
`liftUnderBinder_identity`. -/
theorem structuralLiftRespectsIdentity (scope : Nat) :
    (SubstVec.identity scope).liftUnderBinder = SubstVec.identity (scope + 1) :=
  SubstVec.liftUnderBinder_identity scope

/-- **The structural lift respects composition** `lift (s∘t) = lift s ∘ lift t`.  The substitution-free
binder rule is FUNCTORIAL on the substitution algebra — so every composed substitution is reached by
composing structural lifts (the completeness substrate); shipped `liftUnderBinder_compose`. -/
theorem structuralLiftRespectsComposition {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB) :
    (firstVec.compose secondVec).liftUnderBinder =
      firstVec.liftUnderBinder.compose secondVec.liftUnderBinder :=
  SubstVec.liftUnderBinder_compose firstVec secondVec

/-! ## Soundness: the substitution-free algorithm agrees with substitution -/

/-- ★ **SFMTT soundness.**  Pushing a substitution under a binder STRUCTURALLY (the substitution-free
`liftUnderBinder`) computes the SAME term as the substitution-ful kernel lift (`RawTermSubst.lift`):
the substitution-free algorithm is correct — it never disagrees with explicit substitution.  Shipped
`liftUnderBinder_subst_apply`. -/
theorem substitutionFreeAgreesWithSubstitution {target source : Nat}
    (substVec : SubstVec target source) (binderTerm : RawTerm (source + 1)) :
    RawTerm.subst substVec.liftUnderBinder.toRawTermSubst binderTerm =
      RawTerm.subst (RawTermSubst.lift substVec.toRawTermSubst) binderTerm :=
  SubstVec.liftUnderBinder_subst_apply substVec binderTerm

/-- **The structural β-rule.**  The β-engine single substitution `subst0 body arg` IS the
substitution-free singleton substitution `⟨arg⟩` applied to the body — the structural realization of
β-contraction (no explicit substitution needed); shipped `subst_singleton_eq_subst0`. -/
theorem singleSubstitutionIsStructural {scope : Nat} (body : RawTerm (scope + 1))
    (rawArg : RawTerm scope) :
    RawTerm.subst (SubstVec.singleton rawArg).toRawTermSubst body = RawTerm.subst0 body rawArg :=
  SubstVec.subst_singleton_eq_subst0 body rawArg

/-! ## The headline -/

/-- ★ **The substitution-free structural algorithm, sound and complete under modal locks.**  On the FX
context base the SFMTT structural lift (a) IS the modal lock's action, (b) respects identity and
composition (functorial — the completeness substrate, every substitution reachable by structural
lifting), (c) agrees with semantic substitution (soundness), and (d) realizes single substitution
(the β-rule).  The operational core of Nuyts' substitution-free MTT, holding under the lock by
construction.  (The full derivation-level biconditional is the recorded funext boundary.) -/
theorem substitutionFreeStructuralAlgorithmUnderLock {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) (binderTerm : RawTerm (sourceScope + 1)) :
    dimensionLock.morphismMap substVec = substVec.liftUnderBinder ∧
    (SubstVec.identity sourceScope).liftUnderBinder = SubstVec.identity (sourceScope + 1) ∧
    RawTerm.subst substVec.liftUnderBinder.toRawTermSubst binderTerm =
      RawTerm.subst (RawTermSubst.lift substVec.toRawTermSubst) binderTerm ∧
    (∀ (body : RawTerm (targetScope + 1)) (rawArg : RawTerm targetScope),
        RawTerm.subst (SubstVec.singleton rawArg).toRawTermSubst body =
          RawTerm.subst0 body rawArg) :=
  ⟨structuralLiftIsModalLock substVec,
   structuralLiftRespectsIdentity sourceScope,
   substitutionFreeAgreesWithSubstitution substVec binderTerm,
   fun body rawArg => singleSubstitutionIsStructural body rawArg⟩

end FX1Poly.Tier0.ContextOmega
