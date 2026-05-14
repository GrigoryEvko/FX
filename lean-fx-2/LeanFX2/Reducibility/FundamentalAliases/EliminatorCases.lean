import LeanFX2.Reducibility.FundamentalAliases.DirectCases

/-! # LeanFX2.Reducibility.FundamentalAliases.EliminatorCases

Direct eliminator-form endpoints for strong normalization —
eliminator closures of SN witnesses (app / fst / snd / boolElim /
natElim / listElim / optionMatch / eitherMatch / idJ / oeqJ /
etc.).

## Root status

Layer 3 metatheory leaf.  Final slice of FundamentalAliases. -/

namespace LeanFX2



/-! ## Direct eliminator-form SN endpoints -/

/-- Direct SN case for boolean elimination. -/
theorem Term.boolElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue)
        thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse)
        elseRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (thenIsSN : Term.isStronglyNormalizing thenBranch)
    (elseIsSN : Term.isStronglyNormalizing elseBranch) :
    Term.isStronglyNormalizing
      (Term.boolElim scrutinee thenBranch elseBranch) :=
  RawTerm.boolElim_isStronglyNormalizing thenIsSN elseIsSN scrutineeIsSN

/-- Direct SN case for identity elimination. -/
theorem Term.idJ_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.idJ baseCase witness) :=
  RawTerm.idJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- Direct SN case for observational equality elimination. -/
theorem Term.oeqJ_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.oeqJ baseCase witness) :=
  RawTerm.oeqJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- Direct SN case for strict identity elimination. -/
theorem Term.idStrictRec_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  RawTerm.idStrictRec_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- Fundamental case: `Term.equivApp` at `Ty.equiv` (K12.23.A).

First fundamental atomic over HOTT-adjacent eliminators.  Same
binary Reducible-composition pattern as K12.21.A
`fundamental_app_at_arrow` — `Term.equivApp` is the kernel-
internal application form for type equivalences (per K11.B8 docs
in `Term.lean:1029`+), mirroring `Term.app`'s shape exactly:
takes the equivalence + an argument at carrierA, produces a
result at carrierB.

K12.11's equiv closure ships the FULL Reducible (not SN-fallback)
on the output side, because both carriers (carrierA, carrierB)
are strict sub-Ty of `Ty.equiv carrierA carrierB` — the closure
can recurse on both via def-by-recursion on Ty:

    Reducible (Ty.equiv carrierA carrierB) equivTerm =
      SN(equivTerm) ∧ ∀ argumentTerm,
        Reducible carrierA argumentTerm →
        Reducible carrierB (Term.equivApp equivTerm argumentTerm)

The fundamental atomic projects the second conjunct and applies
to the substituted argument:

    equivIH.2 (Term.subst termSubst argumentTerm) argumentIH

`Term.subst` commutes over `.equivApp` definitionally
(`Term/Subst.lean:414` — no cast, since `Ty.equiv.subst` is
also definitional per `Foundation/Subst.lean:142`).  Same audit
gate as the existing K12.21 cluster.

Note: `Term.equivApply` (the D3.6-P4 univalence-target ctor at
`Term.lean:990`+) is a SEPARATE constructor projecting to a
different raw form; its fundamental case will ship as K12.23.B
once we audit which closure governs it. -/
theorem Reducible.fundamental_equivApp_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIH :
        Reducible ((Ty.equiv carrierA carrierB).subst sigma)
                  (Term.subst termSubst equivTerm))
    (argumentIH :
        Reducible (carrierA.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Reducible (carrierB.subst sigma)
              (Term.subst termSubst (Term.equivApp equivTerm argumentTerm)) :=
  equivIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-- Equivalence application preserves fundamental stability. -/
theorem Reducible.fundamental_equivApp_at_equiv_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIsStable :
      IsRenamingStableReducible
        ((Ty.equiv carrierA carrierB).subst sigma)
        (Term.subst termSubst equivTerm))
    (argumentIsStable :
      IsRenamingStableReducible (carrierA.subst sigma)
        (Term.subst termSubst argumentTerm)) :
    IsRenamingStableReducible (carrierB.subst sigma)
      (Term.subst termSubst
        (Term.equivApp equivTerm argumentTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (equivIsStable rhoIsInjective termRenaming).2
    (Term.rename termRenaming (Term.subst termSubst argumentTerm))
    (argumentIsStable rhoIsInjective termRenaming)

/-- Fundamental case: `Term.equivApply` at `Ty.equiv`
(K12.23.E, SN-output endpoint).

`Term.equivApply` is distinct from `Term.equivApp`: it projects to
`RawTerm.equivApply`, whose current raw fragment includes ua-refl beta
arms returning argument reducts.  The present `Ty.equiv` candidate stores
full Reducible closure for `equivApp`, not for this univalence-target raw
form, so this endpoint deliberately states the Tait-relevant SN conclusion
only. -/
theorem Reducible.fundamental_equivApply_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIH :
        Reducible ((Ty.equiv carrierA carrierB).subst sigma)
                  (Term.subst termSubst equivTerm))
    (argumentIH :
        Reducible (carrierA.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.equivApply equivTerm argumentTerm)) :=
  Term.equivApply_isStronglyNormalizing
    (Reducible.isStronglyNormalizing equivIH)
    (Reducible.isStronglyNormalizing argumentIH)

/-- Fundamental SN endpoint: `Term.equivIntroHet` at `Ty.equiv`
(K12.26 support).

The current `Ty.equiv` candidate stores full `equivApp` closure.
Building that closure for a freshly introduced equivalence would need
a backward bridge from `equivApp (equivIntro forward backward) arg` to
`app forward arg`, which is still tracked under the general
head-β/ι expansion work.  This endpoint therefore records only the
Tait-relevant SN fact for the constructor raw form. -/
theorem Reducible.fundamental_equivIntroHet_at_equiv_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIH :
      Reducible ((Ty.arrow carrierA carrierB).subst sigma)
        (Term.subst termSubst forward))
    (backwardIH :
      Reducible ((Ty.arrow carrierB carrierA).subst sigma)
        (Term.subst termSubst backward)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.equivIntroHet forward backward leftInv rightInv)) :=
  Term.equivIntroHet_isStronglyNormalizing
    (Reducible.isStronglyNormalizing forwardIH)
    (Reducible.isStronglyNormalizing backwardIH)

/-- Renaming-stable SN of `Term.equivIntroHet` at `Ty.equiv` —
`IsRenamingStableIsSN` mirror of `fundamental_equivIntroHet_at_equiv_sn`.

Instantiates forward and backward renaming-stable arrow reducibility
witnesses at each renaming and feeds raw SN to
`Term.equivIntroHet_isStronglyNormalizing`. -/
theorem Reducible.fundamental_equivIntroHet_at_equiv_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIsStable :
      IsRenamingStableReducible ((Ty.arrow carrierA carrierB).subst sigma)
        (Term.subst termSubst forward))
    (backwardIsStable :
      IsRenamingStableReducible ((Ty.arrow carrierB carrierA).subst sigma)
        (Term.subst termSubst backward)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.equivIntroHet forward backward leftInv rightInv)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have forwardReducibleAtRho :=
    forwardIsStable rhoIsInjective termRenaming
  have backwardReducibleAtRho :=
    backwardIsStable rhoIsInjective termRenaming
  exact Term.equivIntroHet_isStronglyNormalizing
    (Reducible.isStronglyNormalizing forwardReducibleAtRho)
    (Reducible.isStronglyNormalizing backwardReducibleAtRho)

/-- Fundamental SN endpoint: `Term.equivIntroHet` at `Ty.equiv`
(K12.26 support).

The conclusion is the Tait-relevant Tait endpoint for the current
equivalence-introduction constructor: the introduced equivalence is
strongly normalizing whenever its forward and backward functions are
reducible.  The historical `_sn` theorem remains available as a
compatibility alias target. -/
theorem Reducible.fundamental_equivIntroHet_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIH :
      Reducible ((Ty.arrow carrierA carrierB).subst sigma)
        (Term.subst termSubst forward))
    (backwardIH :
      Reducible ((Ty.arrow carrierB carrierA).subst sigma)
        (Term.subst termSubst backward)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.equivIntroHet forward backward leftInv rightInv)) :=
  Reducible.fundamental_equivIntroHet_at_equiv_sn forwardIH backwardIH

/-- Fundamental case: `Term.oeqFunext` at `Ty.oeq` (K12.23.B).

The current `Ty.oeq` reducibility arm is weak-J shaped: SN of the
witness plus SN preservation for `Term.oeqJ` over every SN base case.
`Term.oeqFunext` has a typed pointwise proof subterm, so its SN follows
from that subterm's reducibility by `RawTerm.oeqFunext_isStronglyNormalizing`.
The `oeqJ` closure is pure congruence in the present raw reduction
fragment, discharged by `RawTerm.oeqJ_isStronglyNormalizing`. -/
theorem Reducible.fundamental_oeqFunext_at_oeq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {leftFunctionRaw rightFunctionRaw pointwiseRaw : RawTerm scope}
    {pointwiseProof :
        Term sourceCtx
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRaw}
    (pointwiseIH :
        Reducible
          ((oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw).subst sigma)
          (Term.subst termSubst pointwiseProof)) :
    Reducible
      ((Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw).subst sigma)
      (Term.subst termSubst
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqFunext (pointwiseRaw.subst sigma.forRaw)) :=
    RawTerm.oeqFunext_isStronglyNormalizing
      (Reducible.isStronglyNormalizing pointwiseIH)
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Renaming-stable variant of `fundamental_oeqFunext_at_oeq`.

Given a renaming-stable pointwise IH, the typed `Term.oeqFunext`
introducer remains reducible in every injective-renamed future
world.  Unlike the SN-direct closed-leaf cases (interval / session
/ effect), `Reducible` at `Ty.oeq` unfolds to a conjunction of
witness SN plus the per-motive `oeqJ` closure, so the proof rebuilds
both conjuncts at the renamed world from the same raw SN
infrastructure (`oeqFunext_isStronglyNormalizing`,
`oeqJ_isStronglyNormalizing`) — mirroring `fundamental_oeqFunext_at_oeq`
inline at the renamed-world fundamental level. -/
theorem Reducible.fundamental_oeqFunext_at_oeq_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {leftFunctionRaw rightFunctionRaw pointwiseRaw : RawTerm scope}
    {pointwiseProof :
        Term sourceCtx
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRaw}
    (pointwiseIsStable :
        IsRenamingStableReducible
          ((oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw).subst sigma)
          (Term.subst termSubst pointwiseProof)) :
    IsRenamingStableReducible
      ((Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw).subst sigma)
      (Term.subst termSubst
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have pointwiseReducibleAtRho :=
    pointwiseIsStable rhoIsInjective termRenaming
  have witnessIsSN :=
    RawTerm.oeqFunext_isStronglyNormalizing
      (Reducible.isStronglyNormalizing pointwiseReducibleAtRho)
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩



end LeanFX2
