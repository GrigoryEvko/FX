import LeanFX2.Reducibility.FundamentalWrappers

/-! # LeanFX2.Reducibility.FundamentalEliminators.BetaEliminators

Fundamental-theorem cases for β-redex eliminators: `app` at
`Ty.arrow`, `pair`/`fst`/`snd` at `Ty.sigmaTy`, `appPi` at
`Ty.piTy`, `recordProj` at `Ty.record`, `refineElim` at
`Ty.refine`.  Each fires when its scrutinee is the matching
introduction form; cong rules supply the recursive-reduce arm.

## Root status

Layer 3 metatheory leaf.  First slice of `FundamentalEliminators`. -/

namespace LeanFX2


/-! ## K12.21.A fundamental_app at `Ty.arrow` — β-redex elimination
case at the homogeneous (non-dependent) arrow type

First entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.app : Term ctx (Ty.arrow A B) fnRaw → Term ctx A argRaw →
Term ctx B (RawTerm.app fnRaw argRaw)` is the non-dependent
function-application elimination form.

The proof is a single composition of three definitional facts:

1.  `(Ty.arrow A B).subst sigma = Ty.arrow (A.subst sigma)
    (B.subst sigma)`  (`Foundation/Subst.lean:105-106`)
2.  `Reducible (Ty.arrow A' B') f = SN(f) ∧ ∀ argTerm, Reducible
    A' argTerm → Reducible B' (Term.app f argTerm)`  (K12.5, see
    `Reducibility.lean:333-338`)
3.  `Term.subst termSubst (Term.app fn arg) = Term.app
    (Term.subst termSubst fn) (Term.subst termSubst arg)`
    (`Term/Subst.lean:199-200`)

Composing: `functionIH.2 (Term.subst termSubst argumentTerm)
argumentIH` projects the second component of the arrow-closure
witness from the function's IH, applied to the substituted
argument and its argument-IH.  The result has the goal type
modulo the three definitional reductions above. -/

/-- **K12.21.A fundamental_app at `Ty.arrow`** — non-dependent
β-redex elimination.  Direct projection of the arrow's
Reducible-closure (K12.5 second conjunct) applied to the
substituted argument.

This is the strongest fundamental case shipped so far: it
exercises the FULL Tait reducibility framework (not just SN
preservation), proving that the codomain Reducible witness
follows by composing the function's arrow-closure with the
argument's reducibility witness. -/
theorem Reducible.fundamental_app_at_arrow
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIH :
        Reducible ((Ty.arrow domainType codomainType).subst sigma)
                  (Term.subst termSubst functionTerm))
    (argumentIH :
        Reducible (domainType.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Reducible (codomainType.subst sigma)
              (Term.subst termSubst
                (Term.app functionTerm argumentTerm)) :=
  functionIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-- Non-dependent application preserves fundamental stability.

This is the renaming-stable counterpart of
`fundamental_app_at_arrow`: after any injective typed renaming, the
renamed function remains reducible at the renamed arrow type, and its
arrow-closure consumes the renamed argument reducibility witness. -/
theorem Reducible.fundamental_app_at_arrow_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIsStable :
      IsRenamingStableReducible
        ((Ty.arrow domainType codomainType).subst sigma)
        (Term.subst termSubst functionTerm))
    (argumentIsStable :
      IsRenamingStableReducible (domainType.subst sigma)
        (Term.subst termSubst argumentTerm)) :
    IsRenamingStableReducible (codomainType.subst sigma)
      (Term.subst termSubst (Term.app functionTerm argumentTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (functionIsStable rhoIsInjective termRenaming).2
    (Term.rename termRenaming (Term.subst termSubst argumentTerm))
    (argumentIsStable rhoIsInjective termRenaming)

/-- Direct M04 SN endpoint for non-dependent application.

Application is not SN-preserving from child SN alone: the beta arm can
expose the function body's substituted raw term.  The precise Tait
obligation is the arrow reducibility closure for the function plus
reducibility of the argument. -/
theorem Term.app_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionReducible :
        Reducible (Ty.arrow domainType codomainType) functionTerm)
    (argumentReducible : Reducible domainType argumentTerm) :
    Term.isStronglyNormalizing
      (Term.app functionTerm argumentTerm) :=
  Reducible.isStronglyNormalizing
    (functionReducible.2 argumentTerm argumentReducible)

/-- **K12.21 pair-intro SN endpoint at `Ty.sigmaTy`**.

This is the M04-facing pair introduction endpoint: substituting a pair
is strongly normalizing when both substituted components are reducible.
It deliberately returns only SN.  The full sigma Reducible introduction
would additionally need a backward closure proving reducibility of
`fst (pair first second)` at the first component type; that is a
separate CR3-style obligation, not part of this SN endpoint. -/
theorem Reducible.fundamental_pair_at_sigmaTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIH :
      Reducible (firstType.subst sigma)
        (Term.subst termSubst firstValue))
    (secondIH :
      Reducible
        ((secondType.subst0 firstType firstRaw).subst sigma)
        (Term.subst termSubst secondValue)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.pair (secondType := secondType) firstValue secondValue)) := by
  have secondIsSN :
      Term.isStronglyNormalizing
        (Ty.subst0_subst_commute secondType firstType firstRaw sigma ▸
          Term.subst termSubst secondValue) := by
    change RawTerm.isStronglyNormalizing (secondRaw.subst sigma.forRaw)
    exact Reducible.isStronglyNormalizing secondIH
  exact Term.pair_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstIH)
    secondIsSN

/-- Renaming-stable SN of `Term.pair` at `Ty.sigmaTy` —
`IsRenamingStableIsSN` mirror of `fundamental_pair_at_sigmaTy_sn`.

The proof rebuilds the raw-level pair SN witness at each renamed
world by projecting raw SN out of both component
`IsRenamingStableReducible` premises instantiated at the same
renaming, then invoking `RawTerm.pair_isStronglyNormalizing`
directly.  Since `Term.isStronglyNormalizing` is raw-indexed, no
typed-level alignment of the `secondType.subst0` rewrite is
required at the renamed world — the raw `pair` constructor
already matches both inputs by shape. -/
theorem Reducible.fundamental_pair_at_sigmaTy_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsStable :
        IsRenamingStableReducible (firstType.subst sigma)
          (Term.subst termSubst firstValue))
    (secondIsStable :
        IsRenamingStableReducible
          ((secondType.subst0 firstType firstRaw).subst sigma)
          (Term.subst termSubst secondValue)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.pair (secondType := secondType) firstValue secondValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have firstReducibleAtRho :=
    firstIsStable rhoIsInjective termRenaming
  have secondReducibleAtRho :=
    secondIsStable rhoIsInjective termRenaming
  exact RawTerm.pair_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstReducibleAtRho)
    (Reducible.isStronglyNormalizing secondReducibleAtRho)

/-! ## K12.21.B fundamental_fst at `Ty.sigmaTy` — Σ first-projection
elimination

Second entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.fst : Term ctx (Ty.sigmaTy A B) pairRaw → Term ctx A
(RawTerm.fst pairRaw)` projects the first component out of a
dependent pair.

The proof is a single triple-projection on the pair's reducibility
witness.  Three definitional facts compose:

1.  `(Ty.sigmaTy A B).subst sigma = Ty.sigmaTy (A.subst sigma)
    (B.subst sigma.lift)`  (`Foundation/Subst.lean:109-110`)
2.  `Reducible (Ty.sigmaTy A' B') pair = SN(pair) ∧ Reducible A'
    (Term.fst pair) ∧ SN(Term.snd pair)`  (K12.7 asymmetric
    closure, see `Reducibility.lean:367-370`)
3.  `Term.subst termSubst (Term.fst pairTerm) = Term.fst
    (Term.subst termSubst pairTerm)`  (`Term/Subst.lean:215`)

Body: `pairIH.2.1` extracts the middle conjunct (full Reducible
on the substituted firstType applied to the substituted pair's
first projection).

The sibling `fundamental_snd_at_sigmaTy` would extract `.2.2`
(SN of `Term.snd pair`) — but its goal type involves the
substituted-codomain wall `secondType.subst0 firstType
(RawTerm.fst pairRaw)`, which is not a strict sub-Ty of
`Ty.sigmaTy firstType secondType`.  Per K12.7's design, the
snd-projection closure is reserved for the Kripke logical-
relation refactor; the second projection ships at K12.21.snd
with the weak SN target rather than full Reducible. -/

/-- **K12.21.B fundamental_fst at `Ty.sigmaTy`** — Σ
first-projection elimination.  Direct extraction of the middle
conjunct from K12.7's asymmetric sigmaTy closure. -/
theorem Reducible.fundamental_fst_at_sigmaTy
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH :
        Reducible ((Ty.sigmaTy firstType secondType).subst sigma)
                  (Term.subst termSubst pairTerm)) :
    Reducible (firstType.subst sigma)
              (Term.subst termSubst (Term.fst pairTerm)) :=
  pairIH.2.1

/-- Sigma first projection preserves fundamental stability. -/
theorem Reducible.fundamental_fst_at_sigmaTy_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsStable :
      IsRenamingStableReducible
        ((Ty.sigmaTy firstType secondType).subst sigma)
        (Term.subst termSubst pairTerm)) :
    IsRenamingStableReducible (firstType.subst sigma)
      (Term.subst termSubst (Term.fst pairTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (pairIsStable rhoIsInjective termRenaming).2.1

/-! ## K12.21.C fundamental_snd at `Ty.sigmaTy` — Σ second-projection
SN-output case

Third entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.snd : Term ctx (Ty.sigmaTy A B) pairRaw → Term ctx (B.subst0
A (RawTerm.fst pairRaw)) (RawTerm.snd pairRaw)` projects the
second component of a dependent pair.

Asymmetry with K12.21.B: the sigmaTy second-projection target type
`secondType.subst0 firstType (RawTerm.fst pairRaw)` is NOT a
strict sub-Ty of `Ty.sigmaTy firstType secondType` — structural
recursion on Ty cannot inspect it without the Kripke logical-
candidate.  Per K12.7's asymmetric closure design
(`Reducibility.lean:367-370`), the snd-projection closure ships
only as **SN of the snd term**, not full Reducible:

  Reducible (Ty.sigmaTy A' B') pair = SN(pair)
                                    ∧ Reducible A' (Term.fst pair)
                                    ∧ SN(Term.snd pair)

This fundamental case ships at the SN-output level matching K12.7.
Three definitional facts compose:

1.  `(Ty.sigmaTy A B).subst sigma = Ty.sigmaTy (A.subst sigma)
    (B.subst sigma.lift)`  (`Foundation/Subst.lean:109-110`)
2.  K12.7's third conjunct gives SN of Term.snd directly
3.  `Term.isStronglyNormalizing` reads only the raw index
    (`Reducibility.lean:303-307`) — the Ty.subst0_subst_commute
    cast on `Term.subst termSubst (Term.snd ...)` (`Term/Subst.lean:
    217-221`) is irrelevant because both cast and un-cast forms
    share the same RawTerm.snd raw projection.

Body: `pairIH.2.2` extracts the third conjunct (the SN witness on
the snd projection).

When secondType.subst0 is itself SN-direct (e.g. when secondType
is a non-dependent variant `B.weaken` of a closed-leaf type), the
SN-output result IS the full Reducible result.  When secondType is
compound, the lift to full Reducible needs motive-rich infrastructure. -/

/-- **K12.21.C fundamental_snd at `Ty.sigmaTy`** — SN-output
case.  Direct extraction of the third conjunct from K12.7's
asymmetric sigmaTy closure; the substituted-codomain wall blocks
full Reducible at the dependent second projection.

The goal is **SN of the substituted Term.snd**, not Reducible —
matching K12.6/K12.7's documented design (`Reducibility.lean:339-352`).  -/
theorem Reducible.fundamental_snd_at_sigmaTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH :
        Reducible ((Ty.sigmaTy firstType secondType).subst sigma)
                  (Term.subst termSubst pairTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.snd pairTerm)) :=
  pairIH.2.2

/-- Renaming-stable SN of `Term.snd` at `Ty.sigmaTy` —
`IsRenamingStableIsSN` mirror of `fundamental_snd_at_sigmaTy_sn`.

Direct `.2.2` projection over the pair's renaming-stable
reducibility witness at each renamed world. -/
theorem Reducible.fundamental_snd_at_sigmaTy_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsStable :
        IsRenamingStableReducible
          ((Ty.sigmaTy firstType secondType).subst sigma)
          (Term.subst termSubst pairTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.snd pairTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (pairIsStable rhoIsInjective termRenaming).2.2

/-! ## K12.21.U5 head-β endpoints — Σ-eliminator on Σ-introducer

Head-β-expansion endpoints for `Term.fst (Term.pair _ _)` and
`Term.snd (Term.pair _ _)` after substitution.  These are the Σ
analogs of the existing `fundamental_lam_at_arrow_app_sn` family:
they consume `Reducible` witnesses of the substituted components
and produce SN of the head-β redex.

Both reduce by the same composition pattern as
`fundamental_pair_at_sigmaTy_sn`:
1. Extract raw SN from each `Reducible` via `Reducible.isStronglyNormalizing`
2. Realign the second component's typed SN through `Ty.subst0_subst_commute`
3. Apply the raw head-β-expansion endpoint `Term.fst_pair_isStronglyNormalizing`
   (resp. `Term.snd_pair_isStronglyNormalizing`)

Result type is SN of the substituted head-β redex; Lean's kernel
unfolds `Term.subst termSubst (Term.fst (Term.pair _ _))` to
`Term.fst (Term.pair (Term.subst _ fv) (cast ▸ Term.subst _ sv))`
via δ-ι reduction, matching `Term.fst_pair_isStronglyNormalizing`'s
conclusion directly. -/

/-- **K12.21.U5 head-β at Σ.fst** — fundamental wrapper for
`Term.fst (Term.pair _ _)` consuming `Reducible` witnesses of
the substituted pair components. -/
theorem Reducible.fundamental_fst_pair_at_sigmaTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIH :
      Reducible (firstType.subst sigma)
        (Term.subst termSubst firstValue))
    (secondIH :
      Reducible
        ((secondType.subst0 firstType firstRaw).subst sigma)
        (Term.subst termSubst secondValue)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.fst
          (Term.pair (secondType := secondType) firstValue secondValue))) := by
  have secondIsSN :
      Term.isStronglyNormalizing
        (Ty.subst0_subst_commute secondType firstType firstRaw sigma ▸
          Term.subst termSubst secondValue) := by
    change RawTerm.isStronglyNormalizing (secondRaw.subst sigma.forRaw)
    exact Reducible.isStronglyNormalizing secondIH
  exact Term.fst_pair_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstIH)
    secondIsSN

/-- Renaming-stable variant of `fundamental_fst_pair_at_sigmaTy_sn`. -/
theorem Reducible.fundamental_fst_pair_at_sigmaTy_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsStable :
        IsRenamingStableReducible (firstType.subst sigma)
          (Term.subst termSubst firstValue))
    (secondIsStable :
        IsRenamingStableReducible
          ((secondType.subst0 firstType firstRaw).subst sigma)
          (Term.subst termSubst secondValue)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.fst
          (Term.pair (secondType := secondType) firstValue secondValue))) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have firstReducibleAtRho :=
    firstIsStable rhoIsInjective termRenaming
  have secondReducibleAtRho :=
    secondIsStable rhoIsInjective termRenaming
  have firstIsSN := Reducible.isStronglyNormalizing firstReducibleAtRho
  have secondIsSN := Reducible.isStronglyNormalizing secondReducibleAtRho
  exact RawTerm.fst_pair_isStronglyNormalizing firstIsSN secondIsSN

/-- **K12.21.U5 head-β at Σ.snd** — fundamental wrapper for
`Term.snd (Term.pair _ _)` consuming `Reducible` witnesses of
the substituted pair components. -/
theorem Reducible.fundamental_snd_pair_at_sigmaTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIH :
      Reducible (firstType.subst sigma)
        (Term.subst termSubst firstValue))
    (secondIH :
      Reducible
        ((secondType.subst0 firstType firstRaw).subst sigma)
        (Term.subst termSubst secondValue)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.snd
          (Term.pair (secondType := secondType) firstValue secondValue))) := by
  have secondIsSN :
      Term.isStronglyNormalizing
        (Ty.subst0_subst_commute secondType firstType firstRaw sigma ▸
          Term.subst termSubst secondValue) := by
    change RawTerm.isStronglyNormalizing (secondRaw.subst sigma.forRaw)
    exact Reducible.isStronglyNormalizing secondIH
  exact Term.snd_pair_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstIH)
    secondIsSN

/-- Renaming-stable variant of `fundamental_snd_pair_at_sigmaTy_sn`. -/
theorem Reducible.fundamental_snd_pair_at_sigmaTy_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsStable :
        IsRenamingStableReducible (firstType.subst sigma)
          (Term.subst termSubst firstValue))
    (secondIsStable :
        IsRenamingStableReducible
          ((secondType.subst0 firstType firstRaw).subst sigma)
          (Term.subst termSubst secondValue)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.snd
          (Term.pair (secondType := secondType) firstValue secondValue))) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have firstReducibleAtRho :=
    firstIsStable rhoIsInjective termRenaming
  have secondReducibleAtRho :=
    secondIsStable rhoIsInjective termRenaming
  have firstIsSN := Reducible.isStronglyNormalizing firstReducibleAtRho
  have secondIsSN := Reducible.isStronglyNormalizing secondReducibleAtRho
  exact RawTerm.snd_pair_isStronglyNormalizing firstIsSN secondIsSN

/-! ## K12.21.U5 head-β endpoints — record-projection / refinement-
elim on their introducers

Two further entries in the K12.21.U5 head-β-expansion family.
The patterns mirror the Σ-fst / Σ-snd pair above: consume a
`Reducible` witness at the substituted introducer-component
type, extract raw SN via `Reducible.isStronglyNormalizing`, and
apply the corresponding raw head-β endpoint
`Term.{recordProj_recordIntro,refineElim_refineIntro}_isStronglyNormalizing`.

`Term.subst` distributes definitionally through both
`recordProj`/`recordIntro` and `refineElim`/`refineIntro`, so the
substituted goal matches the raw endpoint's conclusion via δ-ι
reduction. -/

/-- **K12.21.U5 head-β at record.proj-of-intro** — fundamental
wrapper for `Term.recordProj (Term.recordIntro field)` consuming a
`Reducible` witness of the substituted single field. -/
theorem Reducible.fundamental_recordProj_recordIntro_at_record_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (firstIH :
        Reducible (singleFieldType.subst sigma)
          (Term.subst termSubst firstField)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.recordProj (Term.recordIntro firstField))) :=
  Term.recordProj_recordIntro_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstIH)

/-- Renaming-stable variant of
`fundamental_recordProj_recordIntro_at_record_sn`. -/
theorem Reducible.fundamental_recordProj_recordIntro_at_record_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (firstIsStable :
        IsRenamingStableReducible (singleFieldType.subst sigma)
          (Term.subst termSubst firstField)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.recordProj (Term.recordIntro firstField))) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have firstReducibleAtRho :=
    firstIsStable rhoIsInjective termRenaming
  have firstIsSN := Reducible.isStronglyNormalizing firstReducibleAtRho
  exact RawTerm.recordProj_recordIntro_isStronglyNormalizing firstIsSN

/-- **K12.21.U5 head-β at refine.elim-of-intro** — fundamental
wrapper for `Term.refineElim (Term.refineIntro predicate value proof)`
consuming `Reducible` witnesses of the substituted base value and
proof payload. -/
theorem Reducible.fundamental_refineElim_refineIntro_at_refine_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (valueIH :
        Reducible (baseType.subst sigma)
          (Term.subst termSubst baseValue))
    (proofIH :
        Reducible (Ty.unit.subst sigma)
          (Term.subst termSubst predicateProof)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.refineElim
          (Term.refineIntro predicate baseValue predicateProof))) :=
  Term.refineElim_refineIntro_isStronglyNormalizing
    (Reducible.isStronglyNormalizing valueIH)
    (Reducible.isStronglyNormalizing proofIH)

/-- Renaming-stable variant of
`fundamental_refineElim_refineIntro_at_refine_sn`. -/
theorem Reducible.fundamental_refineElim_refineIntro_at_refine_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (valueIsStable :
        IsRenamingStableReducible (baseType.subst sigma)
          (Term.subst termSubst baseValue))
    (proofIsStable :
        IsRenamingStableReducible (Ty.unit.subst sigma)
          (Term.subst termSubst predicateProof)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.refineElim
          (Term.refineIntro predicate baseValue predicateProof))) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have valueReducibleAtRho :=
    valueIsStable rhoIsInjective termRenaming
  have proofReducibleAtRho :=
    proofIsStable rhoIsInjective termRenaming
  have valueIsSN := Reducible.isStronglyNormalizing valueReducibleAtRho
  have proofIsSN := Reducible.isStronglyNormalizing proofReducibleAtRho
  exact RawTerm.refineElim_refineIntro_isStronglyNormalizing
    valueIsSN proofIsSN

/-! ## K12.21.D fundamental_appPi at `Ty.piTy` — Π SN-output
elimination

Fourth entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.appPi : Term ctx (Ty.piTy A B) fnRaw → Term ctx A argRaw →
Term ctx (B.subst0 A argRaw) (RawTerm.app fnRaw argRaw)` is the
dependent function-application elimination form.

Asymmetry with K12.21.A: the target type `B.subst0 A argRaw` is
NOT a strict sub-Ty of `Ty.piTy A B` — same structural-recursion
wall as K12.21.C's `B.subst0` codomain on Σ.snd.  Per K12.6's
SN-output closure design (`Reducibility.lean:353-358`), the dep-Π
eliminator closure ships only as SN of the application
(not full Reducible):

  Reducible (Ty.piTy A' B') f = SN(f)
                              ∧ ∀ arg, Reducible A' arg
                                       → SN(Term.appPi f arg)

Cast-invariance: `Term.subst termSubst (Term.appPi fn arg)`
applies a `Ty.subst0_subst_commute.symm ▸` cast (`Term/Subst.lean:
205-208`), but `Term.isStronglyNormalizing` reads only the raw
index (`Reducibility.lean:303-307`) — the cast preserves the
underlying `RawTerm.app (fnRaw.subst sigma.forRaw) (argRaw.subst
sigma.forRaw)` projection.

Body: `functionIH.2 (Term.subst termSubst argumentTerm)
argumentIH` — same composition shape as K12.21.A's
fundamental_app_at_arrow, but the second conjunct of K12.6's
piTy closure returns SN, not Reducible.

The full-Reducible upgrade needs infrastructure that defeats the
structural-recursion barrier on substituted codomains. -/

/-- **K12.21.D fundamental_appPi at `Ty.piTy`** — Π SN-output
elimination.  Dependent function application composes the
function's piTy SN-output closure with the argument's reducibility
witness; the substituted-codomain wall blocks full-Reducible
at the dependent application result.

The goal is **SN of the substituted Term.appPi**, not Reducible —
matching K12.6's documented SN-output closure design (`Reducibility.
lean:339-352`). -/
theorem Reducible.fundamental_appPi_at_piTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIH :
        Reducible ((Ty.piTy domainType codomainType).subst sigma)
                  (Term.subst termSubst functionTerm))
    (argumentIH :
        Reducible (domainType.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.appPi functionTerm argumentTerm)) :=
  functionIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-- Renaming-stable SN of `Term.appPi` at `Ty.piTy` —
`IsRenamingStableIsSN` mirror of `fundamental_appPi_at_piTy_sn`.

Composes function-side and argument-side renaming-stable
reducibility at each renamed world: feed the renamed argument
term and the renamed-argument reducibility witness into the
function's piTy SN-output closure.  K12.6's piTy second
conjunct stores SN, not full Reducible — the substituted-
codomain wall blocks full-Reducible at the dependent
application result, but SN ships cleanly. -/
theorem Reducible.fundamental_appPi_at_piTy_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIsStable :
        IsRenamingStableReducible
          ((Ty.piTy domainType codomainType).subst sigma)
          (Term.subst termSubst functionTerm))
    (argumentIsStable :
        IsRenamingStableReducible (domainType.subst sigma)
          (Term.subst termSubst argumentTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.appPi functionTerm argumentTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (functionIsStable rhoIsInjective termRenaming).2
    (Term.rename termRenaming (Term.subst termSubst argumentTerm))
    (argumentIsStable rhoIsInjective termRenaming)

/-- Direct M04 SN endpoint for dependent application.

The current `piTy` reducibility arm intentionally stores an SN-output
application closure.  This theorem exposes that closure at the typed
`Term.appPi` surface without claiming full reducibility of the
substituted codomain. -/
theorem Term.appPi_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionReducible :
        Reducible (Ty.piTy domainType codomainType) functionTerm)
    (argumentReducible : Reducible domainType argumentTerm) :
    Term.isStronglyNormalizing
      (Term.appPi functionTerm argumentTerm) :=
  functionReducible.2 argumentTerm argumentReducible

/-! ## K12.21.E fundamental_recordProj at `Ty.record` —
single-field record projection

Fifth entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.recordProj : Term ctx (Ty.record A) recordRaw → Term ctx A
(RawTerm.recordProj recordRaw)` projects out the single field
of a record.

The proof is a direct second-conjunct extraction.  Three
definitional facts compose:

1.  `(Ty.record A).subst sigma = Ty.record (A.subst sigma)`
    (`Foundation/Subst.lean:146-147`)
2.  `Reducible (Ty.record A') record = SN(record) ∧ Reducible
    A' (Term.recordProj record)`  (K12.15 closure, see
    `Reducibility.lean:563-565`)
3.  `Term.subst termSubst (Term.recordProj rec) = Term.recordProj
    (Term.subst termSubst rec)`  (`Term/Subst.lean:346-347`)

Body: `recordIH.2` — unary projection.  Closure shape parallels
K12.21.B's `fundamental_fst_at_sigmaTy` (K12.7 first conjunct);
record's single-field design means the eliminator target is
exactly the strict sub-Ty `singleFieldType` with no
substituted-codomain wall, so full Reducible (not weak SN). -/

/-- **K12.21.E fundamental_recordProj at `Ty.record`** — record
field projection.  Direct extraction of the second conjunct from
K12.15's record closure.

Multi-field records compose via nested single-field records (see
`Term.lean:420`+ docstring), preserving this closure shape under
nesting; no separate fundamental case needed for multi-field
projection. -/
theorem Reducible.fundamental_recordProj_at_record
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue :
        Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (recordIH :
        Reducible ((Ty.record singleFieldType).subst sigma)
                  (Term.subst termSubst recordValue)) :
    Reducible (singleFieldType.subst sigma)
              (Term.subst termSubst (Term.recordProj recordValue)) :=
  recordIH.2

/-- Record projection preserves fundamental stability. -/
theorem Reducible.fundamental_recordProj_at_record_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue :
        Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (recordIsStable :
      IsRenamingStableReducible
        ((Ty.record singleFieldType).subst sigma)
        (Term.subst termSubst recordValue)) :
    IsRenamingStableReducible (singleFieldType.subst sigma)
      (Term.subst termSubst (Term.recordProj recordValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (recordIsStable rhoIsInjective termRenaming).2

/-- Fundamental case: `Term.refineElim` at `Ty.refine` (K12.21.F).

`Term.refineElim` projects from a refinement-typed value to the
underlying base type — `Term ctx (Ty.refine baseType predicate)
refinedRaw → Term ctx baseType (RawTerm.refineElim refinedRaw)`.
`Term.subst` commutes definitionally over `.refineElim` (no
cast, since Ty.refine.subst keeps baseType intact under sigma:
`(Ty.refine baseType predicate).subst sigma = Ty.refine
(baseType.subst sigma) (predicate.subst sigma.forRaw.lift)`).

K12.14's refine closure carries the full eliminator-output
witness: `Reducible (Ty.refine baseType _) refinedValue =
SN(refinedValue) ∧ Reducible baseType (Term.refineElim
refinedValue)`.  The fundamental case extracts the second
conjunct — `refineIH.2` — and Lean unifies it with the goal
via the definitional Term.subst commute on `.refineElim`.

Same unary-projection pattern as K12.21.E recordProj and K12.21.B
fst-at-sigmaTy.  The Decidable-predicate discharge aspect of
refinements (the `predicate` argument carrying an SMT obligation)
lives at Layer 5 SMTCert (#1342 D5.6, #1344 D5.8) — orthogonal to
this Reducibility-candidate projection, which only consults the
base-type carrier. -/
theorem Reducible.fundamental_refineElim_at_refine
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue :
        Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refineIH :
        Reducible ((Ty.refine baseType predicate).subst sigma)
                  (Term.subst termSubst refinedValue)) :
    Reducible (baseType.subst sigma)
              (Term.subst termSubst (Term.refineElim refinedValue)) :=
  refineIH.2

/-- Refinement elimination preserves fundamental stability. -/
theorem Reducible.fundamental_refineElim_at_refine_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue :
        Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refinedIsStable :
      IsRenamingStableReducible
        ((Ty.refine baseType predicate).subst sigma)
        (Term.subst termSubst refinedValue)) :
    IsRenamingStableReducible (baseType.subst sigma)
      (Term.subst termSubst (Term.refineElim refinedValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (refinedIsStable rhoIsInjective termRenaming).2

end LeanFX2
