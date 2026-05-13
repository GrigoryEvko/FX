import LeanFX2.Reducibility.FundamentalWrappers

/-! # LeanFX2.Reducibility.FundamentalEliminators — K12.21 / K12.22 / K12.23 / K12.26

The fundamental-theorem cases for β-redex eliminators (K12.21),
ι-eliminators (K12.22), HOTT-J eliminators (K12.23), and
reflexivity introducers (K12.26).

## What ships

* K12.21.A — `Term.fundamental_app` at `Ty.arrow` (β-redex
  elimination at the proper-closure arrow arm).
* K12.21.B — `Term.fundamental_fst` at `Ty.sigmaTy` (Σ
  first-projection).
* K12.21.C — `Term.fundamental_snd` at `Ty.sigmaTy` (Σ
  second-projection).
* K12.21.D — `Term.fundamental_appPi` at `Ty.piTy` (Π SN-output).
* K12.21.E — `Term.fundamental_recordProj` at `Ty.record`.
* K12.22 — fundamental ι-eliminator cases (`boolElim`, `natElim`,
  `natRec`, `listElim`, `optionMatch`, `eitherMatch`) +
  SN-output endpoint aliases.
* K12.23 — fundamental HOTT-eliminator cases (`idJ`, `oeqJ`,
  `idStrictRec`, `equivApply`).
* K12.26 — reflexivity-intro fundamentals (`Term.refl`,
  `Term.oeqRefl`, `Term.idStrictRefl`) with explicit endpoint SN.

## Root status

Layer 3 metatheory leaf.  Part of the K12.20.U4–K12.26
fundamental-theorem cascade. -/

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

/-! ## K12.22 fundamental ι-eliminator cases -/

/-- Fundamental case: `Term.boolElim` at `Ty.bool` (K12.22.A,
SN-output).

The current bool arm is an SN-direct closed-type clause.  Since the motive
type is arbitrary rather than a structural sub-type of `Ty.bool`, this case
returns SN of the eliminator result.
-/
theorem Reducible.fundamental_boolElim_at_bool_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH :
      Reducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (thenIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma)
        (Term.subst termSubst thenBranch))
    (elseIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma)
        (Term.subst termSubst elseBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch)) :=
  RawTerm.boolElim_isStronglyNormalizing
    (Reducible.isStronglyNormalizing thenIH)
    (Reducible.isStronglyNormalizing elseIH)
    scrutineeIH

/-- Fundamental endpoint: canonical `Term.natElim` at `natZero`
(K12.22.D).

This is the zero ι-case needed by the SN-output Tait endpoint: the
eliminator result is strongly normalizing because it contracts to the
zero branch, while congruent movement under the successor branch is
covered by the branch SN premise.
-/
theorem Reducible.fundamental_natElimZero_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat motiveType).subst sigma)
        (Term.subst termSubst succBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natElim Term.natZero zeroBranch succBranch)) :=
  Term.natElim_natZero_isStronglyNormalizing
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)

/-- Fundamental endpoint: canonical `Term.natElim` at `natSucc`
(K12.22.E).

The successor branch is arrow-reducible, so applying it to the
reducible predecessor yields a reducible motive result; CR1 then gives
the SN premise required by the raw successor ι-expansion.
-/
theorem Reducible.fundamental_natElimSucc_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (predecessorIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst predecessor))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat motiveType).subst sigma)
        (Term.subst termSubst succBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natElim
          (Term.natSucc predecessor) zeroBranch succBranch)) :=
  Term.natElim_natSucc_isStronglyNormalizing
    (Reducible.isStronglyNormalizing predecessorIH)
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    (Reducible.isStronglyNormalizing
      (succIH.2 (Term.subst termSubst predecessor) predecessorIH))

/-- Fundamental case: `Term.natElim` at `Ty.nat`
(SN-output endpoint).

The successor-application SN closure is explicit for the same reason it
is explicit in `RawTerm.natElim_isStronglyNormalizing`: a deep successor
ι step exposes an arbitrary raw predecessor developed from the
scrutinee.  This theorem packages the substitution-facing fundamental
case without claiming full Reducible-at-motive closure. -/
theorem Reducible.fundamental_natElim_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat motiveType).subst sigma)
        (Term.subst termSubst succBranch))
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm targetScope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (succRaw.subst sigma.forRaw) predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natElim scrutinee zeroBranch succBranch)) :=
  Term.natElim_isStronglyNormalizing
    scrutineeIH
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    succAppIsSN

/-- Fundamental endpoint: canonical `Term.natRec` at `natZero`
(K12.22.F).

This zero ι-case mirrors `fundamental_natElimZero_at_nat`: the
recursor contracts to the zero branch, while successor-branch
congruence is covered by the branch SN premise.
-/
theorem Reducible.fundamental_natRecZero_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat
                    (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natRec Term.natZero zeroBranch succBranch)) :=
  Term.natRec_natZero_isStronglyNormalizing
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)

/-- Fundamental endpoint: canonical `Term.natRec` at `natSucc`
(K12.22.G).

The successor branch is arrow-reducible twice: first at the predecessor,
then at the recursive call.  The recursive result remains an explicit
premise because this endpoint is a local ι backward-closure, not the
general nat-recursion fundamental theorem. -/
theorem Reducible.fundamental_natRecSucc_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (predecessorIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst predecessor))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat
                    (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch))
    (recursiveIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst
          (Term.natRec predecessor zeroBranch succBranch))) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natRec
          (Term.natSucc predecessor) zeroBranch succBranch)) :=
  Term.natRec_natSucc_isStronglyNormalizing
    (Reducible.isStronglyNormalizing predecessorIH)
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    (Reducible.isStronglyNormalizing recursiveIH)
    (Reducible.isStronglyNormalizing
      ((succIH.2 (Term.subst termSubst predecessor) predecessorIH).2
        (Term.subst termSubst
          (Term.natRec predecessor zeroBranch succBranch))
        recursiveIH))

/-- Fundamental case: `Term.natRec` at `Ty.nat`
(SN-output endpoint).

The successor contractum closure is explicit over raw target branches:
the current `Ty.nat` candidate stores only SN, so this theorem does not
derive full recursive Reducible-at-motive normalization by itself. -/
theorem Reducible.fundamental_natRec_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat
                    (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch))
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm targetScope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natRec scrutinee zeroBranch succBranch)) :=
  Term.natRec_isStronglyNormalizing
    scrutineeIH
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    contractumIsSN

/-- Fundamental case: `Term.optionMatch` at `Ty.optionType` (K12.22.B,
SN-output).

The `Ty.optionType` reducibility arm stores an eliminator closure:
SN of the scrutinee plus SN of the none branch plus SN of each
some-branch application at a reducible element.  The branch-application
premise is supplied by the arrow reducibility of `someBranch`, then
demoted to SN because the current closure returns SN at the arbitrary
motive type.
-/
theorem Reducible.fundamental_optionMatch_at_option_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH :
      Reducible ((Ty.optionType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (noneIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst noneBranch))
    (someIH :
      Reducible ((Ty.arrow elementType motiveType).subst sigma)
        (Term.subst termSubst someBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst noneBranch)
    (Term.subst termSubst someBranch)
    (Reducible.isStronglyNormalizing noneIH)
    (Reducible.isStronglyNormalizing someIH)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (someIH.2 valueTerm valueIH))

/-- Fundamental case: `Term.eitherMatch` at `Ty.eitherType` (K12.22.C,
SN-output).

Same SN-output eliminator pattern as `optionMatch`, with one arrow-typed
branch for each side.  The current candidate can prove SN of the
eliminator result.
-/
theorem Reducible.fundamental_eitherMatch_at_either_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH :
      Reducible ((Ty.eitherType leftType rightType).subst sigma)
        (Term.subst termSubst scrutinee))
    (leftIH :
      Reducible ((Ty.arrow leftType motiveType).subst sigma)
        (Term.subst termSubst leftBranch))
    (rightIH :
      Reducible ((Ty.arrow rightType motiveType).subst sigma)
        (Term.subst termSubst rightBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst leftBranch)
    (Term.subst termSubst rightBranch)
    (Reducible.isStronglyNormalizing leftIH)
    (Reducible.isStronglyNormalizing rightIH)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (leftIH.2 valueTerm valueIH))
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (rightIH.2 valueTerm valueIH))

/-! ## K12.22 SN-output endpoint aliases

These aliases drop the historical `_sn` suffix for K12.22 eliminator
fundamentals.  The theorem statements still state the exact SN-output
contract, matching the current Tait endpoint for M04 strong
normalization without claiming full Reducible-at-motive closure. -/

/-- Fundamental case: `Term.boolElim` at `Ty.bool` (SN-output endpoint). -/
theorem Reducible.fundamental_boolElim_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH :
      Reducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (thenIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma)
        (Term.subst termSubst thenBranch))
    (elseIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma)
        (Term.subst termSubst elseBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch)) :=
  Reducible.fundamental_boolElim_at_bool_sn
    scrutineeIH thenIH elseIH

/-- Fundamental case: `Term.optionMatch` at `Ty.optionType`
(SN-output endpoint). -/
theorem Reducible.fundamental_optionMatch_at_optionType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH :
      Reducible ((Ty.optionType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (noneIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst noneBranch))
    (someIH :
      Reducible ((Ty.arrow elementType motiveType).subst sigma)
        (Term.subst termSubst someBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch)) :=
  Reducible.fundamental_optionMatch_at_option_sn
    scrutineeIH noneIH someIH

/-- Fundamental case: `Term.eitherMatch` at `Ty.eitherType`
(SN-output endpoint). -/
theorem Reducible.fundamental_eitherMatch_at_eitherType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH :
      Reducible ((Ty.eitherType leftType rightType).subst sigma)
        (Term.subst termSubst scrutinee))
    (leftIH :
      Reducible ((Ty.arrow leftType motiveType).subst sigma)
        (Term.subst termSubst leftBranch))
    (rightIH :
      Reducible ((Ty.arrow rightType motiveType).subst sigma)
        (Term.subst termSubst rightBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch)) :=
  Reducible.fundamental_eitherMatch_at_either_sn
    scrutineeIH leftIH rightIH

/-- Fundamental case: `Term.listElim` at `Ty.listType`
(SN-output endpoint).

The current list candidate intentionally asks for the cons-branch
application SN closure at every reducible head and strongly-normalizing
tail.  That premise is load-bearing: the tail component is SN-only in
the K12.8 closure, so the ordinary arrow-reducibility of `consBranch`
is not enough to manufacture this closure for arbitrary tails. -/
theorem Reducible.fundamental_listElim_at_listType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIH :
      Reducible ((Ty.listType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (nilIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst nilBranch))
    (consIH :
      Reducible
        ((Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)).subst sigma)
        (Term.subst termSubst consBranch))
    (consAppIsSN :
      ∀ {headRaw tailRaw : RawTerm targetScope}
        (headTerm : Term targetCtx (elementType.subst sigma) headRaw)
        (tailTerm : Term targetCtx ((Ty.listType elementType).subst sigma) tailRaw),
        Reducible (elementType.subst sigma) headTerm →
        Term.isStronglyNormalizing tailTerm →
        Term.isStronglyNormalizing
          (Term.app
            (Term.app (Term.subst termSubst consBranch) headTerm)
            tailTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.listElim scrutinee nilBranch consBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst nilBranch)
    (Term.subst termSubst consBranch)
    (Reducible.isStronglyNormalizing nilIH)
    (Reducible.isStronglyNormalizing consIH)
    consAppIsSN

/-- Direct M04 SN endpoint for list elimination.

The list reducibility candidate carries the eliminator closure directly.
The cons branch still needs an explicit application-SN premise because
the current list closure tracks the tail only at SN, not full reducible
tail evidence. -/
theorem Term.listElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeReducible :
      Reducible (Ty.listType elementType) scrutinee)
    (nilIsSN : Term.isStronglyNormalizing nilBranch)
    (consIsSN : Term.isStronglyNormalizing consBranch)
    (consAppIsSN :
      ∀ {headRaw tailRaw : RawTerm scope}
        (headTerm : Term sourceCtx elementType headRaw)
        (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw),
        Reducible elementType headTerm →
        Term.isStronglyNormalizing tailTerm →
        Term.isStronglyNormalizing
          (Term.app (Term.app consBranch headTerm) tailTerm)) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) :=
  scrutineeReducible.2 nilBranch consBranch nilIsSN consIsSN consAppIsSN

/-- Direct M04 SN endpoint for option matching.

This exposes the SN-output eliminator closure stored in the option
reducibility candidate: reducible scrutinee, SN branches, and an
application-SN closure for the `Some` branch. -/
theorem Term.optionMatch_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeReducible :
      Reducible (Ty.optionType elementType) scrutinee)
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch)
    (someAppIsSN :
      ∀ {valueRaw : RawTerm scope}
        (valueTerm : Term sourceCtx elementType valueRaw),
        Reducible elementType valueTerm →
        Term.isStronglyNormalizing (Term.app someBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) :=
  scrutineeReducible.2 noneBranch someBranch
    noneIsSN someIsSN someAppIsSN

/-- Direct M04 SN endpoint for either matching.

The either candidate stores symmetric SN-output eliminator closures for the
left and right branches.  This theorem exposes that exact M04 endpoint
without claiming full reducibility at the arbitrary motive type. -/
theorem Term.eitherMatch_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeReducible :
      Reducible (Ty.eitherType leftType rightType) scrutinee)
    (leftIsSN : Term.isStronglyNormalizing leftBranch)
    (rightIsSN : Term.isStronglyNormalizing rightBranch)
    (leftAppIsSN :
      ∀ {valueRaw : RawTerm scope}
        (valueTerm : Term sourceCtx leftType valueRaw),
        Reducible leftType valueTerm →
        Term.isStronglyNormalizing (Term.app leftBranch valueTerm))
    (rightAppIsSN :
      ∀ {valueRaw : RawTerm scope}
        (valueTerm : Term sourceCtx rightType valueRaw),
        Reducible rightType valueTerm →
        Term.isStronglyNormalizing (Term.app rightBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) :=
  scrutineeReducible.2 leftBranch rightBranch
    leftIsSN rightIsSN leftAppIsSN rightAppIsSN

/-! ## K12.23 fundamental HOTT-eliminator cases -/

/-- Fundamental case: `Term.idJ` at `Ty.id` (K12.23.B, SN-output).

The current `Ty.id` reducibility arm stores
SN of the equality witness plus an eliminator closure from any SN
base case to SN of `Term.idJ baseCase witness`.  The motive type is
arbitrary, not a structural sub-type of `Ty.id carrier left right`, so
the conclusion here is exactly `Term.isStronglyNormalizing`, not full
`Reducible motiveType`.
-/
theorem Reducible.fundamental_idJ_at_id_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.id carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.idJ baseCase witness)) :=
  witnessIH.2 (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-- Fundamental case: `Term.oeqJ` at `Ty.oeq` (K12.23.C, SN-output).

Observational equality has the same SN-output eliminator closure shape as
`Ty.id`: SN of the witness plus SN preservation through `oeqJ` for any
SN base case.  The arbitrary motive wall again prevents a full
`Reducible motiveType` conclusion in the current structural-on-`Ty`
candidate.
-/
theorem Reducible.fundamental_oeqJ_at_oeq_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.oeq carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.oeqJ baseCase witness)) :=
  witnessIH.2 (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-- Fundamental case: `Term.idStrictRec` at `Ty.idStrict`
(K12.23.D, SN-output).

Strict identity adds the ambient `mode = Mode.strict` witness to the
same SN-output eliminator closure used by `Ty.id` and `Ty.oeq`.  The result
is SN of the substituted strict recursor, matching the closure stored in
`Reducible (Ty.idStrict ...)`.
-/
theorem Reducible.fundamental_idStrictRec_at_idStrict_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseCase witness)) :=
  witnessIH.2 modeIsStrict (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-! ## K12.26 reflexivity-intro fundamentals with explicit endpoint SN -/

/-- Fundamental case: `Term.refl` at `Ty.id` with an explicit endpoint
SN premise.

`Term.refl` carries a raw endpoint rather than a typed endpoint subterm, so
this lemma does not pretend to be the full structural fundamental-theorem
case.  The caller must provide SN of the substituted endpoint; from there the
weak `Ty.id` closure is discharged by raw refl SN plus generic `idJ` SN.
-/
theorem Reducible.fundamental_refl_at_id_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.id carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.refl carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.refl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.idJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.oeqRefl` at `Ty.oeq` with an explicit
endpoint SN premise.  Observational equality has the same weak-J closure
shape as `Ty.id`. -/
theorem Reducible.fundamental_oeqRefl_at_oeq_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.oeq carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.oeqRefl carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqRefl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.oeqRefl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.idStrictRefl` at `Ty.idStrict` with an
explicit endpoint SN premise.  The strict-mode eliminator closure keeps its
mode equality parameter explicit and otherwise mirrors `Term.refl`. -/
theorem Reducible.fundamental_idStrictRefl_at_idStrict_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.idStrict carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst
        (Term.idStrictRefl modeIsStrict carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.idStrictRefl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.idStrictRefl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun modeIsStrict' {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.idStrictRec_isStronglyNormalizing baseIsSN witnessIsSN⟩


end LeanFX2
