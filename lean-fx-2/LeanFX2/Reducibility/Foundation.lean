import LeanFX2.Reducibility.Classifier

/-! # LeanFX2.Reducibility.Foundation — Reducible substitution + raw foundations

Bundle of small predicates and raw-layer closure lemmas that ride
on top of the `Reducible` predicate and serve as building blocks
for the fundamental-theorem cascade:

* `ReducibleSubst` — substitution-reducibility predicate, the
  universal-quantification target of the fundamental lemma
  (K12.19).  A typed substitution is reducible when every
  per-position term it supplies is `Reducible` at the substituted
  source type.
* `IsRenamingStableReducible` / `IsRenamingStableReducibleSubst` —
  K12.20.U3 renaming-stability scaffolding for the Lam case.
  Allows the fundamental lemma to thread renaming evidence through
  body-of-lambda recursion.
* K12.19.B introducer-SN cases — base lemmas for the
  fundamental-theorem variable / literal / unit / boolTrue cases.
* K12.20.A unary-introducer SN preservation — single-subterm
  closure lemmas (lam-SN, natSucc-SN preservation).
* K12.20.B raw-level CR2 — Reducible's forward step closure at
  the raw layer (`Reducible.cr2` typed shipped at K12.20.U1).
* K12.20.U3.monotone raw weakening evidence + world-stability
  invariant — supporting infrastructure for `ReducibleSubst.lift`.

## Root status

Layer 3 metatheory leaf.  Consumed by every downstream module of
`Reducibility.*` (StableBase, NeutralSN*, TypedCR2*, Fundamental*). -/

namespace LeanFX2


/-- **K12.18/K12.19 substitution-reducibility predicate**: the
universal quantification target of the fundamental lemma cascade
(K12.19-K12.26).

A typed substitution `termSubst : TermSubst sourceCtx targetCtx sigma`
is *reducible* when every per-position typed term it supplies is
`Reducible` at the substituted-source-type / matched-raw view.

## Design (K12.19 refactor of K12.18)

K12.18's first cut packaged the typed witness existentially —
`∀ position, ∃ (term : Term ...), Reducible _ term`.  K12.19's audit
(2026-05-11) revealed the shape is wrong: the fundamental-lemma var
case proves `Reducible _ (Term.subst termSubst (Term.var position))`,
which definitionally reduces to `Reducible _ (termSubst position)`
because `Term.subst termSubst (.var position) = termSubst position`
by the var equation of `Term.subst` (LeanFX2/Term/Subst.lean:192).
But an existential `∃ w, Reducible _ w` cannot supply reducibility
of THAT specific term — eliminating the existential yields SOME
reducible `w`, not the canonical `termSubst position`.

K12.19 therefore reshapes the predicate to take a `TermSubst`
directly.  Now the canonical witness at each position IS
`termSubst position`, and `ReducibleSubst termSubst position`
states reducibility of that exact term.  The fundamental lemma's
var case becomes `substReducible position` (no rewriting, no
existential elimination).

The K12.18 commit's body is replaced — same predicate name, same
audit pin, same zero-axiom discipline, corrected shape.

## Fundamental lemma statement (K12.19-K12.26)

```
theorem Reducible.fundamental
    (term : Term sourceCtx ty raw)
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (substReducible : ReducibleSubst termSubst) :
    Reducible (ty.subst sigma) (Term.subst termSubst term)
```

Induction proceeds on `term`; each arm consumes `substReducible`'s
per-position witnesses to discharge IHs on sub-terms.  K12.19 ships
the var case (and base-leaf cases via "introducer is SN" lemmas);
K12.20-K12.26 ship the remaining arms.

## Constructors (forward-referenced, K12.20+)

* `ReducibleSubst.identity` — the identity TermSubst is reducible
  when "every variable is reducible at its declared type" holds.
  K12.20 ships the prerequisite once the per-Ty neutral-reducibility
  fact is in place.
* `ReducibleSubst.consSingleton` — extending a reducible TermSubst
  with a fresh Reducible argument (for β-reduction) yields a
  reducible TermSubst at the extended context.  Ships in K12.20
  alongside the Lam case (where it's first needed).
-/
def ReducibleSubst {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) : Prop :=
  ∀ (position : Fin scope),
    Reducible ((varType sourceCtx position).subst sigma) (termSubst position)

/-- **K12.19 fundamental-lemma var case**: applying a reducible
typed substitution to a variable term yields a reducible term at
the substituted type.

Direct unpacking of `ReducibleSubst`'s universal quantification at
the given position.  The kernel-definitional reduction
`Term.subst termSubst (.var position) ⇝ termSubst position`
(`LeanFX2/Term/Subst.lean:192`) makes the body literally
`substReducible position`.

This is the foundational base case the cascade builds on; every
later K12.20-K12.26 arm threads `substReducible` through Term-ctor
recursion, ultimately bottoming out here at variable leaves. -/
theorem Reducible.fundamental_var
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substReducible : ReducibleSubst termSubst)
    (position : Fin scope) :
    Reducible ((varType sourceCtx position).subst sigma)
              (Term.subst termSubst (Term.var position)) :=
  substReducible position

/-! ## K12.19.B introducer-SN cases

For nullary introducers (unit / boolTrue / boolFalse / natZero), the
fundamental-lemma arm reduces to "the introducer is strongly
normalizing".  Each introducer is canonical: no β/ι rule fires on
it because there's no destructor chain through a nullary head, so
`RawStep.par` reduces only via `refl` (target = source).  The
`*_inv` lemmas already shipped in `Reduction/RawParInversion.lean`
make this trivial: any step is reflexive, and `parProgress`'s
source-≠-target requirement contradicts the inversion.
-/

/-- `RawTerm.unit` is strongly normalizing.  No β/ι rule has unit
as a source, so any parallel step is `refl`; `parProgress` rules
that out. -/
theorem RawTerm.unit_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.unit : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.unit
    (fun _ parStep =>
      (parStep.2 (RawStep.par.unit_inv parStep.1).symm).elim)

/-- `RawTerm.boolTrue` is strongly normalizing. -/
theorem RawTerm.boolTrue_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.boolTrue : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.boolTrue
    (fun _ parStep =>
      (parStep.2 (RawStep.par.boolTrue_inv parStep.1).symm).elim)

/-- `RawTerm.boolFalse` is strongly normalizing. -/
theorem RawTerm.boolFalse_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.boolFalse : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.boolFalse
    (fun _ parStep =>
      (parStep.2 (RawStep.par.boolFalse_inv parStep.1).symm).elim)

/-- `RawTerm.natZero` is strongly normalizing. -/
theorem RawTerm.natZero_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.natZero : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.natZero
    (fun _ parStep =>
      (parStep.2 (RawStep.par.natZero_inv parStep.1).symm).elim)

/-- **K12.19.B unit case**: substituting through `Term.unit` yields
a reducible term at `Ty.unit`.  `Term.subst termSubst Term.unit =
Term.unit` (by Term.subst's unit equation); `Reducible Ty.unit
Term.unit` unfolds to `Term.isStronglyNormalizing Term.unit`, which
is `RawTerm.unit_isStronglyNormalizing`. -/
theorem Reducible.fundamental_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.unit (context := sourceCtx))) :=
  RawTerm.unit_isStronglyNormalizing

/-- **K12.19.B boolTrue case**: same shape as `fundamental_unit`. -/
theorem Reducible.fundamental_boolTrue
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.boolTrue (context := sourceCtx))) :=
  RawTerm.boolTrue_isStronglyNormalizing

/-- **K12.19.B boolFalse case**. -/
theorem Reducible.fundamental_boolFalse
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.boolFalse (context := sourceCtx))) :=
  RawTerm.boolFalse_isStronglyNormalizing

/-- **K12.19.B natZero case**. -/
theorem Reducible.fundamental_natZero
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.natZero (context := sourceCtx))) :=
  RawTerm.natZero_isStronglyNormalizing

/-! ## K12.20.A unary-introducer SN preservation

K12.20 (Term.lam case of the fundamental lemma) needs three
ingredients per the standard Tait/Girard cascade:

1. **SN preservation under lam** — if body is SN then `lam body`
   is SN.  Proved here as `RawTerm.lam_isStronglyNormalizing`.
2. **ReducibleSubst.singleton + lift** — extending a reducible
   TermSubst with a fresh reducible witness (for β-redex unfolding
   `(lam body) arg ⇝ body.subst0 arg`).  Blocked on CR3
   ("neutral terms are reducible at every type") — variables in
   the lifted TermSubst's positions need to be Reducible.
3. **Closure under reduction (CR2)** — Reducible closed under
   parProgress steps.  Per-Ty case split (25 arms).

K12.20.A ships ingredient (1).  K12.20.B/C ship (2)/(3) once the
neutral-reducibility chain is set up.  The full Term.lam case
follows by combining all three.
-/

/-- `RawTerm.lam body` is strongly normalizing whenever `body` is.
Proof: every `RawStep.par` from `lam body` lands at `lam bodyTarget`
with `par body bodyTarget` (`RawStep.par.lam_inv`); the `parProgress`
disequality `lam body ≠ lam bodyTarget` forces `body ≠ bodyTarget`
(by `RawTerm.lam` injectivity), so the recursive IH on `body`'s SN
witness handles the bodyTarget case. -/
theorem RawTerm.lam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    RawTerm.isStronglyNormalizing (RawTerm.lam body) := by
  induction bodyIsSN with
  | intro currentBody _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro (RawTerm.lam currentBody) ?_
    intro target progressStep
    obtain ⟨bodyTarget, targetEq, bodyStep⟩ :=
      RawStep.par.lam_inv progressStep.1
    subst targetEq
    have bodyDistinct : currentBody ≠ bodyTarget := fun bodyEq =>
      progressStep.2 (congrArg RawTerm.lam bodyEq)
    exact inductiveHypothesis bodyTarget ⟨bodyStep, bodyDistinct⟩

/-- Typed wrapper for non-dependent lambda SN preservation.

This is the SN half of the `Term.lam` fundamental case.  The full
arrow reducibility endpoint still needs the body under a lifted
substitution; that remains the `ReducibleSubst.lift` / world-weakening
blocker tracked by K12.20.U3.monotone. -/
theorem Term.lam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.lam (codomainType := codomainType) bodyTerm) :=
  RawTerm.lam_isStronglyNormalizing bodyIsSN

/-- Typed wrapper for dependent lambda SN preservation.

`Term.lamPi` projects to the same raw lambda constructor as
`Term.lam`, so the direct M04 value-SN endpoint is the same raw
closure over the body. -/
theorem Term.lamPi_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (context.cons domainType) codomainType bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing (Term.lamPi bodyTerm) :=
  RawTerm.lam_isStronglyNormalizing bodyIsSN

/-! ## K12.20.B raw-level CR2 (closure under reduction)

CR2 of Tait's three reducibility-candidate conditions: Reducible
closed under reduction.  At the raw level, this is one step removed
from SN's inductive definition — given SN of source and a progress
step source → target, the SN constructor's closure directly gives
SN of target.

CR2 at typed Reducible reduces to this raw fact for SN-direct arms
(unit / bool / nat / empty / interval / universe / tyVar / session /
effect / modal) because `Reducible Ty.X term = Term.isStronglyNormalizing
term = RawTerm.isStronglyNormalizing term.toRaw`.  The compound
arms (arrow / piTy / Σ / id / list / option / either / path / glue /
oeq / idStrict / equiv / refine / record / codata) need per-Ty
case analysis on the closure structure — those land in K12.20.B
follow-ups.
-/

/-- **K12.20.B raw CR2**: SN is preserved under parallel-progress
reduction.  Direct destructuring of the SN constructor's closure —
the closure says exactly "every progress step lands at SN target",
so we apply it to the given step. -/
theorem RawTerm.isStronglyNormalizing.step_preserves {scope : Nat}
    {source target : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source)
    (progressStep : RawStep.parProgress source target) :
    RawTerm.isStronglyNormalizing target := by
  cases sourceIsSN with
  | intro _ closure => exact closure target progressStep

/-! ## K12.20.U3.monotone raw weakening evidence

Raw strong normalization is stable under one-binder weakening.  This is
not the missing typed `Reducible.weaken` theorem: compound reducibility
also needs world-monotone closure fields.  The lemma records the raw
half of that route and is used to keep the `ReducibleSubst.lift`
blocker precise rather than speculative.
-/

/-- **K12.20.U3.monotone raw lemma**: weakening preserves raw SN.

Any progress step out of `source.weaken` lands in a weakened target by
`RawStep.par.weaken_inv`.  Substituting a dummy singleton back through
that weakened step reflects it to a progress step from `source`, so the
source SN induction supplies SN of the inner target and hence of its
weakened image. -/
theorem RawTerm.isStronglyNormalizing_weaken {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    RawTerm.isStronglyNormalizing source.weaken := by
  induction sourceIsSN with
  | intro currentSource _ sourceIH =>
      refine RawTerm.isStronglyNormalizing.intro
        currentSource.weaken ?_
      intro targetAfter progressStep
      obtain ⟨targetInner, targetEq⟩ :=
        RawStep.par.weaken_inv progressStep.1
      have singletonStep :
          RawStep.par
            (currentSource.weaken.subst
              (RawTermSubst.singleton RawTerm.unit))
            (targetAfter.subst
              (RawTermSubst.singleton RawTerm.unit)) :=
        RawStep.par.subst_par
          (fun _position => RawStep.par.refl _) progressStep.1
      have innerStep : RawStep.par currentSource targetInner := by
        rw [RawTerm.weaken_subst_singleton currentSource RawTerm.unit,
            targetEq,
            RawTerm.weaken_subst_singleton targetInner RawTerm.unit]
          at singletonStep
        exact singletonStep
      have innerDistinct : currentSource ≠ targetInner := by
        intro sourceEq
        apply progressStep.2
        rw [targetEq, sourceEq]
      rw [targetEq]
      exact sourceIH targetInner ⟨innerStep, innerDistinct⟩

/-- **K12.20.U3.monotone typed wrapper**: typed SN is stable under
one-binder weakening.

`Term.isStronglyNormalizing` is raw SN of the term index, and
`Term.weaken` shifts that raw index with `RawTerm.weaken`, so this is
the typed face of `RawTerm.isStronglyNormalizing_weaken`. -/
theorem Term.isStronglyNormalizing_weaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (sourceIsSN : Term.isStronglyNormalizing sourceTerm) :
    Term.isStronglyNormalizing (Term.weaken newType sourceTerm) :=
  RawTerm.isStronglyNormalizing_weaken sourceIsSN

/-- **K12.20.U3.monotone Reducible SN projection**: every reducible
term remains strongly normalizing after one-binder weakening.

This is the SN half of the eventual world-monotone `Reducible.weaken`.
Compound closures still need their own monotonicity fields; this theorem
keeps that blocker explicit while avoiding repeated raw-SN plumbing. -/
theorem Reducible.weaken_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (sourceReducible : Reducible sourceType sourceTerm) :
    Term.isStronglyNormalizing (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken
    (Reducible.isStronglyNormalizing sourceReducible)

/-! ## K12.20.U3.monotone world-stability invariant

The direct theorem

```
Reducible sourceType sourceTerm →
Reducible sourceType.weaken (Term.weaken newType sourceTerm)
```

is not derivable from the current non-Kripke candidate shape at
function-like types.  Already at `Ty.arrow`, the old closure accepts
arguments in the old context, while the weakened closure must quantify
over arbitrary arguments in the extended context.

`IsRenamingStableReducible` records the missing invariant explicitly:
a term is stable when every injective typed renaming of it is reducible
in the target world.  The injectivity premise is load-bearing: the
raw-step reflection API (`RawStep.par.rename_inj_inv`) only reflects
reducts out of renamed terms through injective renamings, and Phase B
only needs future-world extensions such as one-step weakening.
One-step weakening is then just the canonical `TermRenaming.weakenStep`
instance plus `RawRenaming.weaken_injective`.  This is intentionally a
separate predicate for Phase B: it does not retrofit `Reducible`, and it
does not hide the arrow/world-monotonicity proof obligation.
-/

/-- A term is reducible in every injective typed-renamed future world. -/
def IsRenamingStableReducible
    {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    (sourceType : Ty level sourceScope)
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) : Prop :=
  ∀ {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (_rhoIsInjective : ∀ positionA positionB,
      rho positionA = rho positionB → positionA = positionB)
    (termRenaming : TermRenaming sourceCtx targetCtx rho),
    Reducible (sourceType.rename rho) (Term.rename termRenaming sourceTerm)

/-- Renaming-stable reducibility specializes to one-binder weakening. -/
theorem IsRenamingStableReducible.weaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (sourceIsStable : IsRenamingStableReducible sourceType sourceTerm) :
    Reducible sourceType.weaken (Term.weaken newType sourceTerm) :=
  sourceIsStable RawRenaming.weaken_injective
    (TermRenaming.weakenStep context newType)

/-- A typed substitution is renaming-stable pointwise. -/
def IsRenamingStableReducibleSubst
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) : Prop :=
  ∀ position,
    IsRenamingStableReducible
      ((varType sourceCtx position).subst sigma) (termSubst position)

/-- Pointwise renaming-stable substitutions give the old-variable
weakening premise used by `TermSubst.lift` before its unavoidable type
commute cast. -/
theorem IsRenamingStableReducibleSubst.weaken_position
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    (newSourceType : Ty level sourceScope)
    (position : Fin sourceScope) :
    Reducible ((varType sourceCtx position).subst sigma).weaken
      (Term.weaken (newSourceType.subst sigma) (termSubst position)) :=
  IsRenamingStableReducible.weaken
    (newType := newSourceType.subst sigma)
    (substIsStable position)

/-- A typed term is renaming-stable strongly normalizing when its raw
projection remains strongly normalizing in every injective typed-renamed
future world.

Companion to `IsRenamingStableReducible` for fundamental-theorem cases
whose conclusion is SN rather than Reducible (the J-style eliminators at
`Ty.id` / `Ty.oeq` / `Ty.idStrict` whose motive is an arbitrary outer Ty).
The conclusion is rebuilt at each renamed world by re-applying the raw
SN combinator (e.g. `RawTerm.idJ_isStronglyNormalizing`) to subterm IHs
extracted from `IsRenamingStableReducible` witnesses — no
`RawTerm.isStronglyNormalizing_rename` infrastructure is required. -/
def IsRenamingStableIsSN
    {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) : Prop :=
  ∀ {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (_rhoIsInjective : ∀ positionA positionB,
      rho positionA = rho positionB → positionA = positionB)
    (termRenaming : TermRenaming sourceCtx targetCtx rho),
    Term.isStronglyNormalizing (Term.rename termRenaming sourceTerm)

/-- On SN-direct candidate arms, renaming-stable strong normalization
recovers renaming-stable reducibility.

This is the stable analogue of
`Reducible.of_isStronglyNormalizing_when_SNDirect`: callers prove the
raw SN transport once, while the classifier discharges the reducibility
candidate at every renamed world. -/
theorem IsRenamingStableReducible.of_stableSN_when_SNDirect
    {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (sourceTypeIsSNDirect : Reducible.IsSNDirect sourceType)
    (sourceTermIsStableSN : IsRenamingStableIsSN sourceTerm) :
    IsRenamingStableReducible sourceType sourceTerm := by
  intro _targetScope _targetCtx _rho rhoIsInjective termRenaming
  exact Reducible.of_isStronglyNormalizing_when_SNDirect
    (Reducible.IsSNDirect.rename sourceTypeIsSNDirect)
    (sourceTermIsStableSN rhoIsInjective termRenaming)


end LeanFX2
