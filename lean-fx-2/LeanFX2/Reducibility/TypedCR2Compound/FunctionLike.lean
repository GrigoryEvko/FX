import LeanFX2.Reducibility.TypedCR2Compound.IdentityLambda

/-! # LeanFX2.Reducibility.TypedCR2Compound.FunctionLike

K12.20.F through K12.20.L: typed CR2 lift for the function-like
and inductive compound arms.

* `Ty.arrow` (K12.20.F) — strong app-closure
* `Ty.piTy` (K12.20.G) — SN-output compound
* `Ty.sigmaTy` (K12.20.H) — asymmetric fst/snd closure
* `Ty.id` (K12.20.I) — SN-output idJ compound
* `Ty.listType` (K12.20.J) — SN-output listElim compound
* `Ty.optionType` (K12.20.K) — weak-optionMatch closure
* `Ty.eitherType` (K12.20.L) — symmetric eitherMatch closure

## Root status

Layer 3 metatheory leaf.  Second slice of the K12.20.U4 compound
cascade — function-like + parametric inductive families. -/

namespace LeanFX2


/-! ## K12.20.F typed CR2 lift for compound Reducible arms — Ty.arrow

The first of 15 compound-arm CR2 lemmas.  Unlike the 10 SN-direct
arms (K12.20.D), compound arms have closure structure beyond pure SN
that must also be preserved under reduction.

For `Ty.arrow A B`, `Reducible` says: SN(f) ∧ (∀ arg, Reducible A arg
→ Reducible B (app f arg)).  Preserving this under f → f' requires:
1. SN(f'), via K12.20.B's raw `step_preserves` on the SN conjunct.
2. ∀ arg, Reducible A arg → Reducible B (app f' arg).  Given
   `Reducible B (app f arg)` (from source's closure), and step
   `app f arg → app f' arg` (via RawStep.par.app + refl on arg),
   the new closure conclusion follows from CR2 at codomain — the
   recursive ingredient supplied as `codomainCR2`.

Per the warrior-mentality discipline of CLAUDE.md, K12.20.F ships
the arrow case taking `codomainCR2` as an explicit hypothesis rather
than wiring up structural recursion on Ty here.  This keeps the
proof atomic and one-shot.  K12.20.G+ ship the remaining 14
compound arms, each with the same shape (recursion-hypothesis
taken as argument).  The final combined `Reducible.step_preserves`
will be a structurally-recursive bundle wiring all 25 arms together;
its body will invoke each per-arm helper at the right recursive
position.
-/

/-- **K12.20.F arrow arm**: Reducible at `Ty.arrow domain codomain`
is preserved under raw `parProgress` reduction.  Body: SN preserved
via K12.20.B, closure preserved via codomainCR2 + raw app-cong. -/
theorem Reducible.step_preserves_arrow
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.arrow domainType codomainType) sourceRaw}
    {target : Term context (Ty.arrow domainType codomainType) targetRaw}
    (sourceReducible : Reducible (Ty.arrow domainType codomainType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw)
    (codomainCR2 :
        ∀ {sourceRaw' targetRaw' : RawTerm scope}
          {source' : Term context codomainType sourceRaw'}
          {target' : Term context codomainType targetRaw'},
          Reducible codomainType source' →
          RawStep.parProgress sourceRaw' targetRaw' →
          Reducible codomainType target') :
    Reducible (Ty.arrow domainType codomainType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argRaw argTerm argReducible
    have appStep : RawStep.parProgress
        (RawTerm.app sourceRaw argRaw) (RawTerm.app targetRaw argRaw) := by
      refine ⟨RawStep.par.app rawStep.1 (RawStep.par.refl argRaw), ?_⟩
      intro appEq
      apply rawStep.2
      injection appEq
    exact codomainCR2 (sourceReducible.2 argTerm argReducible) appStep

/-! ## K12.20.G typed CR2 lift — Ty.piTy SN-output compound arm

Second compound-arm CR2 lemma.  `Ty.piTy` ships an **SN-output
closure** in K12.6:

```
Reducible (Ty.piTy A B) f =
  SN(f) ∧ ∀ arg, Reducible A arg → SN(Term.appPi f arg)
```

The eliminator output is `SN(appPi f arg)` not `Reducible
codomain (appPi f arg)`.  Consequently, CR2 for piTy needs NO
recursive codomainCR2 hypothesis — both SN preservation (the SN
conjunct) and the eliminator-output closure are pure-SN
preservation, both discharged by K12.20.B's raw `step_preserves`.
This is the simplest compound-arm CR2 of the 15.

Term.appPi's raw projection IS `RawTerm.app` (per Term.lean:127,
`Term.appPi : Term ctx (cod.subst0 dom arg) (RawTerm.app f a)`),
not a separate `RawTerm.appPi`.  So the same `RawStep.par.app`
cong rule we used in K12.20.F applies here.
-/

/-- **K12.20.G piTy arm**: weak-closure CR2 for `Ty.piTy`.  Both
SN-of-functionTerm and SN-of-appPi-result are preserved by the same
raw `step_preserves`.  Distinctness on app via ctor injectivity, same
as K12.20.F. -/
theorem Reducible.step_preserves_piTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.piTy domainType codomainType) sourceRaw}
    {target : Term context (Ty.piTy domainType codomainType) targetRaw}
    (sourceReducible :
        Reducible (Ty.piTy domainType codomainType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.piTy domainType codomainType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argRaw argTerm argReducible
    have appStep : RawStep.parProgress
        (RawTerm.app sourceRaw argRaw) (RawTerm.app targetRaw argRaw) := by
      refine ⟨RawStep.par.app rawStep.1 (RawStep.par.refl argRaw), ?_⟩
      intro appEq
      apply rawStep.2
      injection appEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 argTerm argReducible) appStep

/-! ## K12.20.H typed CR2 lift — Ty.sigmaTy asymmetric-closure compound arm

Third compound-arm CR2 lemma.  `Ty.sigmaTy` ships an **asymmetric
closure** in K12.7 (the second conjunct is full Reducible on the
fst projection because `firstType` IS a strict sub-Ty of
`Ty.sigmaTy firstType secondType` and structural recursion on
Ty admits it; the third conjunct is weak SN on snd, because
`secondType.subst0 firstType (RawTerm.fst pairRaw)` is a
substituted Ty — same substituted-codomain wall as K12.6
piTy):

```
Reducible (Ty.sigmaTy A B) p =
  SN(p) ∧ Reducible A (Term.fst p) ∧ SN(Term.snd p)
```

The three-conjunct shape demands three independent preservation
discharges under one raw-progress step:

* **SN(p)**: pure-SN preservation, K12.20.B's raw
  `step_preserves` handles it directly.
* **Reducible A (fst p)**: needs `firstTypeCR2` hypothesis
  threaded through (the structural-recursion-on-Ty bundling
  comes later when all 15 compound CR2 arms ship as one
  bundle).  The fst-cong step lifts `rawStep` via
  `RawStep.par.fst`; distinctness via `injection` on
  `RawTerm.fst.injEq` (ctor injectivity, propext-free).
* **SN(snd p)**: pure-SN preservation again; snd-cong step
  via `RawStep.par.snd`, distinctness via `injection` on
  `RawTerm.snd.injEq`.

Term.fst's raw projection IS `RawTerm.fst` (per Term.lean:140),
Term.snd's IS `RawTerm.snd` (per Term.lean:145).  So the cong
rules `RawStep.par.fst` and `RawStep.par.snd` apply directly to
typed projections.
-/

/-- **K12.20.H sigmaTy arm**: asymmetric-closure CR2 for
`Ty.sigmaTy`.  Takes `firstTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the smaller `firstType`
sub-Ty — supplied externally per the per-arm decomposition; the
unified structurally-recursive bundling ships after all 15
compound-arm lemmas land).  Both SN conjuncts (pair + snd) are
pure-SN preservation; the middle full-Reducible conjunct uses
firstTypeCR2 with fst-cong. -/
theorem Reducible.step_preserves_sigmaTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.sigmaTy firstType secondType) sourceRaw}
    {target : Term context (Ty.sigmaTy firstType secondType) targetRaw}
    (firstTypeCR2 :
        ∀ {fstSourceRaw fstTargetRaw : RawTerm scope}
          {fstSource : Term context firstType fstSourceRaw}
          {fstTarget : Term context firstType fstTargetRaw},
          Reducible firstType fstSource →
          RawStep.parProgress fstSourceRaw fstTargetRaw →
          Reducible firstType fstTarget)
    (sourceReducible :
        Reducible (Ty.sigmaTy firstType secondType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.sigmaTy firstType secondType) target := by
  refine ⟨?_, ?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have fstStep : RawStep.parProgress
        (RawTerm.fst sourceRaw) (RawTerm.fst targetRaw) := by
      refine ⟨RawStep.par.fst rawStep.1, ?_⟩
      intro fstEq
      apply rawStep.2
      injection fstEq
    exact firstTypeCR2 sourceReducible.2.1 fstStep
  · have sndStep : RawStep.parProgress
        (RawTerm.snd sourceRaw) (RawTerm.snd targetRaw) := by
      refine ⟨RawStep.par.snd rawStep.1, ?_⟩
      intro sndEq
      apply rawStep.2
      injection sndEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.2.2 sndStep

/-! ## K12.20.I typed CR2 lift — Ty.id SN-output idJ compound arm

Fourth compound-arm CR2 lemma.  `Ty.id` ships an **SN-output idJ
closure** in K12.9:

```
Reducible (Ty.id A x y) w =
  SN(w) ∧ ∀ {M : Ty} {br} (bc : Term ctx M br),
            SN(bc) → SN(Term.idJ bc w)
```

The eliminator output is `SN(Term.idJ bc w)` not full
`Reducible motiveType (Term.idJ bc w)`.  Consequently, CR2 for
`Ty.id` needs NO recursive motiveTypeCR2 hypothesis — both
SN-of-witness and SN-of-idJ-result are pure-SN preservation,
both discharged by K12.20.B's raw `step_preserves`.  Same
SN-output pattern as K12.20.G piTy.

Term.idJ's raw projection IS `RawTerm.idJ baseRaw witnessRaw`
(per Term.lean:245), and `RawStep.par.idJ` takes paired par
steps on baseRaw + witnessRaw (per RawPar.lean:179).  For the
CR2 step, baseCase is unchanged across source/target, so the
baseRaw side gets `RawStep.par.refl baseRaw` while the witness
side gets `rawStep.1`.
-/

/-- **K12.20.I id arm**: SN-output idJ closure CR2 for `Ty.id`.  Both
SN-of-witness and SN-of-idJ-result are preserved by the same
raw `step_preserves`.  Distinctness on idJ via ctor injectivity
(injection extracts witness-side raw equality, contradicts
rawStep.2). -/
theorem Reducible.step_preserves_id
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.id carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.id carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.id carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.id carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType baseRaw baseCase baseSN
    have idJStep : RawStep.parProgress
        (RawTerm.idJ baseRaw sourceRaw)
        (RawTerm.idJ baseRaw targetRaw) := by
      refine ⟨RawStep.par.idJ (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro idJEq
      apply rawStep.2
      injection idJEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 baseCase baseSN) idJStep

/-! ## K12.20.J typed CR2 lift — Ty.listType SN-output elim compound arm

Fifth compound-arm CR2 lemma.  `Ty.listType` ships an **SN-output elim
closure** in K12.8: the eliminator output is plain SN, not full
Reducible.  Closure shape (per
Reducibility.lean:404):

```
Reducible (Ty.listType A) xs =
  SN(xs) ∧ ∀ {M} {nilRaw consRaw} (nilBranch consBranch),
    SN(nilBranch) → SN(consBranch) →
    (∀ head tail, Reducible A head → SN(tail) →
                  SN(consBranch head tail)) →
    SN(listElim xs nilBranch consBranch)
```

The branch-SN and application-closure hypotheses are propagated
unchanged by sourceReducible.2 — CR2 needs NO recursive
elementTypeCR2 hypothesis because the eliminator output is plain SN,
not Reducible.  Same weak-closure pattern as K12.20.G piTy and
K12.20.I id.

Term.listElim shares raw form `RawTerm.listElim scrutineeRaw
nilRaw consRaw` (per Term.lean:200); `RawStep.par.listElim`
takes paired par steps on all three components (per RawPar.lean:
120).  For CR2, branches are fixed across source/target, so the
nilRaw/consRaw sides get `par.refl` while scrutinee gets
`rawStep.1`.
-/

/-- **K12.20.J listType arm**: weak-elim-closure CR2 for
`Ty.listType`.  Both SN-of-listTerm and SN-of-listElim-result are
preserved by the same raw `step_preserves`.  Distinctness on
listElim via ctor injectivity (injection extracts scrutinee-side
raw equality, contradicts rawStep.2). -/
theorem Reducible.step_preserves_listType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.listType elementType) sourceRaw}
    {target : Term context (Ty.listType elementType) targetRaw}
    (sourceReducible :
        Reducible (Ty.listType elementType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.listType elementType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType nilRaw consRaw nilBranch consBranch nilSN consSN consApplied
    have listElimStep : RawStep.parProgress
        (RawTerm.listElim sourceRaw nilRaw consRaw)
        (RawTerm.listElim targetRaw nilRaw consRaw) := by
      refine ⟨RawStep.par.listElim rawStep.1
          (RawStep.par.refl nilRaw) (RawStep.par.refl consRaw), ?_⟩
      intro listElimEq
      apply rawStep.2
      injection listElimEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 nilBranch consBranch nilSN consSN consApplied)
      listElimStep

/-! ## K12.20.K typed CR2 lift — Ty.optionType weak-elim-closure compound arm

Sixth compound-arm CR2 lemma.  `Ty.optionType` ships a **weak
elim closure** in K12.8, cleanest of the three K12.8 parametric
arms: someBranch's type matches K12.6 piTy weak shape exactly
when restricted to elementType.  Closure shape (per
Reducibility.lean:426):

```
Reducible (Ty.optionType A) o =
  SN(o) ∧ ∀ {M} {noneRaw someRaw} (noneBranch someBranch),
    SN(noneBranch) → SN(someBranch) →
    (∀ v, Reducible A v → SN(Term.app someBranch v)) →
    SN(optionMatch o noneBranch someBranch)
```

Same mechanical shape as K12.20.J listType — eliminator output
is plain SN, NO recursive elementTypeCR2 hypothesis needed.
Term.optionMatch raw form is `RawTerm.optionMatch scrutineeRaw
noneRaw someRaw` (per Term.lean:216); `RawStep.par.optionMatch`
takes triple par steps (per RawPar.lean:136).  For CR2 the
branches use `par.refl` while scrutinee gets `rawStep.1`.
-/

/-- **K12.20.K optionType arm**: weak-elim-closure CR2 for
`Ty.optionType`.  Both SN-of-optionTerm and SN-of-optionMatch-
result are preserved by the same raw `step_preserves`.
Distinctness on optionMatch via ctor injectivity. -/
theorem Reducible.step_preserves_optionType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.optionType elementType) sourceRaw}
    {target : Term context (Ty.optionType elementType) targetRaw}
    (sourceReducible :
        Reducible (Ty.optionType elementType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.optionType elementType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType noneRaw someRaw noneBranch someBranch noneSN someSN someApplied
    have optionMatchStep : RawStep.parProgress
        (RawTerm.optionMatch sourceRaw noneRaw someRaw)
        (RawTerm.optionMatch targetRaw noneRaw someRaw) := by
      refine ⟨RawStep.par.optionMatch rawStep.1
          (RawStep.par.refl noneRaw) (RawStep.par.refl someRaw), ?_⟩
      intro optionMatchEq
      apply rawStep.2
      injection optionMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 noneBranch someBranch noneSN someSN someApplied)
      optionMatchStep

/-! ## K12.20.L typed CR2 lift — Ty.eitherType symmetric SN-output elim compound arm

Seventh compound-arm CR2 lemma.  `Ty.eitherType` ships a
**symmetric SN-output elim closure** in K12.8: both `leftType` and
`rightType` are strict sub-Ty of `Ty.eitherType leftType
rightType`, so each branch's arrow shape matches K12.6 piTy SN-output
closure per side.  Closure shape (per Reducibility.lean:446):

```
Reducible (Ty.eitherType A B) e =
  SN(e) ∧ ∀ {M} {leftRaw rightRaw} (leftBranch rightBranch),
    SN(leftBranch) → SN(rightBranch) →
    (∀ v, Reducible A v → SN(Term.app leftBranch v)) →
    (∀ v, Reducible B v → SN(Term.app rightBranch v)) →
    SN(eitherMatch e leftBranch rightBranch)
```

Same mechanical shape as K12.20.J listType / K12.20.K
optionType — eliminator output is plain SN, NO recursive
leftTypeCR2 / rightTypeCR2 hypothesis needed.  Term.eitherMatch
raw form is `RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw`
(per Term.lean:234); `RawStep.par.eitherMatch` takes triple par
steps (per RawPar.lean:159).  For CR2 the branches use
`par.refl` while scrutinee gets `rawStep.1`.
-/

/-- **K12.20.L eitherType arm**: symmetric-weak-elim-closure CR2
for `Ty.eitherType`.  Both SN-of-eitherTerm and SN-of-eitherMatch-
result are preserved by the same raw `step_preserves`.
Distinctness on eitherMatch via ctor injectivity. -/
theorem Reducible.step_preserves_eitherType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.eitherType leftType rightType) sourceRaw}
    {target : Term context (Ty.eitherType leftType rightType) targetRaw}
    (sourceReducible :
        Reducible (Ty.eitherType leftType rightType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.eitherType leftType rightType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftSN rightSN leftApplied rightApplied
    have eitherMatchStep : RawStep.parProgress
        (RawTerm.eitherMatch sourceRaw leftRaw rightRaw)
        (RawTerm.eitherMatch targetRaw leftRaw rightRaw) := by
      refine ⟨RawStep.par.eitherMatch rawStep.1
          (RawStep.par.refl leftRaw) (RawStep.par.refl rightRaw), ?_⟩
      intro eitherMatchEq
      apply rawStep.2
      injection eitherMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 leftBranch rightBranch leftSN rightSN
        leftApplied rightApplied)
      eitherMatchStep


end LeanFX2
