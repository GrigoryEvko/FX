import LeanFX2.Reducibility.TypedCR2Compound.FunctionLike

/-! # LeanFX2.Reducibility.TypedCR2Compound.Eliminators

K12.20.M through K12.20.T: typed CR2 lift for the eliminator
compound arms.

* `Ty.path` (K12.20.M) — strong pathApp-closure
* `Ty.glue` (K12.20.N) — strong glueElim-closure
* `Ty.oeq` (K12.20.O) — SN-output oeqJ compound
* `Ty.idStrict` (K12.20.P) — weak idStrictRec-closure
* `Ty.equiv` (K12.20.Q) — strong equivApp-closure
* `Ty.refine` (K12.20.R) — strong refineElim-closure
* `Ty.record` (K12.20.S) — strong recordProj-closure
* `Ty.codata` (K12.20.T) — strong codataDest-closure

## Root status

Layer 3 metatheory leaf.  Third slice of the K12.20.U4 compound
cascade — eliminator/projection families. -/

namespace LeanFX2


/-! ## K12.20.M typed CR2 lift — Ty.path strong-pathApp-closure compound arm

Eighth compound-arm CR2 lemma.  `Ty.path` ships a **strong
pathApp closure** in K12.12: the eliminator produces a full
`Reducible carrier _` verdict (NOT plain SN), because `carrier`
is a strict sub-Ty of `Ty.path carrier left right` and the
structural-recursion-on-Ty checker admits `Reducible carrier`
recursion.  Closure shape (per Reducibility.lean:476):

```
Reducible (Ty.path A x y) p =
  SN(p) ∧ ∀ (modeIsUnivalent : mode = Mode.univalent)
            {intervalRaw} (intervalTerm : Term context Ty.interval intervalRaw),
    SN(intervalTerm) →
    Reducible A (Term.pathApp modeIsUnivalent p intervalTerm)
```

This is the **strong** pattern from K12.20.F arrow: full
Reducible eliminator output forces an explicit `carrierCR2`
hypothesis to lift Reducible across the cong step.  The interval
side stays SN-only (Ty.interval is a sibling Ty constructor, not
a strict sub-Ty of Ty.path — K12.4's closed-leaf arm gives
`Reducible Ty.interval _ = Term.isStronglyNormalizing _`
propositionally, so SN demotion preserves Tait semantics).

Term.pathApp raw form is `RawTerm.pathApp pathRaw intervalRaw`
(per Term.lean:355); `RawStep.par.pathAppCong` takes paired par
steps (per RawPar.lean:558).  For CR2, interval side gets
`par.refl` while path side gets `rawStep.1`.  Distinctness via
`injection` on RawTerm.pathApp.injEq.
-/

/-- **K12.20.M path arm**: strong-pathApp-closure CR2 for
`Ty.path`.  Takes `carrierCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`carrierType`).  SN-of-pathTerm preserved by raw `step_preserves`;
the full-Reducible pathApp conjunct lifted via carrierCR2 over
the pathAppCong step. -/
theorem Reducible.step_preserves_path
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) targetRaw}
    (carrierCR2 :
        ∀ {pathAppSourceRaw pathAppTargetRaw : RawTerm scope}
          {pathAppSource : Term context carrierType pathAppSourceRaw}
          {pathAppTarget : Term context carrierType pathAppTargetRaw},
          Reducible carrierType pathAppSource →
          RawStep.parProgress pathAppSourceRaw pathAppTargetRaw →
          Reducible carrierType pathAppTarget)
    (sourceReducible :
        Reducible (Ty.path carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.path carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsUnivalent intervalRaw intervalTerm intervalSN
    have pathAppStep : RawStep.parProgress
        (RawTerm.pathApp sourceRaw intervalRaw)
        (RawTerm.pathApp targetRaw intervalRaw) := by
      refine ⟨RawStep.par.pathAppCong rawStep.1 (RawStep.par.refl intervalRaw), ?_⟩
      intro pathAppEq
      apply rawStep.2
      injection pathAppEq
    exact carrierCR2
      (sourceReducible.2 modeIsUnivalent intervalTerm intervalSN) pathAppStep

/-! ## K12.20.N typed CR2 lift — Ty.glue strong-glueElim-closure compound arm

Ninth compound-arm CR2 lemma.  `Ty.glue` ships a **strong
glueElim closure** in K12.12: the eliminator produces a full
`Reducible baseType _` verdict (NOT plain SN), because
`baseType` is a strict sub-Ty of `Ty.glue baseType
boundaryWitness` and the structural-recursion-on-Ty checker
admits `Reducible baseType` recursion.  Closure shape (per
Reducibility.lean:491):

```
Reducible (Ty.glue baseType _) gluedValue =
  SN(gluedValue) ∧
  ∀ (modeIsUnivalent : mode = Mode.univalent),
    Reducible baseType
      (Term.glueElim modeIsUnivalent gluedValue)
```

This is the **strong** pattern (mirror of K12.20.F arrow and
K12.20.M path), but **even simpler than path** — no quantifier
over an interval argument, no SN-on-arg conjunct.  Just the
mode-univalent witness binder.  The proof carries an explicit
`baseTypeCR2` hypothesis to lift Reducible across the cong step.

Term.glueElim raw form is `RawTerm.glueElim gluedRaw` (per
Term.lean:373); `RawStep.par.glueElimCong` is a 1-arg cong rule
taking just `gluedRawStep` (per RawPar.lean:633-638).  No paired
substituent: glueElim has only one argument.  Distinctness via
`injection` on `RawTerm.glueElim.injEq`.
-/

/-- **K12.20.N glue arm**: strong-glueElim-closure CR2 for
`Ty.glue`.  Takes `baseTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`baseType`).  SN-of-gluedTerm preserved by raw `step_preserves`;
the full-Reducible glueElim conjunct lifted via baseTypeCR2 over
the glueElimCong step.  Simpler than K12.20.M path — single-
ctor cong rule, no interval binder. -/
theorem Reducible.step_preserves_glue
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.glue baseType boundaryWitness) sourceRaw}
    {target : Term context (Ty.glue baseType boundaryWitness) targetRaw}
    (baseTypeCR2 :
        ∀ {glueElimSourceRaw glueElimTargetRaw : RawTerm scope}
          {glueElimSource : Term context baseType glueElimSourceRaw}
          {glueElimTarget : Term context baseType glueElimTargetRaw},
          Reducible baseType glueElimSource →
          RawStep.parProgress glueElimSourceRaw glueElimTargetRaw →
          Reducible baseType glueElimTarget)
    (sourceReducible :
        Reducible (Ty.glue baseType boundaryWitness) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.glue baseType boundaryWitness) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsUnivalent
    have glueElimStep : RawStep.parProgress
        (RawTerm.glueElim sourceRaw)
        (RawTerm.glueElim targetRaw) := by
      refine ⟨RawStep.par.glueElimCong rawStep.1, ?_⟩
      intro glueElimEq
      apply rawStep.2
      injection glueElimEq
    exact baseTypeCR2
      (sourceReducible.2 modeIsUnivalent) glueElimStep

/-! ## K12.20.O typed CR2 lift — Ty.oeq SN-output oeqJ compound arm

Tenth compound-arm CR2 lemma.  `Ty.oeq` (HoTT observational
equality) ships an **SN-output oeqJ closure** in K12.10: the
eliminator output is plain SN, not full `Reducible motiveType _`.
The arbitrary `motiveType` is NOT a strict sub-Ty of
`Ty.oeq carrier left right` — structural-recursion-on-Ty would
not admit a `Reducible motiveType` recursive call (K12.6 / K12.9
SN-output pattern, identical to K12.20.I for Ty.id and the parametric
inductive SN-output elim arms K12.20.J/K/L).  Closure shape (per
Reducibility.lean:503-509):

```
Reducible (Ty.oeq _ _ _) witness =
  SN(witness) ∧
  ∀ {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw),
    SN baseCase →
    SN (Term.oeqJ baseCase witness)
```

SN-output closure → **no recursive hypothesis needed**.  Eliminator
output is SN, so the cong lift goes via
`RawTerm.isStronglyNormalizing.step_preserves` directly.

Term.oeqJ raw form is `RawTerm.oeqJ baseRaw witnessRaw` (per
Term.lean:261); `RawStep.par.oeqJCong` takes paired par steps
on baseCase + witness (per RawPar.lean:705-710).  For CR2 the
baseCase rides `par.refl` (not progressing); witness rides
`rawStep.1`.  Distinctness via `injection` on
`RawTerm.oeqJ.injEq`.
-/

/-- **K12.20.O oeq arm**: SN-output oeqJ closure CR2 for `Ty.oeq`.
No recursive hypothesis needed (SN-output closure produces SN,
not Reducible).  SN-of-witnessTerm preserved by raw
`step_preserves`; SN-of-oeqJ-applied lifted via raw
`step_preserves` over the oeqJCong step.  Mirror of K12.20.I id
arm; differs only in the raw cong rule name (`oeqJCong` rather
than `idJ`). -/
theorem Reducible.step_preserves_oeq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.oeq carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType baseRaw baseCase baseSN
    have oeqJStep : RawStep.parProgress
        (RawTerm.oeqJ baseRaw sourceRaw)
        (RawTerm.oeqJ baseRaw targetRaw) := by
      refine ⟨RawStep.par.oeqJCong (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro oeqJEq
      apply rawStep.2
      injection oeqJEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 baseCase baseSN) oeqJStep

/-! ## K12.20.P typed CR2 lift — Ty.idStrict weak-idStrictRec-closure compound arm

Eleventh compound-arm CR2 lemma.  `Ty.idStrict` (strict identity
type) ships a **weak idStrictRec closure** in K12.10: the
eliminator output is plain SN, not full `Reducible motiveType _`.
The arbitrary `motiveType` is NOT a strict sub-Ty of
`Ty.idStrict carrier left right` — structural-recursion-on-Ty
cannot recurse `Reducible motiveType`.  Same K12.6 / K12.9 weak-J
pattern as K12.20.I (id) and K12.20.O (oeq).

Closure shape (per Reducibility.lean:517-525):

```
Reducible (Ty.idStrict _ _ _) witness =
  SN(witness) ∧
  ∀ (modeIsStrict : mode = Mode.strict)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw),
    SN baseCase →
    SN (Term.idStrictRec modeIsStrict baseCase witness)
```

When `mode ≠ Mode.strict` the binder is uninhabited and the
inner ∀ is vacuous (closure reduces to SN(witness) alone) —
matches the conditional-elim K12.10 idStrict pattern.

Weak closure → **no recursive hypothesis needed**.  Eliminator
output is SN, so the cong lift goes via
`RawTerm.isStronglyNormalizing.step_preserves` directly.

Term.idStrictRec raw form is `RawTerm.idStrictRec baseRaw
witnessRaw` (per Term.lean:294) — the `modeIsStrict` proof lives
at the typed level only.  `RawStep.par.idStrictRecCong` takes
paired par steps on baseCase + witness (per RawPar.lean:724-729).
For CR2 the baseCase rides `par.refl`; witness rides `rawStep.1`.
Distinctness via `injection` on `RawTerm.idStrictRec.injEq`.
-/

/-- **K12.20.P idStrict arm**: SN-output idStrictRec closure CR2 for
`Ty.idStrict`.  No recursive hypothesis needed (SN-output
closure produces SN, not Reducible).  Identical structure to
K12.20.O oeq, with extra `modeIsStrict` binder threaded through
the per-mode quantifier in the closure body. -/
theorem Reducible.step_preserves_idStrict
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.idStrict carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsStrict motiveType baseRaw baseCase baseSN
    have idStrictRecStep : RawStep.parProgress
        (RawTerm.idStrictRec baseRaw sourceRaw)
        (RawTerm.idStrictRec baseRaw targetRaw) := by
      refine ⟨RawStep.par.idStrictRecCong
        (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro idStrictRecEq
      apply rawStep.2
      injection idStrictRecEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 modeIsStrict baseCase baseSN) idStrictRecStep

/-! ## K12.20.Q typed CR2 lift — Ty.equiv strong-equivApp-closure compound arm

Twelfth compound-arm CR2 lemma.  `Ty.equiv carrierA carrierB`
(type equivalence) ships a **strong equivApp closure** in K12.11:
the eliminator produces full `Reducible carrierB (Term.equivApp
equivTerm argumentTerm)`.  BOTH `carrierA` and `carrierB` are
strict sub-Ty of `Ty.equiv carrierA carrierB` — structural-
recursion-on-Ty admits `Reducible carrierA` AND `Reducible
carrierB` recursive calls (K12.5 RC.arrow shape).

Closure shape (per Reducibility.lean:537-542):

```
Reducible (Ty.equiv carrierA carrierB) equivTerm =
  SN(equivTerm) ∧
  ∀ {argumentRaw : RawTerm scope}
    (argumentTerm : Term context carrierA argumentRaw),
    Reducible carrierA argumentTerm →
    Reducible carrierB
      (Term.equivApp equivTerm argumentTerm)
```

Structurally identical to K12.20.F arrow: `SN(f) ∧ ∀ arg,
Reducible A arg → Reducible B (Term.app f arg)`.  The argument
side stays at carrierA — it rides `par.refl` through the cong
step and does NOT progress.  Only `equivTerm` progresses; the
eliminator output is at carrierB, so the proof carries an
explicit `carrierBCR2` hypothesis to lift Reducible over the
equivAppCong step.  No `carrierACR2` is needed — that side never
moves in this cong step.

Term.equivApp raw form is `RawTerm.equivApp equivRaw argumentRaw`
(per Term.lean:727); `RawStep.par.equivAppCong` takes paired par
steps on equiv + argument (per RawPar.lean:738-743).  For CR2
the equiv side rides `rawStep.1`; argument side rides
`par.refl`.  Distinctness via `injection` on
`RawTerm.equivApp.injEq`.
-/

/-- **K12.20.Q equiv arm**: strong-equivApp-closure CR2 for
`Ty.equiv`.  Takes `carrierBCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`carrierB`).  SN-of-equivTerm preserved by raw `step_preserves`;
the full-Reducible equivApp conjunct lifted via carrierBCR2 over
the equivAppCong step.  Structurally identical to K12.20.F arrow;
differs only in raw cong rule name (`equivAppCong` vs `app`) and
ctor (`equivApp` vs `app`). -/
theorem Reducible.step_preserves_equiv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.equiv carrierA carrierB) sourceRaw}
    {target : Term context (Ty.equiv carrierA carrierB) targetRaw}
    (carrierBCR2 :
        ∀ {equivAppSourceRaw equivAppTargetRaw : RawTerm scope}
          {equivAppSource : Term context carrierB equivAppSourceRaw}
          {equivAppTarget : Term context carrierB equivAppTargetRaw},
          Reducible carrierB equivAppSource →
          RawStep.parProgress equivAppSourceRaw equivAppTargetRaw →
          Reducible carrierB equivAppTarget)
    (sourceReducible :
        Reducible (Ty.equiv carrierA carrierB) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.equiv carrierA carrierB) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argumentRaw argumentTerm argumentReducible
    have equivAppStep : RawStep.parProgress
        (RawTerm.equivApp sourceRaw argumentRaw)
        (RawTerm.equivApp targetRaw argumentRaw) := by
      refine ⟨RawStep.par.equivAppCong rawStep.1
        (RawStep.par.refl argumentRaw), ?_⟩
      intro equivAppEq
      apply rawStep.2
      injection equivAppEq
    exact carrierBCR2
      (sourceReducible.2 argumentTerm argumentReducible) equivAppStep

/-! ## K12.20.R typed CR2 lift — Ty.refine strong-refineElim-closure compound arm

Thirteenth compound-arm CR2 lemma.  `Ty.refine baseType
predicate` ships a **strong refineElim closure** in K12.14:
the eliminator produces full `Reducible baseType (Term.refineElim
refinedValue)` from the simple projection.  `baseType` is a
strict sub-Ty of `Ty.refine baseType predicate` — structural-
recursion-on-Ty admits `Reducible baseType` recursive call.
The `predicate : RawTerm (scope+1)` is a RawTerm-binder with no
typed dependency at the Reducible layer; the "Decidable
predicate discharge" aspect of K12.14 lives at Layer 5 SMT-
recheck (#1342 D5.6, #1344 D5.8) and is orthogonal to the
Reducibility-candidate closure shipped here.

Closure shape (per Reducibility.lean:554-556):

```
Reducible (Ty.refine baseType _) refinedValue =
  SN(refinedValue) ∧
  Reducible baseType (Term.refineElim refinedValue)
```

This is the **simplest** strong compound arm of the 15.  No
quantifier overhead, no mode-univalent / mode-strict witness,
no interval / motive binder.  Pure projection — directly
analogous to K12.20.N glue but stripped down further (no
modeIsUnivalent binder).

Term.refineElim raw form is `RawTerm.refineElim refinedRaw`
(per Term.lean:446); `RawStep.par.refineElimCong` is a 1-arg
cong rule taking just `refinedRawStep` (per RawPar.lean:766-771).
Single-substituent ctor → no `par.refl` companion needed.
Distinctness via `injection` on `RawTerm.refineElim.injEq`.
-/

/-- **K12.20.R refine arm**: strong-refineElim-closure CR2 for
`Ty.refine`.  Takes `baseTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`baseType`).  SN-of-refinedValue preserved by raw
`step_preserves`; the full-Reducible refineElim conjunct lifted
via baseTypeCR2 over the refineElimCong step.  Simplest strong
compound arm — no quantifier, no mode binder. -/
theorem Reducible.step_preserves_refine
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.refine baseType predicate) sourceRaw}
    {target : Term context (Ty.refine baseType predicate) targetRaw}
    (baseTypeCR2 :
        ∀ {refineElimSourceRaw refineElimTargetRaw : RawTerm scope}
          {refineElimSource : Term context baseType refineElimSourceRaw}
          {refineElimTarget : Term context baseType refineElimTargetRaw},
          Reducible baseType refineElimSource →
          RawStep.parProgress refineElimSourceRaw refineElimTargetRaw →
          Reducible baseType refineElimTarget)
    (sourceReducible :
        Reducible (Ty.refine baseType predicate) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.refine baseType predicate) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have refineElimStep : RawStep.parProgress
        (RawTerm.refineElim sourceRaw)
        (RawTerm.refineElim targetRaw) := by
      refine ⟨RawStep.par.refineElimCong rawStep.1, ?_⟩
      intro refineElimEq
      apply rawStep.2
      injection refineElimEq
    exact baseTypeCR2 sourceReducible.2 refineElimStep

/-! ## K12.20.S typed CR2 lift — Ty.record strong-recordProj-closure compound arm

Fourteenth compound-arm CR2 lemma.  `Ty.record singleFieldType`
ships a **strong recordProj closure** in K12.15: the eliminator
produces full `Reducible singleFieldType (Term.recordProj
recordValue)` from the simple projection.  `singleFieldType` is
a strict sub-Ty of `Ty.record singleFieldType` — structural-
recursion-on-Ty admits `Reducible singleFieldType` recursive
call.  Multi-field records compose via nested single-field
records (per Term.lean docstring), preserving this closure
shape under nesting.

Closure shape (per Reducibility.lean:563-565):

```
Reducible (Ty.record singleFieldType) recordValue =
  SN(recordValue) ∧
  Reducible singleFieldType (Term.recordProj recordValue)
```

Structurally identical to K12.20.R refine: pure projection,
single-substituent cong rule, no quantifier overhead.  Only
differences: ctor name (`Ty.record` vs `Ty.refine`), eliminator
(`recordProj` vs `refineElim`), strict-sub-Ty field name
(`singleFieldType` vs `baseType`).  No predicate binder (record
has no SMT-recheck axis — purely structural).

Term.recordProj raw form is `RawTerm.recordProj recordRaw` (per
Term.lean:425); `RawStep.par.recordProjCong` is a 1-arg cong
rule (per RawPar.lean:790-795).  Distinctness via `injection`
on `RawTerm.recordProj.injEq`.
-/

/-- **K12.20.S record arm**: strong-recordProj-closure CR2 for
`Ty.record`.  Takes `singleFieldTypeCR2` as explicit hypothesis
(the recursive Reducible-preservation witness on the strict
sub-Ty `singleFieldType`).  SN-of-recordValue preserved by raw
`step_preserves`; the full-Reducible recordProj conjunct lifted
via singleFieldTypeCR2 over the recordProjCong step.  Mirror of
K12.20.R refine. -/
theorem Reducible.step_preserves_record
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.record singleFieldType) sourceRaw}
    {target : Term context (Ty.record singleFieldType) targetRaw}
    (singleFieldTypeCR2 :
        ∀ {recordProjSourceRaw recordProjTargetRaw : RawTerm scope}
          {recordProjSource :
              Term context singleFieldType recordProjSourceRaw}
          {recordProjTarget :
              Term context singleFieldType recordProjTargetRaw},
          Reducible singleFieldType recordProjSource →
          RawStep.parProgress recordProjSourceRaw recordProjTargetRaw →
          Reducible singleFieldType recordProjTarget)
    (sourceReducible : Reducible (Ty.record singleFieldType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.record singleFieldType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have recordProjStep : RawStep.parProgress
        (RawTerm.recordProj sourceRaw)
        (RawTerm.recordProj targetRaw) := by
      refine ⟨RawStep.par.recordProjCong rawStep.1, ?_⟩
      intro recordProjEq
      apply rawStep.2
      injection recordProjEq
    exact singleFieldTypeCR2 sourceReducible.2 recordProjStep

/-! ## K12.20.T typed CR2 lift — Ty.codata strong-codataDest-closure compound arm

Fifteenth (and final) compound-arm CR2 lemma.  `Ty.codata
stateType outputType` ships a **strong codataDest closure** in
K12.15: the eliminator produces full `Reducible outputType
(Term.codataDest codataValue)` from the observation projection.
`outputType` is a strict sub-Ty of `Ty.codata stateType
outputType` — structural-recursion-on-Ty admits the recursive
`Reducible outputType` call.

Closure shape (per Reducibility.lean:574-576):

```
Reducible (Ty.codata _ outputType) codataValue =
  SN(codataValue) ∧
  Reducible outputType (Term.codataDest codataValue)
```

Note: `stateType` is also a strict sub-Ty of `Ty.codata
stateType outputType`, but the closure does NOT recurse on it
— the stateType is packed into the unfold/initial-state and is
never exposed by an eliminator.  Productivity-checking at higher
observation depths lives at the codata-corecursion Layer (#1267
K08), orthogonal to this RC closure.  So this lemma needs only
ONE recursive-CR2 hypothesis (`outputTypeCR2`).

Structurally identical to K12.20.{R refine, S record}: pure
projection, single-substituent cong rule, no quantifier
overhead.  Only differences: ctor name (`Ty.codata` takes two
Ty args — `stateType` carried implicit, only `outputType`
appears in the recursive hypothesis), eliminator
(`codataDest` vs `recordProj`).

Term.codataDest raw form is `RawTerm.codataDest codataRaw` (per
Term.lean:460-465); `RawStep.par.codataDestCong` is a 1-arg
cong rule (per RawPar.lean:820-825).  Distinctness via
`injection` on `RawTerm.codataDest.injEq`.

**Compound-arm CR2 sweep COMPLETE** with this lemma: all 15
compound-arm closures shipped (arrow / piTy / sigmaTy / id /
listType / optionType / eitherType / path / glue / oeq /
idStrict / equiv / refine / record / codata).  Next: K12.20
wrap-up combining all 25 arms (10 SN-direct + 15 compound) into
a single structurally-recursive `Reducible.step_preserves`.
-/

/-- **K12.20.T codata arm**: strong-codataDest-closure CR2 for
`Ty.codata`.  Takes `outputTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`outputType` — the projection target).  SN-of-codataValue
preserved by raw `step_preserves`; the full-Reducible
codataDest conjunct lifted via outputTypeCR2 over the
codataDestCong step.  Mirror of K12.20.{R refine, S record}.
The `stateType` index is carried implicit and never reached —
codata's state is packed into the unfold/initial-state, not
exposed by any current eliminator. -/
theorem Reducible.step_preserves_codata
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.codata stateType outputType) sourceRaw}
    {target : Term context (Ty.codata stateType outputType) targetRaw}
    (outputTypeCR2 :
        ∀ {codataDestSourceRaw codataDestTargetRaw : RawTerm scope}
          {codataDestSource :
              Term context outputType codataDestSourceRaw}
          {codataDestTarget :
              Term context outputType codataDestTargetRaw},
          Reducible outputType codataDestSource →
          RawStep.parProgress codataDestSourceRaw codataDestTargetRaw →
          Reducible outputType codataDestTarget)
    (sourceReducible :
        Reducible (Ty.codata stateType outputType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.codata stateType outputType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have codataDestStep : RawStep.parProgress
        (RawTerm.codataDest sourceRaw)
        (RawTerm.codataDest targetRaw) := by
      refine ⟨RawStep.par.codataDestCong rawStep.1, ?_⟩
      intro codataDestEq
      apply rawStep.2
      injection codataDestEq
    exact outputTypeCR2 sourceReducible.2 codataDestStep



end LeanFX2
