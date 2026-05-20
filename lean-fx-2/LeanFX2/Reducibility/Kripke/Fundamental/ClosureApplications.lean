import LeanFX2.Reducibility.Kripke.Fundamental.SNEliminators

/-! # LeanFX2.Reducibility.Kripke.Fundamental.ClosureApplications

Priority-1 Kripke closure-application fundamentals for eliminator-side
applications.  These theorems project directly out of ReducibleK closure
clauses.
-/

namespace LeanFX2

/-! ## Priority-1 Kripke closure-application fundamentals (eliminator-side).

The following theorems are the Kripke fundamental-theorem cases for
**eliminator-direction** application: given a Tait-reducible scrutinee
(or function or witness) plus reducible argument(s) where required, the
eliminator application is Tait-reducible at the result type.  These
fundamentals are direct projections from the `ReducibleK` predicate
closures defined in `Predicate.lean`.

Together with the existing `arrow_apply` (Arrow.lean), `piTy_apply`,
`sigmaTy_fst`, `sigmaTy_snd`, `listType_elim`, `optionType_match`,
`eitherType_match`, `refine_elim`, `record_proj`, `codata_dest`,
`session_recv`, `mod_elim`, `effect_rename` (Project.lean), these close
the eliminator-direction half of the fundamental theorem for all 19
Kripke-closure Ty arms.

The remaining fundamental-theorem work is the **introducer-direction**
(reducible-input → reducible-introduction) and **β-redex backward
closure** cases, which require the head-expansion cascade (parProgress
backward closure of ReducibleK).  Those are Priority-2/3 and deferred
per the M04/K12.27 sub-prerequisite scope. -/

/-- Kripke fundamental: identity-type J elimination preserves
reducibility.  Given a Tait-reducible witness at `Ty.id` and a
Tait-reducible base case at the motive (in every future world,
parameterized by an arbitrary motive type), `Term.idJ baseCase witness`
is Tait-reducible at the motive.  Mirrors the J induction principle on
identity types — the motive is universally quantified because the
identity-type's structure does not constrain the eliminator's result
type. -/
theorem ReducibleK.fundamental_idJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    {witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (witnessIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw witnessTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {motiveType : Ty level targetScope}
    {baseRaw : RawTerm targetScope}
    (baseCase : Term targetCtx motiveType baseRaw)
    (baseCaseIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType baseRaw baseCase) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.idJ baseCase (Term.rename termRenaming witnessTerm)) :=
  witnessIsR.2 termRenaming baseCase baseCaseIsR

/-- Kripke fundamental: observational-equality J elimination preserves
reducibility.  Same shape as `fundamental_idJ` over the `Ty.oeq`
carrier. -/
theorem ReducibleK.fundamental_oeqJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    {witnessTerm :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (witnessIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw witnessTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {motiveType : Ty level targetScope}
    {baseRaw : RawTerm targetScope}
    (baseCase : Term targetCtx motiveType baseRaw)
    (baseCaseIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType baseRaw baseCase) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.oeqJ baseCase (Term.rename termRenaming witnessTerm)) :=
  witnessIsR.2 termRenaming baseCase baseCaseIsR

/-- Kripke fundamental: strict-identity recursion preserves
reducibility.  Same shape as `fundamental_idJ` over the `Ty.idStrict`
carrier modulo the strict-mode side condition. -/
theorem ReducibleK.fundamental_idStrictRec
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    {witnessTerm :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (witnessIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw witnessTerm)
    (modeIsStrict : mode = Mode.strict)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {motiveType : Ty level targetScope}
    {baseRaw : RawTerm targetScope}
    (baseCase : Term targetCtx motiveType baseRaw)
    (baseCaseIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType baseRaw baseCase) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.idStrictRec modeIsStrict baseCase
        (Term.rename termRenaming witnessTerm)) :=
  witnessIsR.2 modeIsStrict termRenaming baseCase baseCaseIsR

/-- Kripke fundamental: equivalence-type application preserves
reducibility.  Given a Tait-reducible packaged equivalence at
`Ty.equiv leftTy rightTy` and a Tait-reducible argument at the
renamed leftTy, `Term.equivApply (rename equiv) arg` is Tait-reducible
at the renamed rightTy.  Mirrors `arrow_apply` over the equivalence
carrier swap. -/
theorem ReducibleK.fundamental_equivApply
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {leftTy rightTy : Ty level scope}
    {equivRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv leftTy rightTy) equivRaw}
    (equivIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.equiv leftTy rightTy) equivRaw equivTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (leftTy.rename rho) argumentRaw)
    (argumentIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (leftTy.rename rho) argumentRaw argumentTerm) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (rightTy.rename rho) _
      (Term.equivApply (Term.rename termRenaming equivTerm) argumentTerm) :=
  equivIsR.2 termRenaming argumentTerm argumentIsR

/-- Kripke fundamental: cubical path application preserves reducibility
under the univalent-mode discipline.  Given a Tait-reducible path at
`Ty.path` and a Tait-reducible interval value, `Term.pathApp` is
Tait-reducible at the renamed carrier.  Endpoint specialisation
(pathApp p i0 / pathApp p i1) is governed by Step-level reductions —
the closure only commits to the result sitting at `carrierType.rename
rho`. -/
theorem ReducibleK.fundamental_pathApp
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw : RawTerm scope}
    {pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    (pathIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw pathTerm)
    (modeIsUnivalent : mode = Mode.univalent)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {intervalRaw : RawTerm targetScope}
    (intervalTerm : Term targetCtx Ty.interval intervalRaw)
    (intervalIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        Ty.interval intervalRaw intervalTerm) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (carrierType.rename rho) _
      (Term.pathApp modeIsUnivalent
        (Term.rename termRenaming pathTerm) intervalTerm) :=
  pathIsR.2 modeIsUnivalent termRenaming intervalTerm intervalIsR

/-- Kripke fundamental: glue elimination preserves reducibility under
the univalent-mode discipline.  Given a Tait-reducible glue value at
`Ty.glue baseType boundaryWitness`, `Term.glueElim` produces a
Tait-reducible result at the renamed baseType.  Direct projection from
the glue closure clause in `Predicate.lean`. -/
theorem ReducibleK.fundamental_glueElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedTerm :
      Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.glue baseType boundaryWitness) gluedRaw gluedTerm)
    (modeIsUnivalent : mode = Mode.univalent)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (baseType.rename rho) _
      (Term.glueElim modeIsUnivalent
        (Term.rename termRenaming gluedTerm)) :=
  gluedIsR.2 modeIsUnivalent termRenaming

end LeanFX2
