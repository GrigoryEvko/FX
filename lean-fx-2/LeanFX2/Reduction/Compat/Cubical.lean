import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # Reduction/Compat/Cubical — typed compositional compat for cubical ctors

Split from `Reduction/Compat.lean` (REFACTOR-COMPAT #1550) — keeps
the parent module under the 1000-line ceiling.

This module bundles the 9 per-ctor `Step.par.XCong.{rename,subst}_compatible`
theorems whose subjects are cubical-layer term constructors:

* `intervalOppCong` — interval involution
* `intervalMeetCong` / `intervalJoinCong` — meet/join binary
* `glueElimCong` / `glueIntroCong` — Glue elim/intro (mode-univalent)
* `pathAppCong` — Path application (mode-univalent)
* `hcompCong` — homogeneous composition (mode-univalent)
* `transpCong` — cubical transport (mode-univalent)
* `pathLamCong` — Path-lambda binder (mode-univalent)

All zero-axiom under `#print axioms`.  Naming references via
`LeanFX2.Step.par.XCong.{rename,subst}_compatible` remain
namespace-stable across the split — downstream audit gates in
`Tools/AuditAll/AuditReduction.lean` and smoke files do not need
to change. -/

namespace LeanFX2

namespace Step

namespace par

namespace intervalOppCong

/-- Compositional typed rename-compat for `Step.par.intervalOppCong`.

Given a typed renaming and a Step.par on the inner interval values
that has ALREADY been transported across the renaming, produce the
parent `Step.par` on `Term.intervalOpp ...` after renaming.

The proof reduces to applying the `intervalOppCong` constructor
because `Term.rename` on `Term.intervalOpp innerValue` unfolds to
`Term.intervalOpp (Term.rename termRenaming innerValue)`, and
`Ty.interval.rename rho = Ty.interval` is `rfl`.

Compositional pattern (option (a) in D2.10): the caller supplies the
renamed-inner Step.par as a hypothesis; this lemma packages it into
the outer Step.par.  No typed induction principle for `Step.par`
is required — the toolkit-style API is sufficient for confluence
consumers, which build inner Step.pars first and aggregate via
these combinators. -/
theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx Ty.interval innerRawSource}
    {innerTarget : Term sourceCtx Ty.interval innerRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming innerSource)
               (Term.rename termRenaming innerTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalOpp innerSource))
      (Term.rename termRenaming (Term.intervalOpp innerTarget)) :=
  Step.par.intervalOppCong renamedInnerStep

/-- Compositional typed subst-compat for `Step.par.intervalOppCong`.

Mirror of `rename_compatible` for `Term.subst`.  Given a typed
substitution and a Step.par on the inner interval values that has
ALREADY been transported across the substitution, produce the
parent `Step.par` on `Term.intervalOpp ...` after substitution.

Note: there is only ONE substituted Step.par hypothesis (no
"pointwise-related substs" yet) — the simplest compositional shape.
A future variant for the pointwise-related-substs case (mirror of
`RawStep.par.subst_compatible`) can be added once subst-pointwise
infrastructure is in place at the typed level. -/
theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx Ty.interval innerRawSource}
    {innerTarget : Term sourceCtx Ty.interval innerRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst innerSource)
               (Term.subst termSubst innerTarget)) :
    Step.par
      (Term.subst termSubst (Term.intervalOpp innerSource))
      (Term.subst termSubst (Term.intervalOpp innerTarget)) :=
  Step.par.intervalOppCong substitutedInnerStep

end intervalOppCong

/-! ### `glueElimCong` (unary, mode-univalent gated). -/
namespace glueElimCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource gluedRawTarget : RawTerm sourceScope}
    {gluedSource :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (renamedInnerStep :
      Step.par (Term.rename termRenaming gluedSource)
               (Term.rename termRenaming gluedTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.glueElim modeIsUnivalent gluedSource))
      (Term.rename termRenaming
        (Term.glueElim modeIsUnivalent gluedTarget)) :=
  Step.par.glueElimCong modeIsUnivalent renamedInnerStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource gluedRawTarget : RawTerm sourceScope}
    {gluedSource :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (substitutedInnerStep :
      Step.par (Term.subst termSubst gluedSource)
               (Term.subst termSubst gluedTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.glueElim modeIsUnivalent gluedSource))
      (Term.subst termSubst
        (Term.glueElim modeIsUnivalent gluedTarget)) :=
  Step.par.glueElimCong modeIsUnivalent substitutedInnerStep

end glueElimCong

/-! ### `intervalMeetCong` (binary, both inners at `Ty.interval`). -/
namespace intervalMeetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (renamedLeftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (renamedRightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalMeet leftSource rightSource))
      (Term.rename termRenaming (Term.intervalMeet leftTarget rightTarget)) :=
  Step.par.intervalMeetCong renamedLeftStep renamedRightStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (substitutedLeftStep :
      Step.par (Term.subst termSubst leftSource)
               (Term.subst termSubst leftTarget))
    (substitutedRightStep :
      Step.par (Term.subst termSubst rightSource)
               (Term.subst termSubst rightTarget)) :
    Step.par
      (Term.subst termSubst (Term.intervalMeet leftSource rightSource))
      (Term.subst termSubst (Term.intervalMeet leftTarget rightTarget)) :=
  Step.par.intervalMeetCong substitutedLeftStep substitutedRightStep

end intervalMeetCong

/-! ### `intervalJoinCong` (binary, both inners at `Ty.interval`). -/
namespace intervalJoinCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (renamedLeftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (renamedRightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalJoin leftSource rightSource))
      (Term.rename termRenaming (Term.intervalJoin leftTarget rightTarget)) :=
  Step.par.intervalJoinCong renamedLeftStep renamedRightStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget :
      RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (substitutedLeftStep :
      Step.par (Term.subst termSubst leftSource)
               (Term.subst termSubst leftTarget))
    (substitutedRightStep :
      Step.par (Term.subst termSubst rightSource)
               (Term.subst termSubst rightTarget)) :
    Step.par
      (Term.subst termSubst (Term.intervalJoin leftSource rightSource))
      (Term.subst termSubst (Term.intervalJoin leftTarget rightTarget)) :=
  Step.par.intervalJoinCong substitutedLeftStep substitutedRightStep

end intervalJoinCong

/-! ### `pathAppCong` (binary, mode-univalent gated). -/
namespace pathAppCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
      RawTerm sourceScope}
    {pathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {pathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (renamedPathStep :
      Step.par (Term.rename termRenaming pathSource)
               (Term.rename termRenaming pathTarget))
    (renamedIntervalStep :
      Step.par (Term.rename termRenaming intervalSource)
               (Term.rename termRenaming intervalTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pathApp modeIsUnivalent pathSource intervalSource))
      (Term.rename termRenaming
        (Term.pathApp modeIsUnivalent pathTarget intervalTarget)) :=
  Step.par.pathAppCong modeIsUnivalent renamedPathStep renamedIntervalStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
      RawTerm sourceScope}
    {pathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {pathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (substitutedPathStep :
      Step.par (Term.subst termSubst pathSource)
               (Term.subst termSubst pathTarget))
    (substitutedIntervalStep :
      Step.par (Term.subst termSubst intervalSource)
               (Term.subst termSubst intervalTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.pathApp modeIsUnivalent pathSource intervalSource))
      (Term.subst termSubst
        (Term.pathApp modeIsUnivalent pathTarget intervalTarget)) :=
  Step.par.pathAppCong modeIsUnivalent substitutedPathStep substitutedIntervalStep

end pathAppCong

/-! ### `hcompCong` (binary, mode-univalent gated, both at carrier).

Binary exemplar: two inner Step.par premises (sides + cap), both
at the shared `carrierType`.  Mode hypothesis `mode = .univalent`
threaded through. -/
namespace hcompCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget :
      RawTerm sourceScope}
    {sidesSource : Term sourceCtx carrierType sidesRawSource}
    {sidesTarget : Term sourceCtx carrierType sidesRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (renamedSidesStep :
      Step.par (Term.rename termRenaming sidesSource)
               (Term.rename termRenaming sidesTarget))
    (renamedCapStep :
      Step.par (Term.rename termRenaming capSource)
               (Term.rename termRenaming capTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.hcomp modeIsUnivalent sidesSource capSource))
      (Term.rename termRenaming
        (Term.hcomp modeIsUnivalent sidesTarget capTarget)) :=
  Step.par.hcompCong modeIsUnivalent renamedSidesStep renamedCapStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget :
      RawTerm sourceScope}
    {sidesSource : Term sourceCtx carrierType sidesRawSource}
    {sidesTarget : Term sourceCtx carrierType sidesRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (substitutedSidesStep :
      Step.par (Term.subst termSubst sidesSource)
               (Term.subst termSubst sidesTarget))
    (substitutedCapStep :
      Step.par (Term.subst termSubst capSource)
               (Term.subst termSubst capTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.hcomp modeIsUnivalent sidesSource capSource))
      (Term.subst termSubst
        (Term.hcomp modeIsUnivalent sidesTarget capTarget)) :=
  Step.par.hcompCong modeIsUnivalent substitutedSidesStep substitutedCapStep

end hcompCong

/-! ### `hcompPathCong` (binary, mode-univalent gated, path-shaped sides).

Typed-only sibling of `hcompCong`: raw projection still uses
`RawTerm.hcomp`, but the sides argument is typed as a path. -/
namespace hcompPathCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRawSource sidesPathRawTarget capRawSource capRawTarget :
      RawTerm sourceScope}
    {sidesPathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRawSource}
    {sidesPathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (renamedSidesStep :
      Step.par (Term.rename termRenaming sidesPathSource)
               (Term.rename termRenaming sidesPathTarget))
    (renamedCapStep :
      Step.par (Term.rename termRenaming capSource)
               (Term.rename termRenaming capTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
          sidesPathSource capSource))
      (Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
          sidesPathTarget capTarget)) :=
  Step.par.hcompPathCong modeIsUnivalent
    (leftEndpoint.rename rho) (rightEndpoint.rename rho)
    renamedSidesStep renamedCapStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRawSource sidesPathRawTarget capRawSource capRawTarget :
      RawTerm sourceScope}
    {sidesPathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRawSource}
    {sidesPathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (substitutedSidesStep :
      Step.par (Term.subst termSubst sidesPathSource)
               (Term.subst termSubst sidesPathTarget))
    (substitutedCapStep :
      Step.par (Term.subst termSubst capSource)
               (Term.subst termSubst capTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
          sidesPathSource capSource))
      (Term.subst termSubst
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
          sidesPathTarget capTarget)) :=
  Step.par.hcompPathCong modeIsUnivalent
    (leftEndpoint.subst sigma.forRaw) (rightEndpoint.subst sigma.forRaw)
    substitutedSidesStep substitutedCapStep

end hcompPathCong

/-! ### `glueIntroCong` (binary, mode-univalent gated, both at base).

Binary exemplar: two inner Step.par premises (base + partial),
both at the shared `baseType`.  `boundaryWitness : RawTerm scope`
is index data.  Mode hypothesis `mode = .univalent`. -/
namespace glueIntroCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm sourceScope}
    {baseSource : Term sourceCtx baseType baseRawSource}
    {baseTarget : Term sourceCtx baseType baseRawTarget}
    {partialSource : Term sourceCtx baseType partialRawSource}
    {partialTarget : Term sourceCtx baseType partialRawTarget}
    (renamedBaseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (renamedPartialStep :
      Step.par (Term.rename termRenaming partialSource)
               (Term.rename termRenaming partialTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseSource partialSource))
      (Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseTarget partialTarget)) :=
  Step.par.glueIntroCong modeIsUnivalent renamedBaseStep renamedPartialStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm sourceScope}
    {baseSource : Term sourceCtx baseType baseRawSource}
    {baseTarget : Term sourceCtx baseType baseRawTarget}
    {partialSource : Term sourceCtx baseType partialRawSource}
    {partialTarget : Term sourceCtx baseType partialRawTarget}
    (substitutedBaseStep :
      Step.par (Term.subst termSubst baseSource)
               (Term.subst termSubst baseTarget))
    (substitutedPartialStep :
      Step.par (Term.subst termSubst partialSource)
               (Term.subst termSubst partialTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseSource partialSource))
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseTarget partialTarget)) :=
  Step.par.glueIntroCong modeIsUnivalent substitutedBaseStep substitutedPartialStep

end glueIntroCong

/-! ### `transpCong` (binary, mode-univalent, multi-arg cubical transport).

Binary exemplar with two inner Step.par premises: typePath at the
universe-typed Path, sourceValue at sourceType.  Mode hypothesis
`mode = .univalent`.  All other args (universeLevel, levelLt,
source/target types, source/target type raws) are explicit data,
not step subjects. -/
namespace transpCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
      RawTerm sourceScope}
    {typePathSource :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawSource}
    {typePathTarget :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawTarget}
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (renamedTypePathStep :
      Step.par (Term.rename termRenaming typePathSource)
               (Term.rename termRenaming typePathTarget))
    (renamedSourceValueStep :
      Step.par (Term.rename termRenaming sourceValueSource)
               (Term.rename termRenaming sourceValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource))
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)) :=
  Step.par.transpCong modeIsUnivalent
    universeLevel universeLevelLt
    (sourceType.rename rho) (targetType.rename rho)
    (sourceTypeRaw.rename rho) (targetTypeRaw.rename rho)
    renamedTypePathStep renamedSourceValueStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
      RawTerm sourceScope}
    {typePathSource :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawSource}
    {typePathTarget :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawTarget}
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (substitutedTypePathStep :
      Step.par (Term.subst termSubst typePathSource)
               (Term.subst termSubst typePathTarget))
    (substitutedSourceValueStep :
      Step.par (Term.subst termSubst sourceValueSource)
               (Term.subst termSubst sourceValueTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource))
      (Term.subst termSubst
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)) :=
  Step.par.transpCong modeIsUnivalent
    universeLevel universeLevelLt
    (sourceType.subst sigma) (targetType.subst sigma)
    (sourceTypeRaw.subst sigma.forRaw) (targetTypeRaw.subst sigma.forRaw)
    substitutedTypePathStep substitutedSourceValueStep

end transpCong

/-! ### `pathLamCong` (unary, binder, mode-univalent gated).

Binder rule: the body lives at `(scope + 1)` under
`(context.cons Ty.interval) ⊢ carrierType.weaken : ...`.  After
rename/subst, the body must traverse `TermRenaming.lift` (resp.
`TermSubst.lift`) and bridge `carrierType.weaken` →
`(carrierType.rename rho).weaken` (resp. `.subst sigma`) via
`Ty.weaken_rename_commute` / `Ty.weaken_subst_commute`.  Same
cast-surfacing approach as `oeqFunextCong` — the caller supplies
the inner Step.par premise at the cast type expected by
`Step.par.pathLamCong`. -/
namespace pathLamCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {bodySource :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (renamedBodyStep :
      Step.par
        (Ty.weaken_rename_commute rho carrierType ▸
          Term.rename (termRenaming.lift Ty.interval) bodySource)
        (Ty.weaken_rename_commute rho carrierType ▸
          Term.rename (termRenaming.lift Ty.interval) bodyTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodySource))
      (Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodyTarget)) :=
  Step.par.pathLamCong modeIsUnivalent renamedBodyStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {bodySource :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (substitutedBodyStep :
      Step.par
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodySource)
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodyTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodySource))
      (Term.subst termSubst
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodyTarget)) :=
  Step.par.pathLamCong modeIsUnivalent substitutedBodyStep

end pathLamCong

end par

end Step

end LeanFX2
