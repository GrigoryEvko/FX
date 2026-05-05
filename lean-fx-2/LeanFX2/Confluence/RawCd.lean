import LeanFX2.Foundation.RawSubst

/-! # Confluence/RawCd — raw-side complete development

`RawTerm.cd : RawTerm scope → RawTerm scope` produces the maximal
parallel reduct of a raw term: every redex visible at the head fires,
and every subterm is recursively complete-developed.

## Why a raw-side cd

The typed `Term.cd` (Layer 3 / `Confluence/Cd.lean`) carries Ty
indices and HEq casts on β-reduction arms — substantial work to get
right.  The raw side has no type indices, so cd is a clean recursive
definition with no casts.  Combined with `Bridge.lean`'s
`Step.par.toRawBridge`, raw confluence transfers to typed parallel
reductions on the projected raw indices: the bridge guarantees that
typed Step.par chains form raw Step.par chains, and raw confluence
gives a common raw reduct.

This is the ROI play for unblocking confluence work without first
clearing the typed-Term HEq cascade (W7 wall).

## Zero-axiom discipline

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly — no `_ =>` wildcards — to satisfy AXIOMS.md Layer M
strict-zero-axiom policy.  Per
`feedback_lean_zero_axiom_match.md`, full enumeration over a
non-dependent inductive (RawTerm is Nat-indexed only) keeps the
match compiler from emitting `propext` to discharge the catch-all
redundancy obligation.

## Structure

D1.6 grew RawTerm to 55 ctors.  A monolithic `RawTerm.cd` with 10
inner 55-arm matches × 55 outer arms produced ≈3000 branches —
`unfold` + `split` in `RawCdDominates.lean` exhausted simp's
heartbeat budget (per-whnf 200K, not propagated by file-level
`set_option maxHeartbeats 0`).

The refactor below extracts each redex-bearing case's inner match
into a dedicated helper definition — `cdAppCase`, `cdFstCase`,
`cdPathAppCase`, `cdGlueElimCase`, `cdRefineElimCase`,
`cdRecordProjCase`, `cdSndCase`, `cdBoolElimCase`, `cdNatElimCase`,
`cdNatRecCase`, `cdListElimCase`, `cdOptionMatchCase`,
`cdEitherMatchCase`, `cdIdJCase`.  Each helper carries its own 55-arm
match in its own elaboration scope, so `unfold cdAppCase; split`
inside cd_dominates only walks ~55 branches instead of ~3000.
`RawTerm.cd` itself becomes a thin dispatcher (one short arm per
RawTerm ctor).

## Construction sketch

* Atomic ctors (var, unit, *True/False/Zero/Nil/None) → identity
* Cong ctors (lam, pair, listCons, optionSome, eitherInl/Inr,
  natSucc, refl, modIntro/Elim, subsume, plus 27 D1.6 cong ctors)
  → recurse into subterms
* Redex-bearing ctors (app, pathApp, glueElim, refineElim, recordProj,
  fst, snd, boolElim, natElim, natRec, listElim, optionMatch,
  eitherMatch, idJ) → dispatch to per-redex helper, which handles
  canonical-ctor contraction + cong fallback

Modal ctor `modElim` is redex-bearing: `modElim (modIntro value)`
contracts to `value`; `modIntro` and `subsume` remain pure cong.
-/

namespace LeanFX2

/-- App redex: `(λ b) a → b[a]`; otherwise rebuild `app df da`.
55-arm full enumeration keeps match propext-clean. -/
def RawTerm.cdAppCase {scope : Nat}
    (developedFunction developedArgument : RawTerm scope) : RawTerm scope :=
  match developedFunction with
  | RawTerm.lam body => body.subst0 developedArgument
  | RawTerm.var _ => RawTerm.app developedFunction developedArgument
  | RawTerm.unit => RawTerm.app developedFunction developedArgument
  | RawTerm.app _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pair _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.fst _ => RawTerm.app developedFunction developedArgument
  | RawTerm.snd _ => RawTerm.app developedFunction developedArgument
  | RawTerm.boolTrue => RawTerm.app developedFunction developedArgument
  | RawTerm.boolFalse => RawTerm.app developedFunction developedArgument
  | RawTerm.boolElim _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.natZero => RawTerm.app developedFunction developedArgument
  | RawTerm.natSucc _ => RawTerm.app developedFunction developedArgument
  | RawTerm.natElim _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.natRec _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.listNil => RawTerm.app developedFunction developedArgument
  | RawTerm.listCons _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.listElim _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.optionNone => RawTerm.app developedFunction developedArgument
  | RawTerm.optionSome _ => RawTerm.app developedFunction developedArgument
  | RawTerm.optionMatch _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherInl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherInr _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherMatch _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.refl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idJ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.modIntro _ => RawTerm.app developedFunction developedArgument
  | RawTerm.modElim _ => RawTerm.app developedFunction developedArgument
  | RawTerm.subsume _ => RawTerm.app developedFunction developedArgument
  | RawTerm.interval0 => RawTerm.app developedFunction developedArgument
  | RawTerm.interval1 => RawTerm.app developedFunction developedArgument
  | RawTerm.intervalOpp _ => RawTerm.app developedFunction developedArgument
  | RawTerm.intervalMeet _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.intervalJoin _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pathLam _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pathApp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.glueIntro _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.glueElim _ => RawTerm.app developedFunction developedArgument
  | RawTerm.transp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.hcomp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqRefl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqJ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqFunext _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idStrictRefl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idStrictRec _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivIntro _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivApp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.refineIntro _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.refineElim _ => RawTerm.app developedFunction developedArgument
  | RawTerm.recordIntro _ => RawTerm.app developedFunction developedArgument
  | RawTerm.recordProj _ => RawTerm.app developedFunction developedArgument
  | RawTerm.codataUnfold _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.codataDest _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sessionSend _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sessionRecv _ => RawTerm.app developedFunction developedArgument
  | RawTerm.effectPerform _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.universeCode _ => RawTerm.app developedFunction developedArgument
  | RawTerm.arrowCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.piTyCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sigmaTyCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.productCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sumCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.listCode _ => RawTerm.app developedFunction developedArgument
  | RawTerm.optionCode _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idCode _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.cumulUpMarker _ => RawTerm.app developedFunction developedArgument

/-- Path application redex: `(pathLam body) @ point → body[point/i]`;
otherwise rebuild `pathApp dp di`. -/
def RawTerm.cdPathAppCase {scope : Nat}
    (developedPath developedInterval : RawTerm scope) : RawTerm scope :=
  match developedPath with
  | RawTerm.pathLam body => body.subst0 developedInterval
  | RawTerm.var _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.unit => RawTerm.pathApp developedPath developedInterval
  | RawTerm.lam _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.app _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.pair _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.fst _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.snd _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.boolTrue => RawTerm.pathApp developedPath developedInterval
  | RawTerm.boolFalse => RawTerm.pathApp developedPath developedInterval
  | RawTerm.boolElim _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natZero => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natSucc _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natElim _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natRec _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listNil => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listCons _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listElim _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionNone => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionSome _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionMatch _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherInl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherInr _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherMatch _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.refl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idJ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.modIntro _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.modElim _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.subsume _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.interval0 => RawTerm.pathApp developedPath developedInterval
  | RawTerm.interval1 => RawTerm.pathApp developedPath developedInterval
  | RawTerm.intervalOpp _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.intervalMeet _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.intervalJoin _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.pathApp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.glueIntro _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.glueElim _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.transp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.hcomp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqRefl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqJ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqFunext _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idStrictRefl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idStrictRec _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivIntro _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivApp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.refineIntro _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.refineElim _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.recordIntro _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.recordProj _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.codataUnfold _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.codataDest _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sessionSend _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sessionRecv _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.effectPerform _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.universeCode _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.arrowCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.piTyCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sigmaTyCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.productCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sumCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listCode _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionCode _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idCode _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.cumulUpMarker _ => RawTerm.pathApp developedPath developedInterval

/-- Glue elimination redex: `unglue (glue base partial) → base`;
otherwise rebuild `glueElim dg`. -/
def RawTerm.cdGlueElimCase {scope : Nat}
    (developedGlued : RawTerm scope) : RawTerm scope :=
  match developedGlued with
  | RawTerm.glueIntro baseValue _ => baseValue
  | RawTerm.var _ => RawTerm.glueElim developedGlued
  | RawTerm.unit => RawTerm.glueElim developedGlued
  | RawTerm.lam _ => RawTerm.glueElim developedGlued
  | RawTerm.app _ _ => RawTerm.glueElim developedGlued
  | RawTerm.pair _ _ => RawTerm.glueElim developedGlued
  | RawTerm.fst _ => RawTerm.glueElim developedGlued
  | RawTerm.snd _ => RawTerm.glueElim developedGlued
  | RawTerm.boolTrue => RawTerm.glueElim developedGlued
  | RawTerm.boolFalse => RawTerm.glueElim developedGlued
  | RawTerm.boolElim _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.natZero => RawTerm.glueElim developedGlued
  | RawTerm.natSucc _ => RawTerm.glueElim developedGlued
  | RawTerm.natElim _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.natRec _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.listNil => RawTerm.glueElim developedGlued
  | RawTerm.listCons _ _ => RawTerm.glueElim developedGlued
  | RawTerm.listElim _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.optionNone => RawTerm.glueElim developedGlued
  | RawTerm.optionSome _ => RawTerm.glueElim developedGlued
  | RawTerm.optionMatch _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherInl _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherInr _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherMatch _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.refl _ => RawTerm.glueElim developedGlued
  | RawTerm.idJ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.modIntro _ => RawTerm.glueElim developedGlued
  | RawTerm.modElim _ => RawTerm.glueElim developedGlued
  | RawTerm.subsume _ => RawTerm.glueElim developedGlued
  | RawTerm.interval0 => RawTerm.glueElim developedGlued
  | RawTerm.interval1 => RawTerm.glueElim developedGlued
  | RawTerm.intervalOpp _ => RawTerm.glueElim developedGlued
  | RawTerm.intervalMeet _ _ => RawTerm.glueElim developedGlued
  | RawTerm.intervalJoin _ _ => RawTerm.glueElim developedGlued
  | RawTerm.pathLam _ => RawTerm.glueElim developedGlued
  | RawTerm.pathApp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.glueElim _ => RawTerm.glueElim developedGlued
  | RawTerm.transp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.hcomp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqRefl _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqJ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqFunext _ => RawTerm.glueElim developedGlued
  | RawTerm.idStrictRefl _ => RawTerm.glueElim developedGlued
  | RawTerm.idStrictRec _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivIntro _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivApp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.refineIntro _ _ => RawTerm.glueElim developedGlued
  | RawTerm.refineElim _ => RawTerm.glueElim developedGlued
  | RawTerm.recordIntro _ => RawTerm.glueElim developedGlued
  | RawTerm.recordProj _ => RawTerm.glueElim developedGlued
  | RawTerm.codataUnfold _ _ => RawTerm.glueElim developedGlued
  | RawTerm.codataDest _ => RawTerm.glueElim developedGlued
  | RawTerm.sessionSend _ _ => RawTerm.glueElim developedGlued
  | RawTerm.sessionRecv _ => RawTerm.glueElim developedGlued
  | RawTerm.effectPerform _ _ => RawTerm.glueElim developedGlued
  | RawTerm.universeCode _ => RawTerm.glueElim developedGlued
  | RawTerm.arrowCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.piTyCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.sigmaTyCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.productCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.sumCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.listCode _ => RawTerm.glueElim developedGlued
  | RawTerm.optionCode _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.idCode _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.cumulUpMarker _ => RawTerm.glueElim developedGlued

/-- Modal elimination redex: `modElim (modIntro payload) → payload`;
otherwise rebuild `modElim developedInner`. -/
def RawTerm.cdModElimCase {scope : Nat}
    (developedInner : RawTerm scope) : RawTerm scope :=
  match developedInner with
  | RawTerm.modIntro payload => payload
  | RawTerm.var _ => RawTerm.modElim developedInner
  | RawTerm.unit => RawTerm.modElim developedInner
  | RawTerm.lam _ => RawTerm.modElim developedInner
  | RawTerm.app _ _ => RawTerm.modElim developedInner
  | RawTerm.pair _ _ => RawTerm.modElim developedInner
  | RawTerm.fst _ => RawTerm.modElim developedInner
  | RawTerm.snd _ => RawTerm.modElim developedInner
  | RawTerm.boolTrue => RawTerm.modElim developedInner
  | RawTerm.boolFalse => RawTerm.modElim developedInner
  | RawTerm.boolElim _ _ _ => RawTerm.modElim developedInner
  | RawTerm.natZero => RawTerm.modElim developedInner
  | RawTerm.natSucc _ => RawTerm.modElim developedInner
  | RawTerm.natElim _ _ _ => RawTerm.modElim developedInner
  | RawTerm.natRec _ _ _ => RawTerm.modElim developedInner
  | RawTerm.listNil => RawTerm.modElim developedInner
  | RawTerm.listCons _ _ => RawTerm.modElim developedInner
  | RawTerm.listElim _ _ _ => RawTerm.modElim developedInner
  | RawTerm.optionNone => RawTerm.modElim developedInner
  | RawTerm.optionSome _ => RawTerm.modElim developedInner
  | RawTerm.optionMatch _ _ _ => RawTerm.modElim developedInner
  | RawTerm.eitherInl _ => RawTerm.modElim developedInner
  | RawTerm.eitherInr _ => RawTerm.modElim developedInner
  | RawTerm.eitherMatch _ _ _ => RawTerm.modElim developedInner
  | RawTerm.refl _ => RawTerm.modElim developedInner
  | RawTerm.idJ _ _ => RawTerm.modElim developedInner
  | RawTerm.modElim _ => RawTerm.modElim developedInner
  | RawTerm.subsume _ => RawTerm.modElim developedInner
  | RawTerm.interval0 => RawTerm.modElim developedInner
  | RawTerm.interval1 => RawTerm.modElim developedInner
  | RawTerm.intervalOpp _ => RawTerm.modElim developedInner
  | RawTerm.intervalMeet _ _ => RawTerm.modElim developedInner
  | RawTerm.intervalJoin _ _ => RawTerm.modElim developedInner
  | RawTerm.pathLam _ => RawTerm.modElim developedInner
  | RawTerm.pathApp _ _ => RawTerm.modElim developedInner
  | RawTerm.glueIntro _ _ => RawTerm.modElim developedInner
  | RawTerm.glueElim _ => RawTerm.modElim developedInner
  | RawTerm.transp _ _ => RawTerm.modElim developedInner
  | RawTerm.hcomp _ _ => RawTerm.modElim developedInner
  | RawTerm.oeqRefl _ => RawTerm.modElim developedInner
  | RawTerm.oeqJ _ _ => RawTerm.modElim developedInner
  | RawTerm.oeqFunext _ => RawTerm.modElim developedInner
  | RawTerm.idStrictRefl _ => RawTerm.modElim developedInner
  | RawTerm.idStrictRec _ _ => RawTerm.modElim developedInner
  | RawTerm.equivIntro _ _ => RawTerm.modElim developedInner
  | RawTerm.equivApp _ _ => RawTerm.modElim developedInner
  | RawTerm.refineIntro _ _ => RawTerm.modElim developedInner
  | RawTerm.refineElim _ => RawTerm.modElim developedInner
  | RawTerm.recordIntro _ => RawTerm.modElim developedInner
  | RawTerm.recordProj _ => RawTerm.modElim developedInner
  | RawTerm.codataUnfold _ _ => RawTerm.modElim developedInner
  | RawTerm.codataDest _ => RawTerm.modElim developedInner
  | RawTerm.sessionSend _ _ => RawTerm.modElim developedInner
  | RawTerm.sessionRecv _ => RawTerm.modElim developedInner
  | RawTerm.effectPerform _ _ => RawTerm.modElim developedInner
  | RawTerm.universeCode _ => RawTerm.modElim developedInner
  | RawTerm.arrowCode _ _ => RawTerm.modElim developedInner
  | RawTerm.piTyCode _ _ => RawTerm.modElim developedInner
  | RawTerm.sigmaTyCode _ _ => RawTerm.modElim developedInner
  | RawTerm.productCode _ _ => RawTerm.modElim developedInner
  | RawTerm.sumCode _ _ => RawTerm.modElim developedInner
  | RawTerm.listCode _ => RawTerm.modElim developedInner
  | RawTerm.optionCode _ => RawTerm.modElim developedInner
  | RawTerm.eitherCode _ _ => RawTerm.modElim developedInner
  | RawTerm.idCode _ _ _ => RawTerm.modElim developedInner
  | RawTerm.equivCode _ _ => RawTerm.modElim developedInner
  | RawTerm.cumulUpMarker _ => RawTerm.modElim developedInner

/-- Refinement elimination redex: `refineElim (refineIntro value proof)
→ value`; otherwise rebuild `refineElim dr`. -/
def RawTerm.cdRefineElimCase {scope : Nat}
    (developedRefined : RawTerm scope) : RawTerm scope :=
  match developedRefined with
  | RawTerm.refineIntro rawValue _ => rawValue
  | RawTerm.var _ => RawTerm.refineElim developedRefined
  | RawTerm.unit => RawTerm.refineElim developedRefined
  | RawTerm.lam _ => RawTerm.refineElim developedRefined
  | RawTerm.app _ _ => RawTerm.refineElim developedRefined
  | RawTerm.pair _ _ => RawTerm.refineElim developedRefined
  | RawTerm.fst _ => RawTerm.refineElim developedRefined
  | RawTerm.snd _ => RawTerm.refineElim developedRefined
  | RawTerm.boolTrue => RawTerm.refineElim developedRefined
  | RawTerm.boolFalse => RawTerm.refineElim developedRefined
  | RawTerm.boolElim _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.natZero => RawTerm.refineElim developedRefined
  | RawTerm.natSucc _ => RawTerm.refineElim developedRefined
  | RawTerm.natElim _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.natRec _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.listNil => RawTerm.refineElim developedRefined
  | RawTerm.listCons _ _ => RawTerm.refineElim developedRefined
  | RawTerm.listElim _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.optionNone => RawTerm.refineElim developedRefined
  | RawTerm.optionSome _ => RawTerm.refineElim developedRefined
  | RawTerm.optionMatch _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherInl _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherInr _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherMatch _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.refl _ => RawTerm.refineElim developedRefined
  | RawTerm.idJ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.modIntro _ => RawTerm.refineElim developedRefined
  | RawTerm.modElim _ => RawTerm.refineElim developedRefined
  | RawTerm.subsume _ => RawTerm.refineElim developedRefined
  | RawTerm.interval0 => RawTerm.refineElim developedRefined
  | RawTerm.interval1 => RawTerm.refineElim developedRefined
  | RawTerm.intervalOpp _ => RawTerm.refineElim developedRefined
  | RawTerm.intervalMeet _ _ => RawTerm.refineElim developedRefined
  | RawTerm.intervalJoin _ _ => RawTerm.refineElim developedRefined
  | RawTerm.pathLam _ => RawTerm.refineElim developedRefined
  | RawTerm.pathApp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.glueIntro _ _ => RawTerm.refineElim developedRefined
  | RawTerm.glueElim _ => RawTerm.refineElim developedRefined
  | RawTerm.transp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.hcomp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqRefl _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqJ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqFunext _ => RawTerm.refineElim developedRefined
  | RawTerm.idStrictRefl _ => RawTerm.refineElim developedRefined
  | RawTerm.idStrictRec _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivIntro _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivApp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.refineElim _ => RawTerm.refineElim developedRefined
  | RawTerm.recordIntro _ => RawTerm.refineElim developedRefined
  | RawTerm.recordProj _ => RawTerm.refineElim developedRefined
  | RawTerm.codataUnfold _ _ => RawTerm.refineElim developedRefined
  | RawTerm.codataDest _ => RawTerm.refineElim developedRefined
  | RawTerm.sessionSend _ _ => RawTerm.refineElim developedRefined
  | RawTerm.sessionRecv _ => RawTerm.refineElim developedRefined
  | RawTerm.effectPerform _ _ => RawTerm.refineElim developedRefined
  | RawTerm.universeCode _ => RawTerm.refineElim developedRefined
  | RawTerm.arrowCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.piTyCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.sigmaTyCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.productCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.sumCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.listCode _ => RawTerm.refineElim developedRefined
  | RawTerm.optionCode _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.idCode _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.cumulUpMarker _ => RawTerm.refineElim developedRefined

/-- Record projection redex: `recordProj (recordIntro field) → field`;
otherwise rebuild `recordProj dr`. -/
def RawTerm.cdRecordProjCase {scope : Nat}
    (developedRecord : RawTerm scope) : RawTerm scope :=
  match developedRecord with
  | RawTerm.recordIntro firstField => firstField
  | RawTerm.var _ => RawTerm.recordProj developedRecord
  | RawTerm.unit => RawTerm.recordProj developedRecord
  | RawTerm.lam _ => RawTerm.recordProj developedRecord
  | RawTerm.app _ _ => RawTerm.recordProj developedRecord
  | RawTerm.pair _ _ => RawTerm.recordProj developedRecord
  | RawTerm.fst _ => RawTerm.recordProj developedRecord
  | RawTerm.snd _ => RawTerm.recordProj developedRecord
  | RawTerm.boolTrue => RawTerm.recordProj developedRecord
  | RawTerm.boolFalse => RawTerm.recordProj developedRecord
  | RawTerm.boolElim _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.natZero => RawTerm.recordProj developedRecord
  | RawTerm.natSucc _ => RawTerm.recordProj developedRecord
  | RawTerm.natElim _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.natRec _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.listNil => RawTerm.recordProj developedRecord
  | RawTerm.listCons _ _ => RawTerm.recordProj developedRecord
  | RawTerm.listElim _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.optionNone => RawTerm.recordProj developedRecord
  | RawTerm.optionSome _ => RawTerm.recordProj developedRecord
  | RawTerm.optionMatch _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherInl _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherInr _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherMatch _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.refl _ => RawTerm.recordProj developedRecord
  | RawTerm.idJ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.modIntro _ => RawTerm.recordProj developedRecord
  | RawTerm.modElim _ => RawTerm.recordProj developedRecord
  | RawTerm.subsume _ => RawTerm.recordProj developedRecord
  | RawTerm.interval0 => RawTerm.recordProj developedRecord
  | RawTerm.interval1 => RawTerm.recordProj developedRecord
  | RawTerm.intervalOpp _ => RawTerm.recordProj developedRecord
  | RawTerm.intervalMeet _ _ => RawTerm.recordProj developedRecord
  | RawTerm.intervalJoin _ _ => RawTerm.recordProj developedRecord
  | RawTerm.pathLam _ => RawTerm.recordProj developedRecord
  | RawTerm.pathApp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.glueIntro _ _ => RawTerm.recordProj developedRecord
  | RawTerm.glueElim _ => RawTerm.recordProj developedRecord
  | RawTerm.transp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.hcomp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqRefl _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqJ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqFunext _ => RawTerm.recordProj developedRecord
  | RawTerm.idStrictRefl _ => RawTerm.recordProj developedRecord
  | RawTerm.idStrictRec _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivIntro _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivApp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.refineIntro _ _ => RawTerm.recordProj developedRecord
  | RawTerm.refineElim _ => RawTerm.recordProj developedRecord
  | RawTerm.recordProj _ => RawTerm.recordProj developedRecord
  | RawTerm.codataUnfold _ _ => RawTerm.recordProj developedRecord
  | RawTerm.codataDest _ => RawTerm.recordProj developedRecord
  | RawTerm.sessionSend _ _ => RawTerm.recordProj developedRecord
  | RawTerm.sessionRecv _ => RawTerm.recordProj developedRecord
  | RawTerm.effectPerform _ _ => RawTerm.recordProj developedRecord
  | RawTerm.universeCode _ => RawTerm.recordProj developedRecord
  | RawTerm.arrowCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.piTyCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.sigmaTyCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.productCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.sumCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.listCode _ => RawTerm.recordProj developedRecord
  | RawTerm.optionCode _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.idCode _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.cumulUpMarker _ => RawTerm.recordProj developedRecord

/-- Codata observation redex:
`codataDest (codataUnfold state transition) → transition state`;
otherwise rebuild `codataDest developedCodata`. -/
def RawTerm.cdCodataDestCase {scope : Nat}
    (developedCodata : RawTerm scope) : RawTerm scope :=
  match developedCodata with
  | RawTerm.codataUnfold stateValue transition =>
      RawTerm.app transition stateValue
  | RawTerm.var _ => RawTerm.codataDest developedCodata
  | RawTerm.unit => RawTerm.codataDest developedCodata
  | RawTerm.lam _ => RawTerm.codataDest developedCodata
  | RawTerm.app _ _ => RawTerm.codataDest developedCodata
  | RawTerm.pair _ _ => RawTerm.codataDest developedCodata
  | RawTerm.fst _ => RawTerm.codataDest developedCodata
  | RawTerm.snd _ => RawTerm.codataDest developedCodata
  | RawTerm.boolTrue => RawTerm.codataDest developedCodata
  | RawTerm.boolFalse => RawTerm.codataDest developedCodata
  | RawTerm.boolElim _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.natZero => RawTerm.codataDest developedCodata
  | RawTerm.natSucc _ => RawTerm.codataDest developedCodata
  | RawTerm.natElim _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.natRec _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.listNil => RawTerm.codataDest developedCodata
  | RawTerm.listCons _ _ => RawTerm.codataDest developedCodata
  | RawTerm.listElim _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.optionNone => RawTerm.codataDest developedCodata
  | RawTerm.optionSome _ => RawTerm.codataDest developedCodata
  | RawTerm.optionMatch _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherInl _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherInr _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherMatch _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.refl _ => RawTerm.codataDest developedCodata
  | RawTerm.idJ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.modIntro _ => RawTerm.codataDest developedCodata
  | RawTerm.modElim _ => RawTerm.codataDest developedCodata
  | RawTerm.subsume _ => RawTerm.codataDest developedCodata
  | RawTerm.interval0 => RawTerm.codataDest developedCodata
  | RawTerm.interval1 => RawTerm.codataDest developedCodata
  | RawTerm.intervalOpp _ => RawTerm.codataDest developedCodata
  | RawTerm.intervalMeet _ _ => RawTerm.codataDest developedCodata
  | RawTerm.intervalJoin _ _ => RawTerm.codataDest developedCodata
  | RawTerm.pathLam _ => RawTerm.codataDest developedCodata
  | RawTerm.pathApp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.glueIntro _ _ => RawTerm.codataDest developedCodata
  | RawTerm.glueElim _ => RawTerm.codataDest developedCodata
  | RawTerm.transp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.hcomp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqRefl _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqJ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqFunext _ => RawTerm.codataDest developedCodata
  | RawTerm.idStrictRefl _ => RawTerm.codataDest developedCodata
  | RawTerm.idStrictRec _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivIntro _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivApp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.refineIntro _ _ => RawTerm.codataDest developedCodata
  | RawTerm.refineElim _ => RawTerm.codataDest developedCodata
  | RawTerm.recordIntro _ => RawTerm.codataDest developedCodata
  | RawTerm.recordProj _ => RawTerm.codataDest developedCodata
  | RawTerm.codataDest _ => RawTerm.codataDest developedCodata
  | RawTerm.sessionSend _ _ => RawTerm.codataDest developedCodata
  | RawTerm.sessionRecv _ => RawTerm.codataDest developedCodata
  | RawTerm.effectPerform _ _ => RawTerm.codataDest developedCodata
  | RawTerm.universeCode _ => RawTerm.codataDest developedCodata
  | RawTerm.arrowCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.piTyCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.sigmaTyCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.productCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.sumCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.listCode _ => RawTerm.codataDest developedCodata
  | RawTerm.optionCode _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.idCode _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.cumulUpMarker _ => RawTerm.codataDest developedCodata

/-- Fst redex: `fst (a, b) → a`; otherwise rebuild `fst dp`. -/
def RawTerm.cdFstCase {scope : Nat}
    (developedPair : RawTerm scope) : RawTerm scope :=
  match developedPair with
  | RawTerm.pair firstValue _ => firstValue
  | RawTerm.var _ => RawTerm.fst developedPair
  | RawTerm.unit => RawTerm.fst developedPair
  | RawTerm.lam _ => RawTerm.fst developedPair
  | RawTerm.app _ _ => RawTerm.fst developedPair
  | RawTerm.fst _ => RawTerm.fst developedPair
  | RawTerm.snd _ => RawTerm.fst developedPair
  | RawTerm.boolTrue => RawTerm.fst developedPair
  | RawTerm.boolFalse => RawTerm.fst developedPair
  | RawTerm.boolElim _ _ _ => RawTerm.fst developedPair
  | RawTerm.natZero => RawTerm.fst developedPair
  | RawTerm.natSucc _ => RawTerm.fst developedPair
  | RawTerm.natElim _ _ _ => RawTerm.fst developedPair
  | RawTerm.natRec _ _ _ => RawTerm.fst developedPair
  | RawTerm.listNil => RawTerm.fst developedPair
  | RawTerm.listCons _ _ => RawTerm.fst developedPair
  | RawTerm.listElim _ _ _ => RawTerm.fst developedPair
  | RawTerm.optionNone => RawTerm.fst developedPair
  | RawTerm.optionSome _ => RawTerm.fst developedPair
  | RawTerm.optionMatch _ _ _ => RawTerm.fst developedPair
  | RawTerm.eitherInl _ => RawTerm.fst developedPair
  | RawTerm.eitherInr _ => RawTerm.fst developedPair
  | RawTerm.eitherMatch _ _ _ => RawTerm.fst developedPair
  | RawTerm.refl _ => RawTerm.fst developedPair
  | RawTerm.idJ _ _ => RawTerm.fst developedPair
  | RawTerm.modIntro _ => RawTerm.fst developedPair
  | RawTerm.modElim _ => RawTerm.fst developedPair
  | RawTerm.subsume _ => RawTerm.fst developedPair
  | RawTerm.interval0 => RawTerm.fst developedPair
  | RawTerm.interval1 => RawTerm.fst developedPair
  | RawTerm.intervalOpp _ => RawTerm.fst developedPair
  | RawTerm.intervalMeet _ _ => RawTerm.fst developedPair
  | RawTerm.intervalJoin _ _ => RawTerm.fst developedPair
  | RawTerm.pathLam _ => RawTerm.fst developedPair
  | RawTerm.pathApp _ _ => RawTerm.fst developedPair
  | RawTerm.glueIntro _ _ => RawTerm.fst developedPair
  | RawTerm.glueElim _ => RawTerm.fst developedPair
  | RawTerm.transp _ _ => RawTerm.fst developedPair
  | RawTerm.hcomp _ _ => RawTerm.fst developedPair
  | RawTerm.oeqRefl _ => RawTerm.fst developedPair
  | RawTerm.oeqJ _ _ => RawTerm.fst developedPair
  | RawTerm.oeqFunext _ => RawTerm.fst developedPair
  | RawTerm.idStrictRefl _ => RawTerm.fst developedPair
  | RawTerm.idStrictRec _ _ => RawTerm.fst developedPair
  | RawTerm.equivIntro _ _ => RawTerm.fst developedPair
  | RawTerm.equivApp _ _ => RawTerm.fst developedPair
  | RawTerm.refineIntro _ _ => RawTerm.fst developedPair
  | RawTerm.refineElim _ => RawTerm.fst developedPair
  | RawTerm.recordIntro _ => RawTerm.fst developedPair
  | RawTerm.recordProj _ => RawTerm.fst developedPair
  | RawTerm.codataUnfold _ _ => RawTerm.fst developedPair
  | RawTerm.codataDest _ => RawTerm.fst developedPair
  | RawTerm.sessionSend _ _ => RawTerm.fst developedPair
  | RawTerm.sessionRecv _ => RawTerm.fst developedPair
  | RawTerm.effectPerform _ _ => RawTerm.fst developedPair
  | RawTerm.universeCode _ => RawTerm.fst developedPair
  | RawTerm.arrowCode _ _ => RawTerm.fst developedPair
  | RawTerm.piTyCode _ _ => RawTerm.fst developedPair
  | RawTerm.sigmaTyCode _ _ => RawTerm.fst developedPair
  | RawTerm.productCode _ _ => RawTerm.fst developedPair
  | RawTerm.sumCode _ _ => RawTerm.fst developedPair
  | RawTerm.listCode _ => RawTerm.fst developedPair
  | RawTerm.optionCode _ => RawTerm.fst developedPair
  | RawTerm.eitherCode _ _ => RawTerm.fst developedPair
  | RawTerm.idCode _ _ _ => RawTerm.fst developedPair
  | RawTerm.equivCode _ _ => RawTerm.fst developedPair
  | RawTerm.cumulUpMarker _ => RawTerm.fst developedPair

/-- Snd redex: `snd (a, b) → b`; otherwise rebuild `snd dp`. -/
def RawTerm.cdSndCase {scope : Nat}
    (developedPair : RawTerm scope) : RawTerm scope :=
  match developedPair with
  | RawTerm.pair _ secondValue => secondValue
  | RawTerm.var _ => RawTerm.snd developedPair
  | RawTerm.unit => RawTerm.snd developedPair
  | RawTerm.lam _ => RawTerm.snd developedPair
  | RawTerm.app _ _ => RawTerm.snd developedPair
  | RawTerm.fst _ => RawTerm.snd developedPair
  | RawTerm.snd _ => RawTerm.snd developedPair
  | RawTerm.boolTrue => RawTerm.snd developedPair
  | RawTerm.boolFalse => RawTerm.snd developedPair
  | RawTerm.boolElim _ _ _ => RawTerm.snd developedPair
  | RawTerm.natZero => RawTerm.snd developedPair
  | RawTerm.natSucc _ => RawTerm.snd developedPair
  | RawTerm.natElim _ _ _ => RawTerm.snd developedPair
  | RawTerm.natRec _ _ _ => RawTerm.snd developedPair
  | RawTerm.listNil => RawTerm.snd developedPair
  | RawTerm.listCons _ _ => RawTerm.snd developedPair
  | RawTerm.listElim _ _ _ => RawTerm.snd developedPair
  | RawTerm.optionNone => RawTerm.snd developedPair
  | RawTerm.optionSome _ => RawTerm.snd developedPair
  | RawTerm.optionMatch _ _ _ => RawTerm.snd developedPair
  | RawTerm.eitherInl _ => RawTerm.snd developedPair
  | RawTerm.eitherInr _ => RawTerm.snd developedPair
  | RawTerm.eitherMatch _ _ _ => RawTerm.snd developedPair
  | RawTerm.refl _ => RawTerm.snd developedPair
  | RawTerm.idJ _ _ => RawTerm.snd developedPair
  | RawTerm.modIntro _ => RawTerm.snd developedPair
  | RawTerm.modElim _ => RawTerm.snd developedPair
  | RawTerm.subsume _ => RawTerm.snd developedPair
  | RawTerm.interval0 => RawTerm.snd developedPair
  | RawTerm.interval1 => RawTerm.snd developedPair
  | RawTerm.intervalOpp _ => RawTerm.snd developedPair
  | RawTerm.intervalMeet _ _ => RawTerm.snd developedPair
  | RawTerm.intervalJoin _ _ => RawTerm.snd developedPair
  | RawTerm.pathLam _ => RawTerm.snd developedPair
  | RawTerm.pathApp _ _ => RawTerm.snd developedPair
  | RawTerm.glueIntro _ _ => RawTerm.snd developedPair
  | RawTerm.glueElim _ => RawTerm.snd developedPair
  | RawTerm.transp _ _ => RawTerm.snd developedPair
  | RawTerm.hcomp _ _ => RawTerm.snd developedPair
  | RawTerm.oeqRefl _ => RawTerm.snd developedPair
  | RawTerm.oeqJ _ _ => RawTerm.snd developedPair
  | RawTerm.oeqFunext _ => RawTerm.snd developedPair
  | RawTerm.idStrictRefl _ => RawTerm.snd developedPair
  | RawTerm.idStrictRec _ _ => RawTerm.snd developedPair
  | RawTerm.equivIntro _ _ => RawTerm.snd developedPair
  | RawTerm.equivApp _ _ => RawTerm.snd developedPair
  | RawTerm.refineIntro _ _ => RawTerm.snd developedPair
  | RawTerm.refineElim _ => RawTerm.snd developedPair
  | RawTerm.recordIntro _ => RawTerm.snd developedPair
  | RawTerm.recordProj _ => RawTerm.snd developedPair
  | RawTerm.codataUnfold _ _ => RawTerm.snd developedPair
  | RawTerm.codataDest _ => RawTerm.snd developedPair
  | RawTerm.sessionSend _ _ => RawTerm.snd developedPair
  | RawTerm.sessionRecv _ => RawTerm.snd developedPair
  | RawTerm.effectPerform _ _ => RawTerm.snd developedPair
  | RawTerm.universeCode _ => RawTerm.snd developedPair
  | RawTerm.arrowCode _ _ => RawTerm.snd developedPair
  | RawTerm.piTyCode _ _ => RawTerm.snd developedPair
  | RawTerm.sigmaTyCode _ _ => RawTerm.snd developedPair
  | RawTerm.productCode _ _ => RawTerm.snd developedPair
  | RawTerm.sumCode _ _ => RawTerm.snd developedPair
  | RawTerm.listCode _ => RawTerm.snd developedPair
  | RawTerm.optionCode _ => RawTerm.snd developedPair
  | RawTerm.eitherCode _ _ => RawTerm.snd developedPair
  | RawTerm.idCode _ _ _ => RawTerm.snd developedPair
  | RawTerm.equivCode _ _ => RawTerm.snd developedPair
  | RawTerm.cumulUpMarker _ => RawTerm.snd developedPair

/-- BoolElim redex: `boolElim true t e → t`, `boolElim false t e → e`;
otherwise rebuild. -/
def RawTerm.cdBoolElimCase {scope : Nat}
    (developedScrutinee developedThen developedElse : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.boolTrue => developedThen
  | RawTerm.boolFalse => developedElse
  | RawTerm.var _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.unit =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.lam _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.app _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pair _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.fst _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.snd _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.boolElim _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natZero =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natSucc _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natElim _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natRec _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listNil =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listCons _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listElim _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionNone =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionSome _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherInl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherInr _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idJ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.modIntro _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.modElim _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.subsume _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.interval0 =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.interval1 =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.intervalOpp _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.intervalMeet _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.intervalJoin _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pathLam _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pathApp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.glueIntro _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.glueElim _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.transp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.hcomp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqRefl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqJ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqFunext _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idStrictRefl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idStrictRec _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivIntro _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivApp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refineIntro _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refineElim _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.recordIntro _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.recordProj _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.codataUnfold _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.codataDest _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sessionSend _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sessionRecv _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.effectPerform _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.universeCode _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.arrowCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.piTyCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.productCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sumCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listCode _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionCode _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idCode _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.cumulUpMarker _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse

/-- NatElim redex: `natElim 0 z s → z`, `natElim (succ p) z s → s p`;
otherwise rebuild. -/
def RawTerm.cdNatElimCase {scope : Nat}
    (developedScrutinee developedZero developedSucc : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.natZero => developedZero
  | RawTerm.natSucc predecessor =>
      RawTerm.app developedSucc predecessor
  | RawTerm.var _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.unit =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.lam _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.app _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pair _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.fst _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.snd _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolTrue =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolFalse =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolElim _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.natElim _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.natRec _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listNil =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listCons _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listElim _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionNone =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionSome _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherInl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherInr _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idJ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.modIntro _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.modElim _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.subsume _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.interval0 =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.interval1 =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.intervalOpp _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.intervalMeet _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.intervalJoin _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pathLam _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pathApp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.glueIntro _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.glueElim _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.transp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.hcomp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqRefl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqJ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqFunext _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRefl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRec _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivIntro _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivApp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refineIntro _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refineElim _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.recordIntro _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.recordProj _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.codataUnfold _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.codataDest _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sessionSend _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sessionRecv _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.effectPerform _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.universeCode _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.arrowCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.piTyCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.productCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sumCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listCode _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionCode _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idCode _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.cumulUpMarker _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc

/-- NatRec redex: `natRec 0 z s → z`,
`natRec (succ p) z s → s p (natRec p z s)`; otherwise rebuild. -/
def RawTerm.cdNatRecCase {scope : Nat}
    (developedScrutinee developedZero developedSucc : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.natZero => developedZero
  | RawTerm.natSucc predecessor =>
      RawTerm.app (RawTerm.app developedSucc predecessor)
        (RawTerm.natRec predecessor developedZero developedSucc)
  | RawTerm.var _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.unit =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.lam _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.app _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pair _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.fst _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.snd _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolTrue =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolFalse =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolElim _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.natElim _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.natRec _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listNil =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listCons _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listElim _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionNone =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionSome _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherInl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherInr _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idJ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.modIntro _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.modElim _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.subsume _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.interval0 =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.interval1 =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.intervalOpp _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.intervalMeet _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.intervalJoin _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pathLam _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pathApp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.glueIntro _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.glueElim _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.transp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.hcomp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqRefl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqJ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqFunext _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRefl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRec _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivIntro _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivApp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refineIntro _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refineElim _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.recordIntro _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.recordProj _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.codataUnfold _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.codataDest _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sessionSend _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sessionRecv _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.effectPerform _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.universeCode _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.arrowCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.piTyCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.productCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sumCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listCode _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionCode _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idCode _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.cumulUpMarker _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc

/-- ListElim redex: `listElim nil n c → n`,
`listElim (cons h t) n c → c h t`; otherwise rebuild. -/
def RawTerm.cdListElimCase {scope : Nat}
    (developedScrutinee developedNil developedCons : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.listNil => developedNil
  | RawTerm.listCons headTerm tailTerm =>
      RawTerm.app (RawTerm.app developedCons headTerm) tailTerm
  | RawTerm.var _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.unit =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.lam _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.app _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pair _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.fst _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.snd _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolTrue =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolFalse =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolElim _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natZero =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natSucc _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natElim _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natRec _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.listElim _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionNone =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionSome _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherInl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherInr _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.refl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idJ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.modIntro _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.modElim _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.subsume _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.interval0 =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.interval1 =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.intervalOpp _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.intervalMeet _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.intervalJoin _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pathLam _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pathApp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.glueIntro _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.glueElim _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.transp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.hcomp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqRefl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqJ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqFunext _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idStrictRefl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idStrictRec _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivIntro _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivApp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.refineIntro _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.refineElim _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.recordIntro _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.recordProj _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.codataUnfold _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.codataDest _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sessionSend _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sessionRecv _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.effectPerform _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.universeCode _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.arrowCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.piTyCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.productCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sumCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.listCode _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionCode _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idCode _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.cumulUpMarker _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons

/-- OptionMatch redex: `optionMatch none n s → n`,
`optionMatch (some v) n s → s v`; otherwise rebuild. -/
def RawTerm.cdOptionMatchCase {scope : Nat}
    (developedScrutinee developedNone developedSome : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.optionNone => developedNone
  | RawTerm.optionSome valueTerm =>
      RawTerm.app developedSome valueTerm
  | RawTerm.var _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.unit =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.lam _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.app _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pair _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.fst _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.snd _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolTrue =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolFalse =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolElim _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natZero =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natSucc _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natElim _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natRec _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listNil =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listCons _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listElim _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherInl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherInr _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idJ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.modIntro _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.modElim _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.subsume _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.interval0 =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.interval1 =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.intervalOpp _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.intervalMeet _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.intervalJoin _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pathLam _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pathApp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.glueIntro _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.glueElim _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.transp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.hcomp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqRefl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqJ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqFunext _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idStrictRefl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idStrictRec _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivIntro _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivApp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refineIntro _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refineElim _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.recordIntro _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.recordProj _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.codataUnfold _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.codataDest _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sessionSend _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sessionRecv _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.effectPerform _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.universeCode _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.arrowCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.piTyCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.productCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sumCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listCode _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.optionCode _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idCode _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.cumulUpMarker _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome

/-- EitherMatch redex: `eitherMatch (inl v) l r → l v`,
`eitherMatch (inr v) l r → r v`; otherwise rebuild. -/
def RawTerm.cdEitherMatchCase {scope : Nat}
    (developedScrutinee developedLeft developedRight : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.eitherInl valueTerm => RawTerm.app developedLeft valueTerm
  | RawTerm.eitherInr valueTerm => RawTerm.app developedRight valueTerm
  | RawTerm.var _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.unit =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.lam _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.app _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pair _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.fst _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.snd _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolTrue =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolFalse =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolElim _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natZero =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natSucc _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natElim _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natRec _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listNil =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listCons _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listElim _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionNone =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionSome _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refl _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idJ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.modIntro _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.modElim _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.subsume _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.interval0 =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.interval1 =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.intervalOpp _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.intervalMeet _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.intervalJoin _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pathLam _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pathApp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.glueIntro _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.glueElim _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.transp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.hcomp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqRefl _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqJ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqFunext _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idStrictRefl _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idStrictRec _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivIntro _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivApp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refineIntro _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refineElim _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.recordIntro _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.recordProj _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.codataUnfold _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.codataDest _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sessionSend _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sessionRecv _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.effectPerform _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.universeCode _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.arrowCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.piTyCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.productCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sumCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listCode _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionCode _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.eitherCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idCode _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.cumulUpMarker _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight

/-- IdJ redex: `idJ b (refl _) → b`; otherwise rebuild. -/
def RawTerm.cdIdJCase {scope : Nat}
    (developedBase developedWitness : RawTerm scope) : RawTerm scope :=
  match developedWitness with
  | RawTerm.refl _ => developedBase
  | RawTerm.var _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.unit => RawTerm.idJ developedBase developedWitness
  | RawTerm.lam _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.app _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pair _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.fst _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.snd _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.boolTrue => RawTerm.idJ developedBase developedWitness
  | RawTerm.boolFalse => RawTerm.idJ developedBase developedWitness
  | RawTerm.boolElim _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.natZero => RawTerm.idJ developedBase developedWitness
  | RawTerm.natSucc _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.natElim _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.natRec _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.listNil => RawTerm.idJ developedBase developedWitness
  | RawTerm.listCons _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.listElim _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionNone => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionSome _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionMatch _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherInl _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherInr _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherMatch _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idJ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.modIntro _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.modElim _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.subsume _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.interval0 => RawTerm.idJ developedBase developedWitness
  | RawTerm.interval1 => RawTerm.idJ developedBase developedWitness
  | RawTerm.intervalOpp _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.intervalMeet _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.intervalJoin _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pathLam _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pathApp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.glueIntro _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.glueElim _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.transp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.hcomp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqRefl _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqJ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqFunext _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idStrictRefl _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idStrictRec _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivIntro _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivApp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.refineIntro _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.refineElim _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.recordIntro _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.recordProj _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.codataUnfold _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.codataDest _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sessionSend _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sessionRecv _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.effectPerform _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.universeCode _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.arrowCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.piTyCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sigmaTyCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.productCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sumCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.listCode _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionCode _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idCode _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.cumulUpMarker _ => RawTerm.idJ developedBase developedWitness

/-- Complete development on raw terms.  Maximal parallel reduct:
every visible redex contracts, every subterm is recursively
developed.  Zero axioms: full enumeration in every inner match
keeps Lean's match compiler from leaking propext.

Each redex-bearing case dispatches to a per-redex helper
(`cdAppCase`, `cdFstCase`, ..., `cdIdJCase`) — see comment at top.
This factoring keeps `unfold RawTerm.cd` cheap and confines the
55-arm inner match to one helper definition at a time, fitting the
200K-heartbeat budget enforced by simp's nested whnf. -/
def RawTerm.cd : ∀ {scope : Nat}, RawTerm scope → RawTerm scope
  | _, .var position => RawTerm.var position
  | _, .unit => RawTerm.unit
  | _, .lam body => RawTerm.lam (RawTerm.cd body)
  | _, .app functionTerm argumentTerm =>
      RawTerm.cdAppCase (RawTerm.cd functionTerm) (RawTerm.cd argumentTerm)
  | _, .pair firstValue secondValue =>
      RawTerm.pair (RawTerm.cd firstValue) (RawTerm.cd secondValue)
  | _, .fst pairTerm =>
      RawTerm.cdFstCase (RawTerm.cd pairTerm)
  | _, .snd pairTerm =>
      RawTerm.cdSndCase (RawTerm.cd pairTerm)
  | _, .boolTrue => RawTerm.boolTrue
  | _, .boolFalse => RawTerm.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      RawTerm.cdBoolElimCase (RawTerm.cd scrutinee)
        (RawTerm.cd thenBranch) (RawTerm.cd elseBranch)
  | _, .natZero => RawTerm.natZero
  | _, .natSucc predecessor => RawTerm.natSucc (RawTerm.cd predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      RawTerm.cdNatElimCase (RawTerm.cd scrutinee)
        (RawTerm.cd zeroBranch) (RawTerm.cd succBranch)
  | _, .natRec scrutinee zeroBranch succBranch =>
      RawTerm.cdNatRecCase (RawTerm.cd scrutinee)
        (RawTerm.cd zeroBranch) (RawTerm.cd succBranch)
  | _, .listNil => RawTerm.listNil
  | _, .listCons headTerm tailTerm =>
      RawTerm.listCons (RawTerm.cd headTerm) (RawTerm.cd tailTerm)
  | _, .listElim scrutinee nilBranch consBranch =>
      RawTerm.cdListElimCase (RawTerm.cd scrutinee)
        (RawTerm.cd nilBranch) (RawTerm.cd consBranch)
  | _, .optionNone => RawTerm.optionNone
  | _, .optionSome valueTerm => RawTerm.optionSome (RawTerm.cd valueTerm)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      RawTerm.cdOptionMatchCase (RawTerm.cd scrutinee)
        (RawTerm.cd noneBranch) (RawTerm.cd someBranch)
  | _, .eitherInl valueTerm => RawTerm.eitherInl (RawTerm.cd valueTerm)
  | _, .eitherInr valueTerm => RawTerm.eitherInr (RawTerm.cd valueTerm)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      RawTerm.cdEitherMatchCase (RawTerm.cd scrutinee)
        (RawTerm.cd leftBranch) (RawTerm.cd rightBranch)
  | _, .refl rawWitness => RawTerm.refl (RawTerm.cd rawWitness)
  | _, .idJ baseCase witness =>
      RawTerm.cdIdJCase (RawTerm.cd baseCase) (RawTerm.cd witness)
  | _, .modIntro innerTerm => RawTerm.modIntro (RawTerm.cd innerTerm)
  | _, .modElim innerTerm => RawTerm.cdModElimCase (RawTerm.cd innerTerm)
  | _, .subsume innerTerm => RawTerm.subsume (RawTerm.cd innerTerm)
  -- D1.6/D2.5: cubical interval + path; pathApp has betaPathApp.
  | _, .interval0 => RawTerm.interval0
  | _, .interval1 => RawTerm.interval1
  | _, .intervalOpp intervalTerm => RawTerm.intervalOpp (RawTerm.cd intervalTerm)
  | _, .intervalMeet leftInterval rightInterval =>
      RawTerm.intervalMeet (RawTerm.cd leftInterval) (RawTerm.cd rightInterval)
  | _, .intervalJoin leftInterval rightInterval =>
      RawTerm.intervalJoin (RawTerm.cd leftInterval) (RawTerm.cd rightInterval)
  | _, .pathLam body => RawTerm.pathLam (RawTerm.cd body)
  | _, .pathApp pathTerm intervalArg =>
      RawTerm.cdPathAppCase (RawTerm.cd pathTerm) (RawTerm.cd intervalArg)
  | _, .glueIntro baseValue partialValue =>
      RawTerm.glueIntro (RawTerm.cd baseValue) (RawTerm.cd partialValue)
  | _, .glueElim gluedValue => RawTerm.cdGlueElimCase (RawTerm.cd gluedValue)
  | _, .transp pathTerm sourceTerm =>
      RawTerm.transp (RawTerm.cd pathTerm) (RawTerm.cd sourceTerm)
  | _, .hcomp sidesTerm capTerm =>
      RawTerm.hcomp (RawTerm.cd sidesTerm) (RawTerm.cd capTerm)
  -- D1.6: observational + strict equality (pure cong)
  | _, .oeqRefl witnessTerm => RawTerm.oeqRefl (RawTerm.cd witnessTerm)
  | _, .oeqJ baseCase witness =>
      RawTerm.oeqJ (RawTerm.cd baseCase) (RawTerm.cd witness)
  | _, .oeqFunext pointwiseEquality =>
      RawTerm.oeqFunext (RawTerm.cd pointwiseEquality)
  | _, .idStrictRefl witnessTerm => RawTerm.idStrictRefl (RawTerm.cd witnessTerm)
  | _, .idStrictRec baseCase witness =>
      RawTerm.idStrictRec (RawTerm.cd baseCase) (RawTerm.cd witness)
  -- D1.6: type equivalence (pure cong)
  | _, .equivIntro forwardFn backwardFn =>
      RawTerm.equivIntro (RawTerm.cd forwardFn) (RawTerm.cd backwardFn)
  | _, .equivApp equivTerm argument =>
      RawTerm.equivApp (RawTerm.cd equivTerm) (RawTerm.cd argument)
  -- D1.6/D2.7: refinement, record, codata.  `refineElim` and
  -- `recordProj` carry raw β redexes; the rest are pure cong.
  | _, .refineIntro rawValue predicateProof =>
      RawTerm.refineIntro (RawTerm.cd rawValue) (RawTerm.cd predicateProof)
  | _, .refineElim refinedValue =>
      RawTerm.cdRefineElimCase (RawTerm.cd refinedValue)
  | _, .recordIntro firstField => RawTerm.recordIntro (RawTerm.cd firstField)
  | _, .recordProj recordValue =>
      RawTerm.cdRecordProjCase (RawTerm.cd recordValue)
  | _, .codataUnfold initialState transition =>
      RawTerm.codataUnfold (RawTerm.cd initialState) (RawTerm.cd transition)
  | _, .codataDest codataValue => RawTerm.cdCodataDestCase (RawTerm.cd codataValue)
  -- D1.6: sessions, effects (pure cong)
  | _, .sessionSend channel payload =>
      RawTerm.sessionSend (RawTerm.cd channel) (RawTerm.cd payload)
  | _, .sessionRecv channel => RawTerm.sessionRecv (RawTerm.cd channel)
  | _, .effectPerform operationTag arguments =>
      RawTerm.effectPerform (RawTerm.cd operationTag) (RawTerm.cd arguments)
  -- D1.6/A2: universeCode is atomic (no subterms to develop)
  | _, .universeCode innerLevel => RawTerm.universeCode innerLevel
  -- CUMUL-2.1 per-shape type codes (pure cong, no β rules — these
  -- are type-code values, recursing on subterms develops them under
  -- the binder where applicable).
  | _, .arrowCode domainCode codomainCode =>
      RawTerm.arrowCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)
  | _, .piTyCode domainCode codomainCode =>
      RawTerm.piTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)
  | _, .sigmaTyCode domainCode codomainCode =>
      RawTerm.sigmaTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)
  | _, .productCode firstCode secondCode =>
      RawTerm.productCode (RawTerm.cd firstCode) (RawTerm.cd secondCode)
  | _, .sumCode leftCode rightCode =>
      RawTerm.sumCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)
  | _, .listCode elementCode =>
      RawTerm.listCode (RawTerm.cd elementCode)
  | _, .optionCode elementCode =>
      RawTerm.optionCode (RawTerm.cd elementCode)
  | _, .eitherCode leftCode rightCode =>
      RawTerm.eitherCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)
  | _, .idCode typeCode leftRaw rightRaw =>
      RawTerm.idCode (RawTerm.cd typeCode) (RawTerm.cd leftRaw) (RawTerm.cd rightRaw)
  | _, .equivCode leftTypeCode rightTypeCode =>
      RawTerm.equivCode (RawTerm.cd leftTypeCode) (RawTerm.cd rightTypeCode)
  -- CUMUL-2.6: cumulUpMarker recurses on inner code raw.
  | _, .cumulUpMarker innerCodeRaw =>
      RawTerm.cumulUpMarker (RawTerm.cd innerCodeRaw)

end LeanFX2
