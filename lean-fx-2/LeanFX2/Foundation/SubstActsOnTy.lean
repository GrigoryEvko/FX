import LeanFX2.Foundation.Subst

/-! # SubstActsOnTy — Tier 3 / MEGA-Z2.A — `Subst level` instances of
the `ActsOnRawTerm` / `ActsOnTyVar` typeclasses.

`Ty.act` (defined in `Foundation/Ty.lean`) takes a Container with
`[Action Container]`, `[ActsOnRawTerm Container]`, and
`[ActsOnTyVar Container level]`.  The Container's instance of
`Action` ships in Z1.B (`Foundation/RawSubst.lean` and
`Foundation/Subst.lean`); the `ActsOnTyVar` / `ActsOnRawTerm`
instances are Z2.A additions.

For `RawRenaming`, both supplemental instances live in
`Foundation/Ty.lean` directly (no cyclic dependency since RawRenaming
is defined upstream in `Foundation/RawSubst.lean`).

For `Subst level`, the Container type is defined in
`Foundation/Subst.lean` (downstream of `Foundation/Ty.lean`).  Adding
the supplemental instances inside `Foundation/Subst.lean` would be
cleaner, but per the MEGA-Z2.A risk-management constraints
`Foundation/Subst.lean` is SEALED at Z1.B's boundary — no
modifications.  Hence this NEW file ships the `Subst level`
supplemental instances downstream of `Foundation/Subst.lean`.

The file does the following:
* `instance : ActsOnRawTerm (Subst level)` — dispatch surface used by
  `Ty.act`'s raw-payload arms (delegates to `RawTerm.act`)
* `instance ActsOnTyVarOfSubst (level : Nat) : ActsOnTyVar (Subst
  level) level` — dispatch surface for `Ty.tyVar` lookup
* `instance : ActsOnRawTermVar (Subst level)` — Z2.A.1 addition,
  needed for `RawTerm.act` to elaborate over a `Subst level`
  Container; pulls the raw substituent out via `sigma.forRaw position`
* Bridge theorems `RawTerm.act_eq_rename` and
  `RawTerm.act_eq_subst_forRaw` witnessing that the unified
  `RawTerm.act` engine produces the same result as the legacy
  `RawTerm.rename` / `RawTerm.subst` operations.  Used by the Z2.B
  bridge (`Ty.act_eq_rename` / `Ty.act_eq_subst`) at the raw-payload
  arms after Z2.A.1's instance-body alignment.

so `Ty.act t (someSubst : Subst level src tgt)` typechecks and
reduces by `rfl` for representative ctors, and the Z2.B bridge
between `Ty.act` and the legacy `Ty.rename` / `Ty.subst` operations
threads cleanly through `RawTerm.act`'s alignment.
-/

namespace LeanFX2

/-! ## ActsOnRawTermVar instance: Subst level — Z2.A.1.

A `Subst level`'s raw-variable lookup consults the `forRaw` field —
a `RawTermSubst source target` (i.e. `Fin source → RawTerm target`).
Returning `sigma.forRaw position` produces a `RawTerm targetScope` at
the var arm of `RawTerm.act`, exactly as needed.

This instance is the load-bearing addition that makes
`RawTerm.act rawTerm (someSubst : Subst level src tgt)` elaborate.
The Z2.A.1 alignment fix in the `ActsOnRawTerm (Subst level)` instance
body below depends on this `ActsOnRawTermVar` instance being in
scope. -/
instance ActsOnRawTermVarOfSubst (level : Nat) :
    ActsOnRawTermVar (Subst level) where
  varToRawTerm := fun someSubst position => someSubst.forRaw position

/-! ## Tier 3 / MEGA-Z5.A.1 — `ActsOnRawTermVarLifts` instance: Subst level.

Mirror of the `RawRenaming` / `RawTermSubst` instances in
`Foundation/RawSubst.lean`.  For `Subst level`, `Action.liftForRaw
sigma = sigma.lift`, and `(sigma.lift).forRaw = sigma.forRaw.lift`
by the definition of `Subst.lift`.  Composing with the var-arms of
`RawTermSubst.lift`:

* `liftForRaw_var_zero` — `(sigma.lift).forRaw ⟨0, _⟩
    = (sigma.forRaw.lift) ⟨0, _⟩
    = RawTerm.var ⟨0, Nat.zero_lt_succ _⟩`
  by `RawTermSubst.lift`'s var-zero arm.  Holds by `rfl`.

* `liftForRaw_var_succ` — `(sigma.lift).forRaw ⟨k+1, h⟩
    = (sigma.forRaw.lift) ⟨k+1, h⟩
    = (sigma.forRaw ⟨k, _⟩).rename RawRenaming.weaken
    = RawTerm.weaken (sigma.forRaw ⟨k, _⟩)
    = RawTerm.weaken (varToRawTerm sigma ⟨k, _⟩)`
  by `RawTermSubst.lift`'s var-succ arm and the
  `ActsOnRawTermVarOfSubst` body above.  Holds by `rfl`. -/
instance ActsOnRawTermVarLiftsOfSubst (level : Nat) :
    ActsOnRawTermVarLifts (Subst level) where
  liftForRaw_var_zero := fun _ => rfl
  liftForRaw_var_succ := fun _ _ => rfl

/-! ## ActsOnRawTerm instance: Subst level — Z2.A.1 alignment.

A Subst's raw-term action delegates to the unified `RawTerm.act`
engine (Z4.A) over the Subst Container itself.  The `ActsOnRawTermVar
(Subst level)` instance above tells `RawTerm.act` how to look up at
var positions: `sigma.forRaw position`.  That matches the var arm of
`RawTerm.subst sigma.forRaw` exactly, so the bridge theorem
`RawTerm.act_eq_subst_forRaw` (below) closes by structural induction.

Pre-Z2.A.1, this instance delegated directly to `RawTerm.subst
sigma.forRaw`.  The alignment switches it to `RawTerm.act`, which is
the Z5.A prerequisite: `Term.act`'s typeclass dispatch routes raw
payloads through `Ty.act`'s `actOnRawTerm` method, and `Ty.act` uses
the same `actOnRawTerm` method to recurse into raw arms.  After the
alignment, `actOnRawTerm action raw = RawTerm.act raw action` is `rfl`
for both Container instances. -/
instance ActsOnRawTermOfSubst (level : Nat) :
    ActsOnRawTerm (Subst level) where
  actOnRawTerm := fun someSubst rawTerm => RawTerm.act rawTerm someSubst

/-! ## ActsOnTyVar instance: Subst level.

A Subst's variable lookup consults `forTy`, which by definition
returns a `Ty level tgt` substituent.  The instance pins `level`
exactly to the Subst's level parameter. -/

instance ActsOnTyVarOfSubst (level : Nat) :
    ActsOnTyVar (Subst level) level where
  varToTy := fun someSubst position => someSubst.forTy position

/-! ## Z2.A.1 bridge theorems: `RawTerm.act` ↔ legacy operations.

After Z2.A.1's alignment fix, the `ActsOnRawTerm` instances in
`Foundation/Ty.lean` (RawRenaming) and above (Subst level) delegate
to `RawTerm.act` instead of `RawTerm.rename` / `RawTerm.subst`.
This means the Z2.B bridge theorems (`Ty.act_eq_rename` /
`Ty.act_eq_subst`) — which previously closed at raw-payload arms by
`rfl` because the OLD `actOnRawTerm` body produced exactly the
`raw.rename` / `raw.subst` shape — now need a propositional bridge
between `RawTerm.act` and the legacy operations.

The two theorems below ship that bridge by 56-case structural
induction on `RawTerm`.  Each arm reduces to `rfl` (leaves) or to a
recursive IH application (recursive ctors).  Binder arms (`lam`,
`pathLam`) use the fact that `Action.liftForRaw rho = rho.lift` for
`RawRenaming` and `Action.liftForRaw sigma = sigma.lift` for
`Subst level` (and `sigma.lift.forRaw = sigma.forRaw.lift` by
`Subst.lift`'s definition), making the IH applicable directly.

For `Subst level`, the var arm uses
`ActsOnRawTermVarOfSubst.varToRawTerm sigma position = sigma.forRaw
position`, which matches the var arm of `RawTerm.subst sigma.forRaw`
exactly. -/

/-- Bridge theorem: applying `RawTerm.act` over a `RawRenaming`
Container produces the same result as applying `RawTerm.rename`
directly.  Proved by structural induction on the raw term over all 56
RawTerm constructors.

Every arm reduces by `rfl` (leaves) or by the inductive hypothesis
(recursive ctors).  Binder arms (`lam`, `pathLam`) use the fact that
`Action.liftForRaw rho = rho.lift` for the `RawRenaming` Action
instance, so the IH applies directly under the lifted renaming. -/
theorem RawTerm.act_eq_rename :
    ∀ {sourceScope targetScope : Nat}
      (rawTerm : RawTerm sourceScope)
      (someRenaming : RawRenaming sourceScope targetScope),
      RawTerm.act rawTerm someRenaming = RawTerm.rename rawTerm someRenaming := by
  intro sourceScope targetScope rawTerm
  induction rawTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro someRenaming
      show RawTerm.lam (body.act (Action.liftForRaw someRenaming)) =
           RawTerm.lam (body.rename someRenaming.lift)
      rw [bodyIH (Action.liftForRaw someRenaming)]
      rfl
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro someRenaming
      show RawTerm.app (functionTerm.act someRenaming) (argumentTerm.act someRenaming) =
           RawTerm.app (functionTerm.rename someRenaming) (argumentTerm.rename someRenaming)
      rw [functionIH someRenaming, argumentIH someRenaming]
  | pair firstValue secondValue firstIH secondIH =>
      intro someRenaming
      show RawTerm.pair (firstValue.act someRenaming) (secondValue.act someRenaming) =
           RawTerm.pair (firstValue.rename someRenaming) (secondValue.rename someRenaming)
      rw [firstIH someRenaming, secondIH someRenaming]
  | fst pairTerm pairIH =>
      intro someRenaming
      show RawTerm.fst (pairTerm.act someRenaming) =
           RawTerm.fst (pairTerm.rename someRenaming)
      rw [pairIH someRenaming]
  | snd pairTerm pairIH =>
      intro someRenaming
      show RawTerm.snd (pairTerm.act someRenaming) =
           RawTerm.snd (pairTerm.rename someRenaming)
      rw [pairIH someRenaming]
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutIH thenIH elseIH =>
      intro someRenaming
      show RawTerm.boolElim (scrutinee.act someRenaming)
                            (thenBranch.act someRenaming)
                            (elseBranch.act someRenaming) =
           RawTerm.boolElim (scrutinee.rename someRenaming)
                            (thenBranch.rename someRenaming)
                            (elseBranch.rename someRenaming)
      rw [scrutIH someRenaming, thenIH someRenaming, elseIH someRenaming]
  | natZero => intro _; rfl
  | natSucc predecessor predIH =>
      intro someRenaming
      show RawTerm.natSucc (predecessor.act someRenaming) =
           RawTerm.natSucc (predecessor.rename someRenaming)
      rw [predIH someRenaming]
  | natElim scrutinee zeroBranch succBranch scrutIH zeroIH succIH =>
      intro someRenaming
      show RawTerm.natElim (scrutinee.act someRenaming)
                           (zeroBranch.act someRenaming)
                           (succBranch.act someRenaming) =
           RawTerm.natElim (scrutinee.rename someRenaming)
                           (zeroBranch.rename someRenaming)
                           (succBranch.rename someRenaming)
      rw [scrutIH someRenaming, zeroIH someRenaming, succIH someRenaming]
  | natRec scrutinee zeroBranch succBranch scrutIH zeroIH succIH =>
      intro someRenaming
      show RawTerm.natRec (scrutinee.act someRenaming)
                          (zeroBranch.act someRenaming)
                          (succBranch.act someRenaming) =
           RawTerm.natRec (scrutinee.rename someRenaming)
                          (zeroBranch.rename someRenaming)
                          (succBranch.rename someRenaming)
      rw [scrutIH someRenaming, zeroIH someRenaming, succIH someRenaming]
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro someRenaming
      show RawTerm.listCons (headTerm.act someRenaming) (tailTerm.act someRenaming) =
           RawTerm.listCons (headTerm.rename someRenaming) (tailTerm.rename someRenaming)
      rw [headIH someRenaming, tailIH someRenaming]
  | listElim scrutinee nilBranch consBranch scrutIH nilIH consIH =>
      intro someRenaming
      show RawTerm.listElim (scrutinee.act someRenaming)
                            (nilBranch.act someRenaming)
                            (consBranch.act someRenaming) =
           RawTerm.listElim (scrutinee.rename someRenaming)
                            (nilBranch.rename someRenaming)
                            (consBranch.rename someRenaming)
      rw [scrutIH someRenaming, nilIH someRenaming, consIH someRenaming]
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro someRenaming
      show RawTerm.optionSome (valueTerm.act someRenaming) =
           RawTerm.optionSome (valueTerm.rename someRenaming)
      rw [valueIH someRenaming]
  | optionMatch scrutinee noneBranch someBranch scrutIH noneIH someIH =>
      intro someRenaming
      show RawTerm.optionMatch (scrutinee.act someRenaming)
                               (noneBranch.act someRenaming)
                               (someBranch.act someRenaming) =
           RawTerm.optionMatch (scrutinee.rename someRenaming)
                               (noneBranch.rename someRenaming)
                               (someBranch.rename someRenaming)
      rw [scrutIH someRenaming, noneIH someRenaming, someIH someRenaming]
  | eitherInl valueTerm valueIH =>
      intro someRenaming
      show RawTerm.eitherInl (valueTerm.act someRenaming) =
           RawTerm.eitherInl (valueTerm.rename someRenaming)
      rw [valueIH someRenaming]
  | eitherInr valueTerm valueIH =>
      intro someRenaming
      show RawTerm.eitherInr (valueTerm.act someRenaming) =
           RawTerm.eitherInr (valueTerm.rename someRenaming)
      rw [valueIH someRenaming]
  | eitherMatch scrutinee leftBranch rightBranch scrutIH leftIH rightIH =>
      intro someRenaming
      show RawTerm.eitherMatch (scrutinee.act someRenaming)
                               (leftBranch.act someRenaming)
                               (rightBranch.act someRenaming) =
           RawTerm.eitherMatch (scrutinee.rename someRenaming)
                               (leftBranch.rename someRenaming)
                               (rightBranch.rename someRenaming)
      rw [scrutIH someRenaming, leftIH someRenaming, rightIH someRenaming]
  | refl rawWitness witnessIH =>
      intro someRenaming
      show RawTerm.refl (rawWitness.act someRenaming) =
           RawTerm.refl (rawWitness.rename someRenaming)
      rw [witnessIH someRenaming]
  | idJ baseCase witness baseIH witnessIH =>
      intro someRenaming
      show RawTerm.idJ (baseCase.act someRenaming) (witness.act someRenaming) =
           RawTerm.idJ (baseCase.rename someRenaming) (witness.rename someRenaming)
      rw [baseIH someRenaming, witnessIH someRenaming]
  | modIntro inner innerIH =>
      intro someRenaming
      show RawTerm.modIntro (inner.act someRenaming) =
           RawTerm.modIntro (inner.rename someRenaming)
      rw [innerIH someRenaming]
  | modElim inner innerIH =>
      intro someRenaming
      show RawTerm.modElim (inner.act someRenaming) =
           RawTerm.modElim (inner.rename someRenaming)
      rw [innerIH someRenaming]
  | subsume inner innerIH =>
      intro someRenaming
      show RawTerm.subsume (inner.act someRenaming) =
           RawTerm.subsume (inner.rename someRenaming)
      rw [innerIH someRenaming]
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro someRenaming
      show RawTerm.intervalOpp (intervalTerm.act someRenaming) =
           RawTerm.intervalOpp (intervalTerm.rename someRenaming)
      rw [intervalIH someRenaming]
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro someRenaming
      show RawTerm.intervalMeet (leftInterval.act someRenaming)
                                (rightInterval.act someRenaming) =
           RawTerm.intervalMeet (leftInterval.rename someRenaming)
                                (rightInterval.rename someRenaming)
      rw [leftIH someRenaming, rightIH someRenaming]
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro someRenaming
      show RawTerm.intervalJoin (leftInterval.act someRenaming)
                                (rightInterval.act someRenaming) =
           RawTerm.intervalJoin (leftInterval.rename someRenaming)
                                (rightInterval.rename someRenaming)
      rw [leftIH someRenaming, rightIH someRenaming]
  | pathLam body bodyIH =>
      intro someRenaming
      show RawTerm.pathLam (body.act (Action.liftForRaw someRenaming)) =
           RawTerm.pathLam (body.rename someRenaming.lift)
      rw [bodyIH (Action.liftForRaw someRenaming)]
      rfl
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro someRenaming
      show RawTerm.pathApp (pathTerm.act someRenaming) (intervalArg.act someRenaming) =
           RawTerm.pathApp (pathTerm.rename someRenaming) (intervalArg.rename someRenaming)
      rw [pathIH someRenaming, intervalIH someRenaming]
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro someRenaming
      show RawTerm.glueIntro (baseValue.act someRenaming)
                             (partialValue.act someRenaming) =
           RawTerm.glueIntro (baseValue.rename someRenaming)
                             (partialValue.rename someRenaming)
      rw [baseIH someRenaming, partialIH someRenaming]
  | glueElim gluedValue gluedIH =>
      intro someRenaming
      show RawTerm.glueElim (gluedValue.act someRenaming) =
           RawTerm.glueElim (gluedValue.rename someRenaming)
      rw [gluedIH someRenaming]
  | transp path source pathIH sourceIH =>
      intro someRenaming
      show RawTerm.transp (path.act someRenaming) (source.act someRenaming) =
           RawTerm.transp (path.rename someRenaming) (source.rename someRenaming)
      rw [pathIH someRenaming, sourceIH someRenaming]
  | hcomp sides cap sidesIH capIH =>
      intro someRenaming
      show RawTerm.hcomp (sides.act someRenaming) (cap.act someRenaming) =
           RawTerm.hcomp (sides.rename someRenaming) (cap.rename someRenaming)
      rw [sidesIH someRenaming, capIH someRenaming]
  | oeqRefl witness witnessIH =>
      intro someRenaming
      show RawTerm.oeqRefl (witness.act someRenaming) =
           RawTerm.oeqRefl (witness.rename someRenaming)
      rw [witnessIH someRenaming]
  | oeqJ baseCase witness baseIH witnessIH =>
      intro someRenaming
      show RawTerm.oeqJ (baseCase.act someRenaming) (witness.act someRenaming) =
           RawTerm.oeqJ (baseCase.rename someRenaming) (witness.rename someRenaming)
      rw [baseIH someRenaming, witnessIH someRenaming]
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro someRenaming
      show RawTerm.oeqFunext (pointwiseEquality.act someRenaming) =
           RawTerm.oeqFunext (pointwiseEquality.rename someRenaming)
      rw [pointwiseIH someRenaming]
  | idStrictRefl witness witnessIH =>
      intro someRenaming
      show RawTerm.idStrictRefl (witness.act someRenaming) =
           RawTerm.idStrictRefl (witness.rename someRenaming)
      rw [witnessIH someRenaming]
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro someRenaming
      show RawTerm.idStrictRec (baseCase.act someRenaming) (witness.act someRenaming) =
           RawTerm.idStrictRec (baseCase.rename someRenaming) (witness.rename someRenaming)
      rw [baseIH someRenaming, witnessIH someRenaming]
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro someRenaming
      show RawTerm.equivIntro (forwardFn.act someRenaming) (backwardFn.act someRenaming) =
           RawTerm.equivIntro (forwardFn.rename someRenaming) (backwardFn.rename someRenaming)
      rw [forwardIH someRenaming, backwardIH someRenaming]
  | equivApp equivTerm argument equivIH argumentIH =>
      intro someRenaming
      show RawTerm.equivApp (equivTerm.act someRenaming) (argument.act someRenaming) =
           RawTerm.equivApp (equivTerm.rename someRenaming) (argument.rename someRenaming)
      rw [equivIH someRenaming, argumentIH someRenaming]
  | refineIntro rawValue predicateProof rawIH predIH =>
      intro someRenaming
      show RawTerm.refineIntro (rawValue.act someRenaming) (predicateProof.act someRenaming) =
           RawTerm.refineIntro (rawValue.rename someRenaming) (predicateProof.rename someRenaming)
      rw [rawIH someRenaming, predIH someRenaming]
  | refineElim refinedValue refinedIH =>
      intro someRenaming
      show RawTerm.refineElim (refinedValue.act someRenaming) =
           RawTerm.refineElim (refinedValue.rename someRenaming)
      rw [refinedIH someRenaming]
  | recordIntro firstField firstIH =>
      intro someRenaming
      show RawTerm.recordIntro (firstField.act someRenaming) =
           RawTerm.recordIntro (firstField.rename someRenaming)
      rw [firstIH someRenaming]
  | recordProj recordValue recordIH =>
      intro someRenaming
      show RawTerm.recordProj (recordValue.act someRenaming) =
           RawTerm.recordProj (recordValue.rename someRenaming)
      rw [recordIH someRenaming]
  | codataUnfold initialState transition initialIH transIH =>
      intro someRenaming
      show RawTerm.codataUnfold (initialState.act someRenaming)
                                (transition.act someRenaming) =
           RawTerm.codataUnfold (initialState.rename someRenaming)
                                (transition.rename someRenaming)
      rw [initialIH someRenaming, transIH someRenaming]
  | codataDest codataValue codataIH =>
      intro someRenaming
      show RawTerm.codataDest (codataValue.act someRenaming) =
           RawTerm.codataDest (codataValue.rename someRenaming)
      rw [codataIH someRenaming]
  | sessionSend channel payload channelIH payloadIH =>
      intro someRenaming
      show RawTerm.sessionSend (channel.act someRenaming) (payload.act someRenaming) =
           RawTerm.sessionSend (channel.rename someRenaming) (payload.rename someRenaming)
      rw [channelIH someRenaming, payloadIH someRenaming]
  | sessionRecv channel channelIH =>
      intro someRenaming
      show RawTerm.sessionRecv (channel.act someRenaming) =
           RawTerm.sessionRecv (channel.rename someRenaming)
      rw [channelIH someRenaming]
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro someRenaming
      show RawTerm.effectPerform (operationTag.act someRenaming) (arguments.act someRenaming) =
           RawTerm.effectPerform (operationTag.rename someRenaming) (arguments.rename someRenaming)
      rw [operationIH someRenaming, argumentsIH someRenaming]
  | universeCode innerLevel => intro _; rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro someRenaming
      show RawTerm.arrowCode (domainCode.act someRenaming) (codomainCode.act someRenaming) =
           RawTerm.arrowCode (domainCode.rename someRenaming) (codomainCode.rename someRenaming)
      rw [domainIH someRenaming, codomainIH someRenaming]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro someRenaming
      show RawTerm.piTyCode (domainCode.act someRenaming)
                            (codomainCode.act (Action.liftForRaw someRenaming)) =
           RawTerm.piTyCode (domainCode.rename someRenaming)
                            (codomainCode.rename someRenaming.lift)
      rw [domainIH someRenaming, codomainIH (Action.liftForRaw someRenaming)]
      rfl
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro someRenaming
      show RawTerm.sigmaTyCode (domainCode.act someRenaming)
                               (codomainCode.act (Action.liftForRaw someRenaming)) =
           RawTerm.sigmaTyCode (domainCode.rename someRenaming)
                               (codomainCode.rename someRenaming.lift)
      rw [domainIH someRenaming, codomainIH (Action.liftForRaw someRenaming)]
      rfl
  | productCode firstCode secondCode firstIH secondIH =>
      intro someRenaming
      show RawTerm.productCode (firstCode.act someRenaming) (secondCode.act someRenaming) =
           RawTerm.productCode (firstCode.rename someRenaming) (secondCode.rename someRenaming)
      rw [firstIH someRenaming, secondIH someRenaming]
  | sumCode leftCode rightCode leftIH rightIH =>
      intro someRenaming
      show RawTerm.sumCode (leftCode.act someRenaming) (rightCode.act someRenaming) =
           RawTerm.sumCode (leftCode.rename someRenaming) (rightCode.rename someRenaming)
      rw [leftIH someRenaming, rightIH someRenaming]
  | listCode elementCode elementIH =>
      intro someRenaming
      show RawTerm.listCode (elementCode.act someRenaming) =
           RawTerm.listCode (elementCode.rename someRenaming)
      rw [elementIH someRenaming]
  | optionCode elementCode elementIH =>
      intro someRenaming
      show RawTerm.optionCode (elementCode.act someRenaming) =
           RawTerm.optionCode (elementCode.rename someRenaming)
      rw [elementIH someRenaming]
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro someRenaming
      show RawTerm.eitherCode (leftCode.act someRenaming) (rightCode.act someRenaming) =
           RawTerm.eitherCode (leftCode.rename someRenaming) (rightCode.rename someRenaming)
      rw [leftIH someRenaming, rightIH someRenaming]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro someRenaming
      show RawTerm.idCode (typeCode.act someRenaming)
                          (leftRaw.act someRenaming)
                          (rightRaw.act someRenaming) =
           RawTerm.idCode (typeCode.rename someRenaming)
                          (leftRaw.rename someRenaming)
                          (rightRaw.rename someRenaming)
      rw [typeIH someRenaming, leftIH someRenaming, rightIH someRenaming]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro someRenaming
      show RawTerm.equivCode (leftTypeCode.act someRenaming)
                             (rightTypeCode.act someRenaming) =
           RawTerm.equivCode (leftTypeCode.rename someRenaming)
                             (rightTypeCode.rename someRenaming)
      rw [leftIH someRenaming, rightIH someRenaming]

/-- Bridge theorem: applying `RawTerm.act` over a `Subst level`
Container produces the same result as applying `RawTerm.subst
sigma.forRaw` directly.  Proved by structural induction on the raw
term over all 56 RawTerm constructors.

Every arm reduces by `rfl` (leaves) or by the inductive hypothesis
(recursive ctors).  The var arm uses
`ActsOnRawTermVarOfSubst.varToRawTerm sigma position = sigma.forRaw
position` definitionally, matching `RawTerm.subst`'s var arm exactly.
The binder arms (`lam`, `pathLam`) use the fact that for the Subst
Action instance, `Action.liftForRaw sigma = sigma.lift`, and
`sigma.lift.forRaw = sigma.forRaw.lift` definitionally — making the
IH applicable directly under the lifted substitution. -/
theorem RawTerm.act_eq_subst_forRaw {level : Nat} :
    ∀ {sourceScope targetScope : Nat}
      (rawTerm : RawTerm sourceScope)
      (someSubst : Subst level sourceScope targetScope),
      RawTerm.act rawTerm someSubst = RawTerm.subst rawTerm someSubst.forRaw := by
  intro sourceScope targetScope rawTerm
  induction rawTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro someSubst
      show RawTerm.lam (body.act (Action.liftForRaw someSubst)) =
           RawTerm.lam (body.subst someSubst.forRaw.lift)
      rw [bodyIH (Action.liftForRaw someSubst)]
      rfl
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro someSubst
      show RawTerm.app (functionTerm.act someSubst) (argumentTerm.act someSubst) =
           RawTerm.app (functionTerm.subst someSubst.forRaw) (argumentTerm.subst someSubst.forRaw)
      rw [functionIH someSubst, argumentIH someSubst]
  | pair firstValue secondValue firstIH secondIH =>
      intro someSubst
      show RawTerm.pair (firstValue.act someSubst) (secondValue.act someSubst) =
           RawTerm.pair (firstValue.subst someSubst.forRaw) (secondValue.subst someSubst.forRaw)
      rw [firstIH someSubst, secondIH someSubst]
  | fst pairTerm pairIH =>
      intro someSubst
      show RawTerm.fst (pairTerm.act someSubst) =
           RawTerm.fst (pairTerm.subst someSubst.forRaw)
      rw [pairIH someSubst]
  | snd pairTerm pairIH =>
      intro someSubst
      show RawTerm.snd (pairTerm.act someSubst) =
           RawTerm.snd (pairTerm.subst someSubst.forRaw)
      rw [pairIH someSubst]
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutIH thenIH elseIH =>
      intro someSubst
      show RawTerm.boolElim (scrutinee.act someSubst)
                            (thenBranch.act someSubst)
                            (elseBranch.act someSubst) =
           RawTerm.boolElim (scrutinee.subst someSubst.forRaw)
                            (thenBranch.subst someSubst.forRaw)
                            (elseBranch.subst someSubst.forRaw)
      rw [scrutIH someSubst, thenIH someSubst, elseIH someSubst]
  | natZero => intro _; rfl
  | natSucc predecessor predIH =>
      intro someSubst
      show RawTerm.natSucc (predecessor.act someSubst) =
           RawTerm.natSucc (predecessor.subst someSubst.forRaw)
      rw [predIH someSubst]
  | natElim scrutinee zeroBranch succBranch scrutIH zeroIH succIH =>
      intro someSubst
      show RawTerm.natElim (scrutinee.act someSubst)
                           (zeroBranch.act someSubst)
                           (succBranch.act someSubst) =
           RawTerm.natElim (scrutinee.subst someSubst.forRaw)
                           (zeroBranch.subst someSubst.forRaw)
                           (succBranch.subst someSubst.forRaw)
      rw [scrutIH someSubst, zeroIH someSubst, succIH someSubst]
  | natRec scrutinee zeroBranch succBranch scrutIH zeroIH succIH =>
      intro someSubst
      show RawTerm.natRec (scrutinee.act someSubst)
                          (zeroBranch.act someSubst)
                          (succBranch.act someSubst) =
           RawTerm.natRec (scrutinee.subst someSubst.forRaw)
                          (zeroBranch.subst someSubst.forRaw)
                          (succBranch.subst someSubst.forRaw)
      rw [scrutIH someSubst, zeroIH someSubst, succIH someSubst]
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro someSubst
      show RawTerm.listCons (headTerm.act someSubst) (tailTerm.act someSubst) =
           RawTerm.listCons (headTerm.subst someSubst.forRaw) (tailTerm.subst someSubst.forRaw)
      rw [headIH someSubst, tailIH someSubst]
  | listElim scrutinee nilBranch consBranch scrutIH nilIH consIH =>
      intro someSubst
      show RawTerm.listElim (scrutinee.act someSubst)
                            (nilBranch.act someSubst)
                            (consBranch.act someSubst) =
           RawTerm.listElim (scrutinee.subst someSubst.forRaw)
                            (nilBranch.subst someSubst.forRaw)
                            (consBranch.subst someSubst.forRaw)
      rw [scrutIH someSubst, nilIH someSubst, consIH someSubst]
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro someSubst
      show RawTerm.optionSome (valueTerm.act someSubst) =
           RawTerm.optionSome (valueTerm.subst someSubst.forRaw)
      rw [valueIH someSubst]
  | optionMatch scrutinee noneBranch someBranch scrutIH noneIH someIH =>
      intro someSubst
      show RawTerm.optionMatch (scrutinee.act someSubst)
                               (noneBranch.act someSubst)
                               (someBranch.act someSubst) =
           RawTerm.optionMatch (scrutinee.subst someSubst.forRaw)
                               (noneBranch.subst someSubst.forRaw)
                               (someBranch.subst someSubst.forRaw)
      rw [scrutIH someSubst, noneIH someSubst, someIH someSubst]
  | eitherInl valueTerm valueIH =>
      intro someSubst
      show RawTerm.eitherInl (valueTerm.act someSubst) =
           RawTerm.eitherInl (valueTerm.subst someSubst.forRaw)
      rw [valueIH someSubst]
  | eitherInr valueTerm valueIH =>
      intro someSubst
      show RawTerm.eitherInr (valueTerm.act someSubst) =
           RawTerm.eitherInr (valueTerm.subst someSubst.forRaw)
      rw [valueIH someSubst]
  | eitherMatch scrutinee leftBranch rightBranch scrutIH leftIH rightIH =>
      intro someSubst
      show RawTerm.eitherMatch (scrutinee.act someSubst)
                               (leftBranch.act someSubst)
                               (rightBranch.act someSubst) =
           RawTerm.eitherMatch (scrutinee.subst someSubst.forRaw)
                               (leftBranch.subst someSubst.forRaw)
                               (rightBranch.subst someSubst.forRaw)
      rw [scrutIH someSubst, leftIH someSubst, rightIH someSubst]
  | refl rawWitness witnessIH =>
      intro someSubst
      show RawTerm.refl (rawWitness.act someSubst) =
           RawTerm.refl (rawWitness.subst someSubst.forRaw)
      rw [witnessIH someSubst]
  | idJ baseCase witness baseIH witnessIH =>
      intro someSubst
      show RawTerm.idJ (baseCase.act someSubst) (witness.act someSubst) =
           RawTerm.idJ (baseCase.subst someSubst.forRaw) (witness.subst someSubst.forRaw)
      rw [baseIH someSubst, witnessIH someSubst]
  | modIntro inner innerIH =>
      intro someSubst
      show RawTerm.modIntro (inner.act someSubst) =
           RawTerm.modIntro (inner.subst someSubst.forRaw)
      rw [innerIH someSubst]
  | modElim inner innerIH =>
      intro someSubst
      show RawTerm.modElim (inner.act someSubst) =
           RawTerm.modElim (inner.subst someSubst.forRaw)
      rw [innerIH someSubst]
  | subsume inner innerIH =>
      intro someSubst
      show RawTerm.subsume (inner.act someSubst) =
           RawTerm.subsume (inner.subst someSubst.forRaw)
      rw [innerIH someSubst]
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro someSubst
      show RawTerm.intervalOpp (intervalTerm.act someSubst) =
           RawTerm.intervalOpp (intervalTerm.subst someSubst.forRaw)
      rw [intervalIH someSubst]
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro someSubst
      show RawTerm.intervalMeet (leftInterval.act someSubst)
                                (rightInterval.act someSubst) =
           RawTerm.intervalMeet (leftInterval.subst someSubst.forRaw)
                                (rightInterval.subst someSubst.forRaw)
      rw [leftIH someSubst, rightIH someSubst]
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro someSubst
      show RawTerm.intervalJoin (leftInterval.act someSubst)
                                (rightInterval.act someSubst) =
           RawTerm.intervalJoin (leftInterval.subst someSubst.forRaw)
                                (rightInterval.subst someSubst.forRaw)
      rw [leftIH someSubst, rightIH someSubst]
  | pathLam body bodyIH =>
      intro someSubst
      show RawTerm.pathLam (body.act (Action.liftForRaw someSubst)) =
           RawTerm.pathLam (body.subst someSubst.forRaw.lift)
      rw [bodyIH (Action.liftForRaw someSubst)]
      rfl
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro someSubst
      show RawTerm.pathApp (pathTerm.act someSubst) (intervalArg.act someSubst) =
           RawTerm.pathApp (pathTerm.subst someSubst.forRaw) (intervalArg.subst someSubst.forRaw)
      rw [pathIH someSubst, intervalIH someSubst]
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro someSubst
      show RawTerm.glueIntro (baseValue.act someSubst)
                             (partialValue.act someSubst) =
           RawTerm.glueIntro (baseValue.subst someSubst.forRaw)
                             (partialValue.subst someSubst.forRaw)
      rw [baseIH someSubst, partialIH someSubst]
  | glueElim gluedValue gluedIH =>
      intro someSubst
      show RawTerm.glueElim (gluedValue.act someSubst) =
           RawTerm.glueElim (gluedValue.subst someSubst.forRaw)
      rw [gluedIH someSubst]
  | transp path source pathIH sourceIH =>
      intro someSubst
      show RawTerm.transp (path.act someSubst) (source.act someSubst) =
           RawTerm.transp (path.subst someSubst.forRaw) (source.subst someSubst.forRaw)
      rw [pathIH someSubst, sourceIH someSubst]
  | hcomp sides cap sidesIH capIH =>
      intro someSubst
      show RawTerm.hcomp (sides.act someSubst) (cap.act someSubst) =
           RawTerm.hcomp (sides.subst someSubst.forRaw) (cap.subst someSubst.forRaw)
      rw [sidesIH someSubst, capIH someSubst]
  | oeqRefl witness witnessIH =>
      intro someSubst
      show RawTerm.oeqRefl (witness.act someSubst) =
           RawTerm.oeqRefl (witness.subst someSubst.forRaw)
      rw [witnessIH someSubst]
  | oeqJ baseCase witness baseIH witnessIH =>
      intro someSubst
      show RawTerm.oeqJ (baseCase.act someSubst) (witness.act someSubst) =
           RawTerm.oeqJ (baseCase.subst someSubst.forRaw) (witness.subst someSubst.forRaw)
      rw [baseIH someSubst, witnessIH someSubst]
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro someSubst
      show RawTerm.oeqFunext (pointwiseEquality.act someSubst) =
           RawTerm.oeqFunext (pointwiseEquality.subst someSubst.forRaw)
      rw [pointwiseIH someSubst]
  | idStrictRefl witness witnessIH =>
      intro someSubst
      show RawTerm.idStrictRefl (witness.act someSubst) =
           RawTerm.idStrictRefl (witness.subst someSubst.forRaw)
      rw [witnessIH someSubst]
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro someSubst
      show RawTerm.idStrictRec (baseCase.act someSubst) (witness.act someSubst) =
           RawTerm.idStrictRec (baseCase.subst someSubst.forRaw) (witness.subst someSubst.forRaw)
      rw [baseIH someSubst, witnessIH someSubst]
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro someSubst
      show RawTerm.equivIntro (forwardFn.act someSubst) (backwardFn.act someSubst) =
           RawTerm.equivIntro (forwardFn.subst someSubst.forRaw) (backwardFn.subst someSubst.forRaw)
      rw [forwardIH someSubst, backwardIH someSubst]
  | equivApp equivTerm argument equivIH argumentIH =>
      intro someSubst
      show RawTerm.equivApp (equivTerm.act someSubst) (argument.act someSubst) =
           RawTerm.equivApp (equivTerm.subst someSubst.forRaw) (argument.subst someSubst.forRaw)
      rw [equivIH someSubst, argumentIH someSubst]
  | refineIntro rawValue predicateProof rawIH predIH =>
      intro someSubst
      show RawTerm.refineIntro (rawValue.act someSubst) (predicateProof.act someSubst) =
           RawTerm.refineIntro (rawValue.subst someSubst.forRaw) (predicateProof.subst someSubst.forRaw)
      rw [rawIH someSubst, predIH someSubst]
  | refineElim refinedValue refinedIH =>
      intro someSubst
      show RawTerm.refineElim (refinedValue.act someSubst) =
           RawTerm.refineElim (refinedValue.subst someSubst.forRaw)
      rw [refinedIH someSubst]
  | recordIntro firstField firstIH =>
      intro someSubst
      show RawTerm.recordIntro (firstField.act someSubst) =
           RawTerm.recordIntro (firstField.subst someSubst.forRaw)
      rw [firstIH someSubst]
  | recordProj recordValue recordIH =>
      intro someSubst
      show RawTerm.recordProj (recordValue.act someSubst) =
           RawTerm.recordProj (recordValue.subst someSubst.forRaw)
      rw [recordIH someSubst]
  | codataUnfold initialState transition initialIH transIH =>
      intro someSubst
      show RawTerm.codataUnfold (initialState.act someSubst)
                                (transition.act someSubst) =
           RawTerm.codataUnfold (initialState.subst someSubst.forRaw)
                                (transition.subst someSubst.forRaw)
      rw [initialIH someSubst, transIH someSubst]
  | codataDest codataValue codataIH =>
      intro someSubst
      show RawTerm.codataDest (codataValue.act someSubst) =
           RawTerm.codataDest (codataValue.subst someSubst.forRaw)
      rw [codataIH someSubst]
  | sessionSend channel payload channelIH payloadIH =>
      intro someSubst
      show RawTerm.sessionSend (channel.act someSubst) (payload.act someSubst) =
           RawTerm.sessionSend (channel.subst someSubst.forRaw) (payload.subst someSubst.forRaw)
      rw [channelIH someSubst, payloadIH someSubst]
  | sessionRecv channel channelIH =>
      intro someSubst
      show RawTerm.sessionRecv (channel.act someSubst) =
           RawTerm.sessionRecv (channel.subst someSubst.forRaw)
      rw [channelIH someSubst]
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro someSubst
      show RawTerm.effectPerform (operationTag.act someSubst) (arguments.act someSubst) =
           RawTerm.effectPerform (operationTag.subst someSubst.forRaw) (arguments.subst someSubst.forRaw)
      rw [operationIH someSubst, argumentsIH someSubst]
  | universeCode innerLevel => intro _; rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro someSubst
      show RawTerm.arrowCode (domainCode.act someSubst) (codomainCode.act someSubst) =
           RawTerm.arrowCode (domainCode.subst someSubst.forRaw)
                             (codomainCode.subst someSubst.forRaw)
      rw [domainIH someSubst, codomainIH someSubst]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro someSubst
      show RawTerm.piTyCode (domainCode.act someSubst)
                            (codomainCode.act (Action.liftForRaw someSubst)) =
           RawTerm.piTyCode (domainCode.subst someSubst.forRaw)
                            (codomainCode.subst someSubst.forRaw.lift)
      rw [domainIH someSubst, codomainIH (Action.liftForRaw someSubst)]
      rfl
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro someSubst
      show RawTerm.sigmaTyCode (domainCode.act someSubst)
                               (codomainCode.act (Action.liftForRaw someSubst)) =
           RawTerm.sigmaTyCode (domainCode.subst someSubst.forRaw)
                               (codomainCode.subst someSubst.forRaw.lift)
      rw [domainIH someSubst, codomainIH (Action.liftForRaw someSubst)]
      rfl
  | productCode firstCode secondCode firstIH secondIH =>
      intro someSubst
      show RawTerm.productCode (firstCode.act someSubst) (secondCode.act someSubst) =
           RawTerm.productCode (firstCode.subst someSubst.forRaw)
                               (secondCode.subst someSubst.forRaw)
      rw [firstIH someSubst, secondIH someSubst]
  | sumCode leftCode rightCode leftIH rightIH =>
      intro someSubst
      show RawTerm.sumCode (leftCode.act someSubst) (rightCode.act someSubst) =
           RawTerm.sumCode (leftCode.subst someSubst.forRaw)
                           (rightCode.subst someSubst.forRaw)
      rw [leftIH someSubst, rightIH someSubst]
  | listCode elementCode elementIH =>
      intro someSubst
      show RawTerm.listCode (elementCode.act someSubst) =
           RawTerm.listCode (elementCode.subst someSubst.forRaw)
      rw [elementIH someSubst]
  | optionCode elementCode elementIH =>
      intro someSubst
      show RawTerm.optionCode (elementCode.act someSubst) =
           RawTerm.optionCode (elementCode.subst someSubst.forRaw)
      rw [elementIH someSubst]
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro someSubst
      show RawTerm.eitherCode (leftCode.act someSubst) (rightCode.act someSubst) =
           RawTerm.eitherCode (leftCode.subst someSubst.forRaw)
                              (rightCode.subst someSubst.forRaw)
      rw [leftIH someSubst, rightIH someSubst]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro someSubst
      show RawTerm.idCode (typeCode.act someSubst)
                          (leftRaw.act someSubst)
                          (rightRaw.act someSubst) =
           RawTerm.idCode (typeCode.subst someSubst.forRaw)
                          (leftRaw.subst someSubst.forRaw)
                          (rightRaw.subst someSubst.forRaw)
      rw [typeIH someSubst, leftIH someSubst, rightIH someSubst]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro someSubst
      show RawTerm.equivCode (leftTypeCode.act someSubst)
                             (rightTypeCode.act someSubst) =
           RawTerm.equivCode (leftTypeCode.subst someSubst.forRaw)
                             (rightTypeCode.subst someSubst.forRaw)
      rw [leftIH someSubst, rightIH someSubst]

/-! ## Smoke equivalences with existing `Ty.subst`.

The `Ty.act` engine over `Subst level` should produce the same
result as the existing `Ty.subst`.  The full equivalence theorem
`Ty.act_subst_eq_subst` lands in Z2.B (when `Ty.subst` is REDIRECTED
to `Ty.act`).  For Z2.A we ship the per-ctor `rfl` smokes
demonstrating the engine reduces correctly at leaf and binder
positions on a Subst Container.

After Z2.A.1's instance-body alignment, the raw-payload smokes
(`Ty.act_subst_id_smoke`, `Ty.act_subst_refine_smoke`) now produce
`RawTerm.act` invocations on the right-hand side instead of
`RawTerm.subst sigma.forRaw`.  The smokes hold by `rfl` because
`actOnRawTerm sigma raw = RawTerm.act raw sigma` is `rfl` from the
new instance body. -/

theorem Ty.act_subst_unit_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope) :
    (Ty.unit (level := level) (scope := scope)).act someSubst = .unit := rfl

theorem Ty.act_subst_tyVar_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (position : Fin scope) :
    (Ty.tyVar (level := level) position).act someSubst =
      someSubst.forTy position := rfl

theorem Ty.act_subst_arrow_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (domainType codomainType : Ty level scope) :
    (Ty.arrow domainType codomainType).act someSubst =
      Ty.arrow (domainType.act someSubst) (codomainType.act someSubst) := rfl

theorem Ty.act_subst_piTy_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (domainType : Ty level scope)
    (codomainType : Ty level (scope + 1)) :
    (Ty.piTy domainType codomainType).act someSubst =
      Ty.piTy (domainType.act someSubst)
              (codomainType.act (Action.liftForTy someSubst)) := rfl

theorem Ty.act_subst_refine_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (baseType : Ty level scope)
    (predicate : RawTerm (scope + 1)) :
    (Ty.refine baseType predicate).act someSubst =
      Ty.refine (baseType.act someSubst)
                (ActsOnRawTerm.actOnRawTerm
                    (Action.liftForRaw someSubst) predicate) := rfl

theorem Ty.act_subst_id_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    (Ty.id carrier leftEndpoint rightEndpoint).act someSubst =
      Ty.id (carrier.act someSubst)
            (ActsOnRawTerm.actOnRawTerm someSubst leftEndpoint)
            (ActsOnRawTerm.actOnRawTerm someSubst rightEndpoint) := rfl

theorem Ty.act_subst_universe_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 ≤ level) :
    (Ty.universe (scope := scope) universeLevel levelLe).act someSubst =
      Ty.universe universeLevel levelLe := rfl

end LeanFX2
