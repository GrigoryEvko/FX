import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity
import LeanFX2.Reduction.RawParInversion.TypeCodes

/-! # Confluence/RawParStarCong — parStar congruence rules

`RawStep.parStar` (the reflexive-transitive closure of `RawStep.par`)
is closed under the same congruence rules as `RawStep.par`: applying
parallel reduction sub-term-by-sub-term and chaining yields a chain
on the whole term.

This file derives those congruence rules.  Each `parStar.<ctor>`
rule is proved by induction on its parStar argument(s), using
`RawStep.par.<ctor>` as the per-step lifter and parStar.refl /
trans / append for chaining.

## Use

`RawTerm.whnf_reaches` (in `Algo/RawWHNFCorrect`) inducts on the
input term, reducing each sub-term first via the IH (giving a
parStar chain), then assembling the whole-term chain via these
cong rules.
-/

namespace LeanFX2

variable {scope : Nat}

/-- parStar respects `lam` body. -/
theorem RawStep.parStar.lam
    {sourceBody targetBody : RawTerm (scope + 1)}
    (chain : RawStep.parStar sourceBody targetBody) :
    RawStep.parStar (.lam sourceBody) (.lam targetBody) :=
  RawStep.parStar.mapStep RawTerm.lam RawStep.par.lam chain

/-- parStar respects `app` on the function side. -/
theorem RawStep.parStar.appLeft
    {sourceFunction targetFunction : RawTerm scope}
    (argument : RawTerm scope)
    (chain : RawStep.parStar sourceFunction targetFunction) :
    RawStep.parStar (.app sourceFunction argument)
                    (.app targetFunction argument) :=
  RawStep.parStar.mapStep (fun source => .app source argument)
    (fun innerStep => RawStep.par.app innerStep (.refl _)) chain

/-- parStar respects `app` on the argument side. -/
theorem RawStep.parStar.appRight
    (functionTerm : RawTerm scope)
    {sourceArgument targetArgument : RawTerm scope}
    (chain : RawStep.parStar sourceArgument targetArgument) :
    RawStep.parStar (.app functionTerm sourceArgument)
                    (.app functionTerm targetArgument) :=
  RawStep.parStar.mapStep (fun source => .app functionTerm source)
    (fun innerStep => RawStep.par.app (.refl _) innerStep) chain

/-- parStar respects `app` on both sides. -/
theorem RawStep.parStar.app
    {sourceFunction targetFunction : RawTerm scope}
    {sourceArgument targetArgument : RawTerm scope}
    (functionChain : RawStep.parStar sourceFunction targetFunction)
    (argumentChain : RawStep.parStar sourceArgument targetArgument) :
    RawStep.parStar (.app sourceFunction sourceArgument)
                    (.app targetFunction targetArgument) :=
  RawStep.parStar.append
    (RawStep.parStar.appLeft sourceArgument functionChain)
    (RawStep.parStar.appRight targetFunction argumentChain)

/-- parStar respects `pair` on the first component. -/
theorem RawStep.parStar.pairLeft
    {sourceFirst targetFirst : RawTerm scope}
    (secondValue : RawTerm scope)
    (chain : RawStep.parStar sourceFirst targetFirst) :
    RawStep.parStar (.pair sourceFirst secondValue)
                    (.pair targetFirst secondValue) :=
  RawStep.parStar.mapStep (fun source => .pair source secondValue)
    (fun innerStep => RawStep.par.pair innerStep (.refl _)) chain

/-- parStar respects `pair` on the second component. -/
theorem RawStep.parStar.pairRight
    (firstValue : RawTerm scope)
    {sourceSecond targetSecond : RawTerm scope}
    (chain : RawStep.parStar sourceSecond targetSecond) :
    RawStep.parStar (.pair firstValue sourceSecond)
                    (.pair firstValue targetSecond) :=
  RawStep.parStar.mapStep (fun source => .pair firstValue source)
    (fun innerStep => RawStep.par.pair (.refl _) innerStep) chain

/-- parStar respects `pair` on both components. -/
theorem RawStep.parStar.pair
    {sourceFirst targetFirst sourceSecond targetSecond : RawTerm scope}
    (firstChain : RawStep.parStar sourceFirst targetFirst)
    (secondChain : RawStep.parStar sourceSecond targetSecond) :
    RawStep.parStar (.pair sourceFirst sourceSecond)
                    (.pair targetFirst targetSecond) :=
  RawStep.parStar.append
    (RawStep.parStar.pairLeft sourceSecond firstChain)
    (RawStep.parStar.pairRight targetFirst secondChain)

/-- parStar respects `fst`. -/
theorem RawStep.parStar.fst
    {sourcePair targetPair : RawTerm scope}
    (chain : RawStep.parStar sourcePair targetPair) :
    RawStep.parStar (.fst sourcePair) (.fst targetPair) :=
  RawStep.parStar.mapStep RawTerm.fst RawStep.par.fst chain

/-- parStar respects `snd`. -/
theorem RawStep.parStar.snd
    {sourcePair targetPair : RawTerm scope}
    (chain : RawStep.parStar sourcePair targetPair) :
    RawStep.parStar (.snd sourcePair) (.snd targetPair) :=
  RawStep.parStar.mapStep RawTerm.snd RawStep.par.snd chain

/-- parStar respects `boolElim` on the scrutinee. -/
theorem RawStep.parStar.boolElimScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (thenBranch elseBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.boolElim sourceScrutinee thenBranch elseBranch)
                    (.boolElim targetScrutinee thenBranch elseBranch) :=
  RawStep.parStar.mapStep
    (fun source => .boolElim source thenBranch elseBranch)
    (fun innerStep => RawStep.par.boolElim innerStep (.refl _) (.refl _))
    chain

/-- parStar respects `natSucc`. -/
theorem RawStep.parStar.natSucc
    {sourcePred targetPred : RawTerm scope}
    (chain : RawStep.parStar sourcePred targetPred) :
    RawStep.parStar (.natSucc sourcePred) (.natSucc targetPred) :=
  RawStep.parStar.mapStep RawTerm.natSucc RawStep.par.natSucc chain

/-- parStar respects `natElim` on the scrutinee. -/
theorem RawStep.parStar.natElimScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (zeroBranch succBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.natElim sourceScrutinee zeroBranch succBranch)
                    (.natElim targetScrutinee zeroBranch succBranch) :=
  RawStep.parStar.mapStep
    (fun source => .natElim source zeroBranch succBranch)
    (fun innerStep => RawStep.par.natElim innerStep (.refl _) (.refl _))
    chain

/-- parStar respects `natRec` on the scrutinee. -/
theorem RawStep.parStar.natRecScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (zeroBranch succBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.natRec sourceScrutinee zeroBranch succBranch)
                    (.natRec targetScrutinee zeroBranch succBranch) :=
  RawStep.parStar.mapStep
    (fun source => .natRec source zeroBranch succBranch)
    (fun innerStep => RawStep.par.natRec innerStep (.refl _) (.refl _))
    chain

/-- parStar respects `listCons` on the head. -/
theorem RawStep.parStar.listConsHead
    {sourceHead targetHead : RawTerm scope}
    (tailTerm : RawTerm scope)
    (chain : RawStep.parStar sourceHead targetHead) :
    RawStep.parStar (.listCons sourceHead tailTerm)
                    (.listCons targetHead tailTerm) :=
  RawStep.parStar.mapStep (fun source => .listCons source tailTerm)
    (fun innerStep => RawStep.par.listCons innerStep (.refl _)) chain

/-- parStar respects `listCons` on the tail. -/
theorem RawStep.parStar.listConsTail
    (headTerm : RawTerm scope)
    {sourceTail targetTail : RawTerm scope}
    (chain : RawStep.parStar sourceTail targetTail) :
    RawStep.parStar (.listCons headTerm sourceTail)
                    (.listCons headTerm targetTail) :=
  RawStep.parStar.mapStep (fun source => .listCons headTerm source)
    (fun innerStep => RawStep.par.listCons (.refl _) innerStep) chain

/-- parStar respects `listElim` on the scrutinee. -/
theorem RawStep.parStar.listElimScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (nilBranch consBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.listElim sourceScrutinee nilBranch consBranch)
                    (.listElim targetScrutinee nilBranch consBranch) :=
  RawStep.parStar.mapStep
    (fun source => .listElim source nilBranch consBranch)
    (fun innerStep => RawStep.par.listElim innerStep (.refl _) (.refl _))
    chain

/-- parStar respects `optionSome`. -/
theorem RawStep.parStar.optionSome
    {sourceValue targetValue : RawTerm scope}
    (chain : RawStep.parStar sourceValue targetValue) :
    RawStep.parStar (.optionSome sourceValue) (.optionSome targetValue) :=
  RawStep.parStar.mapStep RawTerm.optionSome RawStep.par.optionSome chain

/-- parStar respects `optionMatch` on the scrutinee. -/
theorem RawStep.parStar.optionMatchScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (noneBranch someBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.optionMatch sourceScrutinee noneBranch someBranch)
                    (.optionMatch targetScrutinee noneBranch someBranch) :=
  RawStep.parStar.mapStep
    (fun source => .optionMatch source noneBranch someBranch)
    (fun innerStep => RawStep.par.optionMatch innerStep (.refl _) (.refl _))
    chain

/-- parStar respects `eitherInl`. -/
theorem RawStep.parStar.eitherInl
    {sourceValue targetValue : RawTerm scope}
    (chain : RawStep.parStar sourceValue targetValue) :
    RawStep.parStar (.eitherInl sourceValue) (.eitherInl targetValue) :=
  RawStep.parStar.mapStep RawTerm.eitherInl RawStep.par.eitherInl chain

/-- parStar respects `eitherInr`. -/
theorem RawStep.parStar.eitherInr
    {sourceValue targetValue : RawTerm scope}
    (chain : RawStep.parStar sourceValue targetValue) :
    RawStep.parStar (.eitherInr sourceValue) (.eitherInr targetValue) :=
  RawStep.parStar.mapStep RawTerm.eitherInr RawStep.par.eitherInr chain

/-- parStar respects `eitherMatch` on the scrutinee. -/
theorem RawStep.parStar.eitherMatchScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (leftBranch rightBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.eitherMatch sourceScrutinee leftBranch rightBranch)
                    (.eitherMatch targetScrutinee leftBranch rightBranch) :=
  RawStep.parStar.mapStep
    (fun source => .eitherMatch source leftBranch rightBranch)
    (fun innerStep => RawStep.par.eitherMatch innerStep (.refl _) (.refl _))
    chain

/-- parStar respects `refl` (via reflCong on the witness). -/
theorem RawStep.parStar.reflWitness
    {sourceWitness targetWitness : RawTerm scope}
    (chain : RawStep.parStar sourceWitness targetWitness) :
    RawStep.parStar (.refl sourceWitness) (.refl targetWitness) :=
  RawStep.parStar.mapStep RawTerm.refl RawStep.par.reflCong chain

/-- parStar respects `idJ` on the witness. -/
theorem RawStep.parStar.idJWitness
    (baseCase : RawTerm scope)
    {sourceWitness targetWitness : RawTerm scope}
    (chain : RawStep.parStar sourceWitness targetWitness) :
    RawStep.parStar (.idJ baseCase sourceWitness)
                    (.idJ baseCase targetWitness) :=
  RawStep.parStar.mapStep (fun source => .idJ baseCase source)
    (fun innerStep => RawStep.par.idJ (.refl _) innerStep) chain

/-- parStar respects `modIntro`. -/
theorem RawStep.parStar.modIntro
    {sourceInner targetInner : RawTerm scope}
    (chain : RawStep.parStar sourceInner targetInner) :
    RawStep.parStar (.modIntro sourceInner) (.modIntro targetInner) :=
  RawStep.parStar.mapStep RawTerm.modIntro RawStep.par.modIntro chain

/-- parStar respects `modElim`. -/
theorem RawStep.parStar.modElim
    {sourceInner targetInner : RawTerm scope}
    (chain : RawStep.parStar sourceInner targetInner) :
    RawStep.parStar (.modElim sourceInner) (.modElim targetInner) :=
  RawStep.parStar.mapStep RawTerm.modElim RawStep.par.modElim chain

/-- parStar respects `subsume`. -/
theorem RawStep.parStar.subsume
    {sourceInner targetInner : RawTerm scope}
    (chain : RawStep.parStar sourceInner targetInner) :
    RawStep.parStar (.subsume sourceInner) (.subsume targetInner) :=
  RawStep.parStar.mapStep RawTerm.subsume RawStep.par.subsume chain

/-! ## Canonical-head parStar inversions

Multi-step versions of the single-step `RawStep.par.<ctor>_inv`
inversions for nullary canonical heads (`unit`, `boolTrue`,
`boolFalse`, `natZero`, `listNil`, `optionNone`).  Each says: a
parStar chain whose source is a canonical head reaches only that
canonical head.

These inversions enable Conv-level canonical-form theorems: when
one side of a `Conv` has raw form equal to a canonical head, the
other side's raw form must too. -/

/-! ### Suffices/free-the-index pattern

The pattern below frees the source index via `suffices` so the
inductive recursion sees a generic `source = canonical` hypothesis
and can run `induction` cleanly.  Direct `induction chain` fails
because parStar's source index is concrete (e.g. `RawTerm.unit`),
not a variable, so the dep-elim machinery cannot specialize it.
After `suffices`, the source becomes a generic variable matching
the IH's pattern; the canonical-equality hypothesis carries through
and is used at each `trans` step to constrain the intermediate. -/

/-! ### Generic helper for canonical-head parStar inversions

Given:
* a proof `parStep_inv` that any `RawStep.par canonicalHead target`
  forces `target = canonicalHead`
* a `parStar` chain whose source is `canonicalHead`

we show the chain's target is also `canonicalHead`.

Strategy: induction on the chain's length via `RawStep.parStar`'s
recursive `trans` constructor.  We introduce a fresh `someChain`
hypothesis with the source generalized so the dep-elim machinery
can specialize it cleanly. -/

private theorem RawStep.parStar.canonical_inv_helper
    {scope : Nat} {canonicalHead : RawTerm scope}
    (parStepInv : ∀ {target : RawTerm scope},
        RawStep.par canonicalHead target → target = canonicalHead)
    {target : RawTerm scope}
    (chain : RawStep.parStar canonicalHead target) :
    target = canonicalHead := by
  -- We induct on chain's length.  Each `trans` step reduces a
  -- `parStar canonicalHead target` to `parStar middle target` with
  -- middle determined by the single par step from canonicalHead.
  -- `parStepInv` constrains middle to canonicalHead, so the IH
  -- applies recursively at the same canonicalHead source.
  induction chain with
  | refl _ => rfl
  | trans firstStep _ restIH =>
      have midEq := parStepInv firstStep
      cases midEq
      exact restIH parStepInv

/-- `RawStep.parStar unit target → target = unit`. -/
theorem RawStep.parStar.unit_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.unit : RawTerm scope) target) :
    target = RawTerm.unit :=
  RawStep.parStar.canonical_inv_helper RawStep.par.unit_inv chain

/-- `RawStep.parStar boolTrue target → target = boolTrue`. -/
theorem RawStep.parStar.boolTrue_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.boolTrue : RawTerm scope) target) :
    target = RawTerm.boolTrue :=
  RawStep.parStar.canonical_inv_helper RawStep.par.boolTrue_inv chain

/-- `RawStep.parStar boolFalse target → target = boolFalse`. -/
theorem RawStep.parStar.boolFalse_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.boolFalse : RawTerm scope) target) :
    target = RawTerm.boolFalse :=
  RawStep.parStar.canonical_inv_helper RawStep.par.boolFalse_inv chain

/-- `RawStep.parStar natZero target → target = natZero`. -/
theorem RawStep.parStar.natZero_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.natZero : RawTerm scope) target) :
    target = RawTerm.natZero :=
  RawStep.parStar.canonical_inv_helper RawStep.par.natZero_inv chain

/-- `RawStep.parStar listNil target → target = listNil`. -/
theorem RawStep.parStar.listNil_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.listNil : RawTerm scope) target) :
    target = RawTerm.listNil :=
  RawStep.parStar.canonical_inv_helper RawStep.par.listNil_inv chain

/-- `RawStep.parStar optionNone target → target = optionNone`. -/
theorem RawStep.parStar.optionNone_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.optionNone : RawTerm scope) target) :
    target = RawTerm.optionNone :=
  RawStep.parStar.canonical_inv_helper RawStep.par.optionNone_inv chain

/-- `RawStep.parStar (var position) target → target = var position`.

Variables have no `RawStep.par` reduction beyond `refl` (no β/ι rule
takes a variable as source), so any chain from `var position` stays
at the same variable.  Completes the canonical-head inversion family
alongside the closed-canonical shipped above. -/
theorem RawStep.parStar.var_inv {position : Fin scope}
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.var position : RawTerm scope) target) :
    target = RawTerm.var position :=
  RawStep.parStar.canonical_inv_helper RawStep.par.var_inv chain

/-- `RawStep.parStar (universeCode innerLevel) target → target =
universeCode innerLevel`.

Universe codes are atomic type-code heads with no β/ι reduction —
`RawStep.par.universeCode_inv` (`Reduction/RawParInversion/TypeCodes.lean:235`)
forces the single-step target to be the same code, so any chain
stays at the same code.  Completes the canonical-head inversion
family across the type-code atomic head alongside the value
canonical heads above. -/
theorem RawStep.parStar.universeCode_inv {innerLevel : Nat}
    {target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.universeCode innerLevel : RawTerm scope)
        target) :
    target = RawTerm.universeCode innerLevel :=
  RawStep.parStar.canonical_inv_helper
    RawStep.par.universeCode_inv chain

/-! ### Cong-family parStar inversions

The canonical-head family above covers vacuous-source ctors with
no β/ι reduction — every step from source is `refl`, so target =
source.  The cong family (`natSucc`, `listCons`, `optionSome`,
`eitherInl`, `eitherInr`, `pair`, `refl`, `lam`) has the
`Wrap subterm` shape and admits one-step cong rules — so a chain
moves through `Wrap subterm₀ → Wrap subterm₁ → ... → Wrap
subterm_n` while the subterm itself undergoes a `parStar` chain.

The cong-family lift returns existential structure
`(∃ subtermTarget, target = Wrap subtermTarget ∧ parStar subterm
subtermTarget)` rather than a flat equality.  This requires an
auxiliary "fully-generalized" theorem on arbitrary `source` with
the natSucc-shape hypothesis, since the standard `induction
chain` motive cannot specialize the implicit `predecessor`
inside the recursive call.

Pattern documented here for future extension to the remaining
cong-family heads. -/

/-- Generalized unary-head `parStar` inversion.

The source is carried as an arbitrary index plus an explicit shape
equality so recursive calls can consume the midpoint shape recovered by
the one-step inversion. -/
private theorem RawStep.parStar.unary_inv_aux
    {outerScope innerScope : Nat}
    (wrap : RawTerm innerScope → RawTerm outerScope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (wrap innerSource) target →
        ∃ innerTarget,
          target = wrap innerTarget ∧
          RawStep.par innerSource innerTarget)
    {source target : RawTerm outerScope}
    (chain : RawStep.parStar source target) :
    ∀ {innerSource : RawTerm innerScope},
      source = wrap innerSource →
      ∃ innerTarget,
        target = wrap innerTarget ∧
        RawStep.parStar innerSource innerTarget := by
  induction chain with
  | refl _ =>
      intro innerSource sourceEq
      exact ⟨innerSource, sourceEq, RawStep.parStar.refl _⟩
  | trans firstStep _ restIH =>
      intro innerSource sourceEq
      subst sourceEq
      obtain ⟨middleInner, middleEq, innerStep⟩ :=
        parStepInv firstStep
      obtain ⟨targetInner, targetEq, innerChainRest⟩ :=
        restIH middleEq
      exact ⟨targetInner, targetEq,
        RawStep.parStar.trans innerStep innerChainRest⟩

/-- Unary-head `parStar` inversion for an exactly wrapped source. -/
private theorem RawStep.parStar.unary_inv_helper
    {outerScope innerScope : Nat}
    (wrap : RawTerm innerScope → RawTerm outerScope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (wrap innerSource) target →
        ∃ innerTarget,
          target = wrap innerTarget ∧
          RawStep.par innerSource innerTarget)
    {innerSource : RawTerm innerScope} {target : RawTerm outerScope}
    (chain : RawStep.parStar (wrap innerSource) target) :
    ∃ innerTarget,
      target = wrap innerTarget ∧
      RawStep.parStar innerSource innerTarget :=
  RawStep.parStar.unary_inv_aux wrap parStepInv chain rfl

/-- `RawStep.parStar (natSucc predecessor) target → ∃ target's
predecessor with target = natSucc that predecessor and a parStar
chain from the source predecessor to it`.

Cong-family parStar lift — first entry, demonstrating the
existential-output pattern for ctors with cong rules.  Uses the
`natSucc_inv_aux` auxiliary above via a trivial `rfl` source
witness. -/
theorem RawStep.parStar.natSucc_inv {scope : Nat}
    {predecessor target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.natSucc predecessor) target) :
    ∃ predecessorTarget,
      target = RawTerm.natSucc predecessorTarget ∧
      RawStep.parStar predecessor predecessorTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.natSucc
    RawStep.par.natSucc_inv chain

/-- `RawStep.parStar (optionSome value) target` preserves the
`optionSome` head and projects to a value-level `parStar` chain. -/
theorem RawStep.parStar.optionSome_inv {scope : Nat}
    {valueTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.optionSome valueTerm) target) :
    ∃ valueTarget,
      target = RawTerm.optionSome valueTarget ∧
      RawStep.parStar valueTerm valueTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.optionSome
    RawStep.par.optionSome_inv chain

/-- `RawStep.parStar (eitherInl value) target` preserves the
`eitherInl` head and projects to a value-level `parStar` chain. -/
theorem RawStep.parStar.eitherInl_inv {scope : Nat}
    {valueTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.eitherInl valueTerm) target) :
    ∃ valueTarget,
      target = RawTerm.eitherInl valueTarget ∧
      RawStep.parStar valueTerm valueTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.eitherInl
    RawStep.par.eitherInl_inv chain

/-- `RawStep.parStar (eitherInr value) target` preserves the
`eitherInr` head and projects to a value-level `parStar` chain. -/
theorem RawStep.parStar.eitherInr_inv {scope : Nat}
    {valueTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.eitherInr valueTerm) target) :
    ∃ valueTarget,
      target = RawTerm.eitherInr valueTarget ∧
      RawStep.parStar valueTerm valueTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.eitherInr
    RawStep.par.eitherInr_inv chain

/-- `RawStep.parStar (refl witness) target` preserves the `refl` head
and projects to a witness-level `parStar` chain. -/
theorem RawStep.parStar.refl_inv {scope : Nat}
    {rawWitness target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.refl rawWitness) target) :
    ∃ witnessTarget,
      target = RawTerm.refl witnessTarget ∧
      RawStep.parStar rawWitness witnessTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.refl
    RawStep.par.refl_inv chain

/-- `RawStep.parStar (lam body) target` preserves the lambda head and
projects to a body-level `parStar` chain. -/
theorem RawStep.parStar.lam_inv {scope : Nat}
    {body : RawTerm (scope + 1)} {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.lam body) target) :
    ∃ bodyTarget,
      target = RawTerm.lam bodyTarget ∧
      RawStep.parStar body bodyTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.lam
    RawStep.par.lam_inv chain

/-- `RawStep.parStar (pathLam body) target` preserves the path-lambda head
and projects to a body-level `parStar` chain. -/
theorem RawStep.parStar.pathLam_inv {scope : Nat}
    {body : RawTerm (scope + 1)} {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.pathLam body) target) :
    ∃ bodyTarget,
      target = RawTerm.pathLam bodyTarget ∧
      RawStep.parStar body bodyTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.pathLam
    RawStep.par.pathLam_inv chain

end LeanFX2
