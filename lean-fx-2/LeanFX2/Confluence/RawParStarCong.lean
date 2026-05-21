import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity
import LeanFX2.Reduction.RawParInversion.ModalAndAdvanced
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

/-- `RawStep.parStar interval0 target → target = interval0`. -/
theorem RawStep.parStar.interval0_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.interval0 : RawTerm scope) target) :
    target = RawTerm.interval0 :=
  RawStep.parStar.canonical_inv_helper RawStep.par.interval0_inv chain

/-- `RawStep.parStar interval1 target → target = interval1`. -/
theorem RawStep.parStar.interval1_inv
    {target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.interval1 : RawTerm scope) target) :
    target = RawTerm.interval1 :=
  RawStep.parStar.canonical_inv_helper RawStep.par.interval1_inv chain

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

/-- Generalized unary eliminator `parStar` inversion for eliminators whose
β arm returns a developed payload directly.

For a chain from `elimWrap innerSource`, either the whole chain preserves
the eliminator head, or some step fires β after `innerSource` develops to
`introWrap payloadTarget`, followed by an arbitrary tail chain from that
payload. -/
private theorem RawStep.parStar.unary_payload_elim_inv_aux {scope : Nat}
    (elimWrap introWrap : RawTerm scope → RawTerm scope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (elimWrap innerSource) target →
        (∃ innerTarget,
          target = elimWrap innerTarget ∧
          RawStep.par innerSource innerTarget) ∨
        (∃ payloadTarget,
          target = payloadTarget ∧
          RawStep.par innerSource (introWrap payloadTarget)))
    {source target : RawTerm scope}
    (chain : RawStep.parStar source target) :
    ∀ {innerSource : RawTerm scope},
      source = elimWrap innerSource →
      (∃ innerTarget,
        target = elimWrap innerTarget ∧
        RawStep.parStar innerSource innerTarget) ∨
      (∃ payloadTarget,
        RawStep.parStar innerSource (introWrap payloadTarget) ∧
        RawStep.parStar payloadTarget target) := by
  induction chain with
  | refl _ =>
      intro innerSource sourceEq
      exact Or.inl ⟨innerSource, sourceEq, RawStep.parStar.refl _⟩
  | trans firstStep restChain restIH =>
      intro innerSource sourceEq
      subst sourceEq
      cases parStepInv firstStep with
      | inl headCase =>
          obtain ⟨middleInner, middleEq, innerStep⟩ := headCase
          cases restIH middleEq with
          | inl preservedCase =>
              obtain ⟨targetInner, targetEq, innerChainRest⟩ :=
                preservedCase
              exact Or.inl ⟨targetInner, targetEq,
                RawStep.parStar.trans innerStep innerChainRest⟩
          | inr firedCase =>
              obtain ⟨payloadTarget, introChainRest, payloadChain⟩ :=
                firedCase
              exact Or.inr ⟨payloadTarget,
                RawStep.parStar.trans innerStep introChainRest,
                payloadChain⟩
      | inr betaCase =>
          obtain ⟨payloadTarget, middleEq, introStep⟩ := betaCase
          cases middleEq
          exact Or.inr ⟨_,
            RawStep.parStar.trans introStep (RawStep.parStar.refl _),
            restChain⟩

/-- Unary payload-eliminator `parStar` inversion for an exactly wrapped
source. -/
private theorem RawStep.parStar.unary_payload_elim_inv_helper {scope : Nat}
    (elimWrap introWrap : RawTerm scope → RawTerm scope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (elimWrap innerSource) target →
        (∃ innerTarget,
          target = elimWrap innerTarget ∧
          RawStep.par innerSource innerTarget) ∨
        (∃ payloadTarget,
          target = payloadTarget ∧
          RawStep.par innerSource (introWrap payloadTarget)))
    {innerSource target : RawTerm scope}
    (chain : RawStep.parStar (elimWrap innerSource) target) :
    (∃ innerTarget,
      target = elimWrap innerTarget ∧
      RawStep.parStar innerSource innerTarget) ∨
    (∃ payloadTarget,
      RawStep.parStar innerSource (introWrap payloadTarget) ∧
      RawStep.parStar payloadTarget target) :=
  RawStep.parStar.unary_payload_elim_inv_aux elimWrap introWrap
    parStepInv chain rfl

/-- Generalized unary eliminator `parStar` inversion for eliminators whose
β arm returns a contractum built from a two-field developed intro.

This covers raw eliminators such as `refineElim` and `codataDest`:
the source subterm may develop structurally, or it may develop to a
two-field intro whose β contractum then continues reducing. -/
private theorem RawStep.parStar.binary_intro_elim_inv_aux {scope : Nat}
    (elimWrap : RawTerm scope → RawTerm scope)
    (introWrap contractum :
      RawTerm scope → RawTerm scope → RawTerm scope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (elimWrap innerSource) target →
        (∃ innerTarget,
          target = elimWrap innerTarget ∧
          RawStep.par innerSource innerTarget) ∨
        (∃ firstTarget secondTarget,
          target = contractum firstTarget secondTarget ∧
          RawStep.par innerSource (introWrap firstTarget secondTarget)))
    {source target : RawTerm scope}
    (chain : RawStep.parStar source target) :
    ∀ {innerSource : RawTerm scope},
      source = elimWrap innerSource →
      (∃ innerTarget,
        target = elimWrap innerTarget ∧
        RawStep.parStar innerSource innerTarget) ∨
      (∃ firstTarget secondTarget,
        RawStep.parStar innerSource (introWrap firstTarget secondTarget) ∧
        RawStep.parStar (contractum firstTarget secondTarget) target) := by
  induction chain with
  | refl _ =>
      intro innerSource sourceEq
      exact Or.inl ⟨innerSource, sourceEq, RawStep.parStar.refl _⟩
  | trans firstStep restChain restIH =>
      intro innerSource sourceEq
      subst sourceEq
      cases parStepInv firstStep with
      | inl headCase =>
          obtain ⟨middleInner, middleEq, innerStep⟩ := headCase
          cases restIH middleEq with
          | inl preservedCase =>
              obtain ⟨targetInner, targetEq, innerChainRest⟩ :=
                preservedCase
              exact Or.inl ⟨targetInner, targetEq,
                RawStep.parStar.trans innerStep innerChainRest⟩
          | inr firedCase =>
              obtain ⟨firstTarget, secondTarget, introChainRest,
                contractumChain⟩ := firedCase
              exact Or.inr ⟨firstTarget, secondTarget,
                RawStep.parStar.trans innerStep introChainRest,
                contractumChain⟩
      | inr betaCase =>
          obtain ⟨firstTarget, secondTarget, middleEq, introStep⟩ :=
            betaCase
          cases middleEq
          exact Or.inr ⟨firstTarget, secondTarget,
            RawStep.parStar.trans introStep (RawStep.parStar.refl _),
            restChain⟩

/-- Binary-intro eliminator `parStar` inversion for an exactly wrapped
source. -/
private theorem RawStep.parStar.binary_intro_elim_inv_helper {scope : Nat}
    (elimWrap : RawTerm scope → RawTerm scope)
    (introWrap contractum :
      RawTerm scope → RawTerm scope → RawTerm scope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (elimWrap innerSource) target →
        (∃ innerTarget,
          target = elimWrap innerTarget ∧
          RawStep.par innerSource innerTarget) ∨
        (∃ firstTarget secondTarget,
          target = contractum firstTarget secondTarget ∧
          RawStep.par innerSource (introWrap firstTarget secondTarget)))
    {innerSource target : RawTerm scope}
    (chain : RawStep.parStar (elimWrap innerSource) target) :
    (∃ innerTarget,
      target = elimWrap innerTarget ∧
      RawStep.parStar innerSource innerTarget) ∨
    (∃ firstTarget secondTarget,
      RawStep.parStar innerSource (introWrap firstTarget secondTarget) ∧
      RawStep.parStar (contractum firstTarget secondTarget) target) :=
  RawStep.parStar.binary_intro_elim_inv_aux elimWrap introWrap
    contractum parStepInv chain rfl

/-- Generalized binary-head `parStar` inversion.

This is the two-subterm counterpart to `unary_inv_aux`; it threads the
left and right subchains independently through the midpoint produced by
the one-step inversion. -/
private theorem RawStep.parStar.binary_inv_aux
    {outerScope leftScope rightScope : Nat}
    (wrap : RawTerm leftScope → RawTerm rightScope → RawTerm outerScope)
    (parStepInv : ∀ {leftSource rightSource target},
      RawStep.par (wrap leftSource rightSource) target →
        ∃ leftTarget rightTarget,
          target = wrap leftTarget rightTarget ∧
          RawStep.par leftSource leftTarget ∧
          RawStep.par rightSource rightTarget)
    {source target : RawTerm outerScope}
    (chain : RawStep.parStar source target) :
    ∀ {leftSource : RawTerm leftScope} {rightSource : RawTerm rightScope},
      source = wrap leftSource rightSource →
      ∃ leftTarget rightTarget,
        target = wrap leftTarget rightTarget ∧
        RawStep.parStar leftSource leftTarget ∧
        RawStep.parStar rightSource rightTarget := by
  induction chain with
  | refl _ =>
      intro leftSource rightSource sourceEq
      exact ⟨leftSource, rightSource, sourceEq,
        RawStep.parStar.refl _, RawStep.parStar.refl _⟩
  | trans firstStep _ restIH =>
      intro leftSource rightSource sourceEq
      subst sourceEq
      obtain ⟨middleLeft, middleRight, middleEq,
        leftStep, rightStep⟩ := parStepInv firstStep
      obtain ⟨targetLeft, targetRight, targetEq,
        leftChainRest, rightChainRest⟩ := restIH middleEq
      exact ⟨targetLeft, targetRight, targetEq,
        RawStep.parStar.trans leftStep leftChainRest,
        RawStep.parStar.trans rightStep rightChainRest⟩

/-- Binary-head `parStar` inversion for an exactly wrapped source. -/
private theorem RawStep.parStar.binary_inv_helper
    {outerScope leftScope rightScope : Nat}
    (wrap : RawTerm leftScope → RawTerm rightScope → RawTerm outerScope)
    (parStepInv : ∀ {leftSource rightSource target},
      RawStep.par (wrap leftSource rightSource) target →
        ∃ leftTarget rightTarget,
          target = wrap leftTarget rightTarget ∧
          RawStep.par leftSource leftTarget ∧
          RawStep.par rightSource rightTarget)
    {leftSource : RawTerm leftScope} {rightSource : RawTerm rightScope}
    {target : RawTerm outerScope}
    (chain : RawStep.parStar (wrap leftSource rightSource) target) :
    ∃ leftTarget rightTarget,
      target = wrap leftTarget rightTarget ∧
      RawStep.parStar leftSource leftTarget ∧
      RawStep.parStar rightSource rightTarget :=
  RawStep.parStar.binary_inv_aux wrap parStepInv chain rfl

/-- Generalized ternary-head `parStar` inversion.

Used for non-redex constructors with three independently developing
subterms, such as `idCode` and `transpFill`. -/
private theorem RawStep.parStar.ternary_inv_aux
    {outerScope firstScope secondScope thirdScope : Nat}
    (wrap : RawTerm firstScope → RawTerm secondScope → RawTerm thirdScope →
      RawTerm outerScope)
    (parStepInv : ∀ {firstSource secondSource thirdSource target},
      RawStep.par (wrap firstSource secondSource thirdSource) target →
        ∃ firstTarget secondTarget thirdTarget,
          target = wrap firstTarget secondTarget thirdTarget ∧
          RawStep.par firstSource firstTarget ∧
          RawStep.par secondSource secondTarget ∧
          RawStep.par thirdSource thirdTarget)
    {source target : RawTerm outerScope}
    (chain : RawStep.parStar source target) :
    ∀ {firstSource : RawTerm firstScope}
      {secondSource : RawTerm secondScope}
      {thirdSource : RawTerm thirdScope},
      source = wrap firstSource secondSource thirdSource →
      ∃ firstTarget secondTarget thirdTarget,
        target = wrap firstTarget secondTarget thirdTarget ∧
        RawStep.parStar firstSource firstTarget ∧
        RawStep.parStar secondSource secondTarget ∧
        RawStep.parStar thirdSource thirdTarget := by
  induction chain with
  | refl _ =>
      intro firstSource secondSource thirdSource sourceEq
      exact ⟨firstSource, secondSource, thirdSource, sourceEq,
        RawStep.parStar.refl _, RawStep.parStar.refl _,
        RawStep.parStar.refl _⟩
  | trans firstStep _ restIH =>
      intro firstSource secondSource thirdSource sourceEq
      subst sourceEq
      obtain ⟨middleFirst, middleSecond, middleThird, middleEq,
        firstStepInner, secondStepInner, thirdStepInner⟩ :=
        parStepInv firstStep
      obtain ⟨targetFirst, targetSecond, targetThird, targetEq,
        firstChainRest, secondChainRest, thirdChainRest⟩ :=
        restIH middleEq
      exact ⟨targetFirst, targetSecond, targetThird, targetEq,
        RawStep.parStar.trans firstStepInner firstChainRest,
        RawStep.parStar.trans secondStepInner secondChainRest,
        RawStep.parStar.trans thirdStepInner thirdChainRest⟩

/-- Ternary-head `parStar` inversion for an exactly wrapped source. -/
private theorem RawStep.parStar.ternary_inv_helper
    {outerScope firstScope secondScope thirdScope : Nat}
    (wrap : RawTerm firstScope → RawTerm secondScope → RawTerm thirdScope →
      RawTerm outerScope)
    (parStepInv : ∀ {firstSource secondSource thirdSource target},
      RawStep.par (wrap firstSource secondSource thirdSource) target →
        ∃ firstTarget secondTarget thirdTarget,
          target = wrap firstTarget secondTarget thirdTarget ∧
          RawStep.par firstSource firstTarget ∧
          RawStep.par secondSource secondTarget ∧
          RawStep.par thirdSource thirdTarget)
    {firstSource : RawTerm firstScope}
    {secondSource : RawTerm secondScope}
    {thirdSource : RawTerm thirdScope}
    {target : RawTerm outerScope}
    (chain :
      RawStep.parStar (wrap firstSource secondSource thirdSource) target) :
    ∃ firstTarget secondTarget thirdTarget,
      target = wrap firstTarget secondTarget thirdTarget ∧
      RawStep.parStar firstSource firstTarget ∧
      RawStep.parStar secondSource secondTarget ∧
      RawStep.parStar thirdSource thirdTarget :=
  RawStep.parStar.ternary_inv_aux wrap parStepInv chain rfl

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

/-- `RawStep.parStar (pair first second) target` preserves the `pair`
head and projects to component-level `parStar` chains. -/
theorem RawStep.parStar.pair_inv {scope : Nat}
    {firstValue secondValue target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.pair firstValue secondValue) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.pair firstTarget secondTarget ∧
      RawStep.parStar firstValue firstTarget ∧
      RawStep.parStar secondValue secondTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.pair
    RawStep.par.pair_inv chain

/-- `RawStep.parStar (listCons head tail) target` preserves the
`listCons` head and projects to component-level `parStar` chains. -/
theorem RawStep.parStar.listCons_inv {scope : Nat}
    {headTerm tailTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.listCons headTerm tailTerm) target) :
    ∃ headTarget tailTarget,
      target = RawTerm.listCons headTarget tailTarget ∧
      RawStep.parStar headTerm headTarget ∧
      RawStep.parStar tailTerm tailTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.listCons
    RawStep.par.listCons_inv chain

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

/-- `RawStep.parStar (listCode element) target` preserves the
`listCode` head and projects to an element-code `parStar` chain. -/
theorem RawStep.parStar.listCode_inv {scope : Nat}
    {elementCode target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.listCode elementCode) target) :
    ∃ elementTarget,
      target = RawTerm.listCode elementTarget ∧
      RawStep.parStar elementCode elementTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.listCode
    RawStep.par.listCode_inv chain

/-- `RawStep.parStar (optionCode element) target` preserves the
`optionCode` head and projects to an element-code `parStar` chain. -/
theorem RawStep.parStar.optionCode_inv {scope : Nat}
    {elementCode target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.optionCode elementCode) target) :
    ∃ elementTarget,
      target = RawTerm.optionCode elementTarget ∧
      RawStep.parStar elementCode elementTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.optionCode
    RawStep.par.optionCode_inv chain

/-- `RawStep.parStar (arrowCode domain codomain) target` preserves the
`arrowCode` head and projects to code-level `parStar` chains. -/
theorem RawStep.parStar.arrowCode_inv {scope : Nat}
    {domainCode codomainCode target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.arrowCode domainCode codomainCode) target) :
    ∃ domainTarget codomainTarget,
      target = RawTerm.arrowCode domainTarget codomainTarget ∧
      RawStep.parStar domainCode domainTarget ∧
      RawStep.parStar codomainCode codomainTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.arrowCode
    RawStep.par.arrowCode_inv chain

/-- `RawStep.parStar (piTyCode domain codomain) target` preserves the
`piTyCode` head and projects across both code payloads. -/
theorem RawStep.parStar.piTyCode_inv {scope : Nat}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.piTyCode domainCode codomainCode) target) :
    ∃ (domainTarget : RawTerm scope) (codomainTarget : RawTerm (scope + 1)),
      target = RawTerm.piTyCode domainTarget codomainTarget ∧
      RawStep.parStar domainCode domainTarget ∧
      RawStep.parStar codomainCode codomainTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.piTyCode
    RawStep.par.piTyCode_inv chain

/-- `RawStep.parStar (sigmaTyCode first second) target` preserves the
`sigmaTyCode` head and projects across both code payloads. -/
theorem RawStep.parStar.sigmaTyCode_inv {scope : Nat}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.sigmaTyCode firstCode secondCode) target) :
    ∃ (firstTarget : RawTerm scope) (secondTarget : RawTerm (scope + 1)),
      target = RawTerm.sigmaTyCode firstTarget secondTarget ∧
      RawStep.parStar firstCode firstTarget ∧
      RawStep.parStar secondCode secondTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.sigmaTyCode
    RawStep.par.sigmaTyCode_inv chain

/-- `RawStep.parStar (productCode first second) target` preserves the
`productCode` head and projects to component code chains. -/
theorem RawStep.parStar.productCode_inv {scope : Nat}
    {firstCode secondCode target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.productCode firstCode secondCode) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.productCode firstTarget secondTarget ∧
      RawStep.parStar firstCode firstTarget ∧
      RawStep.parStar secondCode secondTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.productCode
    RawStep.par.productCode_inv chain

/-- `RawStep.parStar (sumCode left right) target` preserves the
`sumCode` head and projects to component code chains. -/
theorem RawStep.parStar.sumCode_inv {scope : Nat}
    {leftCode rightCode target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.sumCode leftCode rightCode) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.sumCode leftTarget rightTarget ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.sumCode
    RawStep.par.sumCode_inv chain

/-- `RawStep.parStar (eitherCode left right) target` preserves the
`eitherCode` head and projects to component code chains. -/
theorem RawStep.parStar.eitherCode_inv {scope : Nat}
    {leftCode rightCode target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.eitherCode leftCode rightCode) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.eitherCode leftTarget rightTarget ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.eitherCode
    RawStep.par.eitherCode_inv chain

/-- `RawStep.parStar (equivCode left right) target` preserves the
`equivCode` head and projects to component code chains. -/
theorem RawStep.parStar.equivCode_inv {scope : Nat}
    {leftCode rightCode target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.equivCode leftCode rightCode) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.equivCode leftTarget rightTarget ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.equivCode
    RawStep.par.equivCode_inv chain

/-- `RawStep.parStar (idCode type left right) target` preserves the
`idCode` head and projects to all three code chains. -/
theorem RawStep.parStar.idCode_inv {scope : Nat}
    {typeCode leftCode rightCode target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.idCode typeCode leftCode rightCode) target) :
    ∃ typeTarget leftTarget rightTarget,
      target = RawTerm.idCode typeTarget leftTarget rightTarget ∧
      RawStep.parStar typeCode typeTarget ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  RawStep.parStar.ternary_inv_helper RawTerm.idCode
    RawStep.par.idCode_inv chain

/-- `RawStep.parStar (intervalOpp interval) target` preserves the
`intervalOpp` head and projects to an interval-level chain. -/
theorem RawStep.parStar.intervalOpp_inv {scope : Nat}
    {intervalTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.intervalOpp intervalTerm) target) :
    ∃ intervalTarget,
      target = RawTerm.intervalOpp intervalTarget ∧
      RawStep.parStar intervalTerm intervalTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.intervalOpp
    RawStep.par.intervalOpp_inv chain

/-- `RawStep.parStar (intervalMeet left right) target` preserves the
`intervalMeet` head and projects to component chains. -/
theorem RawStep.parStar.intervalMeet_inv {scope : Nat}
    {leftInterval rightInterval target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.intervalMeet leftInterval rightInterval) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.intervalMeet leftTarget rightTarget ∧
      RawStep.parStar leftInterval leftTarget ∧
      RawStep.parStar rightInterval rightTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.intervalMeet
    RawStep.par.intervalMeet_inv chain

/-- `RawStep.parStar (intervalJoin left right) target` preserves the
`intervalJoin` head and projects to component chains. -/
theorem RawStep.parStar.intervalJoin_inv {scope : Nat}
    {leftInterval rightInterval target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.intervalJoin leftInterval rightInterval) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.intervalJoin leftTarget rightTarget ∧
      RawStep.parStar leftInterval leftTarget ∧
      RawStep.parStar rightInterval rightTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.intervalJoin
    RawStep.par.intervalJoin_inv chain

/-- `RawStep.parStar (uaToEquiv proof) target` preserves the
`uaToEquiv` head and projects to a proof chain. -/
theorem RawStep.parStar.uaToEquiv_inv {scope : Nat}
    {proofTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.uaToEquiv proofTerm) target) :
    ∃ proofTarget,
      target = RawTerm.uaToEquiv proofTarget ∧
      RawStep.parStar proofTerm proofTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.uaToEquiv
    RawStep.par.uaToEquiv_inv chain

/-- `RawStep.parStar (pathCompose left right) target` preserves the
`pathCompose` head and projects to component path chains. -/
theorem RawStep.parStar.pathCompose_inv {scope : Nat}
    {leftPath rightPath target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.pathCompose leftPath rightPath) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.pathCompose leftTarget rightTarget ∧
      RawStep.parStar leftPath leftTarget ∧
      RawStep.parStar rightPath rightTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.pathCompose
    RawStep.par.pathCompose_inv chain

/-- `RawStep.parStar (oeqTrans first second) target` preserves the
`oeqTrans` head and projects to proof chains. -/
theorem RawStep.parStar.oeqTrans_inv {scope : Nat}
    {firstProof secondProof target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.oeqTrans firstProof secondProof) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.oeqTrans firstTarget secondTarget ∧
      RawStep.parStar firstProof firstTarget ∧
      RawStep.parStar secondProof secondTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.oeqTrans
    RawStep.par.oeqTrans_inv chain

/-- `RawStep.parStar (equivCompose first second) target` preserves the
`equivCompose` head and projects to equivalence chains. -/
theorem RawStep.parStar.equivCompose_inv {scope : Nat}
    {firstEquiv secondEquiv target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.equivCompose firstEquiv secondEquiv) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.equivCompose firstTarget secondTarget ∧
      RawStep.parStar firstEquiv firstTarget ∧
      RawStep.parStar secondEquiv secondTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.equivCompose
    RawStep.par.equivCompose_inv chain

/-- `RawStep.parStar (glueIntro base partial) target` preserves the
`glueIntro` head and projects to component chains. -/
theorem RawStep.parStar.glueIntro_inv {scope : Nat}
    {baseValue partialValue target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.glueIntro baseValue partialValue) target) :
    ∃ baseTarget partialTarget,
      target = RawTerm.glueIntro baseTarget partialTarget ∧
      RawStep.parStar baseValue baseTarget ∧
      RawStep.parStar partialValue partialTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.glueIntro
    RawStep.par.glueIntro_inv chain

/-- `RawStep.parStar (oeqRefl witness) target` preserves the
`oeqRefl` head and projects to a witness chain. -/
theorem RawStep.parStar.oeqRefl_inv {scope : Nat}
    {witness target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.oeqRefl witness) target) :
    ∃ witnessTarget,
      target = RawTerm.oeqRefl witnessTarget ∧
      RawStep.parStar witness witnessTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.oeqRefl
    RawStep.par.oeqRefl_inv chain

/-- `RawStep.parStar (oeqFunext pointwise) target` preserves the
`oeqFunext` head and projects to a pointwise-proof chain. -/
theorem RawStep.parStar.oeqFunext_inv {scope : Nat}
    {pointwiseEquality target : RawTerm scope}
    (chain : RawStep.parStar
      (RawTerm.oeqFunext pointwiseEquality) target) :
    ∃ pointwiseTarget,
      target = RawTerm.oeqFunext pointwiseTarget ∧
      RawStep.parStar pointwiseEquality pointwiseTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.oeqFunext
    RawStep.par.oeqFunext_inv chain

/-- `RawStep.parStar (oeqJ base witness) target` preserves the `oeqJ`
head and projects to base/witness chains. -/
theorem RawStep.parStar.oeqJ_inv {scope : Nat}
    {baseCase witness target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.oeqJ baseCase witness) target) :
    ∃ baseTarget witnessTarget,
      target = RawTerm.oeqJ baseTarget witnessTarget ∧
      RawStep.parStar baseCase baseTarget ∧
      RawStep.parStar witness witnessTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.oeqJ
    RawStep.par.oeqJ_inv chain

/-- `RawStep.parStar (idStrictRefl witness) target` preserves the
`idStrictRefl` head and projects to a witness chain. -/
theorem RawStep.parStar.idStrictRefl_inv {scope : Nat}
    {witness target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.idStrictRefl witness) target) :
    ∃ witnessTarget,
      target = RawTerm.idStrictRefl witnessTarget ∧
      RawStep.parStar witness witnessTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.idStrictRefl
    RawStep.par.idStrictRefl_inv chain

/-- `RawStep.parStar (equivIntro forward backward) target` preserves
the `equivIntro` head and projects to both function chains. -/
theorem RawStep.parStar.equivIntro_inv {scope : Nat}
    {forwardFn backwardFn target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.equivIntro forwardFn backwardFn) target) :
    ∃ forwardTarget backwardTarget,
      target = RawTerm.equivIntro forwardTarget backwardTarget ∧
      RawStep.parStar forwardFn forwardTarget ∧
      RawStep.parStar backwardFn backwardTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.equivIntro
    RawStep.par.equivIntro_inv chain

/-- `RawStep.parStar (equivApp equiv argument) target` preserves the
`equivApp` head and projects to equiv/argument chains. -/
theorem RawStep.parStar.equivApp_inv {scope : Nat}
    {equivTerm argument target : RawTerm scope}
    (chain : RawStep.parStar
      (RawTerm.equivApp equivTerm argument) target) :
    ∃ equivTarget argumentTarget,
      target = RawTerm.equivApp equivTarget argumentTarget ∧
      RawStep.parStar equivTerm equivTarget ∧
      RawStep.parStar argument argumentTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.equivApp
    RawStep.par.equivApp_inv chain

/-- `RawStep.parStar (transpFill path interval source) target`
preserves the `transpFill` head and projects to all three component
chains. -/
theorem RawStep.parStar.transpFill_inv {scope : Nat}
    {pathTerm intervalTerm sourceTerm target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.transpFill pathTerm intervalTerm sourceTerm) target) :
    ∃ pathTarget intervalTarget sourceTarget,
      target = RawTerm.transpFill pathTarget intervalTarget sourceTarget ∧
      RawStep.parStar pathTerm pathTarget ∧
      RawStep.parStar intervalTerm intervalTarget ∧
      RawStep.parStar sourceTerm sourceTarget :=
  RawStep.parStar.ternary_inv_helper RawTerm.transpFill
    RawStep.par.transpFill_inv chain

/-- `RawStep.parStar (modIntro inner) target` preserves the `modIntro`
head and projects to an inner chain. -/
theorem RawStep.parStar.modIntro_inv {scope : Nat}
    {innerTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.modIntro innerTerm) target) :
    ∃ innerTarget,
      target = RawTerm.modIntro innerTarget ∧
      RawStep.parStar innerTerm innerTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.modIntro
    RawStep.par.modIntro_inv chain

/-- `RawStep.parStar (modElim inner) target` either preserves the
`modElim` head or fires modal β after the inner term develops to a
`modIntro` payload. -/
theorem RawStep.parStar.modElim_inv {scope : Nat}
    {innerTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.modElim innerTerm) target) :
    (∃ innerTarget,
      target = RawTerm.modElim innerTarget ∧
      RawStep.parStar innerTerm innerTarget) ∨
    (∃ payloadTarget,
      RawStep.parStar innerTerm (RawTerm.modIntro payloadTarget) ∧
      RawStep.parStar payloadTarget target) :=
  RawStep.parStar.unary_payload_elim_inv_helper RawTerm.modElim
    RawTerm.modIntro RawStep.par.modElim_inv chain

/-- `RawStep.parStar (subsume inner) target` preserves the `subsume`
head and projects to an inner chain. -/
theorem RawStep.parStar.subsume_inv {scope : Nat}
    {innerTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.subsume innerTerm) target) :
    ∃ innerTarget,
      target = RawTerm.subsume innerTarget ∧
      RawStep.parStar innerTerm innerTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.subsume
    RawStep.par.subsume_inv chain

/-- `RawStep.parStar (cumulUpMarker inner) target` preserves the
`cumulUpMarker` head and projects to an inner-code chain. -/
theorem RawStep.parStar.cumulUpMarker_inv {scope : Nat}
    {innerCodeRaw target : RawTerm scope}
    (chain : RawStep.parStar
      (RawTerm.cumulUpMarker innerCodeRaw) target) :
    ∃ innerTarget,
      target = RawTerm.cumulUpMarker innerTarget ∧
      RawStep.parStar innerCodeRaw innerTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.cumulUpMarker
    RawStep.par.cumulUpMarker_inv chain

/-- `RawStep.parStar (refineIntro value proof) target` preserves the
`refineIntro` head and projects to value/proof chains. -/
theorem RawStep.parStar.refineIntro_inv {scope : Nat}
    {rawValue predicateProof target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.refineIntro rawValue predicateProof) target) :
    ∃ valueTarget proofTarget,
      target = RawTerm.refineIntro valueTarget proofTarget ∧
      RawStep.parStar rawValue valueTarget ∧
      RawStep.parStar predicateProof proofTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.refineIntro
    RawStep.par.refineIntro_inv chain

/-- `RawStep.parStar (refineElim refinedValue) target` either preserves
the `refineElim` head or fires refinement β after the refined value
develops to a `refineIntro`. -/
theorem RawStep.parStar.refineElim_inv {scope : Nat}
    {refinedValue target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.refineElim refinedValue) target) :
    (∃ refinedTarget,
      target = RawTerm.refineElim refinedTarget ∧
      RawStep.parStar refinedValue refinedTarget) ∨
    (∃ valueTarget proofTarget,
      RawStep.parStar refinedValue
        (RawTerm.refineIntro valueTarget proofTarget) ∧
      RawStep.parStar valueTarget target) :=
  RawStep.parStar.binary_intro_elim_inv_helper RawTerm.refineElim
    RawTerm.refineIntro (fun valueTarget _ => valueTarget)
    RawStep.par.refineElim_inv chain

/-- `RawStep.parStar (recordIntro firstField) target` preserves the
`recordIntro` head and projects to the field chain. -/
theorem RawStep.parStar.recordIntro_inv {scope : Nat}
    {firstField target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.recordIntro firstField) target) :
    ∃ firstTarget,
      target = RawTerm.recordIntro firstTarget ∧
      RawStep.parStar firstField firstTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.recordIntro
    RawStep.par.recordIntro_inv chain

/-- `RawStep.parStar (recordProj recordValue) target` either preserves
the `recordProj` head or fires record β after the record develops to a
`recordIntro` field. -/
theorem RawStep.parStar.recordProj_inv {scope : Nat}
    {recordValue target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.recordProj recordValue) target) :
    (∃ recordTarget,
      target = RawTerm.recordProj recordTarget ∧
      RawStep.parStar recordValue recordTarget) ∨
    (∃ firstTarget,
      RawStep.parStar recordValue (RawTerm.recordIntro firstTarget) ∧
      RawStep.parStar firstTarget target) :=
  RawStep.parStar.unary_payload_elim_inv_helper RawTerm.recordProj
    RawTerm.recordIntro RawStep.par.recordProj_inv chain

/-- `RawStep.parStar (codataUnfold state transition) target` preserves
the `codataUnfold` head and projects to state/transition chains. -/
theorem RawStep.parStar.codataUnfold_inv {scope : Nat}
    {initialState transition target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.codataUnfold initialState transition) target) :
    ∃ stateTarget transitionTarget,
      target = RawTerm.codataUnfold stateTarget transitionTarget ∧
      RawStep.parStar initialState stateTarget ∧
      RawStep.parStar transition transitionTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.codataUnfold
    RawStep.par.codataUnfold_inv chain

/-- `RawStep.parStar (codataDest codataValue) target` either preserves
the `codataDest` head or fires codata β after the codata value develops
to an unfold. -/
theorem RawStep.parStar.codataDest_inv {scope : Nat}
    {codataValue target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.codataDest codataValue) target) :
    (∃ codataTarget,
      target = RawTerm.codataDest codataTarget ∧
      RawStep.parStar codataValue codataTarget) ∨
    (∃ stateTarget transitionTarget,
      RawStep.parStar codataValue
        (RawTerm.codataUnfold stateTarget transitionTarget) ∧
      RawStep.parStar (RawTerm.app transitionTarget stateTarget) target) :=
  RawStep.parStar.binary_intro_elim_inv_helper RawTerm.codataDest
    RawTerm.codataUnfold
    (fun stateTarget transitionTarget => RawTerm.app transitionTarget stateTarget)
    RawStep.par.codataDest_inv chain

/-- `RawStep.parStar (sessionSend channel payload) target` preserves
the `sessionSend` head and projects to channel/payload chains. -/
theorem RawStep.parStar.sessionSend_inv {scope : Nat}
    {channel payload target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.sessionSend channel payload) target) :
    ∃ channelTarget payloadTarget,
      target = RawTerm.sessionSend channelTarget payloadTarget ∧
      RawStep.parStar channel channelTarget ∧
      RawStep.parStar payload payloadTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.sessionSend
    RawStep.par.sessionSend_inv chain

/-- `RawStep.parStar (sessionRecv channel) target` preserves the
`sessionRecv` head and projects to the channel chain. -/
theorem RawStep.parStar.sessionRecv_inv {scope : Nat}
    {channel target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.sessionRecv channel) target) :
    ∃ channelTarget,
      target = RawTerm.sessionRecv channelTarget ∧
      RawStep.parStar channel channelTarget :=
  RawStep.parStar.unary_inv_helper RawTerm.sessionRecv
    RawStep.par.sessionRecv_inv chain

/-- `RawStep.parStar (effectPerform operation arguments) target`
preserves the `effectPerform` head and projects to both argument
chains. -/
theorem RawStep.parStar.effectPerform_inv {scope : Nat}
    {operationTag arguments target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.effectPerform operationTag arguments) target) :
    ∃ operationTarget argumentsTarget,
      target = RawTerm.effectPerform operationTarget argumentsTarget ∧
      RawStep.parStar operationTag operationTarget ∧
      RawStep.parStar arguments argumentsTarget :=
  RawStep.parStar.binary_inv_helper RawTerm.effectPerform
    RawStep.par.effectPerform_inv chain

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
