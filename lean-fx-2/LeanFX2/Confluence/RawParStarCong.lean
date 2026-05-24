import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParInversion.AtomicCtors
import LeanFX2.Reduction.RawParInversion.CubicalAndIdentity
import LeanFX2.Reduction.RawParInversion.ModalAndAdvanced
import LeanFX2.Reduction.RawParInversion.TypeCodes

/-! # RawParStarCong — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


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

/-- Generalized unary eliminator `parStar` inversion with two redex
families.

This is used by raw `idToEquiv`: the proof argument may develop
structurally, to `refl`, or to `oeqTrans`, with two different
contractum families. -/
private theorem RawStep.parStar.unary_two_redex_elim_inv_aux
    {PayloadLeft PayloadRight : Type}
    {scope : Nat}
    (elimWrap : RawTerm scope → RawTerm scope)
    (leftIntro : PayloadLeft → RawTerm scope)
    (rightIntro : PayloadRight → RawTerm scope)
    (leftContractum : PayloadLeft → RawTerm scope)
    (rightContractum : PayloadRight → RawTerm scope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (elimWrap innerSource) target →
        (∃ innerTarget,
          target = elimWrap innerTarget ∧
          RawStep.par innerSource innerTarget) ∨
        (∃ payload,
          target = leftContractum payload ∧
          RawStep.par innerSource (leftIntro payload)) ∨
        (∃ payload,
          target = rightContractum payload ∧
          RawStep.par innerSource (rightIntro payload)))
    {source target : RawTerm scope}
    (chain : RawStep.parStar source target) :
    ∀ {innerSource : RawTerm scope},
      source = elimWrap innerSource →
      (∃ innerTarget,
        target = elimWrap innerTarget ∧
        RawStep.parStar innerSource innerTarget) ∨
      (∃ payload,
        RawStep.parStar innerSource (leftIntro payload) ∧
        RawStep.parStar (leftContractum payload) target) ∨
      (∃ payload,
        RawStep.parStar innerSource (rightIntro payload) ∧
        RawStep.parStar (rightContractum payload) target) := by
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
          | inr redexCases =>
              cases redexCases with
              | inl leftCase =>
                  obtain ⟨payload, introChainRest,
                    contractumChain⟩ := leftCase
                  exact Or.inr (Or.inl ⟨payload,
                    RawStep.parStar.trans innerStep introChainRest,
                    contractumChain⟩)
              | inr rightCase =>
                  obtain ⟨payload, introChainRest,
                    contractumChain⟩ := rightCase
                  exact Or.inr (Or.inr ⟨payload,
                    RawStep.parStar.trans innerStep introChainRest,
                    contractumChain⟩)
      | inr redexCases =>
          cases redexCases with
          | inl leftCase =>
              obtain ⟨payload, middleEq, innerStep⟩ := leftCase
              cases middleEq
              exact Or.inr (Or.inl ⟨payload,
                RawStep.parStar.trans innerStep (RawStep.parStar.refl _),
                restChain⟩)
          | inr rightCase =>
              obtain ⟨payload, middleEq, innerStep⟩ := rightCase
              cases middleEq
              exact Or.inr (Or.inr ⟨payload,
                RawStep.parStar.trans innerStep (RawStep.parStar.refl _),
                restChain⟩)

/-- Unary, two-redex eliminator inversion for an exactly wrapped source. -/
private theorem RawStep.parStar.unary_two_redex_elim_inv_helper
    {PayloadLeft PayloadRight : Type}
    {scope : Nat}
    (elimWrap : RawTerm scope → RawTerm scope)
    (leftIntro : PayloadLeft → RawTerm scope)
    (rightIntro : PayloadRight → RawTerm scope)
    (leftContractum : PayloadLeft → RawTerm scope)
    (rightContractum : PayloadRight → RawTerm scope)
    (parStepInv : ∀ {innerSource target},
      RawStep.par (elimWrap innerSource) target →
        (∃ innerTarget,
          target = elimWrap innerTarget ∧
          RawStep.par innerSource innerTarget) ∨
        (∃ payload,
          target = leftContractum payload ∧
          RawStep.par innerSource (leftIntro payload)) ∨
        (∃ payload,
          target = rightContractum payload ∧
          RawStep.par innerSource (rightIntro payload)))
    {innerSource target : RawTerm scope}
    (chain : RawStep.parStar (elimWrap innerSource) target) :
    (∃ innerTarget,
      target = elimWrap innerTarget ∧
      RawStep.parStar innerSource innerTarget) ∨
    (∃ payload,
      RawStep.parStar innerSource (leftIntro payload) ∧
      RawStep.parStar (leftContractum payload) target) ∨
    (∃ payload,
      RawStep.parStar innerSource (rightIntro payload) ∧
      RawStep.parStar (rightContractum payload) target) :=
  RawStep.parStar.unary_two_redex_elim_inv_aux
    elimWrap leftIntro rightIntro leftContractum rightContractum
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

/-- Generalized binary eliminator `parStar` inversion for redex parents
whose β arm is triggered by the left subterm developing to a unary
intro, while the right subterm develops independently.

This covers application-like heads such as `app` and `pathApp`. -/
private theorem RawStep.parStar.binary_left_intro_elim_inv_aux
    {outerScope leftScope rightScope introScope : Nat}
    (elimWrap :
      RawTerm leftScope → RawTerm rightScope → RawTerm outerScope)
    (introWrap : RawTerm introScope → RawTerm leftScope)
    (contractum :
      RawTerm introScope → RawTerm rightScope → RawTerm outerScope)
    (parStepInv : ∀ {leftSource rightSource target},
      RawStep.par (elimWrap leftSource rightSource) target →
        (∃ leftTarget rightTarget,
          target = elimWrap leftTarget rightTarget ∧
          RawStep.par leftSource leftTarget ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ introTarget rightTarget,
          target = contractum introTarget rightTarget ∧
          RawStep.par leftSource (introWrap introTarget) ∧
          RawStep.par rightSource rightTarget))
    {source target : RawTerm outerScope}
    (chain : RawStep.parStar source target) :
    ∀ {leftSource : RawTerm leftScope}
      {rightSource : RawTerm rightScope},
      source = elimWrap leftSource rightSource →
      (∃ leftTarget rightTarget,
        target = elimWrap leftTarget rightTarget ∧
        RawStep.parStar leftSource leftTarget ∧
        RawStep.parStar rightSource rightTarget) ∨
      (∃ introTarget rightTarget,
        RawStep.parStar leftSource (introWrap introTarget) ∧
        RawStep.parStar rightSource rightTarget ∧
        RawStep.parStar (contractum introTarget rightTarget) target) := by
  induction chain with
  | refl _ =>
      intro leftSource rightSource sourceEq
      exact Or.inl ⟨leftSource, rightSource, sourceEq,
        RawStep.parStar.refl _, RawStep.parStar.refl _⟩
  | trans firstStep restChain restIH =>
      intro leftSource rightSource sourceEq
      subst sourceEq
      cases parStepInv firstStep with
      | inl headCase =>
          obtain ⟨middleLeft, middleRight, middleEq, leftStep,
            rightStep⟩ := headCase
          cases restIH middleEq with
          | inl preservedCase =>
              obtain ⟨targetLeft, targetRight, targetEq, leftChainRest,
                rightChainRest⟩ := preservedCase
              exact Or.inl ⟨targetLeft, targetRight, targetEq,
                RawStep.parStar.trans leftStep leftChainRest,
                RawStep.parStar.trans rightStep rightChainRest⟩
          | inr firedCase =>
              obtain ⟨introTarget, rightTarget, introChainRest,
                rightChainRest, contractumChain⟩ := firedCase
              exact Or.inr ⟨introTarget, rightTarget,
                RawStep.parStar.trans leftStep introChainRest,
                RawStep.parStar.trans rightStep rightChainRest,
                contractumChain⟩
      | inr betaCase =>
          obtain ⟨introTarget, rightTarget, middleEq, leftStep,
            rightStep⟩ := betaCase
          cases middleEq
          exact Or.inr ⟨introTarget, rightTarget,
            RawStep.parStar.trans leftStep (RawStep.parStar.refl _),
            RawStep.parStar.trans rightStep (RawStep.parStar.refl _),
            restChain⟩

/-- Application-like `parStar` inversion for an exactly wrapped source. -/
private theorem RawStep.parStar.binary_left_intro_elim_inv_helper
    {outerScope leftScope rightScope introScope : Nat}
    (elimWrap :
      RawTerm leftScope → RawTerm rightScope → RawTerm outerScope)
    (introWrap : RawTerm introScope → RawTerm leftScope)
    (contractum :
      RawTerm introScope → RawTerm rightScope → RawTerm outerScope)
    (parStepInv : ∀ {leftSource rightSource target},
      RawStep.par (elimWrap leftSource rightSource) target →
        (∃ leftTarget rightTarget,
          target = elimWrap leftTarget rightTarget ∧
          RawStep.par leftSource leftTarget ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ introTarget rightTarget,
          target = contractum introTarget rightTarget ∧
          RawStep.par leftSource (introWrap introTarget) ∧
          RawStep.par rightSource rightTarget))
    {leftSource : RawTerm leftScope}
    {rightSource : RawTerm rightScope}
    {target : RawTerm outerScope}
    (chain : RawStep.parStar (elimWrap leftSource rightSource) target) :
    (∃ leftTarget rightTarget,
      target = elimWrap leftTarget rightTarget ∧
      RawStep.parStar leftSource leftTarget ∧
      RawStep.parStar rightSource rightTarget) ∨
    (∃ introTarget rightTarget,
      RawStep.parStar leftSource (introWrap introTarget) ∧
      RawStep.parStar rightSource rightTarget ∧
      RawStep.parStar (contractum introTarget rightTarget) target) :=
  RawStep.parStar.binary_left_intro_elim_inv_aux elimWrap introWrap
    contractum parStepInv chain rfl

/-- Generalized binary eliminator `parStar` inversion where the left
subterm may trigger one of three redex families.

This is the raw shape of `transp`: the path side can develop to a
constant `pathLam`, a `uaToEquiv`, or a `pathCompose`, and each family
has its own contractum. -/
private theorem RawStep.parStar.binary_left_three_redex_elim_inv_aux
    {PayloadFirst PayloadSecond PayloadThird : Type}
    {outerScope leftScope rightScope : Nat}
    (elimWrap :
      RawTerm leftScope → RawTerm rightScope → RawTerm outerScope)
    (firstIntro : PayloadFirst → RawTerm leftScope)
    (secondIntro : PayloadSecond → RawTerm leftScope)
    (thirdIntro : PayloadThird → RawTerm leftScope)
    (firstContractum :
      PayloadFirst → RawTerm rightScope → RawTerm outerScope)
    (secondContractum :
      PayloadSecond → RawTerm rightScope → RawTerm outerScope)
    (thirdContractum :
      PayloadThird → RawTerm rightScope → RawTerm outerScope)
    (parStepInv : ∀ {leftSource rightSource target},
      RawStep.par (elimWrap leftSource rightSource) target →
        (∃ leftTarget rightTarget,
          target = elimWrap leftTarget rightTarget ∧
          RawStep.par leftSource leftTarget ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ payload rightTarget,
          target = firstContractum payload rightTarget ∧
          RawStep.par leftSource (firstIntro payload) ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ payload rightTarget,
          target = secondContractum payload rightTarget ∧
          RawStep.par leftSource (secondIntro payload) ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ payload rightTarget,
          target = thirdContractum payload rightTarget ∧
          RawStep.par leftSource (thirdIntro payload) ∧
          RawStep.par rightSource rightTarget))
    {source target : RawTerm outerScope}
    (chain : RawStep.parStar source target) :
    ∀ {leftSource : RawTerm leftScope} {rightSource : RawTerm rightScope},
      source = elimWrap leftSource rightSource →
      (∃ leftTarget rightTarget,
        target = elimWrap leftTarget rightTarget ∧
        RawStep.parStar leftSource leftTarget ∧
        RawStep.parStar rightSource rightTarget) ∨
      (∃ payload rightTarget,
        RawStep.parStar leftSource (firstIntro payload) ∧
        RawStep.parStar rightSource rightTarget ∧
        RawStep.parStar (firstContractum payload rightTarget) target) ∨
      (∃ payload rightTarget,
        RawStep.parStar leftSource (secondIntro payload) ∧
        RawStep.parStar rightSource rightTarget ∧
        RawStep.parStar (secondContractum payload rightTarget) target) ∨
      (∃ payload rightTarget,
        RawStep.parStar leftSource (thirdIntro payload) ∧
        RawStep.parStar rightSource rightTarget ∧
        RawStep.parStar (thirdContractum payload rightTarget) target) := by
  induction chain with
  | refl _ =>
      intro leftSource rightSource sourceEq
      exact Or.inl ⟨leftSource, rightSource, sourceEq,
        RawStep.parStar.refl _, RawStep.parStar.refl _⟩
  | trans firstStep restChain restIH =>
      intro leftSource rightSource sourceEq
      subst sourceEq
      cases parStepInv firstStep with
      | inl headCase =>
          obtain ⟨middleLeft, middleRight, middleEq, leftStep,
            rightStep⟩ := headCase
          cases restIH middleEq with
          | inl preservedCase =>
              obtain ⟨targetLeft, targetRight, targetEq, leftRest,
                rightRest⟩ := preservedCase
              exact Or.inl ⟨targetLeft, targetRight, targetEq,
                RawStep.parStar.trans leftStep leftRest,
                RawStep.parStar.trans rightStep rightRest⟩
          | inr redexCases =>
              cases redexCases with
              | inl firstCase =>
                  obtain ⟨payload, rightTarget, leftRest, rightRest,
                    contractumChain⟩ := firstCase
                  exact Or.inr (Or.inl ⟨payload, rightTarget,
                    RawStep.parStar.trans leftStep leftRest,
                    RawStep.parStar.trans rightStep rightRest,
                    contractumChain⟩)
              | inr moreRedexCases =>
                  cases moreRedexCases with
                  | inl secondCase =>
                      obtain ⟨payload, rightTarget, leftRest, rightRest,
                        contractumChain⟩ := secondCase
                      exact Or.inr (Or.inr (Or.inl ⟨payload, rightTarget,
                        RawStep.parStar.trans leftStep leftRest,
                        RawStep.parStar.trans rightStep rightRest,
                        contractumChain⟩))
                  | inr thirdCase =>
                      obtain ⟨payload, rightTarget, leftRest, rightRest,
                        contractumChain⟩ := thirdCase
                      exact Or.inr (Or.inr (Or.inr ⟨payload, rightTarget,
                        RawStep.parStar.trans leftStep leftRest,
                        RawStep.parStar.trans rightStep rightRest,
                        contractumChain⟩))
      | inr redexCases =>
          cases redexCases with
          | inl firstCase =>
              obtain ⟨payload, rightTarget, middleEq, leftStep,
                rightStep⟩ := firstCase
              cases middleEq
              exact Or.inr (Or.inl ⟨payload, rightTarget,
                RawStep.parStar.trans leftStep (RawStep.parStar.refl _),
                RawStep.parStar.trans rightStep (RawStep.parStar.refl _),
                restChain⟩)
          | inr moreRedexCases =>
              cases moreRedexCases with
              | inl secondCase =>
                  obtain ⟨payload, rightTarget, middleEq, leftStep,
                    rightStep⟩ := secondCase
                  cases middleEq
                  exact Or.inr (Or.inr (Or.inl ⟨payload, rightTarget,
                    RawStep.parStar.trans leftStep
                      (RawStep.parStar.refl _),
                    RawStep.parStar.trans rightStep
                      (RawStep.parStar.refl _),
                    restChain⟩))
              | inr thirdCase =>
                  obtain ⟨payload, rightTarget, middleEq, leftStep,
                    rightStep⟩ := thirdCase
                  cases middleEq
                  exact Or.inr (Or.inr (Or.inr ⟨payload, rightTarget,
                    RawStep.parStar.trans leftStep
                      (RawStep.parStar.refl _),
                    RawStep.parStar.trans rightStep
                      (RawStep.parStar.refl _),
                    restChain⟩))

/-- Binary-left, three-redex eliminator inversion for an exactly wrapped
source. -/
private theorem RawStep.parStar.binary_left_three_redex_elim_inv_helper
    {PayloadFirst PayloadSecond PayloadThird : Type}
    {outerScope leftScope rightScope : Nat}
    (elimWrap :
      RawTerm leftScope → RawTerm rightScope → RawTerm outerScope)
    (firstIntro : PayloadFirst → RawTerm leftScope)
    (secondIntro : PayloadSecond → RawTerm leftScope)
    (thirdIntro : PayloadThird → RawTerm leftScope)
    (firstContractum :
      PayloadFirst → RawTerm rightScope → RawTerm outerScope)
    (secondContractum :
      PayloadSecond → RawTerm rightScope → RawTerm outerScope)
    (thirdContractum :
      PayloadThird → RawTerm rightScope → RawTerm outerScope)
    (parStepInv : ∀ {leftSource rightSource target},
      RawStep.par (elimWrap leftSource rightSource) target →
        (∃ leftTarget rightTarget,
          target = elimWrap leftTarget rightTarget ∧
          RawStep.par leftSource leftTarget ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ payload rightTarget,
          target = firstContractum payload rightTarget ∧
          RawStep.par leftSource (firstIntro payload) ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ payload rightTarget,
          target = secondContractum payload rightTarget ∧
          RawStep.par leftSource (secondIntro payload) ∧
          RawStep.par rightSource rightTarget) ∨
        (∃ payload rightTarget,
          target = thirdContractum payload rightTarget ∧
          RawStep.par leftSource (thirdIntro payload) ∧
          RawStep.par rightSource rightTarget))
    {leftSource : RawTerm leftScope}
    {rightSource : RawTerm rightScope}
    {target : RawTerm outerScope}
    (chain : RawStep.parStar (elimWrap leftSource rightSource) target) :
    (∃ leftTarget rightTarget,
      target = elimWrap leftTarget rightTarget ∧
      RawStep.parStar leftSource leftTarget ∧
      RawStep.parStar rightSource rightTarget) ∨
    (∃ payload rightTarget,
      RawStep.parStar leftSource (firstIntro payload) ∧
      RawStep.parStar rightSource rightTarget ∧
      RawStep.parStar (firstContractum payload rightTarget) target) ∨
    (∃ payload rightTarget,
      RawStep.parStar leftSource (secondIntro payload) ∧
      RawStep.parStar rightSource rightTarget ∧
      RawStep.parStar (secondContractum payload rightTarget) target) ∨
    (∃ payload rightTarget,
      RawStep.parStar leftSource (thirdIntro payload) ∧
      RawStep.parStar rightSource rightTarget ∧
      RawStep.parStar (thirdContractum payload rightTarget) target) :=
  RawStep.parStar.binary_left_three_redex_elim_inv_aux
    elimWrap firstIntro secondIntro thirdIntro firstContractum
    secondContractum thirdContractum parStepInv chain rfl

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

/-- Generalized three-subterm eliminator `parStar` inversion with two
iota/redex branches.

The helper keeps both branch subchains in the redex cases.  Some
eliminators ignore one branch after firing, but retaining the chain
gives a uniform shape that also covers `natRec`, whose successor
contractum mentions both branches. -/
private theorem RawStep.parStar.ternary_two_redex_elim_inv_aux
    {PayloadLeft PayloadRight : Type}
    {scope : Nat}
    (elimWrap :
      RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope)
    (leftIntro : PayloadLeft → RawTerm scope)
    (rightIntro : PayloadRight → RawTerm scope)
    (leftContractum :
      PayloadLeft → RawTerm scope → RawTerm scope → RawTerm scope)
    (rightContractum :
      PayloadRight → RawTerm scope → RawTerm scope → RawTerm scope)
    (parStepInv : ∀ {scrutineeSource firstBranch secondBranch target},
      RawStep.par
        (elimWrap scrutineeSource firstBranch secondBranch) target →
        (∃ scrutineeTarget firstTarget secondTarget,
          target = elimWrap scrutineeTarget firstTarget secondTarget ∧
          RawStep.par scrutineeSource scrutineeTarget ∧
          RawStep.par firstBranch firstTarget ∧
          RawStep.par secondBranch secondTarget) ∨
        (∃ payload firstTarget secondTarget,
          target = leftContractum payload firstTarget secondTarget ∧
          RawStep.par scrutineeSource (leftIntro payload) ∧
          RawStep.par firstBranch firstTarget ∧
          RawStep.par secondBranch secondTarget) ∨
        (∃ payload firstTarget secondTarget,
          target = rightContractum payload firstTarget secondTarget ∧
          RawStep.par scrutineeSource (rightIntro payload) ∧
          RawStep.par firstBranch firstTarget ∧
          RawStep.par secondBranch secondTarget))
    {source target : RawTerm scope}
    (chain : RawStep.parStar source target) :
    ∀ {scrutineeSource firstBranch secondBranch : RawTerm scope},
      source = elimWrap scrutineeSource firstBranch secondBranch →
      (∃ scrutineeTarget firstTarget secondTarget,
        target = elimWrap scrutineeTarget firstTarget secondTarget ∧
        RawStep.parStar scrutineeSource scrutineeTarget ∧
        RawStep.parStar firstBranch firstTarget ∧
        RawStep.parStar secondBranch secondTarget) ∨
      (∃ payload firstTarget secondTarget,
        RawStep.parStar scrutineeSource (leftIntro payload) ∧
        RawStep.parStar firstBranch firstTarget ∧
        RawStep.parStar secondBranch secondTarget ∧
        RawStep.parStar
          (leftContractum payload firstTarget secondTarget) target) ∨
      (∃ payload firstTarget secondTarget,
        RawStep.parStar scrutineeSource (rightIntro payload) ∧
        RawStep.parStar firstBranch firstTarget ∧
        RawStep.parStar secondBranch secondTarget ∧
        RawStep.parStar
          (rightContractum payload firstTarget secondTarget) target) := by
  induction chain with
  | refl _ =>
      intro scrutineeSource firstBranch secondBranch sourceEq
      exact Or.inl ⟨scrutineeSource, firstBranch, secondBranch, sourceEq,
        RawStep.parStar.refl _, RawStep.parStar.refl _,
        RawStep.parStar.refl _⟩
  | trans firstStep restChain restIH =>
      intro scrutineeSource firstBranch secondBranch sourceEq
      subst sourceEq
      cases parStepInv firstStep with
      | inl headCase =>
          obtain ⟨middleScrutinee, middleFirst, middleSecond, middleEq,
            scrutineeStep, firstBranchStep, secondBranchStep⟩ := headCase
          cases restIH middleEq with
          | inl preservedCase =>
              obtain ⟨targetScrutinee, targetFirst, targetSecond, targetEq,
                scrutineeRest, firstRest, secondRest⟩ := preservedCase
              exact Or.inl ⟨targetScrutinee, targetFirst, targetSecond,
                targetEq,
                RawStep.parStar.trans scrutineeStep scrutineeRest,
                RawStep.parStar.trans firstBranchStep firstRest,
                RawStep.parStar.trans secondBranchStep secondRest⟩
          | inr redexCases =>
              cases redexCases with
              | inl leftCase =>
                  obtain ⟨payload, targetFirst, targetSecond,
                    scrutineeRest, firstRest, secondRest,
                    contractumChain⟩ := leftCase
                  exact Or.inr (Or.inl ⟨payload, targetFirst, targetSecond,
                    RawStep.parStar.trans scrutineeStep scrutineeRest,
                    RawStep.parStar.trans firstBranchStep firstRest,
                    RawStep.parStar.trans secondBranchStep secondRest,
                    contractumChain⟩)
              | inr rightCase =>
                  obtain ⟨payload, targetFirst, targetSecond,
                    scrutineeRest, firstRest, secondRest,
                    contractumChain⟩ := rightCase
                  exact Or.inr (Or.inr ⟨payload, targetFirst, targetSecond,
                    RawStep.parStar.trans scrutineeStep scrutineeRest,
                    RawStep.parStar.trans firstBranchStep firstRest,
                    RawStep.parStar.trans secondBranchStep secondRest,
                    contractumChain⟩)
      | inr redexCases =>
          cases redexCases with
          | inl leftCase =>
              obtain ⟨payload, middleFirst, middleSecond, middleEq,
                scrutineeStep, firstBranchStep, secondBranchStep⟩ := leftCase
              cases middleEq
              exact Or.inr (Or.inl ⟨payload, middleFirst, middleSecond,
                RawStep.parStar.trans scrutineeStep
                  (RawStep.parStar.refl _),
                RawStep.parStar.trans firstBranchStep
                  (RawStep.parStar.refl _),
                RawStep.parStar.trans secondBranchStep
                  (RawStep.parStar.refl _),
                restChain⟩)
          | inr rightCase =>
              obtain ⟨payload, middleFirst, middleSecond, middleEq,
                scrutineeStep, firstBranchStep, secondBranchStep⟩ :=
                rightCase
              cases middleEq
              exact Or.inr (Or.inr ⟨payload, middleFirst, middleSecond,
                RawStep.parStar.trans scrutineeStep
                  (RawStep.parStar.refl _),
                RawStep.parStar.trans firstBranchStep
                  (RawStep.parStar.refl _),
                RawStep.parStar.trans secondBranchStep
                  (RawStep.parStar.refl _),
                restChain⟩)

/-- Three-subterm, two-redex eliminator inversion for an exactly wrapped
source. -/
private theorem RawStep.parStar.ternary_two_redex_elim_inv_helper
    {PayloadLeft PayloadRight : Type}
    {scope : Nat}
    (elimWrap :
      RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope)
    (leftIntro : PayloadLeft → RawTerm scope)
    (rightIntro : PayloadRight → RawTerm scope)
    (leftContractum :
      PayloadLeft → RawTerm scope → RawTerm scope → RawTerm scope)
    (rightContractum :
      PayloadRight → RawTerm scope → RawTerm scope → RawTerm scope)
    (parStepInv : ∀ {scrutineeSource firstBranch secondBranch target},
      RawStep.par
        (elimWrap scrutineeSource firstBranch secondBranch) target →
        (∃ scrutineeTarget firstTarget secondTarget,
          target = elimWrap scrutineeTarget firstTarget secondTarget ∧
          RawStep.par scrutineeSource scrutineeTarget ∧
          RawStep.par firstBranch firstTarget ∧
          RawStep.par secondBranch secondTarget) ∨
        (∃ payload firstTarget secondTarget,
          target = leftContractum payload firstTarget secondTarget ∧
          RawStep.par scrutineeSource (leftIntro payload) ∧
          RawStep.par firstBranch firstTarget ∧
          RawStep.par secondBranch secondTarget) ∨
        (∃ payload firstTarget secondTarget,
          target = rightContractum payload firstTarget secondTarget ∧
          RawStep.par scrutineeSource (rightIntro payload) ∧
          RawStep.par firstBranch firstTarget ∧
          RawStep.par secondBranch secondTarget))
    {scrutineeSource firstBranch secondBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (elimWrap scrutineeSource firstBranch secondBranch) target) :
    (∃ scrutineeTarget firstTarget secondTarget,
      target = elimWrap scrutineeTarget firstTarget secondTarget ∧
      RawStep.parStar scrutineeSource scrutineeTarget ∧
      RawStep.parStar firstBranch firstTarget ∧
      RawStep.parStar secondBranch secondTarget) ∨
    (∃ payload firstTarget secondTarget,
      RawStep.parStar scrutineeSource (leftIntro payload) ∧
      RawStep.parStar firstBranch firstTarget ∧
      RawStep.parStar secondBranch secondTarget ∧
      RawStep.parStar
        (leftContractum payload firstTarget secondTarget) target) ∨
    (∃ payload firstTarget secondTarget,
      RawStep.parStar scrutineeSource (rightIntro payload) ∧
      RawStep.parStar firstBranch firstTarget ∧
      RawStep.parStar secondBranch secondTarget ∧
      RawStep.parStar
        (rightContractum payload firstTarget secondTarget) target) :=
  RawStep.parStar.ternary_two_redex_elim_inv_aux
    elimWrap leftIntro rightIntro leftContractum rightContractum
    parStepInv chain rfl

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

/-- `RawStep.parStar (boolElim scrutinee thenBranch elseBranch) target`
preserves the eliminator head or fires the true/false iota branch after
the scrutinee develops to the corresponding boolean. -/
theorem RawStep.parStar.boolElim_inv {scope : Nat}
    {scrutinee thenBranch elseBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.boolElim scrutinee thenBranch elseBranch) target) :
    (∃ scrutineeTarget thenTarget elseTarget,
      target = RawTerm.boolElim scrutineeTarget thenTarget elseTarget ∧
      RawStep.parStar scrutinee scrutineeTarget ∧
      RawStep.parStar thenBranch thenTarget ∧
      RawStep.parStar elseBranch elseTarget) ∨
    (∃ thenTarget elseTarget,
      RawStep.parStar scrutinee RawTerm.boolTrue ∧
      RawStep.parStar thenBranch thenTarget ∧
      RawStep.parStar elseBranch elseTarget ∧
      RawStep.parStar thenTarget target) ∨
    (∃ thenTarget elseTarget,
      RawStep.parStar scrutinee RawTerm.boolFalse ∧
      RawStep.parStar thenBranch thenTarget ∧
      RawStep.parStar elseBranch elseTarget ∧
      RawStep.parStar elseTarget target) := by
  cases RawStep.parStar.ternary_two_redex_elim_inv_helper
      RawTerm.boolElim
      (fun (_ : PUnit) => RawTerm.boolTrue)
      (fun (_ : PUnit) => RawTerm.boolFalse)
      (fun _ thenTarget _ => thenTarget)
      (fun _ _ elseTarget => elseTarget)
      (fun step => by
        cases RawStep.par.boolElim_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl trueCase =>
                obtain ⟨thenTarget, targetEq, scrutineeStep,
                  thenStep⟩ := trueCase
                exact Or.inr (Or.inl ⟨PUnit.unit, thenTarget, _,
                  targetEq, scrutineeStep, thenStep, RawStep.par.refl _⟩)
            | inr falseCase =>
                obtain ⟨elseTarget, targetEq, scrutineeStep,
                  elseStep⟩ := falseCase
                exact Or.inr (Or.inr ⟨PUnit.unit, _, elseTarget,
                  targetEq, scrutineeStep, RawStep.par.refl _, elseStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl trueCase =>
          obtain ⟨_, thenTarget, elseTarget, scrutineeChain,
            thenChain, elseChain, targetChain⟩ := trueCase
          exact Or.inr (Or.inl ⟨thenTarget, elseTarget, scrutineeChain,
            thenChain, elseChain, targetChain⟩)
      | inr falseCase =>
          obtain ⟨_, thenTarget, elseTarget, scrutineeChain,
            thenChain, elseChain, targetChain⟩ := falseCase
          exact Or.inr (Or.inr ⟨thenTarget, elseTarget, scrutineeChain,
            thenChain, elseChain, targetChain⟩)

/-- `RawStep.parStar (natElim scrutinee zeroBranch succBranch) target`
preserves the eliminator head or fires the zero/successor iota branch
after the scrutinee develops to the corresponding natural constructor. -/
theorem RawStep.parStar.natElim_inv {scope : Nat}
    {scrutinee zeroBranch succBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.natElim scrutinee zeroBranch succBranch) target) :
    (∃ scrutineeTarget zeroTarget succTarget,
      target = RawTerm.natElim scrutineeTarget zeroTarget succTarget ∧
      RawStep.parStar scrutinee scrutineeTarget ∧
      RawStep.parStar zeroBranch zeroTarget ∧
      RawStep.parStar succBranch succTarget) ∨
    (∃ zeroTarget succTarget,
      RawStep.parStar scrutinee RawTerm.natZero ∧
      RawStep.parStar zeroBranch zeroTarget ∧
      RawStep.parStar succBranch succTarget ∧
      RawStep.parStar zeroTarget target) ∨
    (∃ predRaw zeroTarget succTarget,
      RawStep.parStar scrutinee (RawTerm.natSucc predRaw) ∧
      RawStep.parStar zeroBranch zeroTarget ∧
      RawStep.parStar succBranch succTarget ∧
      RawStep.parStar (RawTerm.app succTarget predRaw) target) := by
  cases RawStep.parStar.ternary_two_redex_elim_inv_helper
      RawTerm.natElim
      (fun (_ : PUnit) => RawTerm.natZero)
      RawTerm.natSucc
      (fun _ zeroTarget _ => zeroTarget)
      (fun predRaw _ succTarget => RawTerm.app succTarget predRaw)
      (fun step => by
        cases RawStep.par.natElim_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl zeroCase =>
                obtain ⟨zeroTarget, targetEq, scrutineeStep,
                  zeroStep⟩ := zeroCase
                exact Or.inr (Or.inl ⟨PUnit.unit, zeroTarget, _,
                  targetEq, scrutineeStep, zeroStep, RawStep.par.refl _⟩)
            | inr succCase =>
                obtain ⟨predRaw, succTarget, targetEq, scrutineeStep,
                  succStep⟩ := succCase
                exact Or.inr (Or.inr ⟨predRaw, _, succTarget,
                  targetEq, scrutineeStep, RawStep.par.refl _, succStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl zeroCase =>
          obtain ⟨_, zeroTarget, succTarget, scrutineeChain,
            zeroChain, succChain, targetChain⟩ := zeroCase
          exact Or.inr (Or.inl ⟨zeroTarget, succTarget, scrutineeChain,
            zeroChain, succChain, targetChain⟩)
      | inr succCase =>
          obtain ⟨predRaw, zeroTarget, succTarget, scrutineeChain,
            zeroChain, succChain, targetChain⟩ := succCase
          exact Or.inr (Or.inr ⟨predRaw, zeroTarget, succTarget,
            scrutineeChain, zeroChain, succChain, targetChain⟩)

/-- `RawStep.parStar (natRec scrutinee zeroBranch succBranch) target`
preserves the recursor head or fires zero/successor iota after the
scrutinee develops to the corresponding natural constructor. -/
theorem RawStep.parStar.natRec_inv {scope : Nat}
    {scrutinee zeroBranch succBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.natRec scrutinee zeroBranch succBranch) target) :
    (∃ scrutineeTarget zeroTarget succTarget,
      target = RawTerm.natRec scrutineeTarget zeroTarget succTarget ∧
      RawStep.parStar scrutinee scrutineeTarget ∧
      RawStep.parStar zeroBranch zeroTarget ∧
      RawStep.parStar succBranch succTarget) ∨
    (∃ zeroTarget succTarget,
      RawStep.parStar scrutinee RawTerm.natZero ∧
      RawStep.parStar zeroBranch zeroTarget ∧
      RawStep.parStar succBranch succTarget ∧
      RawStep.parStar zeroTarget target) ∨
    (∃ predRaw zeroTarget succTarget,
      RawStep.parStar scrutinee (RawTerm.natSucc predRaw) ∧
      RawStep.parStar zeroBranch zeroTarget ∧
      RawStep.parStar succBranch succTarget ∧
      RawStep.parStar
        (RawTerm.app (RawTerm.app succTarget predRaw)
          (RawTerm.natRec predRaw zeroTarget succTarget)) target) := by
  cases RawStep.parStar.ternary_two_redex_elim_inv_helper
      RawTerm.natRec
      (fun (_ : PUnit) => RawTerm.natZero)
      RawTerm.natSucc
      (fun _ zeroTarget _ => zeroTarget)
      (fun predRaw zeroTarget succTarget =>
        RawTerm.app (RawTerm.app succTarget predRaw)
          (RawTerm.natRec predRaw zeroTarget succTarget))
      (fun step => by
        cases RawStep.par.natRec_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl zeroCase =>
                obtain ⟨zeroTarget, targetEq, scrutineeStep,
                  zeroStep⟩ := zeroCase
                exact Or.inr (Or.inl ⟨PUnit.unit, zeroTarget, _,
                  targetEq, scrutineeStep, zeroStep, RawStep.par.refl _⟩)
            | inr succCase =>
                obtain ⟨predRaw, zeroTarget, succTarget, targetEq,
                  scrutineeStep, zeroStep, succStep⟩ := succCase
                exact Or.inr (Or.inr ⟨predRaw, zeroTarget, succTarget,
                  targetEq, scrutineeStep, zeroStep, succStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl zeroCase =>
          obtain ⟨_, zeroTarget, succTarget, scrutineeChain,
            zeroChain, succChain, targetChain⟩ := zeroCase
          exact Or.inr (Or.inl ⟨zeroTarget, succTarget, scrutineeChain,
            zeroChain, succChain, targetChain⟩)
      | inr succCase =>
          obtain ⟨predRaw, zeroTarget, succTarget, scrutineeChain,
            zeroChain, succChain, targetChain⟩ := succCase
          exact Or.inr (Or.inr ⟨predRaw, zeroTarget, succTarget,
            scrutineeChain, zeroChain, succChain, targetChain⟩)

/-- `RawStep.parStar (listElim scrutinee nilBranch consBranch) target`
preserves the eliminator head or fires nil/cons iota after the
scrutinee develops to the corresponding list constructor. -/
theorem RawStep.parStar.listElim_inv {scope : Nat}
    {scrutinee nilBranch consBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.listElim scrutinee nilBranch consBranch) target) :
    (∃ scrutineeTarget nilTarget consTarget,
      target = RawTerm.listElim scrutineeTarget nilTarget consTarget ∧
      RawStep.parStar scrutinee scrutineeTarget ∧
      RawStep.parStar nilBranch nilTarget ∧
      RawStep.parStar consBranch consTarget) ∨
    (∃ nilTarget consTarget,
      RawStep.parStar scrutinee RawTerm.listNil ∧
      RawStep.parStar nilBranch nilTarget ∧
      RawStep.parStar consBranch consTarget ∧
      RawStep.parStar nilTarget target) ∨
    (∃ headRaw tailRaw nilTarget consTarget,
      RawStep.parStar scrutinee (RawTerm.listCons headRaw tailRaw) ∧
      RawStep.parStar nilBranch nilTarget ∧
      RawStep.parStar consBranch consTarget ∧
      RawStep.parStar
        (RawTerm.app (RawTerm.app consTarget headRaw) tailRaw) target) := by
  cases RawStep.parStar.ternary_two_redex_elim_inv_helper
      RawTerm.listElim
      (fun (_ : PUnit) => RawTerm.listNil)
      (fun (payload : RawTerm scope × RawTerm scope) =>
        RawTerm.listCons payload.1 payload.2)
      (fun _ nilTarget _ => nilTarget)
      (fun (payload : RawTerm scope × RawTerm scope) _ consTarget =>
        RawTerm.app (RawTerm.app consTarget payload.1) payload.2)
      (fun step => by
        cases RawStep.par.listElim_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl nilCase =>
                obtain ⟨nilTarget, targetEq, scrutineeStep,
                  nilStep⟩ := nilCase
                exact Or.inr (Or.inl ⟨PUnit.unit, nilTarget, _,
                  targetEq, scrutineeStep, nilStep, RawStep.par.refl _⟩)
            | inr consCase =>
                obtain ⟨headRaw, tailRaw, consTarget, targetEq,
                  scrutineeStep, consStep⟩ := consCase
                exact Or.inr (Or.inr
                  ⟨(headRaw, tailRaw), _, consTarget, targetEq,
                    scrutineeStep, RawStep.par.refl _, consStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl nilCase =>
          obtain ⟨_, nilTarget, consTarget, scrutineeChain,
            nilChain, consChain, targetChain⟩ := nilCase
          exact Or.inr (Or.inl ⟨nilTarget, consTarget, scrutineeChain,
            nilChain, consChain, targetChain⟩)
      | inr consCase =>
          obtain ⟨payload, nilTarget, consTarget, scrutineeChain,
            nilChain, consChain, targetChain⟩ := consCase
          exact Or.inr (Or.inr ⟨payload.1, payload.2, nilTarget,
            consTarget, scrutineeChain, nilChain, consChain,
            targetChain⟩)

/-- `RawStep.parStar (optionMatch scrutinee noneBranch someBranch) target`
preserves the match head or fires none/some iota after the scrutinee
develops to the corresponding option constructor. -/
theorem RawStep.parStar.optionMatch_inv {scope : Nat}
    {scrutinee noneBranch someBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.optionMatch scrutinee noneBranch someBranch) target) :
    (∃ scrutineeTarget noneTarget someTarget,
      target = RawTerm.optionMatch scrutineeTarget noneTarget someTarget ∧
      RawStep.parStar scrutinee scrutineeTarget ∧
      RawStep.parStar noneBranch noneTarget ∧
      RawStep.parStar someBranch someTarget) ∨
    (∃ noneTarget someTarget,
      RawStep.parStar scrutinee RawTerm.optionNone ∧
      RawStep.parStar noneBranch noneTarget ∧
      RawStep.parStar someBranch someTarget ∧
      RawStep.parStar noneTarget target) ∨
    (∃ valueRaw noneTarget someTarget,
      RawStep.parStar scrutinee (RawTerm.optionSome valueRaw) ∧
      RawStep.parStar noneBranch noneTarget ∧
      RawStep.parStar someBranch someTarget ∧
      RawStep.parStar (RawTerm.app someTarget valueRaw) target) := by
  cases RawStep.parStar.ternary_two_redex_elim_inv_helper
      RawTerm.optionMatch
      (fun (_ : PUnit) => RawTerm.optionNone)
      RawTerm.optionSome
      (fun _ noneTarget _ => noneTarget)
      (fun valueRaw _ someTarget => RawTerm.app someTarget valueRaw)
      (fun step => by
        cases RawStep.par.optionMatch_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl noneCase =>
                obtain ⟨noneTarget, targetEq, scrutineeStep,
                  noneStep⟩ := noneCase
                exact Or.inr (Or.inl ⟨PUnit.unit, noneTarget, _,
                  targetEq, scrutineeStep, noneStep, RawStep.par.refl _⟩)
            | inr someCase =>
                obtain ⟨valueRaw, someTarget, targetEq,
                  scrutineeStep, someStep⟩ := someCase
                exact Or.inr (Or.inr ⟨valueRaw, _, someTarget,
                  targetEq, scrutineeStep, RawStep.par.refl _, someStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl noneCase =>
          obtain ⟨_, noneTarget, someTarget, scrutineeChain,
            noneChain, someChain, targetChain⟩ := noneCase
          exact Or.inr (Or.inl ⟨noneTarget, someTarget, scrutineeChain,
            noneChain, someChain, targetChain⟩)
      | inr someCase =>
          obtain ⟨valueRaw, noneTarget, someTarget, scrutineeChain,
            noneChain, someChain, targetChain⟩ := someCase
          exact Or.inr (Or.inr ⟨valueRaw, noneTarget, someTarget,
            scrutineeChain, noneChain, someChain, targetChain⟩)

/-- `RawStep.parStar (eitherMatch scrutinee leftBranch rightBranch) target`
preserves the match head or fires inl/inr iota after the scrutinee
develops to the corresponding either constructor. -/
theorem RawStep.parStar.eitherMatch_inv {scope : Nat}
    {scrutinee leftBranch rightBranch target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch) target) :
    (∃ scrutineeTarget leftTarget rightTarget,
      target = RawTerm.eitherMatch scrutineeTarget leftTarget rightTarget ∧
      RawStep.parStar scrutinee scrutineeTarget ∧
      RawStep.parStar leftBranch leftTarget ∧
      RawStep.parStar rightBranch rightTarget) ∨
    (∃ valueRaw leftTarget rightTarget,
      RawStep.parStar scrutinee (RawTerm.eitherInl valueRaw) ∧
      RawStep.parStar leftBranch leftTarget ∧
      RawStep.parStar rightBranch rightTarget ∧
      RawStep.parStar (RawTerm.app leftTarget valueRaw) target) ∨
    (∃ valueRaw leftTarget rightTarget,
      RawStep.parStar scrutinee (RawTerm.eitherInr valueRaw) ∧
      RawStep.parStar leftBranch leftTarget ∧
      RawStep.parStar rightBranch rightTarget ∧
      RawStep.parStar (RawTerm.app rightTarget valueRaw) target) := by
  cases RawStep.parStar.ternary_two_redex_elim_inv_helper
      RawTerm.eitherMatch
      RawTerm.eitherInl
      RawTerm.eitherInr
      (fun valueRaw leftTarget _ => RawTerm.app leftTarget valueRaw)
      (fun valueRaw _ rightTarget => RawTerm.app rightTarget valueRaw)
      (fun step => by
        cases RawStep.par.eitherMatch_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl leftCase =>
                obtain ⟨valueRaw, leftTarget, targetEq, scrutineeStep,
                  leftStep⟩ := leftCase
                exact Or.inr (Or.inl ⟨valueRaw, leftTarget, _,
                  targetEq, scrutineeStep, leftStep, RawStep.par.refl _⟩)
            | inr rightCase =>
                obtain ⟨valueRaw, rightTarget, targetEq, scrutineeStep,
                  rightStep⟩ := rightCase
                exact Or.inr (Or.inr ⟨valueRaw, _, rightTarget,
                  targetEq, scrutineeStep, RawStep.par.refl _, rightStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl leftCase =>
          obtain ⟨valueRaw, leftTarget, rightTarget, scrutineeChain,
            leftChain, rightChain, targetChain⟩ := leftCase
          exact Or.inr (Or.inl ⟨valueRaw, leftTarget, rightTarget,
            scrutineeChain, leftChain, rightChain, targetChain⟩)
      | inr rightCase =>
          obtain ⟨valueRaw, leftTarget, rightTarget, scrutineeChain,
            leftChain, rightChain, targetChain⟩ := rightCase
          exact Or.inr (Or.inr ⟨valueRaw, leftTarget, rightTarget,
            scrutineeChain, leftChain, rightChain, targetChain⟩)

/-- `RawStep.parStar (app function argument) target` either preserves the
`app` head or fires function β after the function develops to a lambda. -/
theorem RawStep.parStar.app_inv {scope : Nat}
    {functionTerm argumentTerm target : RawTerm scope}
    (chain :
      RawStep.parStar
        (RawTerm.app functionTerm argumentTerm) target) :
    (∃ functionTarget argumentTarget,
      target = RawTerm.app functionTarget argumentTarget ∧
      RawStep.parStar functionTerm functionTarget ∧
      RawStep.parStar argumentTerm argumentTarget) ∨
    (∃ bodyTarget argumentTarget,
      RawStep.parStar functionTerm (RawTerm.lam bodyTarget) ∧
      RawStep.parStar argumentTerm argumentTarget ∧
      RawStep.parStar (bodyTarget.subst0 argumentTarget) target) :=
  RawStep.parStar.binary_left_intro_elim_inv_helper RawTerm.app
    RawTerm.lam (fun bodyTarget argumentTarget =>
      bodyTarget.subst0 argumentTarget)
    RawStep.par.app_inv chain

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

/-- `RawStep.parStar (fst pairTerm) target` either preserves the `fst`
head or fires pair β after the pair term develops to a pair. -/
theorem RawStep.parStar.fst_inv {scope : Nat}
    {pairTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.fst pairTerm) target) :
    (∃ pairTarget,
      target = RawTerm.fst pairTarget ∧
      RawStep.parStar pairTerm pairTarget) ∨
    (∃ firstTarget secondTarget,
      RawStep.parStar pairTerm (RawTerm.pair firstTarget secondTarget) ∧
      RawStep.parStar firstTarget target) :=
  RawStep.parStar.binary_intro_elim_inv_helper RawTerm.fst
    RawTerm.pair (fun firstTarget _ => firstTarget)
    RawStep.par.fst_inv chain

/-- `RawStep.parStar (snd pairTerm) target` either preserves the `snd`
head or fires pair β after the pair term develops to a pair. -/
theorem RawStep.parStar.snd_inv {scope : Nat}
    {pairTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.snd pairTerm) target) :
    (∃ pairTarget,
      target = RawTerm.snd pairTarget ∧
      RawStep.parStar pairTerm pairTarget) ∨
    (∃ firstTarget secondTarget,
      RawStep.parStar pairTerm (RawTerm.pair firstTarget secondTarget) ∧
      RawStep.parStar secondTarget target) :=
  RawStep.parStar.binary_intro_elim_inv_helper RawTerm.snd
    RawTerm.pair (fun _ secondTarget => secondTarget)
    RawStep.par.snd_inv chain

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

/-- `RawStep.parStar (idJ base witness) target` either preserves the `idJ`
head or fires identity ι after the witness develops to reflexivity. -/
theorem RawStep.parStar.idJ_inv {scope : Nat}
    {baseCase witness target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.idJ baseCase witness) target) :
    (∃ baseTarget witnessTarget,
      target = RawTerm.idJ baseTarget witnessTarget ∧
      RawStep.parStar baseCase baseTarget ∧
      RawStep.parStar witness witnessTarget) ∨
    (∃ witnessTarget baseTarget,
      RawStep.parStar witness (RawTerm.refl witnessTarget) ∧
      RawStep.parStar baseCase baseTarget ∧
      RawStep.parStar baseTarget target) := by
  cases RawStep.parStar.binary_left_intro_elim_inv_helper
      (fun witnessTerm baseTerm => RawTerm.idJ baseTerm witnessTerm)
      RawTerm.refl (fun _ baseTarget => baseTarget)
      (fun step => by
        cases RawStep.par.idJ_inv step with
        | inl headCase =>
            obtain ⟨baseTarget, witnessTarget, targetEq, baseStep,
              witnessStep⟩ := headCase
            exact Or.inl ⟨witnessTarget, baseTarget, targetEq,
              witnessStep, baseStep⟩
        | inr betaCase =>
            obtain ⟨witnessTarget, baseTarget, targetEq, witnessStep,
              baseStep⟩ := betaCase
            exact Or.inr ⟨witnessTarget, baseTarget, targetEq,
              witnessStep, baseStep⟩)
      chain with
  | inl preservedCase =>
      obtain ⟨witnessTarget, baseTarget, targetEq, witnessChain,
        baseChain⟩ := preservedCase
      exact Or.inl ⟨baseTarget, witnessTarget, targetEq, baseChain,
        witnessChain⟩
  | inr firedCase =>
      obtain ⟨witnessTarget, baseTarget, witnessChain, baseChain,
        targetChain⟩ := firedCase
      exact Or.inr ⟨witnessTarget, baseTarget, witnessChain, baseChain,
        targetChain⟩

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

/-- `RawStep.parStar (idToEquiv proofSource) target` either preserves
the `idToEquiv` head, fires the reflexivity contractum after the proof
develops to `refl`, or fires the composition contractum after the proof
develops to `oeqTrans`. -/
theorem RawStep.parStar.idToEquiv_inv {scope : Nat}
    {proofSource target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.idToEquiv proofSource) target) :
    (∃ proofTarget,
      target = RawTerm.idToEquiv proofTarget ∧
      RawStep.parStar proofSource proofTarget) ∨
    (∃ witnessTarget,
      RawStep.parStar proofSource (RawTerm.refl witnessTarget) ∧
      RawStep.parStar
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _)))))
        target) ∨
    (∃ firstTarget secondTarget,
      RawStep.parStar proofSource
        (RawTerm.oeqTrans firstTarget secondTarget) ∧
      RawStep.parStar
        (RawTerm.equivCompose
          (RawTerm.idToEquiv firstTarget)
          (RawTerm.idToEquiv secondTarget))
        target) := by
  cases RawStep.parStar.unary_two_redex_elim_inv_helper
      RawTerm.idToEquiv
      RawTerm.refl
      (fun (payload : RawTerm scope × RawTerm scope) =>
        RawTerm.oeqTrans payload.1 payload.2)
      (fun _ =>
        RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _)))))
      (fun (payload : RawTerm scope × RawTerm scope) =>
        RawTerm.equivCompose
          (RawTerm.idToEquiv payload.1)
          (RawTerm.idToEquiv payload.2))
      (fun step => by
        cases RawStep.par.idToEquiv_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl reflShallow =>
                obtain ⟨witnessSource, witnessTarget, proofEq,
                  targetEq, witnessStep⟩ := reflShallow
                cases proofEq
                exact Or.inr (Or.inl ⟨witnessTarget, targetEq,
                  RawStep.par.reflCong witnessStep⟩)
            | inr moreRedexCases =>
                cases moreRedexCases with
                | inl reflDeep =>
                    obtain ⟨witnessTarget, targetEq, proofStep⟩ :=
                      reflDeep
                    exact Or.inr (Or.inl ⟨witnessTarget, targetEq,
                      proofStep⟩)
                | inr composeCases =>
                    cases composeCases with
                    | inl composeShallow =>
                        obtain ⟨firstSource, secondSource, firstTarget,
                          secondTarget, proofEq, targetEq, firstStep,
                          secondStep⟩ := composeShallow
                        cases proofEq
                        exact Or.inr (Or.inr
                          ⟨(firstTarget, secondTarget), targetEq,
                            RawStep.par.oeqTransCong firstStep
                              secondStep⟩)
                    | inr composeDeep =>
                        obtain ⟨firstTarget, secondTarget, targetEq,
                          proofStep⟩ := composeDeep
                        exact Or.inr (Or.inr
                          ⟨(firstTarget, secondTarget), targetEq,
                            proofStep⟩))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl reflCase =>
          obtain ⟨witnessTarget, proofChain, targetChain⟩ := reflCase
          exact Or.inr (Or.inl ⟨witnessTarget, proofChain,
            targetChain⟩)
      | inr composeCase =>
          obtain ⟨payload, proofChain, targetChain⟩ := composeCase
          exact Or.inr (Or.inr ⟨payload.1, payload.2, proofChain,
            targetChain⟩)

/-- `RawStep.parStar (equivApply equivalence argument) target` either
preserves the `equivApply` head or fires the ua-refl round-trip β rule
after the equivalence develops to `uaToEquiv (oeqRefl witness)`. -/
theorem RawStep.parStar.equivApply_inv {scope : Nat}
    {equivRaw argRaw target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.equivApply equivRaw argRaw) target) :
    (∃ equivTarget argTarget,
      target = RawTerm.equivApply equivTarget argTarget ∧
      RawStep.parStar equivRaw equivTarget ∧
      RawStep.parStar argRaw argTarget) ∨
    (∃ witnessTarget sourceTarget,
      RawStep.parStar equivRaw
        (RawTerm.uaToEquiv (RawTerm.oeqRefl witnessTarget)) ∧
      RawStep.parStar argRaw sourceTarget ∧
      RawStep.parStar sourceTarget target) := by
  exact RawStep.parStar.binary_left_intro_elim_inv_helper
    RawTerm.equivApply
    (fun witnessTarget =>
      RawTerm.uaToEquiv (RawTerm.oeqRefl witnessTarget))
    (fun _ sourceTarget => sourceTarget)
    (fun step => by
      cases RawStep.par.equivApply_inv step with
      | inl headCase =>
          exact Or.inl headCase
      | inr redexCases =>
          cases redexCases with
          | inl shallowCase =>
              obtain ⟨witnessSource, witnessTarget, sourceTarget,
                equivEq, targetEq, witnessStep, sourceStep⟩ :=
                shallowCase
              cases equivEq
              exact Or.inr ⟨witnessTarget, sourceTarget, targetEq,
                RawStep.par.uaToEquivCong
                  (RawStep.par.oeqReflCong witnessStep),
                sourceStep⟩
          | inr deepCase =>
              obtain ⟨witnessTarget, sourceTarget, targetEq, equivStep,
                sourceStep⟩ := deepCase
              exact Or.inr ⟨witnessTarget, sourceTarget, targetEq,
                equivStep, sourceStep⟩)
    chain

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

/-- `RawStep.parStar (pathApp path interval) target` either preserves the
`pathApp` head or fires path β after the path develops to a path lambda. -/
theorem RawStep.parStar.pathApp_inv {scope : Nat}
    {pathTerm intervalArg target : RawTerm scope}
    (chain :
      RawStep.parStar (RawTerm.pathApp pathTerm intervalArg) target) :
    (∃ pathTarget intervalTarget,
      target = RawTerm.pathApp pathTarget intervalTarget ∧
      RawStep.parStar pathTerm pathTarget ∧
      RawStep.parStar intervalArg intervalTarget) ∨
    (∃ bodyTarget intervalTarget,
      RawStep.parStar pathTerm (RawTerm.pathLam bodyTarget) ∧
      RawStep.parStar intervalArg intervalTarget ∧
      RawStep.parStar (bodyTarget.subst0 intervalTarget) target) :=
  RawStep.parStar.binary_left_intro_elim_inv_helper RawTerm.pathApp
    RawTerm.pathLam (fun bodyTarget intervalTarget =>
      bodyTarget.subst0 intervalTarget)
    RawStep.par.pathApp_inv chain

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

/-- `RawStep.parStar (glueElim gluedValue) target` either preserves the
`glueElim` head or fires Glue β after the glued value develops to
`glueIntro`. -/
theorem RawStep.parStar.glueElim_inv {scope : Nat}
    {gluedValue target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.glueElim gluedValue) target) :
    (∃ gluedTarget,
      target = RawTerm.glueElim gluedTarget ∧
      RawStep.parStar gluedValue gluedTarget) ∨
    (∃ baseTarget partialTarget,
      RawStep.parStar gluedValue
        (RawTerm.glueIntro baseTarget partialTarget) ∧
      RawStep.parStar baseTarget target) :=
  RawStep.parStar.binary_intro_elim_inv_helper RawTerm.glueElim
    RawTerm.glueIntro (fun baseTarget _ => baseTarget)
    RawStep.par.glueElim_inv chain

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

/-- `RawStep.parStar (idStrictRec base witness) target` either preserves
the strict recursor head or fires strict-identity ι after the witness
develops to strict reflexivity. -/
theorem RawStep.parStar.idStrictRec_inv {scope : Nat}
    {baseCase witness target : RawTerm scope}
    (chain : RawStep.parStar
      (RawTerm.idStrictRec baseCase witness) target) :
    (∃ baseTarget witnessTarget,
      target = RawTerm.idStrictRec baseTarget witnessTarget ∧
      RawStep.parStar baseCase baseTarget ∧
      RawStep.parStar witness witnessTarget) ∨
    (∃ witnessTarget baseTarget,
      RawStep.parStar witness (RawTerm.idStrictRefl witnessTarget) ∧
      RawStep.parStar baseCase baseTarget ∧
      RawStep.parStar baseTarget target) := by
  cases RawStep.parStar.binary_left_intro_elim_inv_helper
      (fun witnessTerm baseTerm =>
        RawTerm.idStrictRec baseTerm witnessTerm)
      RawTerm.idStrictRefl (fun _ baseTarget => baseTarget)
      (fun step => by
        cases RawStep.par.idStrictRec_inv step with
        | inl headCase =>
            obtain ⟨baseTarget, witnessTarget, targetEq, baseStep,
              witnessStep⟩ := headCase
            exact Or.inl ⟨witnessTarget, baseTarget, targetEq,
              witnessStep, baseStep⟩
        | inr betaCase =>
            obtain ⟨witnessTarget, baseTarget, targetEq, witnessStep,
              baseStep⟩ := betaCase
            exact Or.inr ⟨witnessTarget, baseTarget, targetEq,
              witnessStep, baseStep⟩)
      chain with
  | inl preservedCase =>
      obtain ⟨witnessTarget, baseTarget, targetEq, witnessChain,
        baseChain⟩ := preservedCase
      exact Or.inl ⟨baseTarget, witnessTarget, targetEq, baseChain,
        witnessChain⟩
  | inr firedCase =>
      obtain ⟨witnessTarget, baseTarget, witnessChain, baseChain,
        targetChain⟩ := firedCase
      exact Or.inr ⟨witnessTarget, baseTarget, witnessChain, baseChain,
        targetChain⟩

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

/-- `RawStep.parStar (transp path source) target` either preserves the
`transp` head, fires constant-path transport, fires univalence
transport, or distributes over path composition after the path develops
to the corresponding raw head. -/
theorem RawStep.parStar.transp_inv {scope : Nat}
    {pathTerm sourceTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.transp pathTerm sourceTerm) target) :
    (∃ pathTarget sourceTarget,
      target = RawTerm.transp pathTarget sourceTarget ∧
      RawStep.parStar pathTerm pathTarget ∧
      RawStep.parStar sourceTerm sourceTarget) ∨
    (∃ (typeRawTarget : RawTerm scope) (sourceTarget : RawTerm scope),
      RawStep.parStar pathTerm (RawTerm.pathLam typeRawTarget.weaken) ∧
      RawStep.parStar sourceTerm sourceTarget ∧
      RawStep.parStar sourceTarget target) ∨
    (∃ proofRawTarget sourceTarget,
      RawStep.parStar pathTerm (RawTerm.uaToEquiv proofRawTarget) ∧
      RawStep.parStar sourceTerm sourceTarget ∧
      RawStep.parStar
        (RawTerm.equivApply (RawTerm.uaToEquiv proofRawTarget)
          sourceTarget)
        target) ∨
    (∃ leftRawTarget rightRawTarget sourceTarget,
      RawStep.parStar pathTerm
        (RawTerm.pathCompose leftRawTarget rightRawTarget) ∧
      RawStep.parStar sourceTerm sourceTarget ∧
      RawStep.parStar
        (RawTerm.transp rightRawTarget
          (RawTerm.transp leftRawTarget sourceTarget))
        target) := by
  cases RawStep.parStar.binary_left_three_redex_elim_inv_helper
      RawTerm.transp
      (fun (typeRawTarget : RawTerm scope) =>
        RawTerm.pathLam typeRawTarget.weaken)
      RawTerm.uaToEquiv
      (fun (payload : RawTerm scope × RawTerm scope) =>
        RawTerm.pathCompose payload.1 payload.2)
      (fun _ sourceTarget => sourceTarget)
      (fun proofRawTarget sourceTarget =>
        RawTerm.equivApply (RawTerm.uaToEquiv proofRawTarget)
          sourceTarget)
      (fun (payload : RawTerm scope × RawTerm scope) sourceTarget =>
        RawTerm.transp payload.2
          (RawTerm.transp payload.1 sourceTarget))
      (fun step => by
        cases RawStep.par.transp_inv step with
        | inl headCase =>
            exact Or.inl headCase
        | inr redexCases =>
            cases redexCases with
            | inl reflShallow =>
                obtain ⟨typeRawSource, sourceTarget, pathEq, targetEq,
                  sourceStep⟩ := reflShallow
                cases pathEq
                exact Or.inr (Or.inl ⟨typeRawSource, sourceTarget,
                  targetEq, RawStep.par.refl _, sourceStep⟩)
            | inr moreRedexCases =>
                cases moreRedexCases with
                | inl reflDeep =>
                    obtain ⟨typeRawTarget, sourceTarget, targetEq,
                      pathStep, sourceStep⟩ := reflDeep
                    exact Or.inr (Or.inl ⟨typeRawTarget, sourceTarget,
                      targetEq, pathStep, sourceStep⟩)
                | inr moreRedexCases =>
                    cases moreRedexCases with
                    | inl uaShallow =>
                        obtain ⟨proofRawSource, proofRawTarget,
                          sourceTarget, pathEq, targetEq, proofStep,
                          sourceStep⟩ := uaShallow
                        cases pathEq
                        exact Or.inr (Or.inr (Or.inl
                          ⟨proofRawTarget, sourceTarget, targetEq,
                            RawStep.par.uaToEquivCong proofStep,
                            sourceStep⟩))
                    | inr moreRedexCases =>
                        cases moreRedexCases with
                        | inl uaDeep =>
                            obtain ⟨proofRawTarget, sourceTarget,
                              targetEq, pathStep, sourceStep⟩ := uaDeep
                            exact Or.inr (Or.inr (Or.inl
                              ⟨proofRawTarget, sourceTarget, targetEq,
                                pathStep, sourceStep⟩))
                        | inr moreRedexCases =>
                            cases moreRedexCases with
                            | inl composeShallow =>
                                obtain ⟨leftRawSource, leftRawTarget,
                                  rightRawSource, rightRawTarget,
                                  sourceTarget, pathEq, targetEq, leftStep,
                                  rightStep, sourceStep⟩ := composeShallow
                                cases pathEq
                                exact Or.inr (Or.inr (Or.inr
                                  ⟨(leftRawTarget, rightRawTarget),
                                    sourceTarget, targetEq,
                                    RawStep.par.pathComposeCong leftStep
                                      rightStep,
                                    sourceStep⟩))
                            | inr composeDeep =>
                                obtain ⟨leftRawTarget, rightRawTarget,
                                  sourceTarget, targetEq, pathStep,
                                  sourceStep⟩ := composeDeep
                                exact Or.inr (Or.inr (Or.inr
                                  ⟨(leftRawTarget, rightRawTarget),
                                    sourceTarget, targetEq, pathStep,
                                    sourceStep⟩)))
      chain with
  | inl preservedCase =>
      exact Or.inl preservedCase
  | inr redexCases =>
      cases redexCases with
      | inl reflCase =>
          obtain ⟨typeRawTarget, sourceTarget, pathChain, sourceChain,
            targetChain⟩ := reflCase
          exact Or.inr (Or.inl ⟨typeRawTarget, sourceTarget,
            pathChain, sourceChain, targetChain⟩)
      | inr moreRedexCases =>
          cases moreRedexCases with
          | inl uaCase =>
              obtain ⟨proofRawTarget, sourceTarget, pathChain,
                sourceChain, targetChain⟩ := uaCase
              exact Or.inr (Or.inr (Or.inl ⟨proofRawTarget,
                sourceTarget, pathChain, sourceChain, targetChain⟩))
          | inr composeCase =>
              obtain ⟨payload, sourceTarget, pathChain, sourceChain,
                targetChain⟩ := composeCase
              exact Or.inr (Or.inr (Or.inr ⟨payload.1, payload.2,
                sourceTarget, pathChain, sourceChain, targetChain⟩))

/-- `RawStep.parStar (hcomp sides cap) target` either preserves the
`hcomp` head or fires the constant-sides hcomp β rule after `sides`
develops to `pathLam body.weaken`. -/
theorem RawStep.parStar.hcomp_inv {scope : Nat}
    {sidesTerm capTerm target : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.hcomp sidesTerm capTerm) target) :
    (∃ sidesTarget capTarget,
      target = RawTerm.hcomp sidesTarget capTarget ∧
      RawStep.parStar sidesTerm sidesTarget ∧
      RawStep.parStar capTerm capTarget) ∨
    (∃ (pathBodyTarget : RawTerm scope) (capTarget : RawTerm scope),
      RawStep.parStar sidesTerm
        (RawTerm.pathLam pathBodyTarget.weaken) ∧
      RawStep.parStar capTerm capTarget ∧
      RawStep.parStar capTarget target) :=
  RawStep.parStar.binary_left_intro_elim_inv_helper RawTerm.hcomp
    (fun (pathBodyTarget : RawTerm scope) =>
      RawTerm.pathLam pathBodyTarget.weaken)
    (fun _ capTarget => capTarget)
    (fun step => by
      cases RawStep.par.hcomp_inv step with
      | inl headCase =>
          exact Or.inl headCase
      | inr redexCases =>
          cases redexCases with
          | inl shallowCase =>
              obtain ⟨pathBodySource, capTarget, sidesEq, targetEq,
                capStep⟩ := shallowCase
              cases sidesEq
              exact Or.inr ⟨pathBodySource, capTarget, targetEq,
                RawStep.par.refl _, capStep⟩
          | inr deepCase =>
              obtain ⟨pathBodyTarget, capTarget, targetEq, sidesStep,
                capStep⟩ := deepCase
              exact Or.inr ⟨pathBodyTarget, capTarget, targetEq,
                sidesStep, capStep⟩)
    chain

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

-/
