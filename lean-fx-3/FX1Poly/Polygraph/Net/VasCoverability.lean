import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem
import FX1Poly.ComputerAlgebra.Order.AlmostFull

/-! # FX1Poly/Polygraph/Net/VasCoverability — backward coverability for vector
    addition systems (NET-5: the bounded-fuel decision + the Dickson termination wall)

A **vector addition system** (VAS / Petri net) is a finite family of transitions over a
fixed dimension `dim`.  A **marking** is a fixed-length vector in `Nat^dim`, carried here as
a `List Nat`.  A transition is a pair `(guard, delta)` of markings: it is *enabled* at
`marking` when `guard ≤ marking` componentwise, and firing it produces
`(marking ∸ guard) + delta`.  The **coverability** question — "starting from `source`, can
we fire a sequence of transitions reaching a marking `≥ target`?" — is the classical
Karp–Miller / backward-antichain problem.

This module ships the CONSTRUCTIVE, correct-when-it-halts core:

## What is DECIDED / SOUND (zero-axiom)

* **T1 — vectors + VAS.**  `cvbVecLe` (pairwise structural `cswLe`), `cvbVecAdd`
  (componentwise `cvbAdd`), `cvbVecMonus` (componentwise truncated subtraction, own
  structural `cvbMonus` — no `Nat.sub` order lemma), reflexivity/transitivity of the vector
  order, `CvbVas`, `cvbFireEnabled`, `cvbFire`.
* **T2 — backward step + antichain.**  `cvbBackwardMarking` (the minimal pre-image of one
  target under one transition), `cvbPreStep` (all pre-images, minimised), and the
  antichain-minimisation fold `cvbAntichainMinimise` that drops dominated markings.
* **T3 — bounded-fuel coverability + soundness.**  `cvbCoverBounded` iterates `cvbPreStep`
  on structural fuel until the basis stabilises or fuel runs out (`CvbVerdict`).  Two
  soundness theorems, both zero-axiom:
    - `cvbBackwardStepSound` — a single backward pre-image step is a *genuine* cover: if a
      marking dominates `cvbBackwardMarking guard delta target` for a transition of the VAS,
      then `target` is really coverable (the `CvbCovers` inductive witnesses a real firing).
    - `cvbCheckCoverSound` — a checked FORWARD firing chain (all transitions of the VAS,
      each enabled along the way, final marking `≥ target`) witnesses `CvbCovers`, by
      structural induction on the chain length (the "per-step soundness on the fuel" content,
      mirroring `cswCheckDerivationSound`).

## What is WALLED

* **`cvbHasUnconditionalCoverabilityTermination := false`** — the backward antichain
  iteration always stabilises because the `⊆`-increasing sequence of upward-closed sets in
  `Nat^k` is a well-quasi-order (Dickson).  But the zero-axiom proof that the fixpoint is
  reached at SOME fuel is exactly the almost-full PRODUCT over `List Nat`, whose both-`later`
  case needs the non-structural well-founded tree recursion `WellFounded.fix` supplies —
  the certified NET-4 impossibility `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false`.
  Burned attacks: (1) bounded-unrolling under-approximation is one-sided — `some true` is
  sound but the absence of a cover within fuel never proves non-coverability (matches the
  NET-9 attack recorded at `ocpHasCompositionalCoverability`); (2) fuel-induction on the
  basis chain has NO decreasing structural measure without the WQO — an unbounded VAS grows
  the antichain forever, so `cvbAntichainMinimise` never fires a termination certificate.
* **`cvbHasKarpMillerTree := false`** — the forward `ω`-accelerated Karp–Miller covering
  tree (markings extended with `ω = none` on unboundedly-growing coordinates, acceleration
  on a dominating ancestor) decides boundedness two-sided.  Its finiteness rests on the
  SAME `Nat^k`-WQO on `ω`-markings.  The `ω`-carrier (`List (Option Nat)`) and the
  acceleration step are computable; only tree-finiteness is walled at `fxNet4_dicksonWall`.
  Burned attacks: (1) depth-bounded tree unrolling misses covers that need a longer branch
  — one-sided again; (2) proving "every branch meets a dominating ancestor" is the bar
  induction the AF-product supplies — the walled `WellFounded.fix`.

`cvbTerminationWallEqualsDickson` concretely equates the termination marker to the NET-4
Dickson wall by `rfl`.  Compositional coverability across an open-net cospan
(`ocpHasCompositionalCoverability = false`, NET-9) is the composite version of the same wall.

## Zero-axiom

Structural recursion throughout: on `Nat`, on `List Nat`, on the fuel `Nat`, on the
`CvbCovers` / chain derivations.  Every `Nat`/vector order fact is a hand-rolled structural
recursion; no leak-prone library order/append lemma is used.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical.choice`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Net/VasCoverability.lean`. -/

namespace FX1Poly.Polygraph.Net

open FX1Poly.ComputerAlgebra (cswLe cswLeRefl cswLeTrans cswCondTrue cswCondFalse cswListNatBeq)

/-! ## Scalar arithmetic — own structural `cvbAdd` / `cvbMonus` (no library order lemma) -/

/-- Addition, structural on the second argument (so `cvbMonus (cvbAdd base addend) base`
cancels cleanly). -/
def cvbAdd : Nat → Nat → Nat
  | base, 0 => base
  | base, Nat.succ addend => Nat.succ (cvbAdd base addend)

/-- Truncated subtraction (monus), fully structural — never touches `Nat.sub`. -/
def cvbMonus : Nat → Nat → Nat
  | minuend, 0 => minuend
  | 0, Nat.succ _ => 0
  | Nat.succ minuendPred, Nat.succ subtrahendPred => cvbMonus minuendPred subtrahendPred

/-- `cvbAdd 0 addend = addend`. -/
theorem cvbAddZeroLeft : (addend : Nat) → cvbAdd 0 addend = addend
  | 0 => rfl
  | Nat.succ predecessor => congrArg Nat.succ (cvbAddZeroLeft predecessor)

/-- `cvbMonus minuend 0 = minuend` (not definitional — the matcher splits the first
argument, so a variable minuend needs a case split). -/
theorem cvbMonusZeroRight : (minuend : Nat) → cvbMonus minuend 0 = minuend
  | 0 => rfl
  | Nat.succ _ => rfl

/-- `cvbAdd (succ base) addend = succ (cvbAdd base addend)`. -/
theorem cvbAddSuccLeft : (base addend : Nat) →
    cvbAdd (Nat.succ base) addend = Nat.succ (cvbAdd base addend)
  | _, 0 => rfl
  | base, Nat.succ addendPred => congrArg Nat.succ (cvbAddSuccLeft base addendPred)

/-- **Cancellation**: `(base + addend) ∸ base = addend`. -/
theorem cvbMonusAddCancel : (base addend : Nat) → cvbMonus (cvbAdd base addend) base = addend
  | 0, addend => by rw [cvbAddZeroLeft addend]; exact cvbMonusZeroRight addend
  | Nat.succ base, addend => by
      rw [cvbAddSuccLeft base addend]
      exact cvbMonusAddCancel base addend

/-- `lower ≤ upper` implies `lower ≤ upper + 1`. -/
theorem cvbLeSuccRight : (lower upper : Nat) →
    cswLe lower upper = true → cswLe lower (Nat.succ upper) = true
  | 0, _, _ => rfl
  | Nat.succ _, 0, hle => Bool.noConfusion hle
  | Nat.succ lowerPred, Nat.succ upperPred, hle => cvbLeSuccRight lowerPred upperPred hle

/-- `base ≤ base + addend`. -/
theorem cvbLeAddSelf : (base addend : Nat) → cswLe base (cvbAdd base addend) = true
  | base, 0 => cswLeRefl base
  | base, Nat.succ addendPred =>
      cvbLeSuccRight base (cvbAdd base addendPred) (cvbLeAddSelf base addendPred)

/-- `target ≤ (target ∸ subtrahend) + subtrahend`. -/
theorem cvbLeMonusAdd : (target subtrahend : Nat) →
    cswLe target (cvbAdd (cvbMonus target subtrahend) subtrahend) = true
  | target, 0 => by rw [cvbMonusZeroRight target]; exact cswLeRefl target
  | 0, Nat.succ _ => rfl
  | Nat.succ targetPred, Nat.succ subtrahendPred => cvbLeMonusAdd targetPred subtrahendPred

/-- **The scalar backward-cover fact**: firing the minimal pre-image covers the target
component.  `q ≤ ((pre + (q ∸ post)) ∸ pre) + post`, which the cancellation collapses to
`q ≤ (q ∸ post) + post`. -/
theorem cvbLePreOneFire (guardScalar targetScalar deltaScalar : Nat) :
    cswLe targetScalar
      (cvbAdd (cvbMonus (cvbAdd guardScalar (cvbMonus targetScalar deltaScalar)) guardScalar)
        deltaScalar) = true := by
  rw [cvbMonusAddCancel guardScalar (cvbMonus targetScalar deltaScalar)]
  exact cvbLeMonusAdd targetScalar deltaScalar

/-- Monotonicity of `cvbAdd` in the left argument (right constant fixed). -/
theorem cvbAddMonoLeft : (valueLeft valueRight addedConstant : Nat) →
    cswLe valueLeft valueRight = true →
    cswLe (cvbAdd valueLeft addedConstant) (cvbAdd valueRight addedConstant) = true
  | _, _, 0, hle => hle
  | valueLeft, valueRight, Nat.succ constantPred, hle =>
      cvbAddMonoLeft valueLeft valueRight constantPred hle

/-- Monotonicity of `cvbMonus` in the left (minuend) argument. -/
theorem cvbMonusMonoLeft : (valueLeft valueRight subtractor : Nat) →
    cswLe valueLeft valueRight = true →
    cswLe (cvbMonus valueLeft subtractor) (cvbMonus valueRight subtractor) = true
  | valueLeft, valueRight, 0, hle => by
      rw [cvbMonusZeroRight valueLeft, cvbMonusZeroRight valueRight]; exact hle
  | 0, _, Nat.succ _, _ => rfl
  | Nat.succ _, 0, Nat.succ _, hle => Bool.noConfusion hle
  | Nat.succ valueLeftPred, Nat.succ valueRightPred, Nat.succ subtractorPred, hle =>
      cvbMonusMonoLeft valueLeftPred valueRightPred subtractorPred hle

/-! ## Guarded-`cond` elimination (the shared `cond flag payload false` splitter) -/

/-- If `cond flag payload false = true` then both `flag` and `payload` are `true`. -/
theorem cvbCondGuardElim (flag payload : Bool)
    (hcond : cond flag payload false = true) : flag = true ∧ payload = true := by
  cases hflag : flag with
  | true => rw [hflag] at hcond; rw [cswCondTrue] at hcond; exact ⟨rfl, hcond⟩
  | false => rw [hflag] at hcond; rw [cswCondFalse] at hcond; exact Bool.noConfusion hcond

/-! ## The vector order `cvbVecLe` (pairwise `cswLe`) -/

/-- Componentwise `≤` on markings (pairwise `cswLe`; length-sensitive). -/
def cvbVecLe : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      cond (cswLe leftHead rightHead) (cvbVecLe leftRest rightRest) false

/-- Introduce a `cvbVecLe` on a cons from head-`cswLe` and tail-`cvbVecLe`. -/
theorem cvbVecLeConsIntro (leftHead rightHead : Nat) (leftRest rightRest : List Nat)
    (hHead : cswLe leftHead rightHead = true)
    (hRest : cvbVecLe leftRest rightRest = true) :
    cvbVecLe (leftHead :: leftRest) (rightHead :: rightRest) = true := by
  show cond (cswLe leftHead rightHead) (cvbVecLe leftRest rightRest) false = true
  rw [hHead, cswCondTrue]
  exact hRest

/-- Eliminate a `cvbVecLe` on a cons into head-`cswLe` and tail-`cvbVecLe`. -/
theorem cvbVecLeConsElim (leftHead rightHead : Nat) (leftRest rightRest : List Nat)
    (hle : cvbVecLe (leftHead :: leftRest) (rightHead :: rightRest) = true) :
    cswLe leftHead rightHead = true ∧ cvbVecLe leftRest rightRest = true :=
  cvbCondGuardElim (cswLe leftHead rightHead) (cvbVecLe leftRest rightRest) hle

/-- `cvbVecLe` is reflexive. -/
theorem cvbVecLeRefl : (vector : List Nat) → cvbVecLe vector vector = true
  | [] => rfl
  | head :: rest => cvbVecLeConsIntro head head rest rest (cswLeRefl head) (cvbVecLeRefl rest)

/-- `cvbVecLe` is transitive. -/
theorem cvbVecLeTrans : (vectorLeft vectorMid vectorRight : List Nat) →
    cvbVecLe vectorLeft vectorMid = true → cvbVecLe vectorMid vectorRight = true →
    cvbVecLe vectorLeft vectorRight = true
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, hmr => Bool.noConfusion hmr
  | [], _ :: _, _, hlm, _ => Bool.noConfusion hlm
  | _ :: _, [], _, hlm, _ => Bool.noConfusion hlm
  | _ :: _, _ :: _, [], _, hmr => Bool.noConfusion hmr
  | leftHead :: leftRest, midHead :: midRest, rightHead :: rightRest, hlm, hmr => by
      have hlmSplit := cvbVecLeConsElim leftHead midHead leftRest midRest hlm
      have hmrSplit := cvbVecLeConsElim midHead rightHead midRest rightRest hmr
      exact cvbVecLeConsIntro leftHead rightHead leftRest rightRest
        (cswLeTrans leftHead midHead rightHead hlmSplit.left hmrSplit.left)
        (cvbVecLeTrans leftRest midRest rightRest hlmSplit.right hmrSplit.right)

/-! ## Vector arithmetic — `cvbVecAdd`, `cvbVecMonus`, shape -/

/-- Componentwise addition (truncates to the length of the first vector). -/
def cvbVecAdd : List Nat → List Nat → List Nat
  | [], _ => []
  | head :: rest, [] => head :: rest
  | leftHead :: leftRest, rightHead :: rightRest =>
      cvbAdd leftHead rightHead :: cvbVecAdd leftRest rightRest

/-- Componentwise truncated subtraction (truncates to the length of the first vector). -/
def cvbVecMonus : List Nat → List Nat → List Nat
  | [], _ => []
  | head :: rest, [] => head :: rest
  | leftHead :: leftRest, rightHead :: rightRest =>
      cvbMonus leftHead rightHead :: cvbVecMonus leftRest rightRest

/-- Structural same-length test on markings. -/
def cvbSameShape : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | _ :: leftRest, _ :: rightRest => cvbSameShape leftRest rightRest

/-- `vector ≤ vector + addend` (the pre-image dominates its guard). -/
theorem cvbVecLeAddSelf : (vector addend : List Nat) →
    cvbVecLe vector (cvbVecAdd vector addend) = true
  | [], _ => rfl
  | head :: rest, [] => cvbVecLeRefl (head :: rest)
  | head :: rest, addendHead :: addendRest =>
      cvbVecLeConsIntro head (cvbAdd head addendHead) rest (cvbVecAdd rest addendRest)
        (cvbLeAddSelf head addendHead) (cvbVecLeAddSelf rest addendRest)

/-- Monotonicity of `cvbVecMonus` in the left (minuend) vector. -/
theorem cvbVecMonusMono : (markingLeft markingRight guard : List Nat) →
    cvbVecLe markingLeft markingRight = true →
    cvbVecLe (cvbVecMonus markingLeft guard) (cvbVecMonus markingRight guard) = true
  | [], [], _, _ => rfl
  | [], _ :: _, _, hle => Bool.noConfusion hle
  | _ :: _, [], _, hle => Bool.noConfusion hle
  | leftHead :: leftRest, rightHead :: rightRest, [], hle => hle
  | leftHead :: leftRest, rightHead :: rightRest, guardHead :: guardRest, hle => by
      have hSplit := cvbVecLeConsElim leftHead rightHead leftRest rightRest hle
      exact cvbVecLeConsIntro (cvbMonus leftHead guardHead) (cvbMonus rightHead guardHead)
        (cvbVecMonus leftRest guardRest) (cvbVecMonus rightRest guardRest)
        (cvbMonusMonoLeft leftHead rightHead guardHead hSplit.left)
        (cvbVecMonusMono leftRest rightRest guardRest hSplit.right)

/-- Monotonicity of `cvbVecAdd` in the left vector (right constant fixed). -/
theorem cvbVecAddMono : (vectorLeft vectorRight addend : List Nat) →
    cvbVecLe vectorLeft vectorRight = true →
    cvbVecLe (cvbVecAdd vectorLeft addend) (cvbVecAdd vectorRight addend) = true
  | [], [], _, _ => rfl
  | [], _ :: _, _, hle => Bool.noConfusion hle
  | _ :: _, [], _, hle => Bool.noConfusion hle
  | leftHead :: leftRest, rightHead :: rightRest, [], hle => hle
  | leftHead :: leftRest, rightHead :: rightRest, addendHead :: addendRest, hle => by
      have hSplit := cvbVecLeConsElim leftHead rightHead leftRest rightRest hle
      exact cvbVecLeConsIntro (cvbAdd leftHead addendHead) (cvbAdd rightHead addendHead)
        (cvbVecAdd leftRest addendRest) (cvbVecAdd rightRest addendRest)
        (cvbAddMonoLeft leftHead rightHead addendHead hSplit.left)
        (cvbVecAddMono leftRest rightRest addendRest hSplit.right)

/-! ## The VAS carrier + firing -/

/-- A vector addition system: a dimension and a list of `(guard, delta)` transitions. -/
structure CvbVas where
  dim : Nat
  transitions : List (List Nat × List Nat)

/-- A transition with guard `guard` is enabled at `marking` iff `guard ≤ marking`. -/
def cvbFireEnabled (guard marking : List Nat) : Bool := cvbVecLe guard marking

/-- Fire a transition `(guard, delta)` at `marking`: `(marking ∸ guard) + delta`. -/
def cvbFire (marking guard delta : List Nat) : List Nat :=
  cvbVecAdd (cvbVecMonus marking guard) delta

/-- The minimal pre-image of `target` under one transition `(guard, delta)`:
`guard + (target ∸ delta)`.  Any marking dominating it enables the transition and fires to
a marking `≥ target`. -/
def cvbBackwardMarking (guard delta target : List Nat) : List Nat :=
  cvbVecAdd guard (cvbVecMonus target delta)

/-- Structural equality of transitions. -/
def cvbTransitionBeq (transitionLeft transitionRight : List Nat × List Nat) : Bool :=
  cswListNatBeq transitionLeft.1 transitionRight.1 && cswListNatBeq transitionLeft.2 transitionRight.2

/-- Membership of a transition in a list (cons-only). -/
def cvbTransitionMem (transition : List Nat × List Nat) :
    List (List Nat × List Nat) → Bool
  | [] => false
  | head :: rest => cond (cvbTransitionBeq transition head) true (cvbTransitionMem transition rest)

/-- Membership of a transition in a VAS. -/
def cvbTransitionMemVas (transition : List Nat × List Nat) (vas : CvbVas) : Bool :=
  cvbTransitionMem transition vas.transitions

/-- **The scalar-to-vector backward-cover lemma**: firing the minimal pre-image of `target`
covers `target`, given the three vectors share a length. -/
theorem cvbVecLePreOneFire : (guard target delta : List Nat) →
    cvbSameShape target guard = true → cvbSameShape target delta = true →
    cvbVecLe target (cvbFire (cvbBackwardMarking guard delta target) guard delta) = true
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, hsd => Bool.noConfusion hsd
  | _ :: _, [], _, hsg, _ => Bool.noConfusion hsg
  | [], _ :: _, _, hsg, _ => Bool.noConfusion hsg
  | _ :: _, _ :: _, [], _, hsd => Bool.noConfusion hsd
  | guardHead :: guardRest, targetHead :: targetRest, deltaHead :: deltaRest, hsg, hsd => by
      show cvbVecLe (targetHead :: targetRest)
          (cvbAdd (cvbMonus (cvbAdd guardHead (cvbMonus targetHead deltaHead)) guardHead) deltaHead
            :: cvbFire (cvbBackwardMarking guardRest deltaRest targetRest) guardRest deltaRest) = true
      exact cvbVecLeConsIntro targetHead
        (cvbAdd (cvbMonus (cvbAdd guardHead (cvbMonus targetHead deltaHead)) guardHead) deltaHead)
        targetRest (cvbFire (cvbBackwardMarking guardRest deltaRest targetRest) guardRest deltaRest)
        (cvbLePreOneFire guardHead targetHead deltaHead)
        (cvbVecLePreOneFire guardRest targetRest deltaRest hsg hsd)

/-- Firing is monotone in the marking: a larger marking fires to a larger result. -/
theorem cvbFireMono (markingLeft markingRight guard delta : List Nat)
    (hle : cvbVecLe markingLeft markingRight = true) :
    cvbVecLe (cvbFire markingLeft guard delta) (cvbFire markingRight guard delta) = true :=
  cvbVecAddMono (cvbVecMonus markingLeft guard) (cvbVecMonus markingRight guard) delta
    (cvbVecMonusMono markingLeft markingRight guard hle)

/-! ## Genuine coverability + the two soundness theorems -/

/-- `CvbCovers vas marking target`: from `marking`, firing enabled transitions of `vas`,
we reach a marking `≥ target`.  `here` = already covers; `step` = fire one enabled
transition of the VAS, then cover from the result. -/
inductive CvbCovers (vas : CvbVas) : List Nat → List Nat → Prop where
  | here (marking target : List Nat) :
      cvbVecLe target marking = true → CvbCovers vas marking target
  | step (marking target : List Nat) (transition : List Nat × List Nat) :
      cvbTransitionMemVas transition vas = true →
      cvbFireEnabled transition.1 marking = true →
      CvbCovers vas (cvbFire marking transition.1 transition.2) target →
      CvbCovers vas marking target

/-- **T3 backward soundness**: if `marking` dominates the minimal pre-image of `target`
under a genuine transition `(guard, delta)` of the VAS (with matching shapes), then
`target` is really coverable from `marking`. -/
theorem cvbBackwardStepSound (vas : CvbVas) (guard delta target marking : List Nat)
    (hMem : cvbTransitionMemVas (guard, delta) vas = true)
    (hShapeGuard : cvbSameShape target guard = true)
    (hShapeDelta : cvbSameShape target delta = true)
    (hDominates : cvbVecLe (cvbBackwardMarking guard delta target) marking = true) :
    CvbCovers vas marking target := by
  have hGuardBackward : cvbVecLe guard (cvbBackwardMarking guard delta target) = true :=
    cvbVecLeAddSelf guard (cvbVecMonus target delta)
  have hGuardMarking : cvbVecLe guard marking = true :=
    cvbVecLeTrans guard (cvbBackwardMarking guard delta target) marking hGuardBackward hDominates
  have hCoverBackward :
      cvbVecLe target (cvbFire (cvbBackwardMarking guard delta target) guard delta) = true :=
    cvbVecLePreOneFire guard target delta hShapeGuard hShapeDelta
  have hFireMonotone :
      cvbVecLe (cvbFire (cvbBackwardMarking guard delta target) guard delta)
        (cvbFire marking guard delta) = true :=
    cvbFireMono (cvbBackwardMarking guard delta target) marking guard delta hDominates
  have hCoverMarking : cvbVecLe target (cvbFire marking guard delta) = true :=
    cvbVecLeTrans target (cvbFire (cvbBackwardMarking guard delta target) guard delta)
      (cvbFire marking guard delta) hCoverBackward hFireMonotone
  exact CvbCovers.step marking target (guard, delta) hMem hGuardMarking
    (CvbCovers.here (cvbFire marking guard delta) target hCoverMarking)

/-- All transitions of a chain are genuine transitions of the VAS. -/
def cvbChainInVas (vas : CvbVas) : List (List Nat × List Nat) → Bool
  | [] => true
  | head :: rest => cond (cvbTransitionMemVas head vas) (cvbChainInVas vas rest) false

/-- Check a forward firing chain from `marking`: every transition enabled along the way,
final marking `≥ target`. -/
def cvbCheckCover : List Nat → List (List Nat × List Nat) → List Nat → Bool
  | marking, [], target => cvbVecLe target marking
  | marking, transition :: rest, target =>
      cond (cvbFireEnabled transition.1 marking)
        (cvbCheckCover (cvbFire marking transition.1 transition.2) rest target)
        false

/-- **T3 forward soundness (per-step on the fuel)**: a checked forward firing chain of
VAS transitions witnesses genuine coverability, by structural induction on the chain. -/
theorem cvbCheckCoverSound (vas : CvbVas) :
    (chain : List (List Nat × List Nat)) → (marking target : List Nat) →
    cvbChainInVas vas chain = true →
    cvbCheckCover marking chain target = true →
    CvbCovers vas marking target
  | [], marking, target, _, hCheck =>
      CvbCovers.here marking target hCheck
  | transition :: rest, marking, target, hChain, hCheck => by
      have hChainSplit :=
        cvbCondGuardElim (cvbTransitionMemVas transition vas) (cvbChainInVas vas rest) hChain
      have hCheckSplit :=
        cvbCondGuardElim (cvbFireEnabled transition.1 marking)
          (cvbCheckCover (cvbFire marking transition.1 transition.2) rest target) hCheck
      exact CvbCovers.step marking target transition hChainSplit.left hCheckSplit.left
        (cvbCheckCoverSound vas rest (cvbFire marking transition.1 transition.2) target
          hChainSplit.right hCheckSplit.right)

/-! ## The bounded-fuel decision engine -/

/-- Cons-only concatenation of marking lists. -/
def cvbConcat : List (List Nat) → List (List Nat) → List (List Nat)
  | [], rightList => rightList
  | head :: rest, rightList => head :: cvbConcat rest rightList

/-- Backward pre-images of one `target` under every transition. -/
def cvbMapPreOne : List (List Nat × List Nat) → List Nat → List (List Nat)
  | [], _ => []
  | (guard, delta) :: rest, target =>
      cvbBackwardMarking guard delta target :: cvbMapPreOne rest target

/-- Backward pre-images of every `target` in a basis under every transition. -/
def cvbPreImagesAll (transitions : List (List Nat × List Nat)) :
    List (List Nat) → List (List Nat)
  | [] => []
  | target :: rest =>
      cvbConcat (cvbMapPreOne transitions target) (cvbPreImagesAll transitions rest)

/-- Is `candidate` dominated by some element `m ≤ candidate` of the basis? -/
def cvbDominated (candidate : List Nat) : List (List Nat) → Bool
  | [] => false
  | head :: rest => cond (cvbVecLe head candidate) true (cvbDominated candidate rest)

/-- Drop every basis element that `pivot` dominates (`pivot ≤ element`). -/
def cvbDropDominatedBy (pivot : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | head :: rest =>
      cond (cvbVecLe pivot head) (cvbDropDominatedBy pivot rest)
        (head :: cvbDropDominatedBy pivot rest)

/-- Insert `candidate` into a minimal antichain: skip it if already dominated, else add it
and drop the elements it dominates. -/
def cvbAntichainInsert (candidate : List Nat) (basis : List (List Nat)) : List (List Nat) :=
  cond (cvbDominated candidate basis) basis (candidate :: cvbDropDominatedBy candidate basis)

/-- Minimise a list of markings to its `cvbVecLe`-minimal antichain. -/
def cvbAntichainMinimise : List (List Nat) → List (List Nat)
  | [] => []
  | head :: rest => cvbAntichainInsert head (cvbAntichainMinimise rest)

/-- One backward step: accumulate the basis with all pre-images, then minimise. -/
def cvbPreStep (vas : CvbVas) (basis : List (List Nat)) : List (List Nat) :=
  cvbAntichainMinimise (cvbConcat basis (cvbPreImagesAll vas.transitions basis))

/-- Does `source` dominate some basis element (`element ≤ source`)? -/
def cvbSourceCovers (source : List Nat) : List (List Nat) → Bool
  | [] => false
  | head :: rest => cond (cvbVecLe head source) true (cvbSourceCovers source rest)

/-- Structural equality of bases (order-sensitive, for stabilisation detection). -/
def cvbBasisBeq : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      cond (cswListNatBeq leftHead rightHead) (cvbBasisBeq leftRest rightRest) false

/-- The three-valued verdict of the bounded coverability decision. -/
inductive CvbVerdict where
  | covered : CvbVerdict
  | notYetAtFuel : CvbVerdict
  | stableUncovered : CvbVerdict

/-- Bounded-fuel backward coverability: iterate `cvbPreStep` on structural fuel, testing at
each round whether `source` already dominates the backward basis.  `covered` = a genuine
cover found; `stableUncovered` = the basis stabilised before fuel ran out (a correct
non-coverability verdict, when it fires); `notYetAtFuel` = fuel exhausted without a
decision (honest "unknown"). -/
def cvbCoverBounded (vas : CvbVas) (source : List Nat) :
    Nat → List (List Nat) → CvbVerdict
  | 0, basis => cond (cvbSourceCovers source basis) CvbVerdict.covered CvbVerdict.notYetAtFuel
  | Nat.succ fuelPred, basis =>
      cond (cvbSourceCovers source basis)
        CvbVerdict.covered
        (cond (cvbBasisBeq (cvbPreStep vas basis) basis)
          CvbVerdict.stableUncovered
          (cvbCoverBounded vas source fuelPred (cvbPreStep vas basis)))

/-- Decide coverability of `target` from `source` within `fuel` backward steps. -/
def cvbDecideCover (vas : CvbVas) (source target : List Nat) (fuel : Nat) : CvbVerdict :=
  cvbCoverBounded vas source fuel [target]

/-! ## T4 — the Dickson termination walls -/

/-- **WALL** — the backward antichain iteration ALWAYS stabilises because the `⊆`-increasing
sequence of upward-closed sets in `Nat^k` is a well-quasi-order (Dickson).  But the
zero-axiom proof that the fixpoint is reached at SOME fuel is exactly the almost-full
PRODUCT over `List Nat`, whose both-`later` case needs the non-structural well-founded tree
recursion that `WellFounded.fix` would supply — the certified NET-4 impossibility
`FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false`.  Shipped instead: `cvbCoverBounded`,
correct when it halts.  Burned attacks: (1) bounded-unrolling under-approximation is
one-sided — the absence of a cover within fuel never refutes coverability; (2) fuel-induction
on the basis chain has no decreasing structural measure without the WQO, so an unbounded VAS
grows the antichain forever. -/
def cvbHasUnconditionalCoverabilityTermination : Bool := false

/-- **WALL** — the forward `ω`-accelerated Karp–Miller covering tree (markings extended with
`ω = none` on unboundedly-growing coordinates, acceleration on a dominating ancestor)
decides boundedness two-sided.  Its finiteness rests on the SAME `Nat^k`-WQO on
`ω`-markings.  The `ω`-carrier (`List (Option Nat)`) and the acceleration step are
computable; only tree-finiteness is walled at `fxNet4_dicksonWall`.  Burned attacks: (1)
depth-bounded tree unrolling misses covers needing a longer branch — one-sided; (2) proving
"every branch meets a dominating ancestor" is the bar induction the AF-product supplies —
the walled `WellFounded.fix`. -/
def cvbHasKarpMillerTree : Bool := false

/-- The termination wall is definitionally the NET-4 Dickson wall. -/
theorem cvbTerminationWallEqualsDickson :
    cvbHasUnconditionalCoverabilityTermination = FX1Poly.ComputerAlgebra.fxNet4_dicksonWall := rfl

/-! ## T5 — ground fires -/

/-- A concrete 2-place VAS with a single transition that adds one token to place `0`. -/
def cvbExampleVas : CvbVas := { dim := 2, transitions := [([0, 0], [1, 0])] }

/-- `cvbVecLe` computes: `[1,2] ≤ [2,2]`. -/
theorem cvbFireVecLeComputes : cvbVecLe [1, 2] [2, 2] = true := rfl

/-- `cvbVecLe` computes: `[3,0] ≤ [2,0]` is false. -/
theorem cvbFireVecLeComputesFalse : cvbVecLe [3, 0] [2, 0] = false := rfl

/-- `cvbVecAdd` computes: `[1,2] + [3,4] = [4,6]`. -/
theorem cvbFireVecAddComputes : cvbVecAdd [1, 2] [3, 4] = [4, 6] := rfl

/-- `cvbVecMonus` computes: `[5,1] ∸ [2,3] = [3,0]`. -/
theorem cvbFireVecMonusComputes : cvbVecMonus [5, 1] [2, 3] = [3, 0] := rfl

/-- `cvbFireEnabled` true: `[1,0] ≤ [2,1]`. -/
theorem cvbFireEnabledTrue : cvbFireEnabled [1, 0] [2, 1] = true := rfl

/-- `cvbFireEnabled` false: `[2,0]` is not `≤ [1,0]`. -/
theorem cvbFireEnabledFalse : cvbFireEnabled [2, 0] [1, 0] = false := rfl

/-- Firing the transition once from `[0,0]` reaches `[1,0]`. -/
theorem cvbFireProducesToken : cvbFire [0, 0] [0, 0] [1, 0] = [1, 0] := rfl

/-- **Coverable fire**: `[2,0]` IS coverable from `[0,0]` within fuel `3` — verdict
`covered`. -/
theorem cvbFireCovered : cvbDecideCover cvbExampleVas [0, 0] [2, 0] 3 = CvbVerdict.covered := rfl

/-- **Honest non-coverable fire**: `[0,1]` (a token in place `1`) is NOT coverable — the
backward basis stabilises, verdict `stableUncovered`. -/
theorem cvbFireStableUncovered :
    cvbDecideCover cvbExampleVas [0, 0] [0, 1] 3 = CvbVerdict.stableUncovered := rfl

/-- **Honest fuel-exhaustion fire**: at fuel `0`, `[2,0]` is not yet decided — verdict
`notYetAtFuel`. -/
theorem cvbFireNotYetAtFuel :
    cvbDecideCover cvbExampleVas [0, 0] [2, 0] 0 = CvbVerdict.notYetAtFuel := rfl

/-- **Backward-soundness fire**: dominating the minimal pre-image of `[1,0]` at `[0,0]`
yields a genuine `CvbCovers` witness (fire the transition once). -/
theorem cvbFireBackwardStepCovers : CvbCovers cvbExampleVas [0, 0] [1, 0] :=
  cvbBackwardStepSound cvbExampleVas [0, 0] [1, 0] [1, 0] [0, 0] rfl rfl rfl rfl

/-- **Forward-soundness fire**: the one-step firing chain from `[0,0]` witnesses
`CvbCovers` of `[1,0]`. -/
theorem cvbFireForwardChainCovers : CvbCovers cvbExampleVas [0, 0] [1, 0] :=
  cvbCheckCoverSound cvbExampleVas [([0, 0], [1, 0])] [0, 0] [1, 0] rfl rfl

end FX1Poly.Polygraph.Net
