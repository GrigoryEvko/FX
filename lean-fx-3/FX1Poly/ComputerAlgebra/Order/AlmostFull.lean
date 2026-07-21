/-! # Constructive almost-full relations

Classically a well-quasi-order is a relation in which every infinite sequence has an
increasing pair; constructively it is the inductive almost-full predicate on a decidable
(`Bool`-valued) relation (Coquand-Fridlender; Vytiniotis-Coquand-Wahlstedt).  `AlmostFull rel`
holds when `rel` is already full (`now`) or when the lift of `rel` by any chosen element is
almost-full (`later`), the derivation being a bar securing that every sequence eventually meets
the relation.  The order on `Nat` uses a structural `Bool` comparison `afNatBle`, the
`Nat.le`/`Nat.ble` library lemmas leaking `propext`.

The AF intersection/product theorem `afInter : AlmostFull relA -> AlmostFull relB ->
AlmostFull (fun p q => relA p.1 q.1 && relB p.2 q.2)` (equivalently `afProduct`), the core of
Dickson's lemma, is not provable here: its both-`later` case intersects two hypothesis-derived
relations that are not structural sub-derivations, and the Vytiniotis-Coquand-Wahlstedt fix
uses an `oplus` combinator on securing trees whose recursion terminates only by
`WellFounded.fix`, unavailable in this Init-only setting.  So `dicksonLemma` is left
undeclared, not `sorry`d, and `fxNet4_dicksonWall := false` records the wall.

Upstream is zero-axiom by structural recursion; the audit twin gates each declaration free of
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`,
`WellFounded.fix`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Structural Boolean order on `Nat` -/

/-- Structural Boolean order on `Nat`, avoiding the `propext`-leaky `Nat.ble`/`Nat.le`. -/
def afNatBle : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ first, Nat.succ second => afNatBle first second

/-- Reflexivity of `afNatBle`. -/
theorem afNatBleRefl : (value : Nat) → afNatBle value value = true
  | 0 => rfl
  | Nat.succ predecessor => afNatBleRefl predecessor

/-- Totality: `afNatBle first second = false` gives `afNatBle second first = true`. -/
theorem afNatBleTotal : (first second : Nat) →
    afNatBle first second = false → afNatBle second first = true
  | 0, _, hfalse => Bool.noConfusion hfalse
  | Nat.succ _, 0, _ => rfl
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, hfalse =>
      afNatBleTotal firstPredecessor secondPredecessor hfalse

/-- Transitivity of `afNatBle`. -/
theorem afNatBleTrans : (first second third : Nat) →
    afNatBle first second = true → afNatBle second third = true → afNatBle first third = true
  | 0, _, _, _, _ => rfl
  | Nat.succ _, 0, _, hab, _ => Bool.noConfusion hab
  | Nat.succ _, Nat.succ _, 0, _, hbc => Bool.noConfusion hbc
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, Nat.succ thirdPredecessor, hab, hbc =>
      afNatBleTrans firstPredecessor secondPredecessor thirdPredecessor hab hbc

/-- Boundary lemma: `afNatBle (succ upper) lower = false` gives `afNatBle lower upper = true`
(the `lower = upper + 1` corner is impossible by reflexivity). -/
theorem afNatSuccFalseLe : (upper lower : Nat) →
    afNatBle (Nat.succ upper) lower = false → afNatBle lower upper = true
  | _, 0, _ => rfl
  | 0, Nat.succ _, hfalse => Bool.noConfusion hfalse
  | Nat.succ upperPredecessor, Nat.succ lowerPredecessor, hfalse =>
      afNatSuccFalseLe upperPredecessor lowerPredecessor hfalse

/-- `b || true = true`. -/
theorem afOrTrue : (flag : Bool) → (flag || true) = true
  | true => rfl
  | false => rfl

/-- Elimination for a true disjunction. -/
theorem afOrElim : (left right : Bool) →
    (left || right) = true → (left = true) ∨ (right = true)
  | true, _, _ => Or.inl rfl
  | false, _, hright => Or.inr hright

/-- Introduce a true disjunction from the left operand. -/
theorem afOrIntroLeft : (left right : Bool) → left = true → (left || right) = true
  | true, _, _ => rfl
  | false, _, hleft => Bool.noConfusion hleft

/-- Introduce a true disjunction from the right operand. -/
theorem afOrIntroRight : (left right : Bool) → right = true → (left || right) = true
  | true, _, _ => rfl
  | false, _, hright => hright

/-! ## The almost-full inductive -/

/-- Almost-full relations (Coquand-Fridlender, "secured by a bar"): full now, or almost-full
after lifting by any chosen element, the lift being `fun y z => rel y z || rel chosen y`. -/
inductive AlmostFull {carrier : Type} : (carrier → carrier → Bool) → Prop where
  | now (rel : carrier → carrier → Bool) : (∀ x y, rel x y = true) → AlmostFull rel
  | later (rel : carrier → carrier → Bool) :
      (∀ chosen, AlmostFull (fun y z => (rel y z) || (rel chosen y))) → AlmostFull rel

/-- The always-true relation is almost-full via `now`. -/
theorem afAlwaysTrue {carrier : Type} :
    AlmostFull (carrier := carrier) (fun _ _ => true) :=
  AlmostFull.now _ (fun _ _ => rfl)

/-! ## Closure properties and the order on `Nat` -/

/-- Generalized weakening: any pointwise-larger relation is almost-full. -/
theorem afWeaken {carrier : Type} {rel1 : carrier → carrier → Bool}
    (derivation : AlmostFull rel1) :
    ∀ (rel2 : carrier → carrier → Bool),
      (∀ x y, rel1 x y = true → rel2 x y = true) → AlmostFull rel2 := by
  induction derivation with
  | now rel full =>
      intro rel2 subset
      exact AlmostFull.now rel2 (fun x y => subset x y (full x y))
  | later rel _ liftHypothesis =>
      intro rel2 subset
      apply AlmostFull.later rel2
      intro chosen
      apply liftHypothesis chosen
      intro y z hlifted
      rcases afOrElim _ _ hlifted with hbody | hchosen
      · exact afOrIntroLeft _ _ (subset y z hbody)
      · exact afOrIntroRight _ _ (subset chosen y hchosen)

/-- Monotonicity: if `rel1 ⊆ rel2` pointwise and `rel1` is almost-full, so is `rel2`. -/
theorem afMono {carrier : Type} {rel1 rel2 : carrier → carrier → Bool}
    (subset : ∀ x y, rel1 x y = true → rel2 x y = true)
    (derivation : AlmostFull rel1) : AlmostFull rel2 :=
  afWeaken derivation rel2 subset

/-- Pullback closure: if `rel` is almost-full and `f : source → target`, then
`fun x y => rel (f x) (f y)` is almost-full, by induction on the derivation. -/
theorem afPullback {source target : Type} (f : source → target)
    {rel : target → target → Bool} (derivation : AlmostFull rel) :
    AlmostFull (fun x y => rel (f x) (f y)) := by
  induction derivation with
  | now rel full =>
      exact AlmostFull.now _ (fun x y => full (f x) (f y))
  | later rel _ liftHypothesis =>
      apply AlmostFull.later _
      intro chosen
      exact liftHypothesis (f chosen)

/-- Product order with a degenerate first coordinate: the pullback of `relSecond` along
`Prod.snd`, the fragment of `afProduct` provable without the general intersection theorem. -/
theorem afProductTrivialFirst {first second : Type} (relSecond : second → second → Bool)
    (derivation : AlmostFull relSecond) :
    AlmostFull (fun (leftPair rightPair : first × second) =>
      relSecond leftPair.2 rightPair.2) :=
  afPullback (fun (pair : first × second) => pair.2) derivation

/-- The staged relation `fun x y => afNatBle x y || afNatBle bound x` is almost-full for every
`bound`, by induction on `bound`: at `succ b` the `later` lift by `chosen` is full above the
boundary, else it embeds the predecessor stage via `afMono`. -/
theorem afNatLeStage : (bound : Nat) →
    AlmostFull (fun (x y : Nat) => afNatBle x y || afNatBle bound x) := by
  intro bound
  induction bound with
  | zero =>
      apply AlmostFull.now
      intro x y
      exact afOrIntroRight _ _ rfl
  | succ boundPredecessor stageHypothesis =>
      apply AlmostFull.later
      intro chosen
      cases hchosen : afNatBle (Nat.succ boundPredecessor) chosen with
      | true =>
          apply AlmostFull.now
          intro x y
          exact afOrIntroRight _ _ (afOrTrue _)
      | false =>
          refine afMono ?_ stageHypothesis
          intro x y hstage
          rcases afOrElim _ _ hstage with hbody | hboundary
          · exact afOrIntroLeft _ _ (afOrIntroLeft _ _ hbody)
          · have hchosenBoundary : afNatBle chosen boundPredecessor = true :=
              afNatSuccFalseLe boundPredecessor chosen hchosen
            have hchosenBelow : afNatBle chosen x = true :=
              afNatBleTrans chosen boundPredecessor x hchosenBoundary hboundary
            exact afOrIntroRight _ _ (afOrIntroLeft _ _ hchosenBelow)

/-- The natural order on `Nat` is almost-full: one `later` step over the staged family. -/
theorem afNat : AlmostFull afNatBle :=
  AlmostFull.later afNatBle (fun chosen => afNatLeStage chosen)

/-- Marks that Dickson's lemma is not closed zero-axiom: the AF intersection/product theorem
`afInter` is walled — its both-`later` case needs a non-structural well-founded tree recursion
that only `WellFounded.fix` supplies — so `dicksonLemma` is left undeclared. -/
def fxNet4_dicksonWall : Bool := false

end FX1Poly.ComputerAlgebra
