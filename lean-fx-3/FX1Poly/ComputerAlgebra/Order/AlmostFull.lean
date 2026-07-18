/-! # FX1Poly/ComputerAlgebra/Order/AlmostFull — the constructive almost-full kit
    (NET-4 brick: constructive well-quasi-orders via almost-full relations)

Classically a well-quasi-order (WQO) is a relation in which every infinite sequence has an
increasing pair.  Constructively that reading is captured by the inductive **almost-full**
predicate on a DECIDABLE (`Bool`-valued) relation — the Coquand–Fridlender / Vytiniotis–
Coquand–Wahlstedt "Stop when you are almost-full" form.  `AlmostFull rel` means: `rel` is
already full (`now`), or after choosing any element the lifted relation is almost-full
(`later`); the derivation tree is a bar securing that every sequence eventually meets the
relation.

This module uses a purpose-built structural `Bool` order on `Nat` (`afNatBle`) rather than
`Nat.le`/`Nat.ble`, whose library lemmas leak `propext`.  It ships:

  * `AlmostFull` — the higher-order `Prop` inductive (the `later` constructor lifts `rel`
    by an arbitrarily chosen element; strictly positive, structural, axiom-free).
  * `afAlwaysTrue` — smoke lemma: the always-true relation is almost-full via `now`.
  * `afWeaken` / `afMono` — AF is UPWARD-closed in the relation: `rel1 ⊆ rel2` and
    `AlmostFull rel1` give `AlmostFull rel2` (structural induction on the derivation).
  * `afPullback` — AF is closed under inverse image along any map (`rel ∘ f`).
  * `afProductTrivialFirst` — the product order in the degenerate case where the first
    coordinate's relation is trivially full: reduces to `afPullback` along `Prod.snd`.
  * `afNat` — the natural order on `Nat` is almost-full, via the staged induction
    `afNatLeStage`: the relation `fun x y => afNatBle x y || afNatBle bound x` is AF by
    induction on `bound` (base `bound = 0` is full; step closes by `afMono` from the
    predecessor stage, ruling out the boundary element through `afNatSuccFalseLe`).

## The AF-product WALL (`fxNet4_dicksonWall := false`)

The crux of Dickson's lemma — the AF INTERSECTION / PRODUCT theorem

    afInter : AlmostFull relA → AlmostFull relB
            → AlmostFull (fun p q => relA p.1 q.1 && relB p.2 q.2)   -- on `A × B`

(equivalently `afProduct`) — is **walled** here, and the wall is genuine, not a gap of
effort.  The obstruction, located precisely:

  * The natural proof is a double induction (outer on `AlmostFull relA`, inner on
    `AlmostFull relB`).  In the both-`later` case the goal, after applying `later`, is
    `AlmostFull ((relA ∧ relB) ⇑ z)` for an arbitrary chosen `z`, where the lift is
    `(R ⇑ z) x y = R x y ∨ R z x`.  Concretely this relation is
        `(relA x y ∧ relB x y) ∨ (relA z x ∧ relB z x)`.
  * This is an INTERSECTION-shaped (small) relation.  `afMono` only builds AF UPWARD —
    from `AlmostFull` of a subset to `AlmostFull` of a superset — so it cannot reach a
    small target.  Every relation the two induction hypotheses hand us
        `C := relA ∧ (relB ⇑ z)`   (inner IH at `z`),
        `D := (relA ⇑ z) ∧ relB`   (outer IH at `z`, against the in-scope `AlmostFull relB`)
    satisfies `C ∧ D = relA ∧ relB` (the two extra lift-disjuncts cancel), yet `C` and `D`
    are each incomparable to the goal `(relA ∧ relB) ⇑ z`, so no single `afMono` closes it.
  * Closing it requires INTERSECTING `C` and `D` — but `C` and `D` are not structural
    sub-derivations of either input, so this is not an induction hypothesis.  The standard
    fix (Vytiniotis–Coquand–Wahlstedt) reifies AF as a well-founded tree (`WFT`) and
    combines two securing trees with the `oplus` combinator
        `oplus (SUP f) (SUP g) = SUP (fun x => oplus (oplus (SUP f) (g x)) (oplus (f x) (SUP g)))`,
    whose recursion is NOT structural on the pair of trees; it terminates only by a
    well-founded measure.  In this Init-only zero-axiom setting `WellFounded.fix` is
    forbidden, so that route is closed.

Hence `afInter` / `afProduct` is the named wall, and `dicksonLemma` (which would iterate
`afProduct` from `afNat` over `Nat`-vectors) is left GENUINELY UNDECLARED — not `sorry`d.
Everything upstream of the wall (the inductive, `afMono`, `afPullback`, `afNat`) is a
clean, honest, zero-axiom brick.

## Zero-axiom

Structural recursion throughout: on the `AlmostFull` derivation (`afWeaken`, `afPullback`),
on `Nat` (`afNatLeStage`, the `afNatBle` kit), and on `Bool` constructors (the `af*Or*`
helpers).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`, `WellFounded.fix`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Order/AlmostFull.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Structural Boolean order on `Nat`

A purpose-built `Bool` comparison avoiding every `propext`-leaky `Nat.ble`/`Nat.le` library
lemma.  `afNatBle 0 _ = true`, `afNatBle (succ _) 0 = false`,
`afNatBle (succ a) (succ b) = afNatBle a b`. -/

/-- Structural Boolean `≤` on `Nat`. -/
def afNatBle : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ first, Nat.succ second => afNatBle first second

/-- **Reflexivity of `afNatBle`.** -/
theorem afNatBleRefl : (value : Nat) → afNatBle value value = true
  | 0 => rfl
  | Nat.succ predecessor => afNatBleRefl predecessor

/-- **Totality of `afNatBle`** — if `afNatBle first second` fails then `afNatBle second first`
holds (the order is total). -/
theorem afNatBleTotal : (first second : Nat) →
    afNatBle first second = false → afNatBle second first = true
  | 0, _, hfalse => Bool.noConfusion hfalse
  | Nat.succ _, 0, _ => rfl
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, hfalse =>
      afNatBleTotal firstPredecessor secondPredecessor hfalse

/-- **Transitivity of `afNatBle`.** -/
theorem afNatBleTrans : (first second third : Nat) →
    afNatBle first second = true → afNatBle second third = true → afNatBle first third = true
  | 0, _, _, _, _ => rfl
  | Nat.succ _, 0, _, hab, _ => Bool.noConfusion hab
  | Nat.succ _, Nat.succ _, 0, _, hbc => Bool.noConfusion hbc
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, Nat.succ thirdPredecessor, hab, hbc =>
      afNatBleTrans firstPredecessor secondPredecessor thirdPredecessor hab hbc

/-- **Boundary lemma** — if `afNatBle (succ upper) lower` fails then `afNatBle lower upper`
holds.  In words: `¬ (upper + 1 ≤ lower)` forces `lower ≤ upper`.  Structural recursion on
both arguments; the `lower = upper + 1` corner is impossible because it would make
`afNatBle (succ upper) (succ upper)` false, contradicting reflexivity. -/
theorem afNatSuccFalseLe : (upper lower : Nat) →
    afNatBle (Nat.succ upper) lower = false → afNatBle lower upper = true
  | _, 0, _ => rfl
  | 0, Nat.succ _, hfalse => Bool.noConfusion hfalse
  | Nat.succ upperPredecessor, Nat.succ lowerPredecessor, hfalse =>
      afNatSuccFalseLe upperPredecessor lowerPredecessor hfalse

/-! ## Boolean disjunction helpers

Structural on `Bool` constructors — none touches a `propext`-leaky library lemma. -/

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

/-- **Almost-full relations** (Coquand–Fridlender "secured by a bar").  A `Bool`-valued
relation is almost-full when it is either already full (`now`), or becomes almost-full after
lifting by any chosen element (`later`).  The lift `(rel ⇑ chosen) y z = rel y z || rel
chosen y` records that `chosen` was seen earlier and relates to `y`.  The derivation tree is
the bar witnessing that every infinite sequence eventually contains a related pair. -/
inductive AlmostFull {carrier : Type} : (carrier → carrier → Bool) → Prop where
  | now (rel : carrier → carrier → Bool) : (∀ x y, rel x y = true) → AlmostFull rel
  | later (rel : carrier → carrier → Bool) :
      (∀ chosen, AlmostFull (fun y z => (rel y z) || (rel chosen y))) → AlmostFull rel

/-- Smoke lemma: the always-true relation is almost-full via `now`. -/
theorem afAlwaysTrue {carrier : Type} :
    AlmostFull (carrier := carrier) (fun _ _ => true) :=
  AlmostFull.now _ (fun _ _ => rfl)

/-! ## Weakening / monotonicity

Almost-fullness is UPWARD-closed in the relation: enlarging the relation preserves it.
Structural induction on the `AlmostFull rel1` derivation, with the target relation
generalized so the `later` case can re-apply the hypothesis to the lifted target. -/

/-- **Generalized weakening.** -/
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

/-- **Monotonicity of almost-fullness.**  If `rel1 ⊆ rel2` pointwise and `rel1` is
almost-full, so is `rel2`. -/
theorem afMono {carrier : Type} {rel1 rel2 : carrier → carrier → Bool}
    (subset : ∀ x y, rel1 x y = true → rel2 x y = true)
    (derivation : AlmostFull rel1) : AlmostFull rel2 :=
  afWeaken derivation rel2 subset

/-! ## Closure under inverse image (pullback)

If `rel` on `A` is almost-full and `f : B → A`, then the pullback `fun x y => rel (f x)
(f y)` on `B` is almost-full.  Structural induction on the derivation; the `later` case
re-uses the hypothesis at the mapped element `f chosen`. -/

/-- **Pullback closure** of almost-fullness along a map. -/
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

/-- **Product order, degenerate first coordinate.**  When the first coordinate's relation is
trivially full, the product order on `A × B` reduces to the pullback of `relB` along
`Prod.snd`.  This is the honest partial fragment of the walled `afProduct`: the
`afPullback` reduction is in place; only the general INTERSECTION theorem is missing. -/
theorem afProductTrivialFirst {first second : Type} (relSecond : second → second → Bool)
    (derivation : AlmostFull relSecond) :
    AlmostFull (fun (leftPair rightPair : first × second) =>
      relSecond leftPair.2 rightPair.2) :=
  afPullback (fun (pair : first × second) => pair.2) derivation

/-! ## The natural order on `Nat` is almost-full

The staged relation `fun x y => afNatBle x y || afNatBle bound x` — "`x ≤ y`, or the
boundary `bound` is already `≤ x`" — is almost-full for every `bound`, by induction on
`bound`.  At `bound = 0` it is full (`afNatBle 0 x = true`).  At `bound = succ b` the
`later` lift by any `chosen` splits on whether `chosen` sits above the boundary: if it does
the lift is full; otherwise the predecessor stage (`bound = b`) embeds into the lift via
`afMono`, using `afNatSuccFalseLe` + `afNatBleTrans` to carry the boundary element below
`chosen`.  `afNat` is then one `later` step over this staged family. -/

/-- The staged relation is almost-full for every boundary. -/
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

/-- **The natural order on `Nat` is almost-full.**  One `later` step over the staged
family: lifting `afNatBle` by any `chosen` yields exactly the stage relation at
`bound = chosen`. -/
theorem afNat : AlmostFull afNatBle :=
  AlmostFull.later afNatBle (fun chosen => afNatLeStage chosen)

/-! ## Dickson wall marker

`fxNet4_dicksonWall := false` records that Dickson's lemma is NOT closed: the AF-product /
intersection theorem `afInter` is walled (see the module header for the precise obstruction
— the both-`later` case needs a non-structural, well-founded tree recursion that
`WellFounded.fix` would supply, which is forbidden here).  `dicksonLemma` is therefore left
undeclared. -/
def fxNet4_dicksonWall : Bool := false

end FX1Poly.ComputerAlgebra
