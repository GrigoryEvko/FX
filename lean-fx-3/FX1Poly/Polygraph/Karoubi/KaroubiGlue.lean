import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem

/-! # FX1Poly/Polygraph/Karoubi/KaroubiGlue — Eckmann–Hilton collapse and the
    Karoubi idempotent-completion word problem (WP-GLUE)

Two orthogonal pieces, both zero-axiom (Init only), reusing the propext-free
`csw` word-equality kit from `ComputerAlgebra.Semigroup.CommWordProblem`.

## Piece A — Eckmann–Hilton

`EckmannHiltonData` bundles two unital binary operations `opWhite`, `opBlack`
sharing a unit, tied by the interchange law.  The classical collapse follows by
pure equational reasoning (`Eq.trans`/`congrArg`, no lists, no axioms):

* `kgwOpsCoincide`     : `opWhite = opBlack` pointwise
* `kgwMedial`          : the four-way exchange engine on `opBlack`
* `kgwOpIsCommutative` : `opBlack` is commutative
* `kgwOpIsAssociative` : `opBlack` is associative

Non-vacuity: `kgwNatAddEH`, natural-number addition as a degenerate EH where
both operations are `+`.

## Piece B — Karoubi word problem (idempotent completion, single-generator/free base)

Morphisms are words `List Nat` over generator indices, with an own cons-only
append (`kgwAppend`) carrying its own associativity/identity laws.  An object is
an idempotent word `e` (`kgwAppend e e = e`); a morphism of `(X, e)` is a word
`w` sandwiched by `e` (`kgwAppend e (kgwAppend w e) = w`).  Identity `= e`,
composition `= kgwAppend w1 w2` (proved sandwiched via left/right absorption).
The word-problem decision `kgwDecideConv` compares the sandwiched normal forms
(the `mor` fields) with the `csw` structural beq; the Karoubi congruence
`KarConv` (refl/symm/trans + left/right identity + associativity + composition
congruence) is proved SOUND (`kgwKarConvSound`: convertible ⟹ equal normal
form), giving `kgwDecideConvOfKarConv` and the refutation half.

## Walls

* `kgwHasGeneralKaroubiSplitting := false` — splitting idempotents that are not
  the declared object idempotent needs freshly introduced split objects and the
  universal property of `Kar(C)`; the sandwiched normal form only decides the
  free/declared case (mirrors `cswHasPresentedCommWordDecision := false`).
* `kgwHasDeloopingTower := false` — the higher Eckmann–Hilton / k-tuply-monoidal
  stabilization tower and group completion; cf. the OMEGA-3 undecidability
  ceiling `semiThue_iff_encodedTwoCellSuspended` and
  `fxMode_hasSimpsonSemistrictification := false`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.KaroubiGlue

open FX1Poly.ComputerAlgebra (cswListNatBeq cswListNatBeqRefl cswListNatBeqEq)

/-! ## Piece A — Eckmann–Hilton -/

/-- Two unital binary operations on a common carrier, sharing a unit and tied by
    the interchange (middle-four) law. -/
structure EckmannHiltonData where
  Carrier : Type
  opWhite : Carrier → Carrier → Carrier
  opBlack : Carrier → Carrier → Carrier
  unit : Carrier
  opWhiteUnitLeft  : ∀ element, opWhite unit element = element
  opWhiteUnitRight : ∀ element, opWhite element unit = element
  opBlackUnitLeft  : ∀ element, opBlack unit element = element
  opBlackUnitRight : ∀ element, opBlack element unit = element
  interchange : ∀ topLeft topRight bottomLeft bottomRight,
    opWhite (opBlack topLeft topRight) (opBlack bottomLeft bottomRight)
      = opBlack (opWhite topLeft bottomLeft) (opWhite topRight bottomRight)

/-- The two operations coincide: `opWhite a b = opBlack a b`. -/
theorem kgwOpsCoincide (eh : EckmannHiltonData)
    (leftFactor rightFactor : eh.Carrier) :
    eh.opWhite leftFactor rightFactor = eh.opBlack leftFactor rightFactor :=
  let expandLeft : eh.opWhite leftFactor rightFactor
      = eh.opWhite (eh.opBlack leftFactor eh.unit) rightFactor :=
    congrArg (fun probe => eh.opWhite probe rightFactor)
      (eh.opBlackUnitRight leftFactor).symm
  let expandRight : eh.opWhite (eh.opBlack leftFactor eh.unit) rightFactor
      = eh.opWhite (eh.opBlack leftFactor eh.unit) (eh.opBlack eh.unit rightFactor) :=
    congrArg (fun probe => eh.opWhite (eh.opBlack leftFactor eh.unit) probe)
      (eh.opBlackUnitLeft rightFactor).symm
  let crossExchange :
      eh.opWhite (eh.opBlack leftFactor eh.unit) (eh.opBlack eh.unit rightFactor)
      = eh.opBlack (eh.opWhite leftFactor eh.unit) (eh.opWhite eh.unit rightFactor) :=
    eh.interchange leftFactor eh.unit eh.unit rightFactor
  let collapseLeft :
      eh.opBlack (eh.opWhite leftFactor eh.unit) (eh.opWhite eh.unit rightFactor)
      = eh.opBlack leftFactor (eh.opWhite eh.unit rightFactor) :=
    congrArg (fun probe => eh.opBlack probe (eh.opWhite eh.unit rightFactor))
      (eh.opWhiteUnitRight leftFactor)
  let collapseRight : eh.opBlack leftFactor (eh.opWhite eh.unit rightFactor)
      = eh.opBlack leftFactor rightFactor :=
    congrArg (fun probe => eh.opBlack leftFactor probe)
      (eh.opWhiteUnitLeft rightFactor)
  expandLeft.trans (expandRight.trans (crossExchange.trans
    (collapseLeft.trans collapseRight)))

/-- The medial (four-way exchange) law for `opBlack`, obtained from the
    interchange law after collapsing `opWhite` into `opBlack`. -/
theorem kgwMedial (eh : EckmannHiltonData)
    (topLeft topRight bottomLeft bottomRight : eh.Carrier) :
    eh.opBlack (eh.opBlack topLeft topRight) (eh.opBlack bottomLeft bottomRight)
      = eh.opBlack (eh.opBlack topLeft bottomLeft) (eh.opBlack topRight bottomRight) :=
  let toWhite :
      eh.opBlack (eh.opBlack topLeft topRight) (eh.opBlack bottomLeft bottomRight)
      = eh.opWhite (eh.opBlack topLeft topRight) (eh.opBlack bottomLeft bottomRight) :=
    (kgwOpsCoincide eh (eh.opBlack topLeft topRight) (eh.opBlack bottomLeft bottomRight)).symm
  let exchange :
      eh.opWhite (eh.opBlack topLeft topRight) (eh.opBlack bottomLeft bottomRight)
      = eh.opBlack (eh.opWhite topLeft bottomLeft) (eh.opWhite topRight bottomRight) :=
    eh.interchange topLeft topRight bottomLeft bottomRight
  let innerLeft :
      eh.opBlack (eh.opWhite topLeft bottomLeft) (eh.opWhite topRight bottomRight)
      = eh.opBlack (eh.opBlack topLeft bottomLeft) (eh.opWhite topRight bottomRight) :=
    congrArg (fun probe => eh.opBlack probe (eh.opWhite topRight bottomRight))
      (kgwOpsCoincide eh topLeft bottomLeft)
  let innerRight :
      eh.opBlack (eh.opBlack topLeft bottomLeft) (eh.opWhite topRight bottomRight)
      = eh.opBlack (eh.opBlack topLeft bottomLeft) (eh.opBlack topRight bottomRight) :=
    congrArg (fun probe => eh.opBlack (eh.opBlack topLeft bottomLeft) probe)
      (kgwOpsCoincide eh topRight bottomRight)
  toWhite.trans (exchange.trans (innerLeft.trans innerRight))

/-- `opBlack` is commutative. -/
theorem kgwOpIsCommutative (eh : EckmannHiltonData)
    (leftFactor rightFactor : eh.Carrier) :
    eh.opBlack leftFactor rightFactor = eh.opBlack rightFactor leftFactor :=
  let expandLeft : eh.opBlack leftFactor rightFactor
      = eh.opBlack (eh.opBlack eh.unit leftFactor) rightFactor :=
    congrArg (fun probe => eh.opBlack probe rightFactor)
      (eh.opBlackUnitLeft leftFactor).symm
  let expandRight : eh.opBlack (eh.opBlack eh.unit leftFactor) rightFactor
      = eh.opBlack (eh.opBlack eh.unit leftFactor) (eh.opBlack rightFactor eh.unit) :=
    congrArg (fun probe => eh.opBlack (eh.opBlack eh.unit leftFactor) probe)
      (eh.opBlackUnitRight rightFactor).symm
  let exchange :
      eh.opBlack (eh.opBlack eh.unit leftFactor) (eh.opBlack rightFactor eh.unit)
      = eh.opBlack (eh.opBlack eh.unit rightFactor) (eh.opBlack leftFactor eh.unit) :=
    kgwMedial eh eh.unit leftFactor rightFactor eh.unit
  let collapseLeft :
      eh.opBlack (eh.opBlack eh.unit rightFactor) (eh.opBlack leftFactor eh.unit)
      = eh.opBlack rightFactor (eh.opBlack leftFactor eh.unit) :=
    congrArg (fun probe => eh.opBlack probe (eh.opBlack leftFactor eh.unit))
      (eh.opBlackUnitLeft rightFactor)
  let collapseRight : eh.opBlack rightFactor (eh.opBlack leftFactor eh.unit)
      = eh.opBlack rightFactor leftFactor :=
    congrArg (fun probe => eh.opBlack rightFactor probe)
      (eh.opBlackUnitRight leftFactor)
  expandLeft.trans (expandRight.trans (exchange.trans
    (collapseLeft.trans collapseRight)))

/-- `opBlack` is associative. -/
theorem kgwOpIsAssociative (eh : EckmannHiltonData)
    (first second third : eh.Carrier) :
    eh.opBlack (eh.opBlack first second) third
      = eh.opBlack first (eh.opBlack second third) :=
  let expandThird : eh.opBlack (eh.opBlack first second) third
      = eh.opBlack (eh.opBlack first second) (eh.opBlack eh.unit third) :=
    congrArg (fun probe => eh.opBlack (eh.opBlack first second) probe)
      (eh.opBlackUnitLeft third).symm
  let exchange :
      eh.opBlack (eh.opBlack first second) (eh.opBlack eh.unit third)
      = eh.opBlack (eh.opBlack first eh.unit) (eh.opBlack second third) :=
    kgwMedial eh first second eh.unit third
  let collapseLeft :
      eh.opBlack (eh.opBlack first eh.unit) (eh.opBlack second third)
      = eh.opBlack first (eh.opBlack second third) :=
    congrArg (fun probe => eh.opBlack probe (eh.opBlack second third))
      (eh.opBlackUnitRight first)
  expandThird.trans (exchange.trans collapseLeft)

/-- Natural-number addition as a degenerate Eckmann–Hilton datum: both operations
    are `+`, the unit is `0`, and interchange is the additive rearrangement. -/
def kgwNatAddInterchange (topLeft topRight bottomLeft bottomRight : Nat) :
    Nat.add (Nat.add topLeft topRight) (Nat.add bottomLeft bottomRight)
      = Nat.add (Nat.add topLeft bottomLeft) (Nat.add topRight bottomRight) :=
  let regroupOne : Nat.add (Nat.add topLeft topRight) (Nat.add bottomLeft bottomRight)
      = Nat.add topLeft (Nat.add topRight (Nat.add bottomLeft bottomRight)) :=
    Nat.add_assoc topLeft topRight (Nat.add bottomLeft bottomRight)
  let regroupTwo : Nat.add topLeft (Nat.add topRight (Nat.add bottomLeft bottomRight))
      = Nat.add topLeft (Nat.add (Nat.add topRight bottomLeft) bottomRight) :=
    congrArg (fun probe => Nat.add topLeft probe)
      (Nat.add_assoc topRight bottomLeft bottomRight).symm
  let commuteMiddle : Nat.add topLeft (Nat.add (Nat.add topRight bottomLeft) bottomRight)
      = Nat.add topLeft (Nat.add (Nat.add bottomLeft topRight) bottomRight) :=
    congrArg (fun probe => Nat.add topLeft (Nat.add probe bottomRight))
      (Nat.add_comm topRight bottomLeft)
  let regroupThree : Nat.add topLeft (Nat.add (Nat.add bottomLeft topRight) bottomRight)
      = Nat.add topLeft (Nat.add bottomLeft (Nat.add topRight bottomRight)) :=
    congrArg (fun probe => Nat.add topLeft probe)
      (Nat.add_assoc bottomLeft topRight bottomRight)
  let regroupFour : Nat.add topLeft (Nat.add bottomLeft (Nat.add topRight bottomRight))
      = Nat.add (Nat.add topLeft bottomLeft) (Nat.add topRight bottomRight) :=
    (Nat.add_assoc topLeft bottomLeft (Nat.add topRight bottomRight)).symm
  regroupOne.trans (regroupTwo.trans (commuteMiddle.trans (regroupThree.trans regroupFour)))

/-- The natural-number additive Eckmann–Hilton datum. -/
def kgwNatAddEH : EckmannHiltonData where
  Carrier := Nat
  opWhite := Nat.add
  opBlack := Nat.add
  unit := 0
  opWhiteUnitLeft := Nat.zero_add
  opWhiteUnitRight := fun _element => rfl
  opBlackUnitLeft := Nat.zero_add
  opBlackUnitRight := fun _element => rfl
  interchange := kgwNatAddInterchange

/-! ## Piece B — Karoubi word problem -/

/-- Own cons-only word append over generator indices. -/
def kgwAppend : List Nat → List Nat → List Nat
  | [], rightWord => rightWord
  | letter :: leftRest, rightWord => letter :: kgwAppend leftRest rightWord

/-- Left identity for `kgwAppend` (definitional). -/
theorem kgwNilAppend (rightWord : List Nat) : kgwAppend [] rightWord = rightWord := rfl

/-- Right identity for `kgwAppend`. -/
theorem kgwAppendNil : (leftWord : List Nat) → kgwAppend leftWord [] = leftWord
  | [] => rfl
  | letter :: leftRest => congrArg (fun probe => letter :: probe) (kgwAppendNil leftRest)

/-- Associativity for `kgwAppend`. -/
theorem kgwAppendAssoc : (leftWord middleWord rightWord : List Nat) →
    kgwAppend (kgwAppend leftWord middleWord) rightWord
      = kgwAppend leftWord (kgwAppend middleWord rightWord)
  | [], _, _ => rfl
  | letter :: leftRest, middleWord, rightWord =>
      congrArg (fun probe => letter :: probe) (kgwAppendAssoc leftRest middleWord rightWord)

/-- An object of the Karoubi envelope: an idempotent word. -/
structure KarObject where
  idem : List Nat
  idempotent : kgwAppend idem idem = idem

/-- A morphism of the Karoubi object `obj`: a word sandwiched by `obj.idem`. -/
structure KarMor (obj : KarObject) where
  mor : List Nat
  sandwiched : kgwAppend obj.idem (kgwAppend mor obj.idem) = mor

/-- The sandwiched normal form of a Karoubi morphism (its own `mor` word). -/
def kgwNormalForm {obj : KarObject} (arrow : KarMor obj) : List Nat := arrow.mor

/-- Left absorption: a sandwiched word already absorbs the idempotent on the left. -/
theorem kgwLeftAbsorb (idemWord word : List Nat)
    (hIdem : kgwAppend idemWord idemWord = idemWord)
    (hSand : kgwAppend idemWord (kgwAppend word idemWord) = word) :
    kgwAppend idemWord word = word :=
  let unfoldWord : kgwAppend idemWord word
      = kgwAppend idemWord (kgwAppend idemWord (kgwAppend word idemWord)) :=
    congrArg (fun probe => kgwAppend idemWord probe) hSand.symm
  let regroup : kgwAppend idemWord (kgwAppend idemWord (kgwAppend word idemWord))
      = kgwAppend (kgwAppend idemWord idemWord) (kgwAppend word idemWord) :=
    (kgwAppendAssoc idemWord idemWord (kgwAppend word idemWord)).symm
  let collapseIdem : kgwAppend (kgwAppend idemWord idemWord) (kgwAppend word idemWord)
      = kgwAppend idemWord (kgwAppend word idemWord) :=
    congrArg (fun probe => kgwAppend probe (kgwAppend word idemWord)) hIdem
  unfoldWord.trans (regroup.trans (collapseIdem.trans hSand))

/-- Right absorption: a sandwiched word already absorbs the idempotent on the right. -/
theorem kgwRightAbsorb (idemWord word : List Nat)
    (hIdem : kgwAppend idemWord idemWord = idemWord)
    (hSand : kgwAppend idemWord (kgwAppend word idemWord) = word) :
    kgwAppend word idemWord = word :=
  let unfoldWord : kgwAppend word idemWord
      = kgwAppend (kgwAppend idemWord (kgwAppend word idemWord)) idemWord :=
    congrArg (fun probe => kgwAppend probe idemWord) hSand.symm
  let regroupOuter : kgwAppend (kgwAppend idemWord (kgwAppend word idemWord)) idemWord
      = kgwAppend idemWord (kgwAppend (kgwAppend word idemWord) idemWord) :=
    kgwAppendAssoc idemWord (kgwAppend word idemWord) idemWord
  let regroupInner : kgwAppend idemWord (kgwAppend (kgwAppend word idemWord) idemWord)
      = kgwAppend idemWord (kgwAppend word (kgwAppend idemWord idemWord)) :=
    congrArg (fun probe => kgwAppend idemWord probe) (kgwAppendAssoc word idemWord idemWord)
  let collapseIdem : kgwAppend idemWord (kgwAppend word (kgwAppend idemWord idemWord))
      = kgwAppend idemWord (kgwAppend word idemWord) :=
    congrArg (fun probe => kgwAppend idemWord (kgwAppend word probe)) hIdem
  unfoldWord.trans (regroupOuter.trans (regroupInner.trans (collapseIdem.trans hSand)))

/-- The identity morphism of a Karoubi object: the object's idempotent word. -/
def kgwIdentity (obj : KarObject) : KarMor obj where
  mor := obj.idem
  sandwiched :=
    (congrArg (fun probe => kgwAppend obj.idem probe) obj.idempotent).trans obj.idempotent

/-- Composition of Karoubi morphisms over a common object: word concatenation,
    already sandwiched by absorption. -/
def kgwCompose {obj : KarObject} (first second : KarMor obj) : KarMor obj where
  mor := kgwAppend first.mor second.mor
  sandwiched :=
    let rightAbsorbed : kgwAppend second.mor obj.idem = second.mor :=
      kgwRightAbsorb obj.idem second.mor obj.idempotent second.sandwiched
    let leftAbsorbed : kgwAppend obj.idem first.mor = first.mor :=
      kgwLeftAbsorb obj.idem first.mor obj.idempotent first.sandwiched
    let regroupOuter :
        kgwAppend obj.idem (kgwAppend (kgwAppend first.mor second.mor) obj.idem)
        = kgwAppend obj.idem (kgwAppend first.mor (kgwAppend second.mor obj.idem)) :=
      congrArg (fun probe => kgwAppend obj.idem probe)
        (kgwAppendAssoc first.mor second.mor obj.idem)
    let collapseRight :
        kgwAppend obj.idem (kgwAppend first.mor (kgwAppend second.mor obj.idem))
        = kgwAppend obj.idem (kgwAppend first.mor second.mor) :=
      congrArg (fun probe => kgwAppend obj.idem (kgwAppend first.mor probe)) rightAbsorbed
    let regroupLeft : kgwAppend obj.idem (kgwAppend first.mor second.mor)
        = kgwAppend (kgwAppend obj.idem first.mor) second.mor :=
      (kgwAppendAssoc obj.idem first.mor second.mor).symm
    let collapseLeft : kgwAppend (kgwAppend obj.idem first.mor) second.mor
        = kgwAppend first.mor second.mor :=
      congrArg (fun probe => kgwAppend probe second.mor) leftAbsorbed
    regroupOuter.trans (collapseRight.trans (regroupLeft.trans collapseLeft))

/-- The word-problem decision: compare the sandwiched normal forms with the
    propext-free structural word beq. -/
def kgwDecideConv {obj : KarObject} (left right : KarMor obj) : Bool :=
  cswListNatBeq (kgwNormalForm left) (kgwNormalForm right)

/-- Soundness of the decision at the word level: `beq = true ⟹ equal normal form. -/
theorem kgwDecideConvEq {obj : KarObject} (left right : KarMor obj)
    (hDecide : kgwDecideConv left right = true) :
    kgwNormalForm left = kgwNormalForm right :=
  cswListNatBeqEq (kgwNormalForm left) (kgwNormalForm right) hDecide

/-- The Karoubi congruence: the category laws (identity, associativity) together
    with compatibility with composition, on morphisms of a fixed object. -/
inductive KarConv (obj : KarObject) : KarMor obj → KarMor obj → Prop where
  | refl : (arrow : KarMor obj) → KarConv obj arrow arrow
  | symm : {left right : KarMor obj} → KarConv obj left right → KarConv obj right left
  | trans : {left middle right : KarMor obj} →
      KarConv obj left middle → KarConv obj middle right → KarConv obj left right
  | leftIdentity : (arrow : KarMor obj) →
      KarConv obj (kgwCompose (kgwIdentity obj) arrow) arrow
  | rightIdentity : (arrow : KarMor obj) →
      KarConv obj (kgwCompose arrow (kgwIdentity obj)) arrow
  | associativity : (first second third : KarMor obj) →
      KarConv obj (kgwCompose (kgwCompose first second) third)
        (kgwCompose first (kgwCompose second third))
  | congLeft : {left right : KarMor obj} → (other : KarMor obj) →
      KarConv obj left right → KarConv obj (kgwCompose left other) (kgwCompose right other)
  | congRight : (other : KarMor obj) → {left right : KarMor obj} →
      KarConv obj left right → KarConv obj (kgwCompose other left) (kgwCompose other right)

/-- Soundness of the left-identity law as a word equality. -/
theorem kgwLeftIdentitySound {obj : KarObject} (arrow : KarMor obj) :
    kgwNormalForm (kgwCompose (kgwIdentity obj) arrow) = kgwNormalForm arrow :=
  kgwLeftAbsorb obj.idem arrow.mor obj.idempotent arrow.sandwiched

/-- Soundness of the right-identity law as a word equality. -/
theorem kgwRightIdentitySound {obj : KarObject} (arrow : KarMor obj) :
    kgwNormalForm (kgwCompose arrow (kgwIdentity obj)) = kgwNormalForm arrow :=
  kgwRightAbsorb obj.idem arrow.mor obj.idempotent arrow.sandwiched

/-- Soundness of the associativity law as a word equality. -/
theorem kgwAssociativitySound {obj : KarObject} (first second third : KarMor obj) :
    kgwNormalForm (kgwCompose (kgwCompose first second) third)
      = kgwNormalForm (kgwCompose first (kgwCompose second third)) :=
  kgwAppendAssoc first.mor second.mor third.mor

/-- The congruence is SOUND: convertible morphisms have equal sandwiched normal form. -/
theorem kgwKarConvSound {obj : KarObject} :
    (left right : KarMor obj) → KarConv obj left right →
    kgwNormalForm left = kgwNormalForm right
  | _, _, KarConv.refl _ => rfl
  | _, _, KarConv.symm hConv => (kgwKarConvSound _ _ hConv).symm
  | _, _, KarConv.trans hLeft hRight =>
      (kgwKarConvSound _ _ hLeft).trans (kgwKarConvSound _ _ hRight)
  | _, _, KarConv.leftIdentity arrow => kgwLeftIdentitySound arrow
  | _, _, KarConv.rightIdentity arrow => kgwRightIdentitySound arrow
  | _, _, KarConv.associativity first second third =>
      kgwAssociativitySound first second third
  | _, _, KarConv.congLeft other hConv =>
      congrArg (fun probe => kgwAppend probe other.mor) (kgwKarConvSound _ _ hConv)
  | _, _, KarConv.congRight other hConv =>
      congrArg (fun probe => kgwAppend other.mor probe) (kgwKarConvSound _ _ hConv)

/-- The decision agrees with the congruence: convertible ⟹ decides `true`. -/
theorem kgwDecideConvOfKarConv {obj : KarObject} (left right : KarMor obj)
    (hConv : KarConv obj left right) : kgwDecideConv left right = true :=
  let hEq : kgwNormalForm left = kgwNormalForm right := kgwKarConvSound left right hConv
  let reflRight : cswListNatBeq (kgwNormalForm right) (kgwNormalForm right) = true :=
    cswListNatBeqRefl (kgwNormalForm right)
  (congrArg (fun probe => cswListNatBeq probe (kgwNormalForm right)) hEq).trans reflRight

/-- The refutation half: if the decision says `false`, the morphisms are not
    convertible. -/
theorem kgwNotKarConvOfDecideFalse {obj : KarObject} (left right : KarMor obj)
    (hFalse : kgwDecideConv left right = false) : KarConv obj left right → False :=
  fun hConv =>
    Bool.noConfusion ((kgwDecideConvOfKarConv left right hConv).symm.trans hFalse)

/-! ## Walls -/

/-- WALL.  General idempotent splitting is NOT decided here.  The sandwiched
    normal form decides equality only for morphisms of a DECLARED object
    idempotent `e` over the free word monoid.  Splitting a general idempotent
    `p : X → X` (`p ∘ p = p` that is not the declared `e`) requires introducing a
    fresh split object `(X, p)` together with retraction/section words and the
    universal property that every idempotent in `Kar(C)` splits — data outside
    the sandwiched-word carrier.

    Burned attack 1: extend `KarMor` so every `mor` word carries its own
    idempotency proof and let the object float.  Composition then needs
    `e1 · f2 = e1` collapse across DIFFERENT idempotents, which is exactly the
    presented (non-free) word problem `cswHasPresentedCommWordDecision := false`
    — no free normal form exists.

    Burned attack 2: quotient `List Nat` by a presented relation `[i,i] = [i]`
    and split at `[i]`.  The split object is a NEW generator, so the carrier is
    no longer the original free monoid; the decision `kgwDecideConv` on the old
    words cannot see the new object and returns wrong answers on cross-object
    composites. -/
def kgwHasGeneralKaroubiSplitting : Bool := false

/-- WALL.  The higher Eckmann–Hilton / k-tuply-monoidal stabilization tower and
    group completion are NOT built here.  Piece A collapses ONE interchange
    square (two ops → commutative monoid); the delooping tower iterates this
    across dimension (the Baez–Dolan periodic table) and group-completes, which
    is the undecidability ceiling the OMEGA-3 layer already frames as
    `semiThue_iff_encodedTwoCellSuspended` (word problem stays hard through
    suspension) and walls as `fxMode_hasSimpsonSemistrictification := false`.

    Burned attack 1: iterate `EckmannHiltonData` by nesting a third op with two
    more interchange laws.  The nested collapse forces the carrier to be an
    abelian GROUP (inverses appear from the stabilization), which the equational
    `Eq.trans` engine cannot synthesize — no unit-law field produces an inverse.

    Burned attack 2: encode the tower as a suspended 2-cell word system and
    decide by normal form.  Suspension preserves the semi-Thue reduction, so the
    decision would decide an undecidable word problem — refuted by
    `semiThue_iff_encodedTwoCellSuspended`. -/
def kgwHasDeloopingTower : Bool := false

/-! ## Fires -/

/-- Concrete idempotent object: the empty word (`[] · [] = []`). -/
def kgwEmptyObject : KarObject where
  idem := []
  idempotent := rfl

/-- Concrete sandwiched morphism over the empty object: the word `[1, 2]`. -/
def kgwSampleMor : KarMor kgwEmptyObject where
  mor := [1, 2]
  sandwiched := rfl

/-- A second, distinct concrete morphism: the word `[3]`. -/
def kgwOtherMor : KarMor kgwEmptyObject where
  mor := [3]
  sandwiched := rfl

-- Fire 1: Eckmann–Hilton on `Nat` addition — the two operations coincide.
example : kgwNatAddEH.opWhite (2 : Nat) (3 : Nat) = kgwNatAddEH.opBlack (2 : Nat) (3 : Nat) :=
  kgwOpsCoincide kgwNatAddEH (2 : Nat) (3 : Nat)

-- Fire 2: Eckmann–Hilton commutativity fires as `2 + 3 = 3 + 2`.
example : kgwNatAddEH.opBlack (2 : Nat) (3 : Nat) = kgwNatAddEH.opBlack (3 : Nat) (2 : Nat) :=
  kgwOpIsCommutative kgwNatAddEH (2 : Nat) (3 : Nat)

-- Fire 3: the Karoubi identity of the empty object is its idempotent word.
example : (kgwIdentity kgwEmptyObject).mor = ([] : List Nat) := rfl

-- Fire 4: identity-composed morphism decides equal to its normal form.
example : kgwDecideConv (kgwCompose (kgwIdentity kgwEmptyObject) kgwSampleMor)
    kgwSampleMor = true := rfl

-- Fire 5: control — two distinct Karoubi morphisms decide `false`.
example : kgwDecideConv kgwSampleMor kgwOtherMor = false := rfl

-- Fire 6: the left-identity law is convertible and hence decides `true`.
example : kgwDecideConv (kgwCompose (kgwIdentity kgwEmptyObject) kgwSampleMor)
    kgwSampleMor = true :=
  kgwDecideConvOfKarConv _ _ (KarConv.leftIdentity kgwSampleMor)

-- Fire 7: the control pair is not convertible.
example : KarConv kgwEmptyObject kgwSampleMor kgwOtherMor → False :=
  kgwNotKarConvOfDecideFalse kgwSampleMor kgwOtherMor rfl

end FX1Poly.Polygraph.KaroubiGlue
