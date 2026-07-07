import FX1Poly.ComputerAlgebra.Number.ComplexReal

/-! # SetoidRingHom — the arrow level over `CommutativeRingWitness` (NUM-ALG-1)

The object-level tower ships a `CommutativeRingWitness` at every number floor
(ℤ, ℚ, ℝ, ℂ).  This module builds the ARROWS that turn that stack of objects
into a genuine categorical diagram: a setoid-relative ring homomorphism, its
identity and composition, the three category laws (up to pointwise-`denotesSame`
hom equality), and two carrier-generic inverse-uniqueness engines that the
widenings and the analytic inverses consume downstream.

Everything is `Init`-only, certificate-first, and rides ONLY the shipped
`CommutativeRingWitness` fields — no carrier analysis re-enters here.  The
category laws are DIRECT: the underlying `map` is a bare Lean function, so
composition is definitionally unital and associative, and pointwise
`denotesSame` closes each law by reflexivity.  No hom-extensionality, no
`funext`, no `Quot`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The homomorphism -/

/-- **A setoid-relative commutative-ring homomorphism.**  Doubly indexed by the
source and target ring witnesses (each tower level is a distinct carrier with a
distinct setoid).  Six obligations: the map respects the source setoid, and
preserves addition, multiplication, zero, and one — each up to the TARGET
setoid.  Negation preservation is NOT a field: `map (neg a)` is an additive
inverse of `map a`, and additive inverses are unique up to `denotesSame`, so it
is the derived lemma `homPreservesNeg`. -/
structure SetoidRingHom {sourceCarrier targetCarrier : Type}
    (source : CommutativeRingWitness sourceCarrier)
    (target : CommutativeRingWitness targetCarrier) where
  map : sourceCarrier → targetCarrier
  respectsDenotesSame :
    ∀ leftValue rightValue : sourceCarrier,
      source.denotesSame leftValue rightValue →
        target.denotesSame (map leftValue) (map rightValue)
  preservesAdd :
    ∀ leftValue rightValue : sourceCarrier,
      target.denotesSame (map (source.add leftValue rightValue))
        (target.add (map leftValue) (map rightValue))
  preservesMul :
    ∀ leftValue rightValue : sourceCarrier,
      target.denotesSame (map (source.mul leftValue rightValue))
        (target.mul (map leftValue) (map rightValue))
  preservesZero : target.denotesSame (map source.zero) target.zero
  preservesOne : target.denotesSame (map source.one) target.one

/-! ## Carrier-generic inverse uniqueness

Both engines are ordinary "inverse is unique, hence congruent" ring algebra,
stated once at the `CommutativeRingWitness` altitude so no carrier re-proves
them.  Each is a flat transitive chain of shipped ring-witness fields. -/

/-- **Multiplicative inverse uniqueness with a congruent base.**  If `baseLeft`
and `baseRight` denote the same element, and `leftInverse` / `rightInverse`
invert them respectively, then the two inverses denote the same element.  The
`baseLeft := baseRight` instance is plain witness-independence. -/
theorem inverseUniqueInCommutativeRing {carrier : Type}
    (ring : CommutativeRingWitness carrier)
    {baseLeft baseRight leftInverse rightInverse : carrier}
    (baseAgrees : ring.denotesSame baseLeft baseRight)
    (leftInverts : ring.denotesSame (ring.mul baseLeft leftInverse) ring.one)
    (rightInverts : ring.denotesSame (ring.mul baseRight rightInverse) ring.one) :
    ring.denotesSame leftInverse rightInverse :=
  have leftUnfoldsToTimesOne :
      ring.denotesSame leftInverse (ring.mul leftInverse ring.one) :=
    ring.denotesSameIsSymmetric _ _
      (ring.oneIsRightMultiplicativeIdentity leftInverse)
  have oneReplacedByRightProduct :
      ring.denotesSame (ring.mul leftInverse ring.one)
        (ring.mul leftInverse (ring.mul baseRight rightInverse)) :=
    ring.mulRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive leftInverse)
      (ring.denotesSameIsSymmetric _ _ rightInverts)
  have baseRightReplacedByBaseLeft :
      ring.denotesSame (ring.mul leftInverse (ring.mul baseRight rightInverse))
        (ring.mul leftInverse (ring.mul baseLeft rightInverse)) :=
    ring.mulRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive leftInverse)
      (ring.mulRespectsDenotesSame _ _ _ _
        (ring.denotesSameIsSymmetric _ _ baseAgrees)
        (ring.denotesSameIsReflexive rightInverse))
  have reassociateToLeft :
      ring.denotesSame (ring.mul leftInverse (ring.mul baseLeft rightInverse))
        (ring.mul (ring.mul leftInverse baseLeft) rightInverse) :=
    ring.denotesSameIsSymmetric _ _
      (ring.mulIsAssociative leftInverse baseLeft rightInverse)
  have commuteInnerFactors :
      ring.denotesSame (ring.mul (ring.mul leftInverse baseLeft) rightInverse)
        (ring.mul (ring.mul baseLeft leftInverse) rightInverse) :=
    ring.mulRespectsDenotesSame _ _ _ _
      (ring.mulIsCommutative leftInverse baseLeft)
      (ring.denotesSameIsReflexive rightInverse)
  have leftProductCollapsesToOne :
      ring.denotesSame (ring.mul (ring.mul baseLeft leftInverse) rightInverse)
        (ring.mul ring.one rightInverse) :=
    ring.mulRespectsDenotesSame _ _ _ _ leftInverts
      (ring.denotesSameIsReflexive rightInverse)
  have oneTimesRightIsRight :
      ring.denotesSame (ring.mul ring.one rightInverse) rightInverse :=
    ring.denotesSameIsTransitive _ _ _
      (ring.mulIsCommutative ring.one rightInverse)
      (ring.oneIsRightMultiplicativeIdentity rightInverse)
  ring.denotesSameIsTransitive _ _ _ leftUnfoldsToTimesOne
    (ring.denotesSameIsTransitive _ _ _ oneReplacedByRightProduct
      (ring.denotesSameIsTransitive _ _ _ baseRightReplacedByBaseLeft
        (ring.denotesSameIsTransitive _ _ _ reassociateToLeft
          (ring.denotesSameIsTransitive _ _ _ commuteInnerFactors
            (ring.denotesSameIsTransitive _ _ _ leftProductCollapsesToOne
              oneTimesRightIsRight)))))

/-- **Additive inverse uniqueness** for a shared base — the additive analogue,
consumed by `homPreservesNeg`. -/
theorem additiveInverseUniqueInCommutativeRing {carrier : Type}
    (ring : CommutativeRingWitness carrier)
    {base leftInverse rightInverse : carrier}
    (leftInverts : ring.denotesSame (ring.add base leftInverse) ring.zero)
    (rightInverts : ring.denotesSame (ring.add base rightInverse) ring.zero) :
    ring.denotesSame leftInverse rightInverse :=
  have leftUnfoldsToPlusZero :
      ring.denotesSame leftInverse (ring.add leftInverse ring.zero) :=
    ring.denotesSameIsSymmetric _ _
      (ring.zeroIsRightAdditiveIdentity leftInverse)
  have zeroReplacedByRightSum :
      ring.denotesSame (ring.add leftInverse ring.zero)
        (ring.add leftInverse (ring.add base rightInverse)) :=
    ring.addRespectsDenotesSame _ _ _ _ (ring.denotesSameIsReflexive leftInverse)
      (ring.denotesSameIsSymmetric _ _ rightInverts)
  have reassociateToLeft :
      ring.denotesSame (ring.add leftInverse (ring.add base rightInverse))
        (ring.add (ring.add leftInverse base) rightInverse) :=
    ring.denotesSameIsSymmetric _ _
      (ring.addIsAssociative leftInverse base rightInverse)
  have commuteInnerSummands :
      ring.denotesSame (ring.add (ring.add leftInverse base) rightInverse)
        (ring.add (ring.add base leftInverse) rightInverse) :=
    ring.addRespectsDenotesSame _ _ _ _
      (ring.addIsCommutative leftInverse base)
      (ring.denotesSameIsReflexive rightInverse)
  have leftSumCollapsesToZero :
      ring.denotesSame (ring.add (ring.add base leftInverse) rightInverse)
        (ring.add ring.zero rightInverse) :=
    ring.addRespectsDenotesSame _ _ _ _ leftInverts
      (ring.denotesSameIsReflexive rightInverse)
  have zeroPlusRightIsRight :
      ring.denotesSame (ring.add ring.zero rightInverse) rightInverse :=
    ring.denotesSameIsTransitive _ _ _
      (ring.addIsCommutative ring.zero rightInverse)
      (ring.zeroIsRightAdditiveIdentity rightInverse)
  ring.denotesSameIsTransitive _ _ _ leftUnfoldsToPlusZero
    (ring.denotesSameIsTransitive _ _ _ zeroReplacedByRightSum
      (ring.denotesSameIsTransitive _ _ _ reassociateToLeft
        (ring.denotesSameIsTransitive _ _ _ commuteInnerSummands
          (ring.denotesSameIsTransitive _ _ _ leftSumCollapsesToZero
            zeroPlusRightIsRight))))

/-- **Negation is preserved** (derived).  `map (neg a)` and `neg (map a)` are
both additive inverses of `map a` in the target ring; additive-inverse
uniqueness identifies them. -/
theorem homPreservesNeg {sourceCarrier targetCarrier : Type}
    {source : CommutativeRingWitness sourceCarrier}
    {target : CommutativeRingWitness targetCarrier}
    (hom : SetoidRingHom source target) (value : sourceCarrier) :
    target.denotesSame (hom.map (source.neg value)) (target.neg (hom.map value)) :=
  have imageOfNegInverts :
      target.denotesSame
        (target.add (hom.map value) (hom.map (source.neg value))) target.zero :=
    target.denotesSameIsTransitive _ _ _
      (target.denotesSameIsSymmetric _ _
        (hom.preservesAdd value (source.neg value)))
      (target.denotesSameIsTransitive _ _ _
        (hom.respectsDenotesSame _ _ (source.negIsRightAdditiveInverse value))
        hom.preservesZero)
  have negOfImageInverts :
      target.denotesSame
        (target.add (hom.map value) (target.neg (hom.map value))) target.zero :=
    target.negIsRightAdditiveInverse (hom.map value)
  additiveInverseUniqueInCommutativeRing target imageOfNegInverts negOfImageInverts

/-! ## Hom equality: pointwise target-setoid

`Eq` on the record would demand proof-field equality (`funext` on `map`, and
proof irrelevance we do NOT have for `Type`-valued apartness).  The axiom-free
arrow equality is pointwise `denotesSame`, inherited refl/symm/trans from the
target setoid. -/

/-- **Pointwise sameness of homomorphisms** — equal on every input up to the
target setoid. -/
def HomDenotesSame {sourceCarrier targetCarrier : Type}
    {source : CommutativeRingWitness sourceCarrier}
    {target : CommutativeRingWitness targetCarrier}
    (firstHom secondHom : SetoidRingHom source target) : Prop :=
  ∀ value : sourceCarrier,
    target.denotesSame (firstHom.map value) (secondHom.map value)

/-- Hom sameness is reflexive. -/
theorem homDenotesSameRefl {sourceCarrier targetCarrier : Type}
    {source : CommutativeRingWitness sourceCarrier}
    {target : CommutativeRingWitness targetCarrier}
    (hom : SetoidRingHom source target) : HomDenotesSame hom hom :=
  fun value => target.denotesSameIsReflexive (hom.map value)

/-- Hom sameness is symmetric. -/
theorem homDenotesSameSymm {sourceCarrier targetCarrier : Type}
    {source : CommutativeRingWitness sourceCarrier}
    {target : CommutativeRingWitness targetCarrier}
    {firstHom secondHom : SetoidRingHom source target}
    (areSame : HomDenotesSame firstHom secondHom) :
    HomDenotesSame secondHom firstHom :=
  fun value => target.denotesSameIsSymmetric _ _ (areSame value)

/-- Hom sameness is transitive. -/
theorem homDenotesSameTrans {sourceCarrier targetCarrier : Type}
    {source : CommutativeRingWitness sourceCarrier}
    {target : CommutativeRingWitness targetCarrier}
    {firstHom middleHom lastHom : SetoidRingHom source target}
    (firstAgrees : HomDenotesSame firstHom middleHom)
    (lastAgrees : HomDenotesSame middleHom lastHom) :
    HomDenotesSame firstHom lastHom :=
  fun value =>
    target.denotesSameIsTransitive _ _ _ (firstAgrees value) (lastAgrees value)

/-! ## Identity and composition -/

/-- **The identity homomorphism** — the identity map; every obligation is
reflexivity. -/
def identityRingHom {carrier : Type} (ring : CommutativeRingWitness carrier) :
    SetoidRingHom ring ring where
  map := fun value => value
  respectsDenotesSame := fun _ _ areSame => areSame
  preservesAdd := fun leftValue rightValue =>
    ring.denotesSameIsReflexive (ring.add leftValue rightValue)
  preservesMul := fun leftValue rightValue =>
    ring.denotesSameIsReflexive (ring.mul leftValue rightValue)
  preservesZero := ring.denotesSameIsReflexive ring.zero
  preservesOne := ring.denotesSameIsReflexive ring.one

/-- **Composition of homomorphisms** — compose the maps; each preservation law
pushes the first hom's law through the second hom's map (via
`respectsDenotesSame`) and chains with the second hom's law by target
transitivity. -/
def composeRingHom {sourceCarrier middleCarrier targetCarrier : Type}
    {sourceRing : CommutativeRingWitness sourceCarrier}
    {middleRing : CommutativeRingWitness middleCarrier}
    {targetRing : CommutativeRingWitness targetCarrier}
    (secondHom : SetoidRingHom middleRing targetRing)
    (firstHom : SetoidRingHom sourceRing middleRing) :
    SetoidRingHom sourceRing targetRing where
  map := fun value => secondHom.map (firstHom.map value)
  respectsDenotesSame := fun _ _ areSame =>
    secondHom.respectsDenotesSame _ _ (firstHom.respectsDenotesSame _ _ areSame)
  preservesAdd := fun leftValue rightValue =>
    targetRing.denotesSameIsTransitive _ _ _
      (secondHom.respectsDenotesSame _ _ (firstHom.preservesAdd leftValue rightValue))
      (secondHom.preservesAdd (firstHom.map leftValue) (firstHom.map rightValue))
  preservesMul := fun leftValue rightValue =>
    targetRing.denotesSameIsTransitive _ _ _
      (secondHom.respectsDenotesSame _ _ (firstHom.preservesMul leftValue rightValue))
      (secondHom.preservesMul (firstHom.map leftValue) (firstHom.map rightValue))
  preservesZero :=
    targetRing.denotesSameIsTransitive _ _ _
      (secondHom.respectsDenotesSame _ _ firstHom.preservesZero) secondHom.preservesZero
  preservesOne :=
    targetRing.denotesSameIsTransitive _ _ _
      (secondHom.respectsDenotesSame _ _ firstHom.preservesOne) secondHom.preservesOne

/-! ## The category laws — up to pointwise `HomDenotesSame`

On the underlying `map`, function composition is definitionally unital and
associative, so each law closes by pointwise reflexivity. -/

/-- Left identity: `identity . f ~ f`. -/
theorem composeRingHomIdentityLeft {sourceCarrier targetCarrier : Type}
    {sourceRing : CommutativeRingWitness sourceCarrier}
    {targetRing : CommutativeRingWitness targetCarrier}
    (hom : SetoidRingHom sourceRing targetRing) :
    HomDenotesSame (composeRingHom (identityRingHom targetRing) hom) hom :=
  fun value => targetRing.denotesSameIsReflexive (hom.map value)

/-- Right identity: `f . identity ~ f`. -/
theorem composeRingHomIdentityRight {sourceCarrier targetCarrier : Type}
    {sourceRing : CommutativeRingWitness sourceCarrier}
    {targetRing : CommutativeRingWitness targetCarrier}
    (hom : SetoidRingHom sourceRing targetRing) :
    HomDenotesSame (composeRingHom hom (identityRingHom sourceRing)) hom :=
  fun value => targetRing.denotesSameIsReflexive (hom.map value)

/-- Associativity: `(h . g) . f ~ h . (g . f)`. -/
theorem composeRingHomAssoc {sourceCarrier secondCarrier thirdCarrier targetCarrier : Type}
    {sourceRing : CommutativeRingWitness sourceCarrier}
    {secondRing : CommutativeRingWitness secondCarrier}
    {thirdRing : CommutativeRingWitness thirdCarrier}
    {targetRing : CommutativeRingWitness targetCarrier}
    (thirdHom : SetoidRingHom thirdRing targetRing)
    (secondHom : SetoidRingHom secondRing thirdRing)
    (firstHom : SetoidRingHom sourceRing secondRing) :
    HomDenotesSame
      (composeRingHom (composeRingHom thirdHom secondHom) firstHom)
      (composeRingHom thirdHom (composeRingHom secondHom firstHom)) :=
  fun value =>
    targetRing.denotesSameIsReflexive
      (thirdHom.map (secondHom.map (firstHom.map value)))

/-- **Composition is a congruence for `HomDenotesSame`** — the one law that is
NOT reflexivity: it pushes the first agreement through the second hom's map and
chains with the second agreement.  Needed for the diagram to compose up to
hom-sameness. -/
theorem composeRingHomRespectsHomDenotesSame
    {sourceCarrier middleCarrier targetCarrier : Type}
    {sourceRing : CommutativeRingWitness sourceCarrier}
    {middleRing : CommutativeRingWitness middleCarrier}
    {targetRing : CommutativeRingWitness targetCarrier}
    {secondHom secondHomAlt : SetoidRingHom middleRing targetRing}
    {firstHom firstHomAlt : SetoidRingHom sourceRing middleRing}
    (secondAgrees : HomDenotesSame secondHom secondHomAlt)
    (firstAgrees : HomDenotesSame firstHom firstHomAlt) :
    HomDenotesSame (composeRingHom secondHom firstHom)
      (composeRingHom secondHomAlt firstHomAlt) :=
  fun value =>
    targetRing.denotesSameIsTransitive _ _ _
      (secondHom.respectsDenotesSame _ _ (firstAgrees value))
      (secondAgrees (firstHomAlt.map value))

end FX1Poly.ComputerAlgebra
