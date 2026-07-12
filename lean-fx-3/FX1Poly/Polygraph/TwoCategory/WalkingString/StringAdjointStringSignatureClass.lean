import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleSingletonBlockCoChain
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort

/-! # WalkingString — the ADJOINT-STRING SIGNATURE CLASS + the GENERIC determinacy keystone, instantiated at the
triple AND the quadruple (FC-4 r5, B1 + B2)

The FC-4 rounds r2/r3/r4 re-founded the width-`0` sort's atom-determination floor past its refuted `k = 2`-only
nodes, ONE colour at a time, hardcoded to the adjoint-QUADRUPLE seed (`adjointQuadrupleModeSignature`).  Each round
delivered a fixed-signature pin; a fourth colour (`k = 4`, `adjointQuintupleModeSignature`) would re-copy the same
proof shapes verbatim, unboundedly.  This file re-founds the atom-determination floor ONCE, UNIFORM in the number of
colours, by abstracting exactly the generator-identity data those pins carry into a `structure`
(`AdjointStringSignature`) and re-stating the determinacy keystone / consumers / singleton block over the class.

## The class carrier — the generator-identity data an adjoint string exposes to the sort

`AdjointStringSignature` bundles a `ModeSignature` with the FIVE generator-identity facts the width-`0` sort's
atom pin consumes.  Every field is already a machine-checked theorem at `k = 3` (the FROZEN r2/r3/r4 pins) and, at
`k = 2`, over the shipped adjoint-TRIPLE seed (proven fresh here as the four-generator analogues):

  * `twoCellUniqueOfBoundaries` — parallel generators (same dom AND cod word) are equal (r3
    `stringQuadTwoCell_unique_of_wordBoundaries`; k=2 shipped `stringTwoCell_unique_of_wordBoundaries`).
  * `generatorDomLenZeroOrTwo` — the ARITY DISCIPLINE: a generator's dom word has length `0` (cup) or `2` (cap)
    (r4 `quadAtomDomLenZeroOrTwo`).
  * `capCodZeroOfDomTwo` — the CAP-ARITY BRIDGE: a length-`2` dom forces a length-`0` cod (r3 `quadCapCodZero_ofDomTwo`).
  * `cupCodDeterminesGenerator` — the CUP-RESTRICTED COD pin: among cups (dom length `0`) the COD word determines
    the (dom, cell) pack (r2 `stringQuadTwoCell_domPack_uniqueOfCod_forCups`).  ★ THE GRAVEYARD DISCIPLINE: the
    `(dom, cod)`-pair form, carried uniformly — never the dom-only pin refuted at `k ≥ 3`.
  * `capDomDeterminesGenerator` — the CAP-RESTRICTED DOM pin: among caps (cod length `0`) the DOM word determines
    the (cod, cell) pack (r2 `stringQuadTwoCell_codPack_uniqueOfDom_forCaps`).

The class carries the `(dom, cod)`-pair pins UNIFORMLY at every `k` — at `k = 2` the dom-only forms WERE sound, but
the class never resurrects them; the `k = 2` instance supplies the SAME cup-COD / cap-DOM pins the graveyard demands
at `k ≥ 3` (so the degeneration at `k = 2` is honest, not a dom-only special case).

## The generic keystone / consumers / brick (B2), each FIRED at `k = 2` AND `k = 3`

Over an arbitrary `cls : AdjointStringSignature` the two `composePath_splitPackEqOfPrefixLengthEq`-peeled keystones
and their consumers are re-proven ONCE, consuming the class fields where the r3 proofs consumed the hardcoded pins:

  * `genericStringCupSpineAtom_eq_of_codWordReadOffs` / `genericStringCapSpineAtom_eq_of_domWordReadOffs` — the dual
    keystone (COD-word read-off for cups through `cls.cupCodDeterminesGenerator`, DOM-word read-off for caps through
    `cls.capDomDeterminesGenerator`).
  * `genericStringCupAtom_eq_of_sharedCod_sameWindow` (C3) / `genericStringCapAtom_eq_of_sharedDom_sameWindow` (C2)
    — the two atom-level consumers.
  * `genericStringChainedSingletonBlock_eq_of_readOffPair` — the `(dom, cod)` read-off-pair singleton block (r4).

Each is a GENERIC statement, so the HONESTY LAW demands generic PROOFS fired by instantiation at BOTH ends:

  * ★ `k = 2` recovery — the generic keystone / consumer at `adjointStringSignatureAtTwo` re-derives the NAMED
    shipped `k = 2` results `stringSpineAtom_eq_of_sharedCod_sameWindow` (`StringLastCupSharedTopPin`) and
    `stringCapAtom_eq_of_sharedDom_sameWindow` (`StringPureCapSpineSort`) on the nose (the shipped lemmas are named
    as the recovery TARGETS, inhabiting the same statement).
  * ★ `k = 3` recovery — the generic keystone / consumer / brick at `adjointStringSignatureAtThree` re-derives the
    FROZEN r3 keystones `stringQuadCupSpineAtom_eq_of_codWordReadOffs` / `stringQuadCapSpineAtom_eq_of_domWordReadOffs`
    and the r4 brick `stringQuadChainedSingletonBlock_eq_of_readOffPair`.
  * concrete FIRES + a NEGATIVE control on genuine `L4`-carrying `k = 3` fixtures and concrete `k = 2` cups.

## What this file does NOT do (the FLIP LAW, honest round boundary)

The census marker `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS `false`: its bill is
the FULL width-`0` quad SORT (the fueled cup-sort driver `stringMatchingPureCupSpineSortFueled` + its LOCATE /
drop-injectivity / chord-shift / valley reducer, ~3000 lines hardcoded to the triple), the r6 residual.  r5 lands the
class + the generic determinacy keystone, recording exactly that in NEW markers.  The generic width-arity bridge (the
signature-generic connectivity / drop-injectivity / chord-shift over `signature × midWidth`) and the generic fueled
LOCATE / SORT are the NAMED r6 bill.

ADDITIVE ONLY: no shipped WalkingString file is touched; the FROZEN r2/r3/r4 pins and the shipped `k = 2` keystones
are CONSUMED, never edited.  Raw Lean 4 + Init; the class fields are `cases`-`cases` / `obtain` derivations
(propext-clean per the full-enum recipe), the generic keystones are the FROZEN r3 two-split-pack derivations with the
final node routed through a class field, the recoveries are `abbrev` statements inhabited by the shipped lemma and
re-derived through the class, the fires are `rfl` / concrete atom applications;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated in
the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The class carrier -/

/-- ★★ **The adjoint-string signature class.**  A `ModeSignature` bundled with the five generator-identity facts the
width-`0` sort's atom-determination floor consumes: the parallel-generator subsingleton, the arity discipline (dom
length `0` or `2`), the cap-arity bridge (dom `2` ⇒ cod `0`), and the two restricted determinacy pins — the
CUP-restricted COD pin and the CAP-restricted DOM pin, both carried as the `(dom, cod)`-PAIR form uniformly (never the
dom-only form refuted at `k ≥ 3`).  An `AdjointStringSignature` is exactly what the generic determinacy keystone needs
to decide a width-`0` pure-cup/cap spine at any number of colours. -/
structure AdjointStringSignature where
  /-- The underlying 2-computad presenting the adjoint string. -/
  signature : ModeSignature
  /-- Parallel generators (same dom AND cod word) are equal. -/
  twoCellUniqueOfBoundaries :
    ∀ {sourceMode targetMode : signature.graph.Mode}
      {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
      (cellFirst cellSecond : signature.twoCell generatorDom generatorCod), cellFirst = cellSecond
  /-- The arity discipline: a generator's dom word has length `0` (cup) or `2` (cap). -/
  generatorDomLenZeroOrTwo :
    ∀ {sourceMode targetMode : signature.graph.Mode}
      {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
      (_generator : signature.twoCell generatorDom generatorCod),
      generatorDom.length = 0 ∨ generatorDom.length = 2
  /-- The cap-arity bridge: a length-`2` dom forces a length-`0` cod. -/
  capCodZeroOfDomTwo :
    ∀ {sourceMode targetMode : signature.graph.Mode}
      {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
      (_generator : signature.twoCell generatorDom generatorCod),
      generatorDom.length = 2 → generatorCod.length = 0
  /-- The cup-restricted COD pin: among cups the COD word determines the (dom, cell) pack. -/
  cupCodDeterminesGenerator :
    ∀ {midSource midTarget : signature.graph.Mode}
      {cupCod cupDomFirst cupDomSecond : ModalityPath signature.graph midSource midTarget}
      (cellFirst : signature.twoCell cupDomFirst cupCod) (cellSecond : signature.twoCell cupDomSecond cupCod)
      (_cupFirst : cupDomFirst.length = 0) (_cupSecond : cupDomSecond.length = 0),
      (⟨cupDomFirst, cellFirst⟩ : PSigma fun cupDom => signature.twoCell cupDom cupCod)
        = ⟨cupDomSecond, cellSecond⟩
  /-- The cap-restricted DOM pin: among caps the DOM word determines the (cod, cell) pack. -/
  capDomDeterminesGenerator :
    ∀ {midSource midTarget : signature.graph.Mode}
      {capDom capCodFirst capCodSecond : ModalityPath signature.graph midSource midTarget}
      (cellFirst : signature.twoCell capDom capCodFirst) (cellSecond : signature.twoCell capDom capCodSecond)
      (_capFirst : capCodFirst.length = 0) (_capSecond : capCodSecond.length = 0),
      (⟨capCodFirst, cellFirst⟩ : PSigma fun capCod => signature.twoCell capDom capCod)
        = ⟨capCodSecond, cellSecond⟩

/-! ## The `k = 2` instance fields — the four-generator analogues over the shipped adjoint-TRIPLE seed -/

/-- The `k = 2` arity discipline: a `StringTwoCell` dom has length `0` (the two units) or `2` (the two counits). -/
theorem stringTripleGeneratorDomLenZeroOrTwo
    {sourceMode targetMode : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph sourceMode targetMode}
    (generator : StringTwoCell generatorDom generatorCod) :
    generatorDom.length = 0 ∨ generatorDom.length = 2 := by
  cases generator <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The `k = 2` cap-arity bridge: a length-`2` dom forces a length-`0` cod. -/
theorem stringTripleCapCodZeroOfDomTwo
    {sourceMode targetMode : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph sourceMode targetMode}
    (generator : StringTwoCell generatorDom generatorCod) (domTwo : generatorDom.length = 2) :
    generatorCod.length = 0 := by
  cases generator <;> first | rfl | exact absurd domTwo (by decide)

/-- The `k = 2` cup-restricted COD pin: among cups (dom length `0`) the COD word determines the (dom, cell) pack.
The four-generator analogue of the r2 `stringQuadTwoCell_domPack_uniqueOfCod_forCups`; the `(dom, cod)`-pair form
that the graveyard demands, proven fresh over the shipped `StringTwoCell` (sound at `k = 2` because the two cup cods
`F·G`, `G·H` are distinct). -/
theorem stringTripleCupCodDeterminesGenerator
    {midSource midTarget : AdjointTripleMode}
    {cupCod cupDomFirst cupDomSecond : ModalityPath adjointTripleGraph midSource midTarget}
    (cellFirst : StringTwoCell cupDomFirst cupCod) (cellSecond : StringTwoCell cupDomSecond cupCod)
    (cupFirst : cupDomFirst.length = 0) (cupSecond : cupDomSecond.length = 0) :
    (⟨cupDomFirst, cellFirst⟩ : PSigma fun cupDom => StringTwoCell cupDom cupCod)
      = ⟨cupDomSecond, cellSecond⟩ := by
  cases cellFirst <;> cases cellSecond <;>
    first
      | rfl
      | exact absurd cupFirst (by decide)
      | exact absurd cupSecond (by decide)

/-- The `k = 2` cap-restricted DOM pin: among caps (cod length `0`) the DOM word determines the (cod, cell) pack.
The four-generator analogue of the r2 `stringQuadTwoCell_codPack_uniqueOfDom_forCaps`. -/
theorem stringTripleCapDomDeterminesGenerator
    {midSource midTarget : AdjointTripleMode}
    {capDom capCodFirst capCodSecond : ModalityPath adjointTripleGraph midSource midTarget}
    (cellFirst : StringTwoCell capDom capCodFirst) (cellSecond : StringTwoCell capDom capCodSecond)
    (capFirst : capCodFirst.length = 0) (capSecond : capCodSecond.length = 0) :
    (⟨capCodFirst, cellFirst⟩ : PSigma fun capCod => StringTwoCell capDom capCod)
      = ⟨capCodSecond, cellSecond⟩ := by
  cases cellFirst <;> cases cellSecond <;>
    first
      | rfl
      | exact absurd capFirst (by decide)
      | exact absurd capSecond (by decide)

/-! ## The two instances — the class fired at the triple (`k = 2`) AND the quadruple (`k = 3`) -/

/-- ★ **The `k = 2` instance** — the shipped adjoint-TRIPLE seed as an `AdjointStringSignature`.  The subsingleton is
the shipped `stringTwoCell_unique_of_wordBoundaries`; the arity / cap-bridge / cup-COD / cap-DOM pins are the fresh
four-generator analogues above.  This witnesses the class degenerates correctly at `k = 2`, carrying the SAME
`(dom, cod)`-pair pins uniformly (never a dom-only special case). -/
def adjointStringSignatureAtTwo : AdjointStringSignature where
  signature := adjointTripleModeSignature
  twoCellUniqueOfBoundaries := stringTwoCell_unique_of_wordBoundaries
  generatorDomLenZeroOrTwo := stringTripleGeneratorDomLenZeroOrTwo
  capCodZeroOfDomTwo := stringTripleCapCodZeroOfDomTwo
  cupCodDeterminesGenerator := stringTripleCupCodDeterminesGenerator
  capDomDeterminesGenerator := stringTripleCapDomDeterminesGenerator

/-- ★ **The `k = 3` instance** — the adjoint-QUADRUPLE seed as an `AdjointStringSignature`.  Every field is a FROZEN
r3/r4/r2 pin: the subsingleton `stringQuadTwoCell_unique_of_wordBoundaries` (r3), the arity discipline
`quadAtomDomLenZeroOrTwo` (r4), the cap-arity bridge `quadCapCodZero_ofDomTwo` (r3), the cup-COD pin
`stringQuadTwoCell_domPack_uniqueOfCod_forCups` (r2), the cap-DOM pin `stringQuadTwoCell_codPack_uniqueOfDom_forCaps`
(r2).  The three-colour instance the generic keystone is FIRED at (the genuine `k = 3` seed, fresh letter `L4`). -/
def adjointStringSignatureAtThree : AdjointStringSignature where
  signature := adjointQuadrupleModeSignature
  twoCellUniqueOfBoundaries := stringQuadTwoCell_unique_of_wordBoundaries
  generatorDomLenZeroOrTwo := quadAtomDomLenZeroOrTwo
  capCodZeroOfDomTwo := quadCapCodZero_ofDomTwo
  cupCodDeterminesGenerator := stringQuadTwoCell_domPack_uniqueOfCod_forCups
  capDomDeterminesGenerator := stringQuadTwoCell_codPack_uniqueOfDom_forCaps

/-! ## The generic dual determinacy keystone (B2) — over an arbitrary `AdjointStringSignature` -/

/-- ★★ **The generic CUP determinacy keystone.**  Two spine atoms firing at the SAME codomain boundary WORD with
equal left-context and generator-cod read-off lengths, both CUPS (`generatorDom.length = 0`), are EQUAL.  The FROZEN
r3 `stringQuadCupSpineAtom_eq_of_codWordReadOffs` proof, generic over the class: peel the left context off the shared
COD word by `composePath_splitPackEqOfPrefixLengthEq`, then the generator cod off the residual, and read the generator
AND its dom off the cod by `cls.cupCodDeterminesGenerator` — no unrestricted dom→cod pin. -/
theorem genericStringCupSpineAtom_eq_of_codWordReadOffs (cls : AdjointStringSignature)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom cls.signature overallSource overallTarget)
    (codBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (codLengthsEqual : atomFirst.generatorCod.length = atomSecond.generatorCod.length)
    (cupDomZeroFirst : atomFirst.generatorDom.length = 0)
    (cupDomZeroSecond : atomSecond.generatorDom.length = 0) :
    atomFirst = atomSecond := by
  obtain ⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, generatorCodFirst,
    generatorFirst, rightContextFirst⟩ := atomFirst
  obtain ⟨leftMidSecond, rightMidSecond, leftContextSecond, generatorDomSecond, generatorCodSecond,
    generatorSecond, rightContextSecond⟩ := atomSecond
  dsimp only at codBoundaryWordsEqual leftLengthsEqual codLengthsEqual cupDomZeroFirst cupDomZeroSecond
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    leftContextFirst (composePath generatorCodFirst rightContextFirst)
    leftContextSecond (composePath generatorCodSecond rightContextSecond)
    codBoundaryWordsEqual leftLengthsEqual
  have leftMidEqual : leftMidFirst = leftMidSecond := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _leftFstEqual innerLeftPack
  injection innerLeftPack with leftContextEqual codSuffixesEqual
  subst leftContextEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    generatorCodFirst rightContextFirst generatorCodSecond rightContextSecond
    codSuffixesEqual codLengthsEqual
  have rightMidEqual : rightMidFirst = rightMidSecond := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with generatorCodEqual rightContextEqual
  subst generatorCodEqual
  subst rightContextEqual
  exact congrArg
    (fun pack =>
      (⟨leftMidFirst, rightMidFirst, leftContextFirst, pack.fst, generatorCodFirst, pack.snd,
          rightContextFirst⟩ :
        SpineAtom cls.signature overallSource overallTarget))
    (cls.cupCodDeterminesGenerator generatorFirst generatorSecond cupDomZeroFirst cupDomZeroSecond)

/-- ★★ **The generic CAP determinacy keystone (the dual).**  Two spine atoms firing at the SAME domain boundary WORD
with equal left-context and generator-dom read-off lengths, both CAPS (`generatorCod.length = 0`), are EQUAL.  The
FROZEN r3 `stringQuadCapSpineAtom_eq_of_domWordReadOffs` proof, generic over the class: two peels off the shared DOM
word, then the generator (hence its cod) is read off the dom by `cls.capDomDeterminesGenerator`. -/
theorem genericStringCapSpineAtom_eq_of_domWordReadOffs (cls : AdjointStringSignature)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom cls.signature overallSource overallTarget)
    (domBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (domLengthsEqual : atomFirst.generatorDom.length = atomSecond.generatorDom.length)
    (capCodZeroFirst : atomFirst.generatorCod.length = 0)
    (capCodZeroSecond : atomSecond.generatorCod.length = 0) :
    atomFirst = atomSecond := by
  obtain ⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, generatorCodFirst,
    generatorFirst, rightContextFirst⟩ := atomFirst
  obtain ⟨leftMidSecond, rightMidSecond, leftContextSecond, generatorDomSecond, generatorCodSecond,
    generatorSecond, rightContextSecond⟩ := atomSecond
  dsimp only at domBoundaryWordsEqual leftLengthsEqual domLengthsEqual capCodZeroFirst capCodZeroSecond
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    leftContextFirst (composePath generatorDomFirst rightContextFirst)
    leftContextSecond (composePath generatorDomSecond rightContextSecond)
    domBoundaryWordsEqual leftLengthsEqual
  have leftMidEqual : leftMidFirst = leftMidSecond := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _leftFstEqual innerLeftPack
  injection innerLeftPack with leftContextEqual suffixesEqual
  subst leftContextEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    generatorDomFirst rightContextFirst generatorDomSecond rightContextSecond
    suffixesEqual domLengthsEqual
  have rightMidEqual : rightMidFirst = rightMidSecond := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with generatorDomEqual rightContextEqual
  subst generatorDomEqual
  subst rightContextEqual
  exact congrArg
    (fun pack =>
      (⟨leftMidFirst, rightMidFirst, leftContextFirst, generatorDomFirst, pack.fst, pack.snd,
          rightContextFirst⟩ :
        SpineAtom cls.signature overallSource overallTarget))
    (cls.capDomDeterminesGenerator generatorFirst generatorSecond capCodZeroFirst capCodZeroSecond)

/-! ## The generic atom-level consumers (C2 / C3) -/

/-- ★ **The generic cap shared-DOM consumer (C2).**  Two CAP atoms (dom length `2`) at the same DOM boundary word and
window are EQUAL: the cap-arity bridge supplies the length-`0` cod, and the generic cap keystone concludes.  The
class-generic re-founding of the r3 `stringQuadCapAtom_eq_of_sharedDom_sameWindow`. -/
theorem genericStringCapAtom_eq_of_sharedDom_sameWindow (cls : AdjointStringSignature)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (capFirst capSecond : SpineAtom cls.signature overallSource overallTarget)
    (domBoundaryWordsEqual :
      composePath capFirst.leftContext (composePath capFirst.generatorDom capFirst.rightContext)
        = composePath capSecond.leftContext
            (composePath capSecond.generatorDom capSecond.rightContext))
    (windowEqual : capFirst.leftContext.length = capSecond.leftContext.length)
    (capDomFirst : capFirst.generatorDom.length = 2)
    (capDomSecond : capSecond.generatorDom.length = 2) :
    capFirst = capSecond :=
  genericStringCapSpineAtom_eq_of_domWordReadOffs cls capFirst capSecond domBoundaryWordsEqual windowEqual
    (capDomFirst.trans capDomSecond.symm)
    (cls.capCodZeroOfDomTwo capFirst.generator capDomFirst)
    (cls.capCodZeroOfDomTwo capSecond.generator capDomSecond)

/-- ★ **The generic cup shared-COD consumer (C3, DIRECT).**  Two width-`0` CUP atoms sharing a COD boundary word at
the same window are EQUAL: the dom lengths are `0` directly, so the generic cup keystone concludes — no cod→dom
adapter (that walks the refuted direction).  The class-generic re-founding of the r3
`stringQuadCupAtom_eq_of_sharedCod_sameWindow`. -/
theorem genericStringCupAtom_eq_of_sharedCod_sameWindow (cls : AdjointStringSignature)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (cupFirst cupSecond : SpineAtom cls.signature overallSource overallTarget)
    (codBoundaryWordsEqual :
      composePath cupFirst.leftContext (composePath cupFirst.generatorCod cupFirst.rightContext)
        = composePath cupSecond.leftContext
            (composePath cupSecond.generatorCod cupSecond.rightContext))
    (windowEqual : cupFirst.leftContext.length = cupSecond.leftContext.length)
    (cupCodLengthsEqual : cupFirst.generatorCod.length = cupSecond.generatorCod.length)
    (cupDomZeroFirst : cupFirst.generatorDom.length = 0)
    (cupDomZeroSecond : cupSecond.generatorDom.length = 0) :
    cupFirst = cupSecond :=
  genericStringCupSpineAtom_eq_of_codWordReadOffs cls cupFirst cupSecond codBoundaryWordsEqual windowEqual
    cupCodLengthsEqual cupDomZeroFirst cupDomZeroSecond

/-! ## The generic singleton-block `(dom, cod)` read-off-pair brick -/

/-- ★★ **The generic singleton-block `(dom, cod)` read-off-pair brick.**  Two singleton spines that DOM-chain from the
same bottom word, COD-co-chain equally (`spineListTopWord`), and read off equal left-context / generator-dom /
generator-cod lengths, are EQUAL singletons.  The FROZEN r4 `stringQuadChainedSingletonBlock_eq_of_readOffPair` proof,
generic over the class: the DOM chains give the shared dom boundary word, `topWordEq` reduces to the shared cod
boundary word, and `cls.generatorDomLenZeroOrTwo` dispatches — cups through C3, caps through C2. -/
theorem genericStringChainedSingletonBlock_eq_of_readOffPair (cls : AdjointStringSignature)
    {overallSource overallTarget : cls.signature.graph.Mode}
    {bottomWord : ModalityPath cls.signature.graph overallSource overallTarget}
    {atomFirst atomSecond : SpineAtom cls.signature overallSource overallTarget}
    (domChainedFirst : SpineBoundaryWordChained bottomWord [atomFirst])
    (domChainedSecond : SpineBoundaryWordChained bottomWord [atomSecond])
    (topWordEq : spineListTopWord bottomWord [atomFirst] = spineListTopWord bottomWord [atomSecond])
    (leftLengthsEqual : atomFirst.leftContext.length = atomSecond.leftContext.length)
    (domLengthsEqual : atomFirst.generatorDom.length = atomSecond.generatorDom.length)
    (codLengthsEqual : atomFirst.generatorCod.length = atomSecond.generatorCod.length) :
    [atomFirst] = [atomSecond] := by
  obtain ⟨firstDomFires, _firstTailChained⟩ := spineBoundaryWordChained_tail domChainedFirst
  obtain ⟨secondDomFires, _secondTailChained⟩ := spineBoundaryWordChained_tail domChainedSecond
  have domBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext) :=
    firstDomFires.symm.trans secondDomFires
  have codBoundaryWordsEqual :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext) := by
    dsimp only [spineListTopWord] at topWordEq
    exact topWordEq
  cases cls.generatorDomLenZeroOrTwo atomFirst.generator with
  | inl firstDomZero =>
      have secondDomZero : atomSecond.generatorDom.length = 0 := domLengthsEqual.symm.trans firstDomZero
      exact congrArg (fun atom => [atom])
        (genericStringCupAtom_eq_of_sharedCod_sameWindow cls atomFirst atomSecond codBoundaryWordsEqual
          leftLengthsEqual codLengthsEqual firstDomZero secondDomZero)
  | inr firstDomTwo =>
      have secondDomTwo : atomSecond.generatorDom.length = 2 := domLengthsEqual.symm.trans firstDomTwo
      exact congrArg (fun atom => [atom])
        (genericStringCapAtom_eq_of_sharedDom_sameWindow cls atomFirst atomSecond domBoundaryWordsEqual
          leftLengthsEqual firstDomTwo secondDomTwo)

/-! ## `k = 2` RECOVERY — the generic keystone / consumer re-derives the NAMED shipped `k = 2` results -/

/-- The statement of the shipped `k = 2` shared-top last-cup pin, named as the recovery TARGET. -/
abbrev StringSharedCodCupPinStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext) →
    atomFirst.leftContext.length = atomSecond.leftContext.length →
    atomFirst.generatorCod.length = atomSecond.generatorCod.length →
    atomFirst.generatorDom.length = 0 → atomSecond.generatorDom.length = 0 →
    atomFirst = atomSecond

/-- ★ **The shipped `k = 2` cup pin inhabits the named statement** — `stringSpineAtom_eq_of_sharedCod_sameWindow`
(`StringLastCupSharedTopPin`) IS the recovery target. -/
theorem stringSharedCodCupPin_shippedInhabitant : StringSharedCodCupPinStatement :=
  @stringSpineAtom_eq_of_sharedCod_sameWindow

/-- ★★ **The generic CUP keystone, at `k = 2`, RE-DERIVES the shipped cup pin.**  Instantiating
`genericStringCupSpineAtom_eq_of_codWordReadOffs` at `adjointStringSignatureAtTwo` reproduces
`stringSpineAtom_eq_of_sharedCod_sameWindow` on the nose — the genuine consumption check at `k = 2`. -/
theorem stringSharedCodCupPin_viaGenericClassAtTwo : StringSharedCodCupPinStatement :=
  fun atomFirst atomSecond codBoundaryWordsEqual leftLengthsEqual codLengthsEqual domZeroFirst domZeroSecond =>
    genericStringCupSpineAtom_eq_of_codWordReadOffs adjointStringSignatureAtTwo
      atomFirst atomSecond codBoundaryWordsEqual leftLengthsEqual codLengthsEqual domZeroFirst domZeroSecond

/-- The statement of the shipped `k = 2` cap shared-DOM pin, named as the recovery TARGET. -/
abbrev StringSharedDomCapPinStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode}
    (capFirst capSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    composePath capFirst.leftContext (composePath capFirst.generatorDom capFirst.rightContext)
        = composePath capSecond.leftContext
            (composePath capSecond.generatorDom capSecond.rightContext) →
    capFirst.leftContext.length = capSecond.leftContext.length →
    capFirst.generatorDom.length = 2 → capSecond.generatorDom.length = 2 →
    capFirst = capSecond

/-- ★ **The shipped `k = 2` cap pin inhabits the named statement** — `stringCapAtom_eq_of_sharedDom_sameWindow`
(`StringPureCapSpineSort`) IS the recovery target. -/
theorem stringSharedDomCapPin_shippedInhabitant : StringSharedDomCapPinStatement :=
  @stringCapAtom_eq_of_sharedDom_sameWindow

/-- ★★ **The generic cap consumer, at `k = 2`, RE-DERIVES the shipped cap pin.** -/
theorem stringSharedDomCapPin_viaGenericClassAtTwo : StringSharedDomCapPinStatement :=
  fun capFirst capSecond domBoundaryWordsEqual windowEqual capDomFirst capDomSecond =>
    genericStringCapAtom_eq_of_sharedDom_sameWindow adjointStringSignatureAtTwo
      capFirst capSecond domBoundaryWordsEqual windowEqual capDomFirst capDomSecond

/-! ## `k = 3` RECOVERY — the generic keystone / consumer / brick re-derives the FROZEN r3/r4 results -/

/-- The statement of the FROZEN r3 CUP keystone, named as the recovery TARGET. -/
abbrev StringQuadCupKeystoneStatement : Prop :=
  ∀ {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget),
    composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorCod atomSecond.rightContext) →
    atomFirst.leftContext.length = atomSecond.leftContext.length →
    atomFirst.generatorCod.length = atomSecond.generatorCod.length →
    atomFirst.generatorDom.length = 0 → atomSecond.generatorDom.length = 0 →
    atomFirst = atomSecond

/-- ★ **The FROZEN r3 CUP keystone inhabits the named statement.** -/
theorem stringQuadCupKeystone_shippedInhabitant : StringQuadCupKeystoneStatement :=
  @stringQuadCupSpineAtom_eq_of_codWordReadOffs

/-- ★★ **The generic CUP keystone, at `k = 3`, RE-DERIVES the FROZEN r3 CUP keystone.** -/
theorem stringQuadCupKeystone_viaGenericClassAtThree : StringQuadCupKeystoneStatement :=
  fun atomFirst atomSecond codBoundaryWordsEqual leftLengthsEqual codLengthsEqual cupDomZeroFirst cupDomZeroSecond =>
    genericStringCupSpineAtom_eq_of_codWordReadOffs adjointStringSignatureAtThree
      atomFirst atomSecond codBoundaryWordsEqual leftLengthsEqual codLengthsEqual cupDomZeroFirst cupDomZeroSecond

/-- The statement of the FROZEN r3 CAP keystone, named as the recovery TARGET. -/
abbrev StringQuadCapKeystoneStatement : Prop :=
  ∀ {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget),
    composePath atomFirst.leftContext (composePath atomFirst.generatorDom atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext) →
    atomFirst.leftContext.length = atomSecond.leftContext.length →
    atomFirst.generatorDom.length = atomSecond.generatorDom.length →
    atomFirst.generatorCod.length = 0 → atomSecond.generatorCod.length = 0 →
    atomFirst = atomSecond

/-- ★ **The FROZEN r3 CAP keystone inhabits the named statement.** -/
theorem stringQuadCapKeystone_shippedInhabitant : StringQuadCapKeystoneStatement :=
  @stringQuadCapSpineAtom_eq_of_domWordReadOffs

/-- ★★ **The generic CAP keystone, at `k = 3`, RE-DERIVES the FROZEN r3 CAP keystone.** -/
theorem stringQuadCapKeystone_viaGenericClassAtThree : StringQuadCapKeystoneStatement :=
  fun atomFirst atomSecond domBoundaryWordsEqual leftLengthsEqual domLengthsEqual capCodZeroFirst capCodZeroSecond =>
    genericStringCapSpineAtom_eq_of_domWordReadOffs adjointStringSignatureAtThree
      atomFirst atomSecond domBoundaryWordsEqual leftLengthsEqual domLengthsEqual capCodZeroFirst capCodZeroSecond

/-- The statement of the FROZEN r4 singleton-block brick, named as the recovery TARGET. -/
abbrev StringQuadSingletonBlockStatement : Prop :=
  ∀ {overallSource overallTarget : adjointQuadrupleGraph.Mode}
    {bottomWord : ModalityPath adjointQuadrupleGraph overallSource overallTarget}
    {atomFirst atomSecond : SpineAtom adjointQuadrupleModeSignature overallSource overallTarget},
    SpineBoundaryWordChained bottomWord [atomFirst] →
    SpineBoundaryWordChained bottomWord [atomSecond] →
    spineListTopWord bottomWord [atomFirst] = spineListTopWord bottomWord [atomSecond] →
    atomFirst.leftContext.length = atomSecond.leftContext.length →
    atomFirst.generatorDom.length = atomSecond.generatorDom.length →
    atomFirst.generatorCod.length = atomSecond.generatorCod.length →
    [atomFirst] = [atomSecond]

/-- ★ **The FROZEN r4 singleton-block brick inhabits the named statement.** -/
theorem stringQuadSingletonBlock_shippedInhabitant : StringQuadSingletonBlockStatement :=
  @stringQuadChainedSingletonBlock_eq_of_readOffPair

/-- ★★ **The generic singleton-block brick, at `k = 3`, RE-DERIVES the FROZEN r4 brick.** -/
theorem stringQuadSingletonBlock_viaGenericClassAtThree : StringQuadSingletonBlockStatement :=
  fun domChainedFirst domChainedSecond topWordEq leftLengthsEqual domLengthsEqual codLengthsEqual =>
    genericStringChainedSingletonBlock_eq_of_readOffPair adjointStringSignatureAtThree
      domChainedFirst domChainedSecond topWordEq leftLengthsEqual domLengthsEqual codLengthsEqual

/-! ## Concrete FIRES — non-vacuity at `k = 2` and `k = 3` -/

/-- A concrete `k = 2` CUP atom: the lower unit `η : id_base ⇒ F·G` at `base→base`, empty whiskering. -/
def stringTripleCupAtomBase :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base where
  leftMidMode := AdjointTripleMode.base
  rightMidMode := AdjointTripleMode.base
  leftContext := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base
  generatorDom := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base
  generatorCod := stringFG
  generator := StringTwoCell.unitLower
  rightContext := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base

/-- A concrete `k = 2` CAP atom: the lower counit `ε : G·F ⇒ id_tip` at `tip→tip`, empty whiskering. -/
def stringTripleCapAtomTip :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip where
  leftMidMode := AdjointTripleMode.tip
  rightMidMode := AdjointTripleMode.tip
  leftContext := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip
  generatorDom := stringGF
  generatorCod := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip
  generator := StringTwoCell.counitLower
  rightContext := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip

/-- ★ **The generic CUP keystone FIRES at `k = 2` on a concrete lower cup** (non-vacuity: the hypotheses are inhabited
by a real `F·G` cup). -/
theorem genericCupKeystone_firesAtTwoOnConcreteCup :
    stringTripleCupAtomBase = stringTripleCupAtomBase :=
  genericStringCupSpineAtom_eq_of_codWordReadOffs adjointStringSignatureAtTwo
    stringTripleCupAtomBase stringTripleCupAtomBase rfl rfl rfl rfl rfl

/-- ★ **The generic CAP consumer FIRES at `k = 2` on a concrete lower cap** (non-vacuity by a real `G·F` cap). -/
theorem genericCapConsumer_firesAtTwoOnConcreteCap :
    stringTripleCapAtomTip = stringTripleCapAtomTip :=
  genericStringCapAtom_eq_of_sharedDom_sameWindow adjointStringSignatureAtTwo
    stringTripleCapAtomTip stringTripleCapAtomTip rfl rfl rfl rfl

/-- ★ **The generic CUP keystone FIRES at `k = 3` on the fresh `L4`-carrying cup `η3`** (cod `[3, 4]`). -/
theorem genericCupKeystone_firesAtThreeOnFreshL4Cup :
    quadCupAtomBaseFresh = quadCupAtomBaseFresh :=
  genericStringCupSpineAtom_eq_of_codWordReadOffs adjointStringSignatureAtThree
    quadCupAtomBaseFresh quadCupAtomBaseFresh rfl rfl rfl rfl rfl

/-- ★ **The generic CAP keystone FIRES at `k = 3` on the fresh `L4`-carrying cap `ε3`** (dom `[4, 3]`). -/
theorem genericCapKeystone_firesAtThreeOnFreshL4Cap :
    quadCapAtomTipFresh = quadCapAtomTipFresh :=
  genericStringCapSpineAtom_eq_of_domWordReadOffs adjointStringSignatureAtThree
    quadCapAtomTipFresh quadCapAtomTipFresh rfl rfl rfl rfl rfl

/-- ★ **The generic singleton-block brick FIRES at `k = 3` on the fresh `L4`-carrying cup `η3`.** -/
theorem genericSingletonBlock_firesAtThreeOnFreshL4Cup :
    ([quadCupAtomBaseFresh] :
        List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base))
      = [quadCupAtomBaseFresh] :=
  genericStringChainedSingletonBlock_eq_of_readOffPair adjointStringSignatureAtThree
    quadCupAtomBaseFresh_domChained quadCupAtomBaseFresh_domChained rfl rfl rfl rfl

/-! ## NEGATIVE control — the generic brick distinguishes the `η1` / `η3` pair (COD co-chain load-bearing) -/

/-- ★ **The generic brick correctly DECLINES to equate the `η1` / `η3` pair.**  The two cups share dom `nil` (the
refuted dom-only hypotheses) but their COD co-chain words `[1, 2]` (`η1`) and `[3, 4]` (`η3`) DIFFER, so the generic
brick's `topWordEq` is unsatisfiable for the pair — the class carries the `(dom, cod)` pair, never the dom-only form.
Pinned as the standing distinction (`quadCupSingletonTopWords_differ` from r4). -/
theorem genericBrick_declinesOnDistinctCupPair :
    quadIndexWord
        (spineListTopWord
          (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBase])
      ≠ quadIndexWord
          (spineListTopWord
            (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) [quadCupAtomBaseFresh]) :=
  quadCupSingletonTopWords_differ

/-! ## Road markers -/

/-- **★ ESTABLISHED — the adjoint-string signature class is shipped (FC-4 r5, B1).**  `AdjointStringSignature`
bundles a `ModeSignature` with the five generator-identity facts the width-`0` sort consumes (the subsingleton, the
arity discipline, the cap-arity bridge, and the two restricted `(dom, cod)`-pair determinacy pins), instantiated at
BOTH the shipped adjoint-TRIPLE seed (`adjointStringSignatureAtTwo`, `k = 2`) — the four-generator analogues proven
fresh, the subsingleton the shipped `stringTwoCell_unique_of_wordBoundaries` — AND the adjoint-QUADRUPLE seed
(`adjointStringSignatureAtThree`, `k = 3`) — every field a FROZEN r2/r3/r4 pin.  The class carries the `(dom, cod)`
pins uniformly; the `k = 2` instance never resurrects the dom-only form (the graveyard discipline).  `= true`. -/
def fxString_hasAdjointStringSignatureClass : Bool := true

/-- **★ ESTABLISHED — the GENERIC determinacy keystone is machine-checked and FIRED at `k = 2` AND `k = 3` (FC-4 r5,
B2).**  Over an arbitrary `AdjointStringSignature` the dual keystone
(`genericStringCupSpineAtom_eq_of_codWordReadOffs` / `genericStringCapSpineAtom_eq_of_domWordReadOffs`), its two
consumers (`genericStringCupAtom_eq_of_sharedCod_sameWindow` C3 / `genericStringCapAtom_eq_of_sharedDom_sameWindow`
C2), and the `(dom, cod)` read-off-pair singleton block (`genericStringChainedSingletonBlock_eq_of_readOffPair`) are
re-proven ONCE, consuming the class fields where the FROZEN r3/r4 proofs consumed the hardcoded pins.  The HONESTY LAW
discharged: each generic statement is instantiated at `k = 2` recovering the NAMED shipped
`stringSpineAtom_eq_of_sharedCod_sameWindow` / `stringCapAtom_eq_of_sharedDom_sameWindow` (via the `..._shippedInhabitant`
/ `..._viaGenericClassAtTwo` pair) AND at `k = 3` recovering the FROZEN r3 keystones + the r4 brick (via the
`..._viaGenericClassAtThree` pair), with concrete FIRES on real `k = 2` cups / caps and the `k = 3` `L4`-carrying
fixtures plus the `η1`/`η3` negative control.

  What this marker does NOT close: the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` — its bill is the FULL width-`0` quad SORT (the fueled cup-sort
  driver + its generic width-arity bridge / LOCATE / chord-shift, the r6 residual), which the class is the on-ramp
  for (the generic connectivity engine will consume `generatorDomLenZeroOrTwo`), not the sort itself.  `= true`. -/
def fxString_hasGenericStringDeterminacyKeystone : Bool := true

end FX1Poly.Polygraph
