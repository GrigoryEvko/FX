import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedRelationFamily
import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctorDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.Witness

/-! # Polygraph/TwoCategory/Amalgam/ModeAdmit — the mode-theory ADMISSION GATE (MODE-ADMIT r1, #2214)

`SaturatedRelationFamily.lean` (RELFAM r1, #2213) shipped the packaging record: a family bundles a presentation,
a law relation, a walker convertibility, an iff-bridge, and a walker decider, and `SaturatedRelationFamily.decider`
derives the generic-interface `DecidableSaturatedConvForRel` from those five fields with NO further proof.  The
three registered instances (`monadRelationFamily` / `idempotentRelationFamily` / `involutionRelationFamily`) each
carry a decider ALREADY packaged at the composable interface.

MODE-ADMIT is the CONSUMPTION gate on top of that library: a `registry : List RegisteredModule` of decided
walkers, and admission functions that SCAN it and hand back the pre-packaged decider — the "zero new proofs at the
call site" claim made literal.  A mode theory presented to the gate INHERITS its word-problem decidability from a
registered walker without the caller discharging any obligation.

## The two SOUND, hypothesis-free admission tiers (both flip `fxModeAdmit_hasRegistryGate`)

  * **Tier A — named/family lookup (`admitByName`).**  Look a registered walker up by name; get its packaged
    `SaturatedRelationFamily` and thus its `.decider`.  Zero transport, zero obligations — the returned decider IS
    the registered family's own.  This is the tier that SEPARATES: `admitByName "walking monad"` yields
    `monadRelationFamily`, whose Delta monotone-map decider gives `isFalse` on the two unit faces.

  * **Tier B — thin renaming (`admitModeTheory`, the matcher gate).**  A candidate `ModeComputad` is matched
    against the registry's THIN references by a bijective RENAMING of the presentation fingerprint
    (`isThinPresentationMatch`, a tiny decidable permutation search over the generator lists, sizes 1-3, plain
    `Bool` — NO `native_decide`).  When the candidate is recognised as a renaming of a registered thin walker AND
    is itself thin (`twoCellGenerators.length = 0`), it is admitted with the locally-thin decider
    `saturatedThinDeciderForAnyRel` — SOUND because thinness (no generating 2-cells) is a STRUCTURAL property the
    bijection preserves, so no `mapCellAlong` transport is needed.  A genuinely-distinct fingerprint (generators
    permuted) is admitted and COMPUTES (`admitModeTheory thinRenamedComputad` returns `some decider`; the decider
    decides `isTrue` on a real parallel pair by `rfl`).

## The three named walls (each an honest `false` marker), NOT overclaimed

  * **`fxModeAdmit_hasRenamingDeciderTransport = false` — the NON-thin renaming DECIDER-REUSE leg.**  The FORWARD
    soundness lift is shipped and reused (`mapCellAlong_preservesConvUnconditional`).  Reusing a registered
    decider on a NON-thin renamed presentation needs the BACKWARD direction: an inverse `ComputadMorphismTwo` plus
    the path round-trip `mapPath backward (mapPath forward oneCell) = oneCell`.  That round-trip does NOT hold
    definitionally — `mapPath` is only PROPOSITIONALLY a monoid homomorphism (`mapPath_composePath` is a `congrArg`
    cons-induction, not `rfl`) — so it forces a `castBoundary` / `HEq` reconciliation at every whisker cell.  The
    decider-reuse leg is therefore CONDITIONAL on a supplied transport witness carrying that round-trip; the marker
    stays `false` and the honest gate ships its thin path instead.

  * **`fxModeAdmit_hasDataFingerprintAdmission = false` — automatic DATA-FINGERPRINT admission is UNSOUND today.**
    `monadComputad` and the walking-idempotent-monad walker have the SAME presentation fingerprint (both over the
    single-object one-endo-generator computad, differing ONLY in the `Prop`-valued law relation `MonadLawRel`
    vs `IdempotentLawRel`, which `ModeComputad` does NOT store).  A signature-DATA fingerprint therefore CONFLATES
    the walking monad (separating) with the walking idempotent monad (total) — keying admission on it alone would
    return the wrong decider.  Soundly keying a NON-thin registry requires reflecting the law ROWS as data (an
    untyped `RawCellData` layer), the named future work.  The Tier B matcher is used ONLY where it is sound: the
    THIN fragment, whose empty law relation removes the ambiguity.

  * The bespoke-vs-reconstructed reseat (`fxMode_hasDecidableTwoCellEquality`, fib-3-coupled) is why the
    registered monad/idempotent deciders — living over the BESPOKE `monadModeSignature` — cannot be transported
    through the `mapCellAlong` (computad) machinery at all; Tier A reaches them by NAME instead.

## Literature grounding (per the workflow literature stage)

Word-problem decidability is an invariant of the presented structure, transported by a presentation isomorphism
(Tietze).  Bijective renaming is exactly the T3 (free-group-automorphism) layer for which "it is easy to obtain an
explicit isomorphism and its inverse" (arxiv 1205.0157) and for which the MATCH is a finite decidable search over
tiny generator lists — unlike the general Tietze/isomorphism problem, undecidable.  This mirrors the SMT-LIB
pattern (a NAMED registry / logic lookup, "the most specific logic name possible", not inference — cvc5 theories
tutorial; smt-lib logics catalog) and Lean instance resolution (structural pattern-match delivers a term already
carrying the `Decidable` data — no proof obligation at the call site — lean4.pdf).  The named r2 frontier is
Tietze-closure matching (bounded relator/generator moves), strictly stronger and strictly harder to decide.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## P1 — the presentation fingerprint carrier + its hand-rolled DecidableEq -/

/-- A **flattened 2-cell generator** — the first-order, NON-dependent reflection of a `ComputadTwoGen`: the
`(src, tgt)` endpoint modes and the two boundary words, all recorded as bare `Nat` indices (the `Fin` values
projected).  Non-dependent so its `DecidableEq` is a clean structural fold with no index reconciliation (the
recon's propext-leak risk on indexed `DecidableEq`). -/
structure FlatTwoGen where
  /-- The source mode, as a `Nat` index. -/
  src : Nat
  /-- The target mode, as a `Nat` index. -/
  tgt : Nat
  /-- The source boundary word, as `Nat` 1-generator indices. -/
  lhs : List Nat
  /-- The target boundary word, as `Nat` 1-generator indices. -/
  rhs : List Nat

/-- Hand-rolled structural `DecidableEq` for `FlatTwoGen` — four field comparisons (`Nat` / `List Nat`, both Init
decidable), the mismatch cases projecting the offending field with `congrArg`.  Written by hand (not `deriving`) so
the zero-axiom audit is guaranteed propext-free per the memory recipe. -/
def FlatTwoGen.decEq (first second : FlatTwoGen) : Decidable (first = second) :=
  match first, second with
  | ⟨srcFirst, tgtFirst, lhsFirst, rhsFirst⟩, ⟨srcSecond, tgtSecond, lhsSecond, rhsSecond⟩ =>
    if hsrc : srcFirst = srcSecond then
      if htgt : tgtFirst = tgtSecond then
        if hlhs : lhsFirst = lhsSecond then
          if hrhs : rhsFirst = rhsSecond then
            isTrue (by subst hsrc; subst htgt; subst hlhs; subst hrhs; rfl)
          else isFalse (fun equalGen => hrhs (congrArg FlatTwoGen.rhs equalGen))
        else isFalse (fun equalGen => hlhs (congrArg FlatTwoGen.lhs equalGen))
      else isFalse (fun equalGen => htgt (congrArg FlatTwoGen.tgt equalGen))
    else isFalse (fun equalGen => hsrc (congrArg FlatTwoGen.src equalGen))

instance instDecidableEqFlatTwoGen : DecidableEq FlatTwoGen := FlatTwoGen.decEq

/-- A **presentation fingerprint** — the flattened, non-dependent image of a `ModeComputad`: a mode COUNT, a
`List` of 1-generator endpoint pairs (bare `Nat`s), and a `List` of flattened 2-generators.  The registry key and
the matcher's search domain.  DecidableEq is a clean structural fold (`Nat` / `List (Nat x Nat)` / `List
FlatTwoGen`, the last through the hand-rolled `FlatTwoGen` instance). -/
structure PresentationData where
  /-- The object count. -/
  modeCount : Nat
  /-- The 1-generator endpoint pairs, as `Nat` mode indices. -/
  modalityGenerators : List (Nat × Nat)
  /-- The flattened 2-generators. -/
  twoCellGenerators : List FlatTwoGen

/-- Hand-rolled structural `DecidableEq` for `PresentationData` — three field comparisons, the mismatch cases
projecting with `congrArg`.  Propext-free by construction. -/
def PresentationData.decEq (first second : PresentationData) : Decidable (first = second) :=
  match first, second with
  | ⟨countFirst, oneGenFirst, twoGenFirst⟩, ⟨countSecond, oneGenSecond, twoGenSecond⟩ =>
    if hcount : countFirst = countSecond then
      if hone : oneGenFirst = oneGenSecond then
        if htwo : twoGenFirst = twoGenSecond then
          isTrue (by subst hcount; subst hone; subst htwo; rfl)
        else isFalse (fun equalData => htwo (congrArg PresentationData.twoCellGenerators equalData))
      else isFalse (fun equalData => hone (congrArg PresentationData.modalityGenerators equalData))
    else isFalse (fun equalData => hcount (congrArg PresentationData.modeCount equalData))

instance instDecidableEqPresentationData : DecidableEq PresentationData := PresentationData.decEq

/-! ## P1 — the fingerprint extraction from a `ModeComputad` -/

/-- **Flatten a `ComputadTwoGen`** — project every `Fin` value to a bare `Nat`.  The non-dependent reflection of
one generating 2-cell. -/
def flattenTwoGen {modeCount : Nat} {modalityGenerators : List (Fin modeCount × Fin modeCount)}
    (generator : ComputadTwoGen modeCount modalityGenerators) : FlatTwoGen :=
  { src := generator.src.val
    tgt := generator.tgt.val
    lhs := generator.lhs.map (fun letter => letter.val)
    rhs := generator.rhs.map (fun letter => letter.val) }

/-- ★ **The fingerprint of a `ModeComputad`** — flatten the mode count and both generator lists to `Nat` indices.
The registry key.  Total, structural, zero-axiom.  Declared into `ModeComputad`'s own (`_root_`) namespace so
dot-notation `computad.toPresentationData` resolves. -/
def _root_.FX1Poly.Polygraph.ModeComputad.toPresentationData (computad : ModeComputad) : PresentationData :=
  { modeCount := computad.modeCount
    modalityGenerators :=
      computad.modalityGenerators.map (fun endpoints => (endpoints.1.val, endpoints.2.val))
    twoCellGenerators := computad.twoCellGenerators.map flattenTwoGen }

/-- The walking-involution fingerprint (one mode, one endo-1-generator, NO 2-generators — thin). -/
def involutionPresentation : PresentationData := involutionComputad.toPresentationData

/-- The walking-monad fingerprint (one mode, one endo-1-generator, TWO 2-generators `eta` / `mu`).  Honesty note:
the walking-IDEMPOTENT-monad walker has the SAME fingerprint (same computad; the laws differ, and laws are not
stored on `ModeComputad`) — the collision that makes signature-DATA admission unsound (see
`fxModeAdmit_hasDataFingerprintAdmission = false`). -/
def monadPresentation : PresentationData := monadComputad.toPresentationData

/-- ★ **The fingerprints genuinely differ** — the involution's and the monad's presentations are distinct
`PresentationData` (they differ in the 2-generator count: `0` vs `2`), drawn propext-free by projecting the
`twoCellGenerators` length and `Nat.noConfusion`.  Non-vacuity: the fingerprint carrier separates distinct
computads. -/
theorem involutionPresentation_ne_monadPresentation : involutionPresentation ≠ monadPresentation :=
  fun equalFingerprint =>
    absurd
      (show (0 : Nat) = 2 from
        congrArg (fun presentation => presentation.twoCellGenerators.length) equalFingerprint)
      (fun contradiction => Nat.noConfusion contradiction)

/-! ## P3 — the decidable renaming matcher (tiny bijection enumeration) -/

/-- **Erase the first occurrence of an endpoint pair from a list** — structural on the list; `Nat` beq on both
components (propext-free).  The multiset-difference step underlying the permutation check. -/
def erasePair (target : Nat × Nat) : List (Nat × Nat) → Option (List (Nat × Nat))
  | [] => none
  | head :: rest =>
      if head.1 == target.1 && head.2 == target.2 then some rest
      else (erasePair target rest).map (fun remaining => head :: remaining)

/-- **Decidable list-permutation on endpoint pairs** — structural on the FIRST list: peel each pair, erase its
first occurrence from the second list, recurse; both empty means a permutation.  A tiny bounded search (generator
lists have sizes 1-3), plain `Bool`, NO `native_decide`.  This is the bijection-on-1-generators certification that
a candidate presentation is a RENAMING of a reference. -/
def isPermutationOfPairs : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], others => others.isEmpty
  | first :: rest, others =>
      match erasePair first others with
      | none => false
      | some remaining => isPermutationOfPairs rest remaining

/-- ★ **The thin renaming match predicate** — a candidate fingerprint matches a reference when they have the SAME
mode count, BOTH have no 2-generators (thin), and the 1-generator endpoint lists are a permutation of each other
(the endpoint-preserving bijection).  Restricted to the thin fragment, where the empty law relation removes the
law-row ambiguity that makes general signature-data matching unsound. -/
def isThinPresentationMatch (candidate reference : PresentationData) : Bool :=
  (candidate.modeCount == reference.modeCount)
    && candidate.twoCellGenerators.isEmpty
    && reference.twoCellGenerators.isEmpty
    && isPermutationOfPairs candidate.modalityGenerators reference.modalityGenerators

/-! ## P4 — the thin reference walkers, the registry, and the admission functions -/

/-- **A thin computad's relation family** — the family constructor for any no-2-generator computad: signature
`toModeSignature`, empty law relation, walker conv IS the generic carrier (bridge `Iff.rfl`), decider the shipped
locally-thin decision.  The same shape as `involutionRelationFamily`, generic over the computad. -/
def thinComputadFamily (computad : ModeComputad)
    (thin : computad.twoCellGenerators.length = 0) : SaturatedRelationFamily where
  signature := computad.toModeSignature
  baseRel := emptyCellRel computad.toModeSignature
  walkerConv := fun cellAlpha cellBeta =>
    SaturatedConvOver computad.toModeSignature (emptyCellRel computad.toModeSignature) cellAlpha cellBeta
  walkerIffGeneric := fun _ _ => Iff.rfl
  walkerDecider := saturatedLocallyThinDecider (noGen_of_twoGenLenZero thin)

/-- A **thin reference computad** — two modes, two endpoint-distinct 1-generators (`left : 0 -> 1`,
`right : 1 -> 0`), NO 2-generators.  The registered thin walker against which a permuted copy is matched.  Two
generators (not one) so the renaming bijection is GENUINELY non-trivial (a permutation, not the identity). -/
def thinReferenceComputad : ModeComputad where
  modeCount := 2
  modalityGenerators := [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators := []

/-- The thin reference walker as a relation family. -/
def thinReferenceFamily : SaturatedRelationFamily := thinComputadFamily thinReferenceComputad rfl

/-- A **registered module** — a named decided walker: its display name, its presentation fingerprint (the registry
key), and its packaged `SaturatedRelationFamily` (carrying the pre-derived `.decider`). -/
structure RegisteredModule where
  /-- The walker's display / lookup name. -/
  name : String
  /-- The presentation fingerprint (registry key). -/
  fingerprint : PresentationData
  /-- The packaged decided family. -/
  family : SaturatedRelationFamily

/-- ★ **The MODE-ADMIT registry** — the four registered decided walkers: the walking involution (thin,
separating-free), the walking idempotent monad and the walking monad (BOTH over the `monadComputad` fingerprint —
the honest collision; disambiguated by NAME), and the thin two-generator reference.  Each carries its packaged
`.decider`. -/
def modeAdmitRegistry : List RegisteredModule :=
  [ { name := "walking involution"
      fingerprint := involutionComputad.toPresentationData
      family := involutionRelationFamily },
    { name := "walking idempotent monad"
      fingerprint := monadComputad.toPresentationData
      family := idempotentRelationFamily },
    { name := "walking monad"
      fingerprint := monadComputad.toPresentationData
      family := monadRelationFamily },
    { name := "thin reference"
      fingerprint := thinReferenceComputad.toPresentationData
      family := thinReferenceFamily } ]

/-- ★ **Admission by name (Tier A)** — look a registered walker up by name and return its packaged relation
family (whose `.decider` is the zero-obligation decision).  The tier that reaches the BESPOKE-signature deciders
(monad / idempotent) the computad renaming machinery cannot transport. -/
def admitByName (moduleName : String) : Option SaturatedRelationFamily :=
  (modeAdmitRegistry.find? (fun registered => registered.name == moduleName)).map
    (fun registered => registered.family)

/-- **Is the candidate a renaming of some registered THIN walker?** — scan the registry with the thin renaming
matcher.  The recognition step of Tier B. -/
def isRegisteredThinRenaming (candidate : PresentationData) : Bool :=
  modeAdmitRegistry.any (fun registered => isThinPresentationMatch candidate registered.fingerprint)

/-- ★★ **Admission by renaming (Tier B, the matcher gate)** — scan the registry for a THIN walker whose
fingerprint the candidate matches by bijective renaming; if found AND the candidate is itself thin, hand back the
locally-thin decider for the candidate's OWN word problem.  SOUND with no `mapCellAlong` transport: thinness is a
structural property the bijection preserves, so the candidate's decidability is native, not borrowed.  The
`Option`-carried decider is the "zero call-site obligations" payoff made literal. -/
def admitModeTheory (candidate : ModeComputad) :
    Option (DecidableSaturatedConvForRel candidate.toModeSignature
      (emptyCellRel candidate.toModeSignature)) :=
  if isRegisteredThinRenaming candidate.toPresentationData = true then
    if hthin : candidate.twoCellGenerators.length = 0 then
      some (saturatedThinDeciderForAnyRel (baseRel := emptyCellRel candidate.toModeSignature)
        (noGen_of_twoGenLenZero hthin))
    else none
  else none

/-! ## P4 — the payoff theorems (accepted ==> packaged decider, zero call-site obligations) -/

/-- ★ **Payoff, Tier A** — `admitByName "walking monad"` returns EXACTLY `monadRelationFamily` (by `rfl`), so the
call site receives the walking monad's packaged decider with no proof obligation.  The gate is a genuine lookup
into the shipped library. -/
theorem admitByName_monad_isMonadFamily :
    admitByName "walking monad" = some monadRelationFamily := rfl

/-- ★ **Payoff, Tier A** — `admitByName "walking idempotent monad"` returns `idempotentRelationFamily`, DISTINCT
from the monad despite the SHARED fingerprint: the NAME disambiguates the collision that a data fingerprint could
not.  The honest witness that Tier A is sound where Tier B's data key is not. -/
theorem admitByName_idempotent_isIdempotentFamily :
    admitByName "walking idempotent monad" = some idempotentRelationFamily := rfl

/-- ★ **Payoff, Tier B** — a candidate recognised as a registered thin renaming and itself thin is ADMITTED: the
gate returns `some decider`.  Stated for the reference computad itself (a trivial self-renaming); the genuine
distinct-fingerprint case is the end-to-end below. -/
theorem admitModeTheory_thinReference_isSome :
    (admitModeTheory thinReferenceComputad).isSome = true := rfl

/-! ## P2 — the renaming functoriality brick: forward SHIPPED (reused), backward WALLED

The FORWARD soundness lift of the renaming functor is already shipped and requires no new proof here:
`mapCellAlong_preservesConvUnconditional` (`ConvFullFunctorDispatch.lean`) transports a component saturated
convertibility along a `ComputadMorphismTwo` to the image, discharging the structural functoriality by
`mapTwoCellConvFull`.  Every one of the nine `SaturatedConvOver` constructors commutes (the recon table); the
interchange leg is free (`crossComponentWhiskerCommute`).

What JAMS is the BACKWARD leg needed to REUSE a registered decider on a non-thin renamed presentation: it needs an
inverse `ComputadMorphismTwo` and the path round-trip `mapPath backward (mapPath forward oneCell) = oneCell`.  That
round-trip is not definitional — `mapPath` is only PROPOSITIONALLY a monoid homomorphism (`mapPath_composePath` is
a `congrArg` cons-induction, NOT `rfl`) — so it forces a `castBoundary` / `HEq` reconciliation at every whisker
cell.  Combined with the bespoke-vs-reconstructed reseat wall (the registered monad/idempotent deciders live over
`monadModeSignature`, not `monadComputad.toModeSignature`), the non-thin decider-REUSE leg stays conditional; the
gate ships its thin path, which needs no transport. -/

/-! ## P5 — the end-to-end rehearsal -/

/-- A **renamed copy of the thin reference** — the SAME two modes and two 1-generators, but the generator LIST is
PERMUTED (`right` then `left`).  A genuinely-distinct `PresentationData` (different generator order) that is a
bijective renaming of `thinReferenceComputad`. -/
def thinRenamedComputad : ModeComputad where
  modeCount := 2
  modalityGenerators := [(⟨1, by decide⟩, ⟨0, by decide⟩), (⟨0, by decide⟩, ⟨1, by decide⟩)]
  twoCellGenerators := []

/-- A **genuinely non-matching thin computad** — two modes but a single `(0,0)` endo-generator: NOT a permutation
of the reference's two off-diagonal generators. -/
def thinDistinctComputad : ModeComputad where
  modeCount := 2
  modalityGenerators := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators := []

/-- The source mode of a presentation's first 1-generator (or `0` when there is none) — a total discriminator for
the distinctness proof (propext-free, no obscure list lemmas). -/
def firstGeneratorSource (presentation : PresentationData) : Nat :=
  match presentation.modalityGenerators with
  | [] => 0
  | head :: _ => head.1

/-- ★ The renamed copy is a DISTINCT fingerprint from the reference (generator order differs) — the first
generator's source mode is `1` for the renamed copy and `0` for the reference, drawn apart by `Nat.noConfusion`. -/
theorem thinRenamedPresentation_ne_reference :
    thinRenamedComputad.toPresentationData ≠ thinReferenceComputad.toPresentationData :=
  fun equalFingerprint =>
    absurd (show (1 : Nat) = 0 from congrArg firstGeneratorSource equalFingerprint)
      (fun contradiction => Nat.noConfusion contradiction)

/-- ★ The matcher RECOGNISES the renamed copy as a renaming of the reference (permuted generators). -/
theorem thinRenamed_matches_reference :
    isThinPresentationMatch thinRenamedComputad.toPresentationData thinReferenceComputad.toPresentationData
      = true := rfl

/-- ★ The matcher REJECTS the genuinely-different thin computad (not a permutation). -/
theorem thinDistinct_notMatches_reference :
    isThinPresentationMatch thinDistinctComputad.toPresentationData thinReferenceComputad.toPresentationData
      = false := rfl

/-- ★ The matcher REJECTS the monad (non-thin: it has generating 2-cells). -/
theorem monad_notThinMatches_reference :
    isThinPresentationMatch monadComputad.toPresentationData thinReferenceComputad.toPresentationData
      = false := rfl

/-- The identity 2-cell on the empty 1-cell at mode `0` of the renamed thin computad — a genuine cell over
`thinRenamedComputad.toModeSignature`. -/
def thinRenamedNilCellA :
    RawTwoCellExpr thinRenamedComputad.toModeSignature
      (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩)
      (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩) :=
  RawTwoCellExpr.id (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩)

/-- A SYNTACTICALLY DISTINCT parallel cell — the vertical composite of two identities on the same empty 1-cell.
Parallel to `thinRenamedNilCellA` (same boundary), a different expression, so the decision is non-vacuous. -/
def thinRenamedNilCellB :
    RawTwoCellExpr thinRenamedComputad.toModeSignature
      (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩)
      (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.id (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩))
    (RawTwoCellExpr.id (ModalityPath.nil (graph := thinRenamedComputad.toModeSignature.graph) ⟨0, by decide⟩))

/-- ★★ **The end-to-end thin admission** — feed the renamed thin computad to the gate; it is recognised, admitted,
and its returned decider decides the distinct parallel pair `id` vs `id . id` as `isTrue` (thin: every parallel
pair convertible).  `false` here would mean either NOT admitted or decided `isFalse`. -/
def endToEndThinVerdict : Bool :=
  match admitModeTheory thinRenamedComputad with
  | none => false
  | some decider =>
      match decider thinRenamedNilCellA thinRenamedNilCellB with
      | isTrue _ => true
      | isFalse _ => false

/-- ★ The end-to-end thin admission COMPUTES to `true` by `rfl` — the matcher recognition, the admission, and the
decision all reduce. -/
theorem endToEndThinVerdict_holds : endToEndThinVerdict = true := rfl

/-- ★★ **The end-to-end SEPARATING verdict** — routed through Tier A: `admitByName "walking monad"` hands back the
walking monad's packaged decider (certified by `admitByName_monad_isMonadFamily`), which decides the two unit
faces `t <| eta` vs `eta |> t` as `isFalse` (distinct monotone maps).  HONEST attribution: the separation comes
from the NAMED-family tier (the monad's Delta model), NOT from the thin renaming path — the thin walkers are
TOTAL (always `isTrue`), so the renaming tier cannot exhibit an `isFalse`. -/
def endToEndMonadSeparatesVerdict : Bool :=
  match monadRelationFamily.decider
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- ★ The end-to-end separating verdict COMPUTES to `false` by `rfl` — the monad member genuinely separates. -/
theorem endToEndMonadSeparatesVerdict_holds : endToEndMonadSeparatesVerdict = false := rfl

/-! ## Observability -/

-- The involution fingerprint's 2-generator count: expect `0` (thin).
#eval involutionPresentation.twoCellGenerators.length
-- The monad fingerprint's 2-generator count: expect `2` (eta, mu).
#eval monadPresentation.twoCellGenerators.length
-- The matcher recognises the renamed thin copy: expect `true`.
#eval isThinPresentationMatch thinRenamedComputad.toPresentationData thinReferenceComputad.toPresentationData
-- The matcher rejects the genuinely-different thin computad: expect `false`.
#eval isThinPresentationMatch thinDistinctComputad.toPresentationData thinReferenceComputad.toPresentationData
-- The matcher rejects the non-thin monad: expect `false`.
#eval isThinPresentationMatch monadComputad.toPresentationData thinReferenceComputad.toPresentationData
-- The renamed thin computad is admitted (gate returns `some`): expect `true`.
#eval (admitModeTheory thinRenamedComputad).isSome
-- The end-to-end thin admission decides isTrue: expect `true`.
#eval endToEndThinVerdict
-- The end-to-end named-tier monad separation decides isFalse: expect `false`.
#eval endToEndMonadSeparatesVerdict

/-! ## P6 — honesty markers -/

/-- ★★ **Honesty marker — the MODE-ADMIT registry GATE SHIPS, hypothesis-free (MODE-ADMIT r1).**  The presentation
fingerprint carrier (`PresentationData` + hand-rolled `DecidableEq`), the fingerprint extraction
(`ModeComputad.toPresentationData`), the decidable renaming matcher (`isThinPresentationMatch` over the tiny
permutation search `isPermutationOfPairs`), the registry (`modeAdmitRegistry`), and BOTH admission tiers —
`admitByName` (Tier A, reaching the bespoke-signature deciders incl. the SEPARATING monad) and `admitModeTheory`
(Tier B, the thin renaming matcher gate) — with the packaged decider Option-carried at the call site (zero new
proofs).  Payoffs by `rfl`: `admitByName "walking monad" = some monadRelationFamily`,
`admitByName "walking idempotent monad" = some idempotentRelationFamily` (NAME disambiguates the shared
fingerprint), and `admitModeTheory thinReferenceComputad` is `some`.  `= true`. -/
def fxModeAdmit_hasRegistryGate : Bool := true

/-- ★★ **Honesty marker — end-to-end admission COMPUTES (MODE-ADMIT r1).**  A genuinely-distinct renamed thin
computad (`thinRenamedComputad`, generators permuted, fingerprint distinct from the reference by
`thinRenamedPresentation_ne_reference`) is recognised (`thinRenamed_matches_reference`), admitted through
`admitModeTheory`, and its returned decider decides a real parallel pair as `isTrue`
(`endToEndThinVerdict_holds`, by `rfl`).  The SEPARATING verdict is exhibited through Tier A: the named walking
monad's packaged decider gives `isFalse` on the two unit faces (`endToEndMonadSeparatesVerdict_holds`).  HONEST:
separation comes from the named-family tier (the thin renaming path is TOTAL), stated as such.  `= true`. -/
def fxModeAdmit_hasEndToEndAdmission : Bool := true

/-- ★ **Honesty marker (`false`) — NO NON-THIN renaming decider-REUSE.**  The FORWARD soundness lift is shipped and
reused (`mapCellAlong_preservesConvUnconditional`); reusing a registered decider on a NON-thin renamed
presentation needs the BACKWARD leg — an inverse `ComputadMorphismTwo` plus the path round-trip
`mapPath backward (mapPath forward _) = _`, which is not definitional (`mapPath` is only PROPOSITIONALLY a monoid
hom, `mapPath_composePath` a `congrArg` induction) and forces `castBoundary` / `HEq` reconciliation at every
whisker cell — compounded by the bespoke-vs-reconstructed reseat wall for the only non-thin registered deciders.
The decider-reuse leg is therefore CONDITIONAL on a supplied transport witness; the gate ships its thin path
instead.  `= false`. -/
def fxModeAdmit_hasRenamingDeciderTransport : Bool := false

/-- ★ **Honesty marker (`false`) — automatic DATA-FINGERPRINT admission is UNSOUND today.**  `monadComputad` and
the walking-idempotent-monad walker have the SAME `PresentationData` fingerprint (they differ ONLY in the
`Prop`-valued law relation, which `ModeComputad` does NOT store), so keying admission on the signature-data
fingerprint alone would conflate the separating walking monad with the total walking idempotent monad.  Soundly
keying a NON-thin registry requires reflecting the law ROWS as data (an untyped `RawCellData` layer, named future
work); the Tier B matcher is confined to the THIN fragment, whose empty law relation removes the ambiguity, and
Tier A disambiguates the non-thin walkers by NAME.  `= false`. -/
def fxModeAdmit_hasDataFingerprintAdmission : Bool := false

end FX1Poly.Polygraph.Amalgam
