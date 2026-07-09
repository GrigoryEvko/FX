import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvCliqueSequence
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvFullTraceRoute
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingDecisionAssembly

/-! # mode-3 floor — the DECISIVE reconciliation of `fxMode_hasModeRelativeConvDecision` (flag-B r7 TERMINAL)

The flag-B campaign asked whether the master flag `fxMode_hasModeRelativeConvDecision`
(`ModeRelativeMetatheory`, whose parameter unfolds LITERALLY to `Decidable (TwoCellConv …)`, the BARE free
strict-2-category 2-cell congruence MINUS whisker-by-1-cell functoriality) is decidable by some bare-conv
invariant / normal form.  Six rounds MINED OUT that vein:

  * r1 (`BareConvGoldilocks`) — the separating moment family is SOUND but an over-approximation;
  * r2 (`BareConvCompleteness`) — the moment family is PROVABLY LOSSY;
  * r3 (`BareConvFragmentDecision`) — bare conv is DECIDED on the single-generator fragment, with an INFINITE
    moment tower above it;
  * r4 (`BareConvWordCodeCompleteness`) — the additive whisker word-code is MACHINE-REFUTED incomplete on
    general cells (`wordCode_not_complete`, the two-generator Godement collision);
  * r5 (`BareConvPatternMultiset`) — the flat per-generator pattern MULTISET is SOUND + SEPARATING but NOT
    proven complete (the ceiling of the additive scalar tower);
  * r6 (`BareConvCliqueSequence`) — the ordered Cartier–Foata clique-SEQUENCE is MACHINE-REFUTED UNSOUND
    (`cliqueSequence_not_bareConvInvariant`: interchange permutes the vcomp-level order, over-separating
    bare-convertible cells).

Settlement: interchange-only BARE conv is NOT a plain trace monoid, so NO bare-conv invariant decides it
(r1–r6).  This file does NOT re-attack that vein.  It RECONCILES the master flag against the SHIPPED decisions —
answering the reconciliation question "what IS `fxMode_hasModeRelativeConvDecision` a decision FOR, and is it
dischargeable by an already-shipped decision?" — and CLOSES it as an HONEST DEEP WALL, backed by named proven
terms, without weakening any shipped statement.

## The reconciliation (all four legs machine-backed here)

The master flag's relation is BARE `TwoCellConv`.  The three shipped, zero-axiom, TOTAL decisions each decide a
STRICTLY COARSER relation, so none is a discharge of the bare flag — and the gap is a genuine RELATION MISMATCH,
not a missing proof:

  ★ **`bareConvStrictlyFinerThanFaithfulDecided`** — the DECISIVE separation, machine-checked: the two-generator
    Godement pair `wordCodeCollisionLeft` / `wordCodeCollisionRight` is `TwoCellConvFull` (the FAITHFUL,
    categorically-correct, functorially-whiskered relation — `wordCodeCollision_convFull`) yet is NOT bare
    `TwoCellConv` (`wordCodeCollision_not_twoCellConv`, the bare-conv invariant `coCrossSum` scoring `1 ≠ 0`).
    So BARE `TwoCellConv` is STRICTLY FINER than the faithful decided `TwoCellConvFull`: the shipped faithful
    decision `adjunctionDecideTwoCellConvFull` returns `isTrue` on this pair, where the bare relation is FALSE —
    hence it PROVABLY is not a decision of the bare flag's relation.  (Categorically this is exactly the
    sesquicategory-vs-2-category gap: bare conv keeps whiskering but drops the interchange bifunctoriality that
    makes horizontal composition a functor — nLab "strict 2-category" / "sesquicategory".)

  ★ **`realizableReadbackRefutesBare`** (= the shipped `adjunctionSpineTraceReconstruction_refuted`) — the
    NATURAL / realizable readback conv notion IS `TwoCellConvFull`, not bare: the `reconstruct` leg
    `SpineTraceEquiv → TwoCellConv` at BARE conv is provably FALSE (`atomFrame adjunctionUnitSpineAtom` shares the
    unit spine yet is NOT bare-conv to `gen unit`).  Readback lands at Full (`cellChain_readback_convFull`), so
    the categorically-realizable relation is `TwoCellConvFull` and bare sits strictly below it.  This is the
    Schanuel–Street / Delpeuch–Vicary / Joyal–Street settlement: the decidable canonical 2-cell equality of a
    free strict 2-category / walking adjunction is the FUNCTORIAL (interchange-satisfying) relation, decided by
    the planar string-diagram normal form — which is `TwoCellConvFull`, already shipped.

  ★ the faithful decided notion is TOTAL and UNCONDITIONAL — `adjunctionDecideTwoCellConvFull` (backing
    `fxMode_hasFaithfulTwoCellDecisionModuloTrace = true`), instantiated here at the Godement pair
    (`bareConvDecisionReconciliation.faithfulDecidesGodementPair`) — a decision of a GENUINELY TRUE proposition
    (the pair IS `TwoCellConvFull`, `wordCodeCollision_convFull`), so this sound+complete decider is necessarily
    `isTrue` there (a `Decidable P` for a provable `P` cannot be `isFalse`).  Non-vacuous, not a stub.  The
    generic free version is `decideTwoCellConvFull` (`fxMode_hasUngatedFreeTwoCellDecision = true`).

  ★ the SATURATED modulo-triangles notion is decided TOTALLY too — `decideSaturatedTwoCellConv_ofSeed`
    (`DecidableSaturatedTwoCellConvFor`, backing `fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction =
    true`) — and is ALSO strictly coarser than bare (the snakes provably do NOT collapse freely,
    `leftSnakeSaturatedButNotFree`).

## The honest terminal disposition

`fxMode_hasModeRelativeConvDecision` STAYS `false`, pinned to the strictly-finer BARE relation, and is NOT
dischargeable by any shipped decision (each decides a coarser, categorically-correct relation).  It is a
permanent-AS-STATED terminal — re-openable (bare conv IS decidable in principle via the Makkai /
Delpeuch–Vicary string-diagram normal form; the open frontier is the Gratzer interchange critical-pair
coherence), NOT undecidability-walled — that Markov/Post undecidability wall is the DISJOINT flag A
`fxMode_hasDecidableTwoCellEquality` over ARBITRARY finite presentations.

fib-3 is NOT blocked on this flag: its keystone is discharged at the granularity the MTT fibration consumes —
the SATURATED relation (`fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction = true`) — and the faithful /
realizable relation `TwoCellConvFull` is decided too (`fxMode_hasFaithfulTwoCellDecisionModuloTrace = true`).
Bare `TwoCellConv` is kept honestly live as an over-fine (sesquicategory-like) relation below both.
`fxMode_hasBareConvDecisionDeepWall := true` records this terminal reconciliation; the r1–r6 walls and the
saturated / faithful decisions are UNTOUCHED and NOT weakened.

Raw Lean 4 + Init; every declaration is a bundle of already-audited zero-axiom shipped terms —
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The decisive separation — BARE conv is strictly finer than the faithful decided relation -/

/-- ★★ **The DECISIVE reconciliation core (machine-checked): BARE `TwoCellConv` is STRICTLY FINER than the
faithful decided `TwoCellConvFull`.**  The two-generator Godement pair `wordCodeCollisionLeft` /
`wordCodeCollisionRight` is `TwoCellConvFull` (`wordCodeCollision_convFull`) yet NOT bare `TwoCellConv`
(`wordCodeCollision_not_twoCellConv`).  So the shipped faithful decision `adjunctionDecideTwoCellConvFull` — which
decides `TwoCellConvFull` — answers `isTrue` on a pair that the master flag's BARE relation does NOT relate;
therefore it is provably NOT a decision of `fxMode_hasModeRelativeConvDecision`'s relation.  This is the exact
sesquicategory-vs-2-category gap: bare conv lacks the interchange bifunctoriality (whisker functoriality) that
`TwoCellConvFull` carries. -/
theorem bareConvStrictlyFinerThanFaithfulDecided :
    TwoCellConvFull adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight
    ∧ ¬ TwoCellConv adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight :=
  ⟨wordCodeCollision_convFull, wordCodeCollision_not_twoCellConv⟩

/-! ## The reconciliation bundle -/

/-- ★ The **flag-B r7 reconciliation record** — the four decisive legs of the master-flag disposition, each an
already-audited zero-axiom shipped term, bundled so the terminal marker below is NON-VACUOUSLY backed. -/
structure BareConvDecisionReconciliation : Type where
  /-- The FAITHFUL / realizable decided notion is `TwoCellConvFull`, decided TOTALLY and unconditionally.  Here
  instantiated at the Godement pair — a decision of a GENUINELY TRUE proposition (the pair IS `TwoCellConvFull`,
  `wordCodeCollision_convFull`), so this sound+complete decider is necessarily `isTrue` there.  Non-vacuous, not a
  stub. -/
  faithfulDecidesGodementPair :
    Decidable (TwoCellConvFull adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight)
  /-- The SATURATED modulo-triangles notion is decided TOTALLY too — `DecidableSaturatedTwoCellConvFor`. -/
  saturatedDecision : DecidableSaturatedTwoCellConvFor
  /-- The master flag's BARE relation is STRICTLY FINER than the faithful decided `TwoCellConvFull`: the Godement
  pair is `TwoCellConvFull` yet NOT bare `TwoCellConv`.  So no faithful/saturated decider discharges the bare
  flag — a genuine relation mismatch. -/
  bareStrictlyFinerThanFaithful :
    TwoCellConvFull adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight
    ∧ ¬ TwoCellConv adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight
  /-- The NATURAL / realizable readback conv notion IS `TwoCellConvFull`, NOT bare: the bare reconstruction leg is
  provably FALSE. -/
  realizableReadbackRefutesBare : ¬ AdjunctionSpineTraceReconstruction

/-- ★★ **The reconciliation, INHABITED by shipped terms.**  Every field is a named, already-audited zero-axiom
proof: the total faithful decision on the Godement pair (`adjunctionDecideTwoCellConvFull`), the total saturated
decision (`decideSaturatedTwoCellConv_ofSeed`), the decisive strict-finer separation
(`bareConvStrictlyFinerThanFaithfulDecided`), and the realizable-readback refutation
(`adjunctionSpineTraceReconstruction_refuted`).  This term is the honest, non-fabricated backing of the terminal
marker below. -/
def bareConvDecisionReconciliation : BareConvDecisionReconciliation where
  faithfulDecidesGodementPair :=
    adjunctionDecideTwoCellConvFull wordCodeCollisionLeft wordCodeCollisionRight
  saturatedDecision := decideSaturatedTwoCellConv_ofSeed
  bareStrictlyFinerThanFaithful := bareConvStrictlyFinerThanFaithfulDecided
  realizableReadbackRefutesBare := adjunctionSpineTraceReconstruction_refuted

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the flag-B r7 TERMINAL reconciliation: `fxMode_hasModeRelativeConvDecision` is an HONEST
DEEP WALL over BARE `TwoCellConv`, NOT dischargeable by any shipped decision.**

The master flag `fxMode_hasModeRelativeConvDecision` (`ModeRelativeMetatheory`) is pinned to BARE `TwoCellConv`
(its parameter unfolds to `Decidable (TwoCellConv …)`).  The reconciliation is machine-backed by
`bareConvDecisionReconciliation`:

  * the faithful decided notion is `TwoCellConvFull` (`adjunctionDecideTwoCellConvFull`, total, unconditional,
    `fxMode_hasFaithfulTwoCellDecisionModuloTrace = true`) — the CATEGORICALLY-CORRECT relation (nLab: a strict
    2-category is a sesquicategory PLUS interchange bifunctoriality; the free/walking-adjunction 2-cell equality
    is decided by the Joyal–Street / Delpeuch–Vicary planar string-diagram NF and the Schanuel–Street simplicial
    zig-zag NF);
  * BARE `TwoCellConv` is STRICTLY FINER — `bareConvStrictlyFinerThanFaithfulDecided`: the Godement pair is
    `TwoCellConvFull` yet NOT bare — so the faithful decision is provably not a bare decision (a genuine relation
    mismatch);
  * readback realizes `TwoCellConvFull`, never bare (`realizableReadbackRefutesBare` /
    `cellChain_readback_convFull`) — bare conv is a non-realizable sesquicategory artifact;
  * the saturated modulo-triangles notion is decided too (`decideSaturatedTwoCellConv_ofSeed`,
    `fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction = true`) and is likewise strictly coarser than bare
    (`leftSnakeSaturatedButNotFree`);
  * NO bare-conv invariant decides bare conv (r1–r6: interchange-only bare conv is not a plain trace monoid, the
    ordered clique-sequence is machine-refuted unsound, `cliqueSequence_not_bareConvInvariant`).

So the master flag stays `false` as a permanent-as-stated terminal, re-openable (Makkai / Delpeuch–Vicary
string-diagram NF; open frontier = Gratzer interchange critical-pair coherence) but NOT undecidability-walled
(that is the disjoint flag A `fxMode_hasDecidableTwoCellEquality`, Markov/Post over arbitrary presentations).
fib-3 consumes the SATURATED / faithful granularity and is NOT blocked.  `= true`. -/
def fxMode_hasBareConvDecisionDeepWall : Bool := true

end FX1Poly.Polygraph
