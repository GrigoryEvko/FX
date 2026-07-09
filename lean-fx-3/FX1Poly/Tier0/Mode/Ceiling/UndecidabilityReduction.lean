import FX1Poly.Tier0.Mode.SemiThueReduction

/-! # Tier0/Mode/Ceiling/UndecidabilityReduction — the ceiling: the decidability REDUCTION

This is the top of the CEIL decidability lattice (`DecidableCeilingLedger`): the machine-checked
REDUCTION that carries (un)decidability across the Burroni bridge shipped in `SemiThueReduction`.

`SemiThueReduction.semiThue_iff_encodedTwoCell` already proves the BRIDGE: the Thue congruence of an
arbitrary semi-Thue system IS the 1-cell convertibility (`EncodedConv`) of the one-object 2-polygraph it
encodes, over the shipped `ModalityPath` computad carrier.  This file uses that bridge to state the
REDUCTION in the computability sense, and pins the honest boundary.

## FORM-A vs FORM-B — the reduction target (settled)

The reduction rides **FORM-A**: 1-cell CONVERTIBILITY / hom-inhabitation.  `EncodedConv rules p q` asserts
"there is a 2-cell (a convertibility) between the 1-cells `p` and `q`", so deciding
`EncodedConv rules (encodeWord u) (encodeWord v)` is exactly deciding whether a 2-cell EXISTS between the
encoded words — the CONNECTEDNESS problem of the one-object 2-polygraph.  Over the free-with-arbitrary-rules
carrier this connectedness IS the word problem of the finitely presented monoid the polygraph presents
(Guiraud–Malbos: a 2-polygraph with a single 0-cell is exactly a monoid presentation = string rewriting
system; `Σ₁` freely generates the word monoid, `Σ₂` is the rule set, a rewriting step is a 2-cell
`wϕw' : wuw' ⇒ wvw'`).

FORM-B — equality of two PARALLEL 2-cells modulo the presentation laws (the campaign's `SaturatedConvOver` /
`DecidableSaturatedConvForRel` carrier) — is the WRONG target, for two independent reasons:
  * BOUNDARY-TRIVIALITY.  A saturated 2-cell relation is indexed by a FIXED shared source/target 1-cell pair;
    a "source-word / target-word" invariant reads that fixed boundary, so it is the SAME proposition for both
    cells and discriminates no word problem.
  * ECKMANN–HILTON.  Delooping non-commutative words to endo-2-cells of an identity makes the
    vertical-composition monoid commutative (the EH bubble that FALSIFIED trace-NF invariance in FREE-6b), so
    a non-commutative monoid word problem cannot be faithfully encoded as 2-cell equality.
The shipped `EncodedConv` (six constructors: `rule` / `whiskerLeft` / `whiskerRight` / `refl` / `symm` /
`trans`, with NO interchange / EH arm) is exactly the FORM-A congruence, which is why the bridge is faithful.

## What is mechanized here (and what stays cited)

  * `thueDecidableOfEncodedDecidable` — the per-instance transport: a decision of the encoded connectedness
    at a pair yields a decision of the Thue congruence at that pair (both directions of the bridge, structural
    `Decidable` re-wrapping, no `decidable_of_iff` so no `propext`).
  * `UniformEncodedConnectednessDecider` / `uniformEncodedConnectednessDecider_decidesThue` — the FORWARD
    reduction: a UNIFORM connectedness decider (one that works for every alphabet and rule set) would decide
    the Thue word problem of EVERY semi-Thue system.
  * `noUniformConnectednessDecider_ofUndecidableThue` — the CONTRAPOSITIVE wall: IF some finite rule set has
    an undecidable Thue congruence (the cited Post/Markov fact, taken as a HYPOTHESIS), THEN no uniform
    connectedness decider exists.  This is the rung-3 wall AS A REDUCTION, not an analogy.

HONEST BOUNDARY.  The reduction map is fully mechanized (`fxCeil_hasUndecidabilityReduction = true`).  What
stays CITED, not mechanized, is the EXISTENCE of a finite semi-Thue system whose word problem is undecidable
(Post 1947 / Markov 1947): mechanizing that needs a computability substrate (halting ⪯ string rewriting, as
the Coq undecidability library does; Forster–Heiter–Smolka, ITP 2018), which is out of scope — so it enters
here only as the `thueUndecidable` HYPOTHESIS of the wall theorem, matching the sibling ledger's
`fxMode_hasArbitraryTwoCellUndecidabilityReduction = false` (the full first-principles embedding of a
mechanized-undecidable instance).  The three markers sit in a strict tower: the BRIDGE
(`fxMode_hasSemiThueReductionMechanized = true`) < this REDUCTION
(`fxCeil_hasUndecidabilityReduction = true`) < the first-principles INSTANCE
(`fxMode_hasArbitraryTwoCellUndecidabilityReduction = false`).

Raw Lean 4 + Init; every step is a structural re-wrapping of `Decidable` across the audit-clean shipped
bridge.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-instance transport across the bridge -/

/-- A decision of the encoded 1-cell connectedness at a pair transports to a decision of the Thue congruence
at that pair, by the shipped bridge `semiThue_iff_encodedTwoCell`.  Structural re-wrapping of `Decidable`
(no `decidable_of_iff`, so no `propext`): `isTrue` rides `Iff.mpr`, `isFalse` rides `Iff.mp`. -/
def thueDecidableOfEncodedDecidable {Letter : Type} (rules : List (List Letter × List Letter))
    (u v : List Letter)
    (encodedDecision : Decidable (EncodedConv rules (encodeWord u) (encodeWord v))) :
    Decidable (ThueCong rules u v) :=
  match encodedDecision with
  | isTrue connected => isTrue ((semiThue_iff_encodedTwoCell rules u v).mpr connected)
  | isFalse refuted =>
      isFalse (fun thue => refuted ((semiThue_iff_encodedTwoCell rules u v).mp thue))

/-! ## The uniform connectedness decider (FORM-A) and the forward reduction -/

/-- The UNIFORM 1-cell-connectedness decider hypothesis: for EVERY alphabet and EVERY finite rule set,
existence of a 2-cell between the encoded words is decidable.  This is the FORM-A (hom-inhabitation) decider;
lives in `Type 1` because the `Letter : Type` binder is one universe up. -/
abbrev UniformEncodedConnectednessDecider : Type 1 :=
  ∀ {Letter : Type} (rules : List (List Letter × List Letter)) (u v : List Letter),
    Decidable (EncodedConv rules (encodeWord u) (encodeWord v))

/-- ★ FORWARD REDUCTION.  A uniform connectedness decider decides the Thue word problem of EVERY semi-Thue
system: transport each instance across `thueDecidableOfEncodedDecidable`.  This is the reduction that ties the
one-object 2-polygraph's 1-cell connectedness to the finitely presented monoid word problem. -/
def uniformEncodedConnectednessDecider_decidesThue
    (decideConnectedness : UniformEncodedConnectednessDecider)
    {Letter : Type} (rules : List (List Letter × List Letter)) (u v : List Letter) :
    Decidable (ThueCong rules u v) :=
  thueDecidableOfEncodedDecidable rules u v (decideConnectedness rules u v)

/-- ★ THE WALL, AS A REDUCTION.  IF some finite rule set has an undecidable Thue congruence — the cited
Post/Markov fact, taken here as the HYPOTHESIS `thueUndecidable` (no family-of-pairs decider exists) — THEN no
uniform 1-cell-connectedness decider can exist.  The undecidability of the 2-cell connectedness problem
FOLLOWS from the cited undecidability of the monoid word problem, by a fully-mechanized reduction. -/
theorem noUniformConnectednessDecider_ofUndecidableThue {Letter : Type}
    (rules : List (List Letter × List Letter))
    (thueUndecidable : (∀ (u v : List Letter), Decidable (ThueCong rules u v)) → False) :
    UniformEncodedConnectednessDecider → False :=
  fun decideConnectedness =>
    thueUndecidable (fun u v => uniformEncodedConnectednessDecider_decidesThue decideConnectedness rules u v)

/-! ## The ceiling marker + the honest boundary pin -/

/-- ★ **CEILING MARKER (WP-CEIL-UNDEC).**  The undecidability REDUCTION is mechanized: the decidability of the
one-object 2-polygraph's 1-cell connectedness transports both ways with the Thue word problem of the semi-Thue
system it encodes (`uniformEncodedConnectednessDecider_decidesThue` and its contrapositive wall
`noUniformConnectednessDecider_ofUndecidableThue`).  `= true`.

This is STRICTLY between the shipped BRIDGE (`fxMode_hasSemiThueReductionMechanized = true`, the iff of
relations) and the first-principles INSTANCE embedding
(`fxMode_hasArbitraryTwoCellUndecidabilityReduction = false`, which needs a computability substrate): the
reduction MAP is mechanized, the undecidable instance stays cited (it enters as the `thueUndecidable`
hypothesis of the wall). -/
def fxCeil_hasUndecidabilityReduction : Bool := true

/-- The ceiling marker is the mechanized reduction (non-vacuity: the reduction theorems above exist). -/
theorem fxCeil_hasUndecidabilityReduction_isReduction :
    fxCeil_hasUndecidabilityReduction = true := rfl

/-! ## The Ceitin anchor — the concrete undecidable instance (lit-verified rule list)

The rung-3 wall's undecidable INSTANCE, made concrete AS DATA (never as a kernel-checked undecidability
claim).  Ceitin/Tseytin (1958) exhibited a semigroup on FIVE generators `{a, b, c, d, e}` with SEVEN defining
relations whose word problem is undecidable — the shortest-known such presentation by total relation length.
The seven relations, transcribed VERBATIM from the modern citable translation/survey (Nyberg-Brodda,
"G. S. Tseytin's seven-relation semigroup with undecidable word problem", arXiv:2401.11757 (2024),
equation (1); translating Tseitin, Trudy Mat. Inst. Steklov 52 (1958) 172-189):

    a·c = c·a      a·d = d·a      b·c = c·b      b·d = d·b
    e·c·a = c·e    e·d·b = d·e    c·c·a = c·c·a·e

We ship these AS a semi-Thue system (`ceitinRules`, kernel-checked DATA), embed it as the one-object
2-polygraph `encodedModeSignature ceitinRules`, and instantiate the ceiling reduction at it: IF Ceitin's word
problem is undecidable (CITED — Post 1947 / Markov 1947 undecidability, at this 5-generator/7-relation
witness, taken as the `ceitinThueUndecidable` HYPOTHESIS), THEN the 1-cell connectedness of this concrete
polygraph is undecidable.  Undecidability itself is NEVER asserted as a Lean theorem — mechanizing it needs a
computability substrate, out of scope.  For comparison: Matiyasevich (1967) gives a TWO-generator /
three-relation witness (`a·a·b·a·b = b·a·a`, `a·a·b·b = b·a·a`, and a 304-letter-vs-608-letter third
relation) — smallest generator count, but not blackboard-writable; the Ceitin 7-relation system is the one to
encode. -/

/-- The five generators of Ceitin's (1958) seven-relation semigroup. -/
inductive CeitinLetter where
  /-- Generator `a`. -/
  | a
  /-- Generator `b`. -/
  | b
  /-- Generator `c`. -/
  | c
  /-- Generator `d`. -/
  | d
  /-- Generator `e`. -/
  | e

/-- ★ Ceitin's SEVEN relations as a semi-Thue system over `{a, b, c, d, e}`, verbatim from
arXiv:2401.11757 eq. (1).  Kernel-checked DATA only — the undecidability of its word problem stays CITED. -/
def ceitinRules : List (List CeitinLetter × List CeitinLetter) :=
  [ ([CeitinLetter.a, CeitinLetter.c], [CeitinLetter.c, CeitinLetter.a]),
    ([CeitinLetter.a, CeitinLetter.d], [CeitinLetter.d, CeitinLetter.a]),
    ([CeitinLetter.b, CeitinLetter.c], [CeitinLetter.c, CeitinLetter.b]),
    ([CeitinLetter.b, CeitinLetter.d], [CeitinLetter.d, CeitinLetter.b]),
    ([CeitinLetter.e, CeitinLetter.c, CeitinLetter.a], [CeitinLetter.c, CeitinLetter.e]),
    ([CeitinLetter.e, CeitinLetter.d, CeitinLetter.b], [CeitinLetter.d, CeitinLetter.e]),
    ([CeitinLetter.c, CeitinLetter.c, CeitinLetter.a],
      [CeitinLetter.c, CeitinLetter.c, CeitinLetter.a, CeitinLetter.e]) ]

/-- Ceitin's presentation has exactly SEVEN relations (the count fingerprint). -/
theorem ceitinRuleCount : ceitinRules.length = 7 := rfl

/-- The first Ceitin relation `a·c = c·a` is a member of the rule set. -/
theorem ceitinFirstRule_mem :
    (([CeitinLetter.a, CeitinLetter.c], [CeitinLetter.c, CeitinLetter.a])) ∈ ceitinRules :=
  List.Mem.head _

/-- Non-vacuity: `a·c ~ c·a` is a positive Thue conversion in Ceitin's system (one rule application), so the
encoded one-object 2-polygraph `encodedModeSignature ceitinRules` is genuinely inhabited. -/
theorem ceitinCommutes_ac :
    ThueCong ceitinRules [CeitinLetter.a, CeitinLetter.c] [CeitinLetter.c, CeitinLetter.a] :=
  thueCong_of_mem ceitinFirstRule_mem

/-- ★ THE CONCRETE CEILING.  IF Ceitin's word problem is undecidable — the CITED Post/Markov fact at the
5-generator/7-relation witness, taken as the HYPOTHESIS `ceitinThueUndecidable` — THEN the 1-cell
connectedness of the encoded one-object 2-polygraph `encodedModeSignature ceitinRules` is undecidable: a
per-pair decision of `EncodedConv ceitinRules` would decide every Ceitin word-pair via
`thueDecidableOfEncodedDecidable`.  This is the rung-3 wall at a NAMED, blackboard-writable instance,
mechanized to the honest boundary. -/
theorem ceitinEncodedConnectednessUndecidable_ofThueUndecidable
    (ceitinThueUndecidable :
      (∀ (u v : List CeitinLetter), Decidable (ThueCong ceitinRules u v)) → False) :
    (∀ (u v : List CeitinLetter),
        Decidable (EncodedConv ceitinRules (encodeWord u) (encodeWord v))) → False :=
  fun decideEncoded =>
    ceitinThueUndecidable
      (fun u v => thueDecidableOfEncodedDecidable ceitinRules u v (decideEncoded u v))

/-- **Honesty marker.**  The rung-3 undecidable instance is ANCHORED at a concrete, lit-verified presentation:
Ceitin's (1958) five-generator/seven-relation semigroup (`ceitinRules`, verbatim from Nyberg-Brodda
arXiv:2401.11757).  The rules are kernel-checked DATA; the undecidability of the instance stays CITED (never a
Lean theorem).  `= true` (the anchor is declared and embedded). -/
def fxCeil_hasCeitinAnchor : Bool := true

/-- The Ceitin anchor is declared (non-vacuity of the marker). -/
theorem fxCeil_hasCeitinAnchor_isDeclared : fxCeil_hasCeitinAnchor = true := rfl

/-! ## Toy non-vacuity — the involution as a discriminating point of the FORM-A target (below the wall)

The FORM-A reduction target (`EncodedConv`, the 1-cell connectedness relation) genuinely discriminates: at the
involution semi-Thue system `[s.s ↦ id]` it is INHABITED at one real pair and REFUTED at another, transported
from the shipped `involutionThue_positive` / `involutionThue_separation`.  The involution is a DECIDABLE point
strictly BELOW the rung-3 wall (its word problem is decided by the Z/2 parity classifier, Tier B/C), so the
wall `noUniformConnectednessDecider_ofUndecidableThue involutionThueRules` has an UNSATISFIABLE hypothesis at
the involution — confirming the wall speaks only about the UNDECIDABLE instances (the Ceitin anchor), not the
decidable ones. -/

/-- Positive: the encoded connectedness holds at `s.s` vs `id` (transport of `involutionThue_positive`). -/
theorem involutionEncodedConnectedness_positive :
    EncodedConv involutionThueRules
      (encodeWord [InvolutionLetter.s, InvolutionLetter.s]) (encodeWord ([] : List InvolutionLetter)) :=
  involutionThue_reductionInstance.mp involutionThue_positive

/-- Negative: the encoded connectedness is refuted at `s` vs `id` (transport of `involutionThue_separation`
back through the bridge) — so the FORM-A target discriminates, and the toy is non-vacuous. -/
theorem involutionEncodedConnectedness_separation :
    ¬ EncodedConv involutionThueRules
        (encodeWord [InvolutionLetter.s]) (encodeWord ([] : List InvolutionLetter)) :=
  fun encoded =>
    involutionThue_separation
      ((semiThue_iff_encodedTwoCell involutionThueRules [InvolutionLetter.s] []).mpr encoded)

end FX1Poly.Polygraph
