import FX1Poly.Core.RawTerm
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Typed.CellConstructors
import FX0Poly.CertRecheckSound

/-!
# FX1PolyAudit/FX0Bridge — the rich→minimal certificate bridge (FX0-PC.7)

The two-tier trust architecture (Metamath-Zero discipline) splits the kernel into the RICH proof-carrying
`FX1Poly` elaborator (which PRODUCES certificates) and the SMALL independently-auditable `FX0Poly` re-checker
(which RE-CHECKS them).  Trust then reduces to FX0Poly's tiny core, NOT to FX1Poly's full elaborator — but
only once we exhibit the BRIDGE that carries a rich term to a minimal certificate the small checker accepts.
This file ships that bridge and its structural-soundness theorem.

Because the bridge depends on BOTH stacks (it maps `FX1Poly.RawTerm` to `FX0Poly.Cert`), it cannot live in
`FX0Poly` — that library is deliberately FX1Poly-independent so a reader can audit it without trusting the
rich kernel.  It lives here in the audit library, the only place the two stacks meet.

## The encoder

`encodeCell` maps a scope-indexed `RawTerm` to a flat `FX0Poly.Cert` tree, structurally: a `mkGen` cell
becomes a `Cert.node` whose tag is the generator's NATIVE `Generator.toNat` (the same head byte the `.fx0c`
serializer emits) and whose children are the encoded sub-cells.  `encodeCellChildren` threads the dependent
`RawTermChildren` telescope into a plain `List Cert`.

## The arity model — pinned to FX1Poly's native tags

`FX0Poly.fxArity` is the checker's OWN small tag→arity convention (var = 0, universe = 1, Π = 2, Σ = 3); it
does NOT match FX1Poly's `Generator.toNat` numbering (universe = 55, Π = 57, …).  `bridgeArity` is the arity
model the checker uses for FX1Poly-emitted certificates: recover the generator from the native tag via the
left inverse `Generator.fromTag`, then read off its child count as `binderShifts.length`.  `bridgeArity_toNat`
proves the round trip: `bridgeArity g.toNat = some g.binderShifts.length`, the fact that makes every
well-formed cell's encoding pass the arity check at its node.

## The soundness theorem

`encodeCell_isValidB` (mutually with `encodeCellChildren_allValidB`) proves that EVERY `RawTerm` encodes to a
certificate the intrinsic structural validity predicate `FX0Poly.Cert.isValidB bridgeArity` accepts: by the
`RawTermChildren generator.binderShifts scope` index discipline, a cell carries EXACTLY `binderShifts.length`
children, so each node's child count matches `bridgeArity`'s expected arity, recursively.  Composing with the
re-checker soundness `Cert.recheck_wasAccepted_eq_isValidB` gives the headline `encodeCell_recheck_accepted`:
the independent minimal checker `recheck` ACCEPTS the encoding of any rich term.  This is the structural half
of the cross-check — the rich kernel's per-cell arity invariant is faithfully transmitted to, and
independently re-verified by, the small checker.  (The semantic/typing-preserving half — that the encoding of
a WELL-TYPED term satisfies a typing-aware re-check — is a follow-up increment; this brick establishes the
structural foundation.)

## Zero-axiom verification

The encoder is structural mutual recursion on `RawTerm`/`RawTermChildren`; the soundness is mutual structural
recursion mirroring it, closing each node by `dsimp only` (def unfolding) + `rw` (the round-trip / length /
`decide_eq_true` Nat-`==`-refl facts) — no `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or
`omega`.  The Nat `==` is `decide (· = ·)` (via `instBEqOfDecidableEq`), discharged by `decide_eq_true rfl`,
NOT `beq_self_eq_true` (which pulls propext + Classical + Quot.sound).  Gated per-declaration in
`FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX1Poly.FX0Bridge

open FX1Poly.Core (Generator RawTerm RawTermChildren)
open FX1Poly.Typed (universeCodeCell piTyCodeCell)
open FX1Poly.Universe (LevelExpr UniverseFlag)

mutual
  /-- Encode a rich `RawTerm` into a minimal `FX0Poly.Cert`: the node tag is the generator's NATIVE
  `Generator.toNat` (the `.fx0c` head byte), and the children are encoded structurally.  Mutually structural
  with `encodeCellChildren` over the `RawTerm`/`RawTermChildren` mutual inductive. -/
  def encodeCell : {scope : Nat} → RawTerm scope → FX0Poly.Cert
    | _, .mkGen generator _payload children =>
        FX0Poly.Cert.node generator.toNat (encodeCellChildren children)
  /-- Encode a `RawTermChildren` telescope into the flat `List FX0Poly.Cert` the certificate node carries. -/
  def encodeCellChildren : {shifts : List Nat} → {scope : Nat} →
      RawTermChildren shifts scope → List FX0Poly.Cert
    | _, _, .childNil => []
    | _, _, .childCons childHead childTail =>
        encodeCell childHead :: encodeCellChildren childTail
end

/-- The minimal checker's arity model for FX1Poly-emitted certificates, pinned to FX1Poly's NATIVE tags:
recover the generator from the tag via the left inverse `Generator.fromTag`, then its expected child count is
`binderShifts.length`.  An unrecognized tag (`Generator.fromTag = none`) yields `none`, which the per-node
rule rejects.  Distinct from `FX0Poly.fxArity` — that uses FX0Poly's own small tag convention; this honours
FX1Poly's `Generator.toNat` numbering. -/
def bridgeArity (tag : Nat) : Option Nat :=
  (Generator.fromTag tag).map (fun eachGenerator => eachGenerator.binderShifts.length)

/-- The round-trip fact: `bridgeArity` at a generator's native tag is exactly that generator's child count.
Via the `Generator.fromTag_toNat` left-inverse round-trip; the `Option.map` on `some` reduces by `rfl`. -/
theorem bridgeArity_toNat (generator : Generator) :
    bridgeArity generator.toNat = some generator.binderShifts.length := by
  show (Generator.fromTag generator.toNat).map (fun eachGenerator => eachGenerator.binderShifts.length)
      = some generator.binderShifts.length
  rw [Generator.fromTag_toNat]
  rfl

/-- `Nat`'s `==` is reflexively `true`, zero-axiom.  `==` on `Nat` is `decide (· = ·)` (via
`instBEqOfDecidableEq instDecidableEqNat`), so `decide_eq_true rfl` discharges it — UNLIKE `beq_self_eq_true`,
which pulls `propext`/`Classical.choice`/`Quot.sound` through `LawfulBEq`. -/
theorem natBeqSelfTrue (value : Nat) : (value == value) = true := decide_eq_true (rfl)

/-- **Length preservation.**  The encoded child list has exactly the telescope's length — so the per-node
arity check (`children.length == expected`) is comparing the cell's TRUE child count.  Structural recursion
on the `RawTermChildren` telescope. -/
theorem encodeCellChildren_length : {shifts : List Nat} → {scope : Nat} →
    (children : RawTermChildren shifts scope) →
    (encodeCellChildren children).length = shifts.length
  | _, _, .childNil => rfl
  | _, _, .childCons childHead childTail => by
      show (encodeCell childHead :: encodeCellChildren childTail).length = _
      rw [List.length_cons, List.length_cons, encodeCellChildren_length childTail]

mutual
  /-- **The structural soundness (cell half).**  Every `RawTerm` encodes to a certificate the intrinsic
  structural validity predicate accepts: the node's native tag has a known `bridgeArity` (= its child count),
  that count matches the encoded children's length (`encodeCellChildren_length`), and every child is
  recursively valid.  Mutually structural with `encodeCellChildren_allValidB`. -/
  theorem encodeCell_isValidB : {scope : Nat} → (t : RawTerm scope) →
      FX0Poly.Cert.isValidB bridgeArity (encodeCell t) = true
    | _, .mkGen generator _payload children => by
        dsimp only [encodeCell, FX0Poly.Cert.isValidB]
        rw [bridgeArity_toNat]
        dsimp only []
        rw [encodeCellChildren_length, natBeqSelfTrue]
        exact encodeCellChildren_allValidB children
  /-- The child-list companion: every encoded child of a telescope is recursively structurally valid. -/
  theorem encodeCellChildren_allValidB : {shifts : List Nat} → {scope : Nat} →
      (children : RawTermChildren shifts scope) →
      FX0Poly.Cert.allValidB bridgeArity (encodeCellChildren children) = true
    | _, _, .childNil => rfl
    | _, _, .childCons childHead childTail => by
        dsimp only [encodeCellChildren, FX0Poly.Cert.allValidB]
        rw [encodeCell_isValidB childHead]
        exact encodeCellChildren_allValidB childTail
end

/-- A verdict that `wasAccepted` IS `accepted`: in the 3-constructor `CheckVerdict` enum only `accepted` has
`wasAccepted = true` (`malformed`/`disagreed` both `false`).  `Bool.noConfusion` closes the impossible arms
zero-axiom. -/
theorem verdict_eq_accepted_of_wasAccepted : (verdict : FX0Poly.CheckVerdict) →
    verdict.wasAccepted = true → verdict = FX0Poly.CheckVerdict.accepted
  | .accepted, _ => rfl
  | .malformed, mismatch => Bool.noConfusion mismatch
  | .disagreed, mismatch => Bool.noConfusion mismatch

/-- ★ **The bridge soundness headline.**  The independent minimal checker `recheck` ACCEPTS the encoding of
every rich `RawTerm`: composing the re-checker soundness (`recheck`'s acceptance = intrinsic `isValidB`) with
`encodeCell_isValidB` (every encoding is structurally valid) gives that `recheck bridgeArity (encodeCell t)`
is exactly `accepted`.  The structural half of the FX1↔FX0 cross-check, for every well-formed cell. -/
theorem encodeCell_recheck_accepted {scope : Nat} (t : RawTerm scope) :
    FX0Poly.Cert.recheck bridgeArity (encodeCell t) = FX0Poly.CheckVerdict.accepted := by
  apply verdict_eq_accepted_of_wasAccepted
  rw [FX0Poly.Cert.recheck_wasAccepted_eq_isValidB, encodeCell_isValidB]

/-! ### Concrete non-vacuity smokes

The arity model computes against FX1Poly's native tags, and DIFFERS from `FX0Poly.fxArity` (the Π-type code
is tag `57` here, `2` in `fxArity`) — which is exactly why `bridgeArity` must be `fromTag`-based, not `fxArity`. -/

theorem bridgeArity_smoke_var : bridgeArity 0 = some 0 := rfl
theorem bridgeArity_smoke_lam : bridgeArity 2 = some 2 := rfl
theorem bridgeArity_smoke_piTyCode : bridgeArity 57 = some 2 := rfl
theorem bridgeArity_smoke_unknownTag : bridgeArity 999 = none := rfl

/-- A concrete universe-code cell encodes to the node with FX1Poly's native universe-code tag (`55`) and no
children. -/
theorem encodeCell_smoke_universeCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
    encodeCell (universeCodeCell (scope := 0) levelExpr flag) = FX0Poly.Cert.node 55 [] := rfl

/-- A Π-type-code cell encodes to the native Π-code tag (`57`) over the encoded domain and codomain. -/
theorem encodeCell_smoke_piTyCode {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) :
    encodeCell (piTyCodeCell domainCode codomainCode)
      = FX0Poly.Cert.node 57 [encodeCell domainCode, encodeCell codomainCode] := rfl

/-- End-to-end: a real universe-code cell's encoding re-checks `accepted` through the minimal checker — the
headline soundness specialised to a concrete kernel cell. -/
theorem recheck_smoke_universeCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
    FX0Poly.Cert.recheck bridgeArity (encodeCell (universeCodeCell (scope := 0) levelExpr flag))
      = FX0Poly.CheckVerdict.accepted :=
  encodeCell_recheck_accepted _

end FX1Poly.FX0Bridge
