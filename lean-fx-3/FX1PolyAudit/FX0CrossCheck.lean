import FX1PolyAudit.FX0Bridge
import FX0Poly.CertDeserialize
import FX1Poly.Typed.CellConstructors

/-!
# FX1PolyAudit/FX0CrossCheck — the end-to-end external-verification pipeline (FX0-PC.5)

`FX0Bridge` ships `encodeCell` (rich `RawTerm` → minimal `FX0Poly.Cert`) and the structural soundness
`encodeCell_recheck_accepted` (the minimal checker accepts every cell's encoding).  `CertSerialize` /
`CertDeserialize` ship the `.fx0c` byte format — `Cert.encode` (injective) and `Cert.decode` (with the
`Cert.decode_encode` round-trip).  This file COMPOSES them into the single entry point a real external
verifier exposes: **bytes in, verdict out**, knowing nothing but the byte stream and the tag→arity table.

`externalVerify bytes fuel` decodes the `.fx0c` stream and re-checks the recovered certificate against
`bridgeArity` (the FX1-native-tag arity model).  The headline `externalVerify_encodeCell` then closes the
structural-level FX0 cross-check loop end-to-end:

```
rich RawTerm  --encodeCell-->  Cert  --Cert.encode-->  .fx0c bytes  --externalVerify-->  accepted
```

i.e. the standalone external verifier, handed only the bytes the rich kernel serialized for ANY well-formed
cell, accepts them — the proof composes the serialize/parse round-trip (`Cert.decode_encode`, #980) with the
bridge soundness (`encodeCell_recheck_accepted`, #226).  This is the first milestone that runs a cell through
BOTH verifiers (the rich kernel's intrinsic well-formedness and the minimal external checker) and shows they
agree, generalised from "var 0" to every cell.

The verifier genuinely DISCRIMINATES (it is not a rubber stamp): the negative smokes show it returns
`malformed` on a wrong-arity stream (a Π-code tag with one child instead of two), an unknown generator tag,
and a truncated header.  The positive fixtures run a concrete `var 0` cell and a universe-code cell end to end.

## Zero-axiom verification

`externalVerify` is a total `match`; the headline is `dsimp only [externalVerify]` + `rw [Cert.decode_encode]`
(which fires the decoder round-trip and the resulting `match`-on-`some` iota) + the bridge soundness; the
smokes close by `rfl` (full evaluation of the concrete byte streams); the `var 0` fixture builds its `Fin 1`
index by the explicit `Fin.mk 0 (Nat.zero_lt_succ 0)` (avoiding the `OfNat`-numeral `Fin` literal, which pulls
propext).  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated
per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX1Poly.FX0CrossCheck

open FX1Poly.Core (Generator RawTerm RawTermChildren)
open FX1Poly.FX0Bridge (encodeCell bridgeArity encodeCell_recheck_accepted)
open FX1Poly.Typed (universeCodeCell)
open FX1Poly.Universe (LevelExpr UniverseFlag)

/-- The standalone external verifier: decode the `.fx0c` byte stream at the given fuel, then re-check the
recovered certificate against the FX1-native-tag arity model `bridgeArity`.  A decode failure (exhausted fuel
or malformed header) is itself a `malformed` verdict.  Knows only bytes + the tag→arity table — exactly the
Metamath-Zero trusted-core shape, independent of FX1Poly's elaborator. -/
def externalVerify (bytes : List Nat) (fuel : Nat) : FX0Poly.CheckVerdict :=
  match FX0Poly.Cert.decode fuel bytes with
  | some (cert, _) => FX0Poly.Cert.recheck bridgeArity cert
  | none => FX0Poly.CheckVerdict.malformed

/-- ★ **The end-to-end FX0 cross-check.**  The standalone external verifier accepts the serialized encoding of
EVERY well-formed cell: serialize `encodeCell t` to `.fx0c` bytes, hand them to `externalVerify` at the cell's
own fuel budget, and the verdict is `accepted`.  Composes the `.fx0c` round-trip (`Cert.decode_encode`) with
the bridge structural soundness (`encodeCell_recheck_accepted`) — the rich kernel and the minimal external
verifier agree, through the actual byte channel. -/
theorem externalVerify_encodeCell {scope : Nat} (t : RawTerm scope) :
    externalVerify (FX0Poly.Cert.encode (encodeCell t)) (encodeCell t).budget
      = FX0Poly.CheckVerdict.accepted := by
  dsimp only [externalVerify]
  rw [FX0Poly.Cert.decode_encode]
  exact encodeCell_recheck_accepted t

/-! ### Negative discrimination — the external verifier is not a rubber stamp -/

/-- Rejection: a `.fx0c` stream for a Π-type-code node (native tag `57`, arity 2) carrying only ONE child
re-checks `malformed` — the recovered certificate fails the arity check. -/
theorem externalVerify_smoke_rejectsWrongArity :
    externalVerify [57, 1, 0, 0] 3 = FX0Poly.CheckVerdict.malformed := rfl

/-- Rejection: a stream naming an unrecognized generator tag (`999`) re-checks `malformed`. -/
theorem externalVerify_smoke_rejectsUnknownTag :
    externalVerify [999, 0] 2 = FX0Poly.CheckVerdict.malformed := rfl

/-- Rejection: a truncated stream (a tag with no child-count byte) fails to decode and is `malformed`. -/
theorem externalVerify_smoke_rejectsTruncated :
    externalVerify [57] 3 = FX0Poly.CheckVerdict.malformed := rfl

/-! ### Positive fixtures — concrete cells end-to-end through both verifiers -/

/-- `var 0` (the variable cell at de Bruijn index 0 in scope 1) runs end-to-end through both verifiers and is
accepted — the named "var 0 end-to-end" milestone, as an instance of the universal soundness. -/
theorem externalVerify_var0 :
    externalVerify
        (FX0Poly.Cert.encode (encodeCell (.mkGen .gen_var (Fin.mk 0 (Nat.zero_lt_succ 0)) .childNil)))
        (encodeCell (.mkGen .gen_var (Fin.mk 0 (Nat.zero_lt_succ 0)) .childNil)).budget
      = FX0Poly.CheckVerdict.accepted :=
  externalVerify_encodeCell _

/-- A universe-code cell runs end-to-end through both verifiers and is accepted. -/
theorem externalVerify_universeCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
    externalVerify
        (FX0Poly.Cert.encode (encodeCell (universeCodeCell (scope := 0) levelExpr flag)))
        (encodeCell (universeCodeCell (scope := 0) levelExpr flag)).budget
      = FX0Poly.CheckVerdict.accepted :=
  externalVerify_encodeCell _

end FX1Poly.FX0CrossCheck
