import FX.Syntax.Span
import Tests.Framework

/-!
# Span runtime tests

Covers `fx_lexer.md` §10 position tracking:

  * `Position.zero` defaults
  * `Position.nextByte` advances line on `\n`, column on CR (see
    `Position.nextByte` docstring for why CRLF handling is a layer up)
  * `Span.point`, `Span.merge` (idempotence, commutativity at
    the offset level), `Span.length`, `Span.isEmpty`
-/

namespace Tests.Syntax.SpanTests

open Tests FX.Syntax

def run : IO Unit := Tests.suite "Tests.Syntax.SpanTests" do
  -- Position.zero initial state.
  check "Position.zero.line"   1 Position.zero.line
  check "Position.zero.column" 0 Position.zero.column
  check "Position.zero.offset" 0 Position.zero.offset

  -- nextByte on an ASCII letter.
  let afterA := Position.zero.nextByte 'a'.toNat.toUInt8
  check "nextByte 'a' line"   1 afterA.line
  check "nextByte 'a' column" 1 afterA.column
  check "nextByte 'a' offset" 1 afterA.offset

  -- nextByte on newline.
  let afterNewline := Position.zero.nextByte 0x0A
  check "nextByte '\\n' line"   2 afterNewline.line
  check "nextByte '\\n' column" 0 afterNewline.column
  check "nextByte '\\n' offset" 1 afterNewline.offset

  -- nextByte on CR (0x0D): this helper does NOT advance the
  -- line — the Lexer layer handles CR/CRLF with lookahead.  See
  -- `Position.nextByte` docstring.  This test pins the current
  -- contract so any future change is an intentional break.
  let pCR := Position.zero.nextByte 0x0D
  check "nextByte CR keeps line 1 (lexer handles CRLF)" 1 pCR.line
  check "nextByte CR advances column" 1 pCR.column
  check "nextByte CR advances offset" 1 pCR.offset

  -- UTF-8 continuation byte: column++ only (it is a byte offset).
  let pCont := Position.zero.nextByte 0xA0
  check "nextByte cont byte line"   1 pCont.line
  check "nextByte cont byte column" 1 pCont.column

  -- Sequence through "ab\nc".
  let sequencePos :=
    Position.zero
      |>.nextByte 'a'.toNat.toUInt8
      |>.nextByte 'b'.toNat.toUInt8
      |>.nextByte 0x0A
      |>.nextByte 'c'.toNat.toUInt8
  check "sequence line"   2 sequencePos.line
  check "sequence column" 1 sequencePos.column
  check "sequence offset" 4 sequencePos.offset

  -- Span.point.
  let pointSpan := Span.point afterA
  check "Span.point start = stop" true (pointSpan.start == pointSpan.stop)
  check "Span.point.length = 0"   0 pointSpan.length
  check "Span.point.isEmpty"      true pointSpan.isEmpty

  -- Span.zero.
  check "Span.zero.isEmpty" true Span.zero.isEmpty
  check "Span.zero.length"  0    Span.zero.length

  -- Span.length on a non-empty span.
  let firstSpan : Span := { start := Position.zero, stop := afterA }
  check "Span.length single byte" 1    firstSpan.length
  check "Span.length not empty"   false firstSpan.isEmpty

  -- Span.merge.
  let secondSpan : Span := { start := afterNewline, stop := sequencePos }
  let mergedSpan := Span.merge firstSpan secondSpan
  check "merge start is earlier" Position.zero mergedSpan.start
  check "merge stop is later"   sequencePos mergedSpan.stop

  -- merge is commutative at the offset level.
  check "merge commutative at start" mergedSpan.start (Span.merge secondSpan firstSpan).start
  check "merge commutative at stop"  mergedSpan.stop  (Span.merge secondSpan firstSpan).stop

  -- merge is idempotent: `merge s s = s`.
  check "merge s s = s, start" firstSpan.start (Span.merge firstSpan firstSpan).start
  check "merge s s = s, stop"  firstSpan.stop  (Span.merge firstSpan firstSpan).stop

  -- merge with Span.zero on one side: zero has start=stop=offset 0,
  -- so it wins at start but loses at stop (unless the other span
  -- is also zero).
  let mZ := Span.merge Span.zero firstSpan
  check "merge zero LHS, start" Position.zero mZ.start
  check "merge zero LHS, stop"  afterA       mZ.stop

  -- Disjoint spans: merge covers the gap.
  let pA := Position.zero.nextByte 'a'.toNat.toUInt8
  let pB := pA.nextByte 'b'.toNat.toUInt8
  let pC := pB.nextByte 'c'.toNat.toUInt8
  let pD := pC.nextByte 'd'.toNat.toUInt8
  let sAB : Span := { start := Position.zero, stop := pB }  -- "ab"
  let sCD : Span := { start := pC,       stop := pD }   -- "d" at col 3
  let mABCD := Span.merge sAB sCD
  check "disjoint merge start"             Position.zero mABCD.start
  check "disjoint merge stop"              pD       mABCD.stop
  check "disjoint merge length spans gap"  4        mABCD.length

end Tests.Syntax.SpanTests
