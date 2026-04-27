import FX.Syntax.Token
import Tests.Framework

/-!
# Token runtime tests

Covers `fx_grammar.md` §2.2, `fx_lexer.md` §3.2, and `fx_lexer.md`
§11 (token summary):

  * Keyword round-trip: `Keyword.ofString? (Keyword.toString k) =
    some k` for each of the 92 keywords
  * `Keyword.ofString?` returns `none` for non-keyword idents
    (including `FN`, case-sensitivity per §3.2)
  * Cardinality of the keyword set is exactly 92
  * `Keyword.isContextual` is uniformly `false` — the inductive
    holds only global keywords, never contextual ones
  * `LocatedToken` default (for `Inhabited`) is EOF at `Span.zero`
  * `Token` `DecidableEq` respects payload content — two
    `stringLit`s with different text compare unequal, two idents
    with the same name compare equal, etc.
-/

namespace Tests.Syntax.TokenTests

open Tests FX.Syntax

/--
The full keyword list — 92 entries per fx_grammar.md §2.2.
Any new keyword added to the grammar must be listed here AND
in `Keyword.ofString?` in `FX/Syntax/Token.lean`; the
round-trip test fails otherwise.
-/
def allKeywords : Array Keyword := #[
  .affineKw, .andKw, .asKw, .assertKw, .awaitKw,
  .axiomKw, .beginKw, .benchKw, .bisimulationKw, .breakKw,
  .byKw, .calcKw, .catchKw, .classKw, .codeKw,
  .comptimeKw, .constKw, .continueKw, .codataKw, .contractKw,
  .decreasesKw, .decoratorKw, .declassifyKw, .deferKw, .dimensionKw,
  .dropKw, .dualKw, .effectKw, .elseKw, .endKw,
  .errdeferKw, .exceptionKw, .existsKw, .exportsKw, .externKw,
  .falseKw, .fnKw, .forKw, .forallKw, .ghostKw,
  .handleKw, .hintKw, .ifKw, .implKw, .inKw,
  .includeKw, .instanceKw, .isKw, .labelKw, .layoutKw,
  .lemmaKw, .letKw, .linearKw, .machineKw, .matchKw,
  .moduleKw, .mutKw, .notKw, .openKw, .orKw,
  .ownKw, .postKw, .preKw, .proofKw, .pubKw,
  .quotientKw, .receiveKw, .recKw, .refKw, .refinementKw,
  .returnKw, .sanitizeKw, .secretKw, .selectKw, .selfKw,
  .sendKw, .sessionKw, .sorryKw, .spawnKw, .taintClassKw,
  .taintedKw, .testKw, .trueKw, .tryKw, .typeKw,
  .unfoldKw, .valKw, .verifyKw, .whileKw, .withKw,
  .whereKw, .yieldKw
]

def run : IO Unit := Tests.suite "Tests.Syntax.TokenTests" do
  -- Cardinality is exactly 92.
  check "keyword count is 92" 92 allKeywords.size

  -- Round-trip every keyword.
  let mut roundTripFailures := 0
  for keyword in allKeywords do
    let serialized := keyword.toString
    match Keyword.ofString? serialized with
    | some reparsed =>
      if reparsed != keyword then roundTripFailures := roundTripFailures + 1
    | none    => roundTripFailures := roundTripFailures + 1
  check "Keyword round-trip (92 keywords)" 0 roundTripFailures

  -- A few direct spellings the grammar calls out as unusual.
  check "ofString? \"taint_class\"" (some Keyword.taintClassKw)
    (Keyword.ofString? "taint_class")
  check "toString .taintClassKw"    "taint_class"
    (Keyword.toString Keyword.taintClassKw)
  check "ofString? \"bisimulation\"" (some Keyword.bisimulationKw)
    (Keyword.ofString? "bisimulation")

  -- Non-keywords should not resolve.
  check "ofString? \"foobar\" is none" (none : Option Keyword)
    (Keyword.ofString? "foobar")
  check "ofString? empty is none" (none : Option Keyword)
    (Keyword.ofString? "")
  check "ofString? case sensitivity: \"FN\" is not \"fn\""
    (none : Option Keyword) (Keyword.ofString? "FN")
  check "ofString? \"ref_mut\" is not keyword"
    (none : Option Keyword) (Keyword.ofString? "ref_mut")

  -- No global keyword is contextual — the inductive holds only
  -- the 92 global keywords of §2.2.  If this ever returns `true`,
  -- something leaked in from the contextual keyword list.
  let mut ctxFail := 0
  for k in allKeywords do
    if k.isContextual then ctxFail := ctxFail + 1
  check "no contextual keywords in Keyword inductive" 0 ctxFail

  -- Inhabited default is EOF at Span.zero.
  let dflt : LocatedToken := default
  check "default LocatedToken is eof" Token.eof dflt.token
  check "default LocatedToken.span = Span.zero" Span.zero dflt.span

  -- DecidableEq respects payload content for ident/intLit/stringLit.
  check "ident same name equal" true
    (decide (Token.ident "foo" = Token.ident "foo"))
  check "ident different name unequal" false
    (decide (Token.ident "foo" = Token.ident "bar"))
  check "uident same name equal" true
    (decide (Token.uident "Foo" = Token.uident "Foo"))
  check "ident vs uident same text unequal" false
    (decide (Token.ident "Foo" = Token.uident "Foo"))

  check "intLit same text+base equal" true
    (decide (Token.intLit "42" .dec = Token.intLit "42" .dec))
  check "intLit different base unequal" false
    (decide (Token.intLit "42" .dec = Token.intLit "42" .hex))
  check "intLit different text unequal" false
    (decide (Token.intLit "42" .dec = Token.intLit "43" .dec))

  check "stringLit same text equal" true
    (decide (Token.stringLit "hello" = Token.stringLit "hello"))
  check "stringLit different text unequal" false
    (decide (Token.stringLit "hello" = Token.stringLit "world"))
  -- Content-bearing vs content-less of the same surface form differ:
  check "stringLit vs rstringLit with same text" false
    (decide (Token.stringLit "x" = Token.rstringLit "x"))

  -- Keyword-carrying tokens: `Token.kw k1 = Token.kw k2 ↔ k1 = k2`.
  check "kw fn = kw fn" true
    (decide (Token.kw Keyword.fnKw = Token.kw Keyword.fnKw))
  check "kw fn ≠ kw let" false
    (decide (Token.kw Keyword.fnKw = Token.kw Keyword.letKw))

end Tests.Syntax.TokenTests
