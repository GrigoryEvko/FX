/-! # Axis/Term — game semantics: arenas, plays, deterministic strategies (term-24)

The fourth term-axis SEMANTICS rung.  Game semantics (Hyland-Ong, Abramsky-Jagadeesan-Malacaria) reads a
program as a STRATEGY for a two-player dialogue: Opponent (the environment) and Player (the program)
alternate MOVES in an ARENA, and the strategy says how Player responds to whatever Opponent does.  This
file ships the operational core (each piece zero-axiom, Init-only):

  * **`Polarity`** — the two roles `opponent` / `player` with the involution `flip` (`flip_flip`,
    `flip_ne`): the duality at the heart of the dialogue.
  * **`Arena`** — a configuration of moves with a `polarity` and an `isInitial` predicate.  **`dualArena`**
    swaps every polarity (the linear-logic `A^⊥` / the term-axis echo of session duality), an involution
    POINTWISE (`dualArena_involutive_pointwise`).
  * **`EvenPlay`** — a play of even length built from Opponent/Player move PAIRS (so positions where the
    strategy must respond are exactly the even ones), with the Opponent projection `opponentMoves`.
  * **`RespectsArena`** — a play is legal for an arena when each Player move has Player polarity and each
    Opponent move has Opponent polarity (`respectsArena_prefixClosed`).
  * **`Strategy`** + **`Strategy.determinedByOpponent`** (★) — a strategy is a prefix-closed, DETERMINISTIC
    set of even plays; the headline is that it is COMPLETELY DETERMINED BY OPPONENT'S MOVES — two accepted
    plays with the same Opponent projection are equal, so a strategy DENOTES A FUNCTION from Opponent's
    dialogue to Player's, the bedrock of the games model.
  * **`answerArena`** + **`answerStrategy`** — a concrete witness: the one-question/one-answer arena and the
    strategy that answers it (the game-semantics "value"; the copycat/identity analogue, cf. the GoI wire in
    `term-23`).

## Honest scope

Shipped: the polarity duality, arenas + dual arenas, even plays + the Opponent projection, arena-legality,
and DETERMINISTIC strategies with the determinacy theorem (strategy = function of Opponent's moves), plus a
concrete arena + answering strategy.  DEFERRED: justification POINTERS and the P-view / O-view machinery,
VISIBILITY / INNOCENCE / WELL-BRACKETING conditions, strategy COMPOSITION (parallel composition + hiding)
and the resulting CATEGORY of games, and — the title's deep theorem — FULL ABSTRACTION (denotational
equality = observational equivalence for PCF, after quotienting by the intrinsic equivalence; Hyland-Ong /
AJM).  This is the `term-24` slice of the omnibus `fxTerm_hasDenotationalAdequacy = false`.

## Zero-axiom verification

`opponentMoves` / `RespectsArena` are structural recursion on `EvenPlay`; `flip_flip` / `flip_ne` are full
case analysis on `Polarity`; `determinedByOpponent` is double structural induction on the two plays, using
`injection` on the cons-equality of Opponent projections and the strategy's determinism + prefix-closure
fields, with the cross constructor cases closed by `nomatch`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditAxisTermGameSemantics.lean`.
-/

namespace FX1Poly.Core

/-! ## Polarity — the two dialogue roles -/

/-- A **polarity**: `opponent` (the environment) or `player` (the program). -/
inductive Polarity where
  | opponent
  | player

/-- The polarity involution — swap the two roles. -/
def Polarity.flip : Polarity → Polarity
  | Polarity.opponent => Polarity.player
  | Polarity.player => Polarity.opponent

/-- `flip` is an INVOLUTION: flipping twice is the identity. -/
theorem Polarity.flip_flip (polarity : Polarity) : polarity.flip.flip = polarity := by
  cases polarity with
  | opponent => rfl
  | player => rfl

/-- `flip` has NO FIXED POINT: a role is never its own dual (the duality is genuine, two-valued). -/
theorem Polarity.flip_ne (polarity : Polarity) : polarity.flip ≠ polarity := by
  cases polarity with
  | opponent => intro flipEq; nomatch flipEq
  | player => intro flipEq; nomatch flipEq

/-! ## Arenas -/

/-- An **arena**: a space of moves, each with a polarity, and a predicate marking the initial moves
(the moves Opponent may open with). -/
structure Arena where
  /-- The moves of the arena. -/
  Move : Type
  /-- Each move belongs to Opponent or Player. -/
  polarity : Move → Polarity
  /-- The initial moves (where a play may start). -/
  isInitial : Move → Prop

/-- The **dual arena** `A^⊥`: the same moves, every polarity flipped (Opponent becomes Player and vice
versa).  The linear-logic dual / the games echo of session duality (`mode-25`). -/
def dualArena (arena : Arena) : Arena where
  Move := arena.Move
  polarity := fun move => (arena.polarity move).flip
  isInitial := arena.isInitial

/-- The dual arena's polarity is the flip of the original (definitional). -/
theorem dualArena_polarity (arena : Arena) (move : arena.Move) :
    (dualArena arena).polarity move = (arena.polarity move).flip := rfl

/-- ★ Dualizing TWICE restores the original polarity POINTWISE — `A^⊥⊥ = A` on every move.  (The full
arena-level equality `dualArena (dualArena A) = A` would need `funext` on the polarity field, forbidden
zero-axiom, so the honest statement is pointwise — cf. the antisymmetric-DCPO deferral in `term-22`.) -/
theorem dualArena_involutive_pointwise (arena : Arena) (move : arena.Move) :
    (dualArena (dualArena arena)).polarity move = arena.polarity move := by
  show ((arena.polarity move).flip).flip = arena.polarity move
  exact Polarity.flip_flip (arena.polarity move)

/-! ## The arena algebra — sum/with + the empty arena + De Morgan duality -/

/-- The **sum/with arena** `A ⊕ B`: the disjoint union of moves, each keeping its own polarity and
initial-ness (the underlying object of the games `⊕` / `&` / `⊗` constructions; they differ only in how
strategies branch, not in the arena of moves). -/
def arenaSum (left right : Arena) : Arena where
  Move := left.Move ⊕ right.Move
  polarity := fun move =>
    match move with
    | Sum.inl leftMove => left.polarity leftMove
    | Sum.inr rightMove => right.polarity rightMove
  isInitial := fun move =>
    match move with
    | Sum.inl leftMove => left.isInitial leftMove
    | Sum.inr rightMove => right.isInitial rightMove

/-- The **empty arena**: no moves (the monoidal unit's underlying object / the games `0`). -/
def emptyArena : Arena where
  Move := Empty
  polarity := fun absurdMove => absurdMove.elim
  isInitial := fun absurdMove => absurdMove.elim

/-- ★ **De Morgan duality** (the star-autonomous law): the dual of a sum is the sum of the duals —
`(A ⊕ B)^⊥ = A^⊥ ⊕ B^⊥` POINTWISE on polarity (flipping the polarity of the disjoint union is flipping each
component).  The arena-object half of the games model's linear-logic / star-autonomous structure. -/
theorem dualArena_sum_deMorgan (left right : Arena) (move : (arenaSum left right).Move) :
    (dualArena (arenaSum left right)).polarity move
      = (arenaSum (dualArena left) (dualArena right)).polarity move := by
  cases move with
  | inl leftMove => rfl
  | inr rightMove => rfl

/-! ## Even plays — Opponent/Player move pairs -/

/-- An **even play**: a sequence of Opponent-then-Player move PAIRS, most-recent pair on top.
`snocPair playerMove opponentMove earlier` extends `earlier` by an Opponent move then Player's response.
Even length is automatic, so every play is a position at which Player has just moved (or the empty play). -/
inductive EvenPlay (Move : Type) where
  /-- The empty play. -/
  | nil
  /-- Extend by an Opponent move then the Player response. -/
  | snocPair (playerMove opponentMove : Move) (earlier : EvenPlay Move)

/-- The **Opponent projection**: the list of Opponent moves of a play (most recent first). -/
def opponentMoves {Move : Type} : EvenPlay Move → List Move
  | EvenPlay.nil => []
  | EvenPlay.snocPair _ opponentMove earlier => opponentMove :: opponentMoves earlier

/-- A play **respects an arena** when every Player move has Player polarity and every Opponent move has
Opponent polarity — the play is a legal Opponent/Player dialogue in the arena. -/
def RespectsArena (arena : Arena) : EvenPlay arena.Move → Prop
  | EvenPlay.nil => True
  | EvenPlay.snocPair playerMove opponentMove earlier =>
      arena.polarity playerMove = Polarity.player
        ∧ arena.polarity opponentMove = Polarity.opponent
        ∧ RespectsArena arena earlier

/-- Arena-legality is closed under dropping the most recent pair. -/
theorem respectsArena_prefixClosed (arena : Arena) {playerMove opponentMove : arena.Move}
    {earlier : EvenPlay arena.Move}
    (respects : RespectsArena arena (EvenPlay.snocPair playerMove opponentMove earlier)) :
    RespectsArena arena earlier :=
  respects.2.2

/-! ## Strategies -/

/-- A **strategy**: a set of even plays that contains the empty play, is closed under dropping the most
recent Opponent/Player pair, and is DETERMINISTIC — at any position, Player's response to a given Opponent
move is unique. -/
structure Strategy (Move : Type) where
  /-- The plays the strategy accepts. -/
  accepts : EvenPlay Move → Prop
  /-- The strategy is non-empty (the empty play is always present). -/
  acceptsNil : accepts EvenPlay.nil
  /-- Accepted plays are closed under dropping the most recent pair (even-prefix closure). -/
  prefixClosed : ∀ {playerMove opponentMove : Move} {earlier : EvenPlay Move},
    accepts (EvenPlay.snocPair playerMove opponentMove earlier) → accepts earlier
  /-- DETERMINISM: at a position, an Opponent move determines Player's response uniquely. -/
  deterministic : ∀ {firstResponse secondResponse opponentMove : Move} {earlier : EvenPlay Move},
    accepts (EvenPlay.snocPair firstResponse opponentMove earlier) →
    accepts (EvenPlay.snocPair secondResponse opponentMove earlier) →
    firstResponse = secondResponse

/-- ★ **A strategy is determined by Opponent's moves.**  Two accepted plays with the same Opponent
projection are EQUAL — so a strategy denotes a FUNCTION from Opponent's dialogue to Player's responses (the
defining property of a game-semantics denotation).  Proved by double structural induction: the determinism
field pins the most recent Player response once the rest is fixed by the induction hypothesis. -/
theorem Strategy.determinedByOpponent {Move : Type} (strategy : Strategy Move) :
    ∀ {firstPlay secondPlay : EvenPlay Move},
      strategy.accepts firstPlay → strategy.accepts secondPlay →
      opponentMoves firstPlay = opponentMoves secondPlay → firstPlay = secondPlay := by
  intro firstPlay
  induction firstPlay with
  | nil =>
      intro secondPlay _ _ projectionEq
      cases secondPlay with
      | nil => rfl
      | snocPair secondResponse secondOpponent secondRest =>
          dsimp only [opponentMoves] at projectionEq
          nomatch projectionEq
  | snocPair firstResponse firstOpponent firstRest inductionHypothesis =>
      intro secondPlay acceptsFirst acceptsSecond projectionEq
      cases secondPlay with
      | nil =>
          dsimp only [opponentMoves] at projectionEq
          nomatch projectionEq
      | snocPair secondResponse secondOpponent secondRest =>
          dsimp only [opponentMoves] at projectionEq
          injection projectionEq with opponentEq restProjectionEq
          have acceptsFirstRest := strategy.prefixClosed acceptsFirst
          have acceptsSecondRest := strategy.prefixClosed acceptsSecond
          have restEq := inductionHypothesis acceptsFirstRest acceptsSecondRest restProjectionEq
          subst restEq
          subst opponentEq
          have responseEq := strategy.deterministic acceptsFirst acceptsSecond
          subst responseEq
          rfl

/-! ## A concrete witness — the one-answer game -/

/-- The **answer arena**: one Opponent question (`true`) enabling one Player answer (`false`). -/
def answerArena : Arena where
  Move := Bool
  polarity := fun move =>
    match move with
    | true => Polarity.opponent
    | false => Polarity.player
  isInitial := fun move => move = true

/-- The **answer strategy**: Player responds to Opponent's question with the unique answer.  It accepts the
empty play and the single play `question · answer`, nothing else — the game-semantics "value", the simplest
non-trivial deterministic strategy (the copycat/identity analogue). -/
def answerStrategy : Strategy Bool where
  accepts := fun play =>
    play = EvenPlay.nil ∨ play = EvenPlay.snocPair false true EvenPlay.nil
  acceptsNil := Or.inl rfl
  prefixClosed := by
    intro playerMove opponentMove earlier accepted
    cases accepted with
    | inl isNil => nomatch isNil
    | inr isAnswer =>
        injection isAnswer with _playerEq _opponentEq earlierEq
        subst earlierEq
        exact Or.inl rfl
  deterministic := by
    intro firstResponse secondResponse opponentMove earlier acceptsFirst acceptsSecond
    cases acceptsFirst with
    | inl isNil => nomatch isNil
    | inr firstAnswer =>
        cases acceptsSecond with
        | inl isNil => nomatch isNil
        | inr secondAnswer =>
            injection firstAnswer with firstPlayerEq _firstOpponentEq _firstEarlierEq
            injection secondAnswer with secondPlayerEq _secondOpponentEq _secondEarlierEq
            rw [firstPlayerEq, secondPlayerEq]

/-- The answer strategy accepts the question/answer play (the non-trivial witness). -/
theorem answerStrategy_acceptsAnswer :
    answerStrategy.accepts (EvenPlay.snocPair false true EvenPlay.nil) := Or.inr rfl

/-- The answered play's Opponent projection is the single question. -/
theorem answerStrategy_opponentMoves :
    opponentMoves (EvenPlay.snocPair false true (EvenPlay.nil : EvenPlay Bool)) = [true] := rfl

/-- The answered play respects the answer arena (Player answer has Player polarity, Opponent question has
Opponent polarity). -/
theorem answerStrategy_respectsArena :
    RespectsArena answerArena (EvenPlay.snocPair false true EvenPlay.nil) :=
  ⟨rfl, rfl, trivial⟩

end FX1Poly.Core
