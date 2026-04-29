import LeanFX.Syntax.Ty

/-! # Strengthening — partial inverses of weakening.

`Ty.strengthen : Ty level (scope + 1) → Option (Ty level scope)` is the
partial inverse of `Ty.weaken`.  It returns `some T` exactly when the
input is in the image of weakening, i.e. does not reference the freshly
bound variable.  Required for the η-arrow case of complete development
(`Term.cd`, v2.5a) where the redex `λx. f.weaken x` contracts to `f`,
demanding recovery of `f` from `f.weaken`.

## Why a partial renaming algebra

Strengthening is one instance of a more general pattern: applying a
partial Fin → Fin map across syntax that may fail when the map has no
image at a particular position.  We capture this with an `OptionalRenaming`
abbrev and structural `optRename` functions on `Ty` and `RawTerm` that
mirror the existing `rename` functions but thread `Option` everywhere.

Specialising to `OptionalRenaming.unweaken` (drops position 0) gives the
strengthen operations.  Other instances (drop position k, drop a set of
positions) reuse the same machinery.

## Why `Option.bind` and not nested `match`

Lean 4's match compiler emits `propext` for any pattern that uses a
wildcard fallthrough across an `Option` scrutinee.  All multi-argument
`Option` combinators here therefore use `Option.bind` chains rather
than `match a, b with | some _, some _ | _, _`.  This keeps every
function and theorem in this module strictly axiom-free; the same
discipline appears across the rest of the kernel for the same reason.

## Round-trip lemmas

`Ty.strengthen_weaken : ∀ T, T.weaken.strengthen = some T` and the raw
analogue close the loop: weakening followed by strengthening recovers the
original term.  The proofs reduce to a single `optRename`-after-`rename`
composition lemma plus an `optRename_identity` lemma — both by direct
structural induction with no axioms. -/

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Optional renaming algebra. -/

/-- A partial renaming `OptionalRenaming source target` maps a position
in a `source`-scope context to *optionally* a position in a `target`-scope
context.  `none` records that the position has no image — the canonical
example is strengthening across a weakening, where position 0 (the
freshly bound variable) is precisely the position with no image. -/
abbrev OptionalRenaming (source target : Nat) : Type :=
  Fin source → Option (Fin target)

/-- The identity optional renaming maps every position to `some` of itself. -/
def OptionalRenaming.identity {scope : Nat} :
    OptionalRenaming scope scope :=
  fun position => some position

/-- The strengthening renaming `unweaken` drops the freshly bound
variable: position 0 fails to map (it *is* the bound variable being
removed); position `k + 1` maps to position `k` of the unweakened
scope.  Composing `Renaming.weaken` then `OptionalRenaming.unweaken`
yields `OptionalRenaming.identity` pointwise. -/
def OptionalRenaming.unweaken {scope : Nat} :
    OptionalRenaming (scope + 1) scope
  | ⟨0,     _⟩ => none
  | ⟨k + 1, isWithinSucc⟩ =>
      some ⟨k, Nat.lt_of_succ_lt_succ isWithinSucc⟩

/-- Lift an optional renaming under a binder.  Position 0 of the lifted
source maps to position 0 of the lifted target unconditionally; position
`k + 1` maps via the underlying renaming, with the result shifted up by
one (`Fin.succ`) when present.  Mirrors `Renaming.lift` but in the
`Option` monad on the right. -/
def OptionalRenaming.lift {source target : Nat}
    (optionalRenaming : OptionalRenaming source target) :
    OptionalRenaming (source + 1) (target + 1)
  | ⟨0, _⟩ => some ⟨0, Nat.zero_lt_succ _⟩
  | ⟨position + 1, isWithinSucc⟩ =>
      Option.map Fin.succ
        (optionalRenaming ⟨position, Nat.lt_of_succ_lt_succ isWithinSucc⟩)

/-- Pointwise equivalence on optional renamings. -/
def OptionalRenaming.equiv {source target : Nat}
    (firstRenaming secondRenaming : OptionalRenaming source target) : Prop :=
  ∀ position, firstRenaming position = secondRenaming position

/-- Lifting preserves pointwise equivalence. -/
theorem OptionalRenaming.lift_equiv {source target : Nat}
    {firstRenaming secondRenaming : OptionalRenaming source target}
    (renamingsAreEquivalent :
      OptionalRenaming.equiv firstRenaming secondRenaming) :
    OptionalRenaming.equiv firstRenaming.lift secondRenaming.lift
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isWithinSucc⟩ =>
      congrArg (Option.map Fin.succ)
        (renamingsAreEquivalent
          ⟨position, Nat.lt_of_succ_lt_succ isWithinSucc⟩)

/-- Lifting the identity optional renaming yields the identity at the
extended scope (pointwise).  Both Fin cases reduce to `rfl` modulo
`Fin` proof-irrelevance — the second case maps `⟨k + 1, h⟩` to
`Option.map Fin.succ (some ⟨k, _⟩) = some ⟨k + 1, _⟩`. -/
theorem OptionalRenaming.lift_identity_equiv {scope : Nat} :
    OptionalRenaming.equiv
      (@OptionalRenaming.identity scope).lift
      OptionalRenaming.identity
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Composing a total renaming on the left with an optional renaming
on the right gives an optional renaming.  Used to express the
"rename-then-optRename" composition law. -/
def OptionalRenaming.afterRenaming {source middle target : Nat}
    (totalRenaming : Renaming source middle)
    (optionalRenaming : OptionalRenaming middle target) :
    OptionalRenaming source target :=
  fun position => optionalRenaming (totalRenaming position)

/-- Composing weakening with the strengthening renaming yields the
identity pointwise — the cornerstone of the strengthen-after-weaken
round-trip lemma. -/
theorem OptionalRenaming.weaken_unweaken_equiv_identity {scope : Nat} :
    OptionalRenaming.equiv
      (OptionalRenaming.afterRenaming
        (@Renaming.weaken scope) OptionalRenaming.unweaken)
      OptionalRenaming.identity
  | ⟨_, _⟩ => rfl

/-- Lifting commutes with the after-renaming composition (pointwise). -/
theorem OptionalRenaming.lift_afterRenaming_equiv {source middle target : Nat}
    (totalRenaming : Renaming source middle)
    (optionalRenaming : OptionalRenaming middle target) :
    OptionalRenaming.equiv
      (OptionalRenaming.afterRenaming totalRenaming.lift optionalRenaming.lift)
      (OptionalRenaming.afterRenaming totalRenaming optionalRenaming).lift
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-! ## Optional renaming on raw terms.

Implementation discipline: every multi-argument case uses `Option.bind`
chains rather than `match _, _ with | some _, some _ | _, _ => none`,
because the latter triggers Lean 4's match compiler to emit `propext`
for the wildcard fallthrough.  Single-argument cases use
`Option.map`, which is propext-clean. -/

/-- Apply an optional renaming to a raw term, threading `Option`
everywhere.  Returns `none` if any variable position lacks an image
under the renaming; otherwise returns `some` of the strengthened term. -/
def RawTerm.optRename {source target : Nat} :
    RawTerm source → OptionalRenaming source target → Option (RawTerm target)
  | .var position, optionalRenaming =>
      Option.map RawTerm.var (optionalRenaming position)
  | .unit, _      => some .unit
  | .boolTrue, _  => some .boolTrue
  | .boolFalse, _ => some .boolFalse
  | .natZero, _   => some .natZero
  | .natSucc predecessor, optionalRenaming =>
      Option.map RawTerm.natSucc
        (predecessor.optRename optionalRenaming)
  | .lam body, optionalRenaming =>
      Option.map RawTerm.lam
        (body.optRename optionalRenaming.lift)
  | .app function argument, optionalRenaming =>
      Option.bind (function.optRename optionalRenaming) fun renamedFunction =>
        Option.bind (argument.optRename optionalRenaming) fun renamedArgument =>
          some (RawTerm.app renamedFunction renamedArgument)
  | .pair first second, optionalRenaming =>
      Option.bind (first.optRename optionalRenaming) fun renamedFirst =>
        Option.bind (second.optRename optionalRenaming) fun renamedSecond =>
          some (RawTerm.pair renamedFirst renamedSecond)
  | .fst pairTerm, optionalRenaming =>
      Option.map RawTerm.fst (pairTerm.optRename optionalRenaming)
  | .snd pairTerm, optionalRenaming =>
      Option.map RawTerm.snd (pairTerm.optRename optionalRenaming)
  | .boolElim scrutinee thenBranch elseBranch, optionalRenaming =>
      Option.bind (scrutinee.optRename optionalRenaming) fun renamedScrutinee =>
        Option.bind (thenBranch.optRename optionalRenaming) fun renamedThenBranch =>
          Option.bind (elseBranch.optRename optionalRenaming) fun renamedElseBranch =>
            some (RawTerm.boolElim renamedScrutinee renamedThenBranch renamedElseBranch)
  | .natElim scrutinee zeroBranch succBranch, optionalRenaming =>
      Option.bind (scrutinee.optRename optionalRenaming) fun renamedScrutinee =>
        Option.bind (zeroBranch.optRename optionalRenaming) fun renamedZero =>
          Option.bind (succBranch.optRename optionalRenaming) fun renamedSucc =>
            some (RawTerm.natElim renamedScrutinee renamedZero renamedSucc)
  | .natRec scrutinee zeroBranch succBranch, optionalRenaming =>
      Option.bind (scrutinee.optRename optionalRenaming) fun renamedScrutinee =>
        Option.bind (zeroBranch.optRename optionalRenaming) fun renamedZero =>
          Option.bind (succBranch.optRename optionalRenaming) fun renamedSucc =>
            some (RawTerm.natRec renamedScrutinee renamedZero renamedSucc)
  | .listNil, _ => some .listNil
  | .listCons head tail, optionalRenaming =>
      Option.bind (head.optRename optionalRenaming) fun renamedHead =>
        Option.bind (tail.optRename optionalRenaming) fun renamedTail =>
          some (RawTerm.listCons renamedHead renamedTail)
  | .listElim scrutinee nilBranch consBranch, optionalRenaming =>
      Option.bind (scrutinee.optRename optionalRenaming) fun renamedScrutinee =>
        Option.bind (nilBranch.optRename optionalRenaming) fun renamedNil =>
          Option.bind (consBranch.optRename optionalRenaming) fun renamedCons =>
            some (RawTerm.listElim renamedScrutinee renamedNil renamedCons)
  | .optionNone, _ => some .optionNone
  | .optionSome value, optionalRenaming =>
      Option.map RawTerm.optionSome
        (value.optRename optionalRenaming)
  | .optionMatch scrutinee noneBranch someBranch, optionalRenaming =>
      Option.bind (scrutinee.optRename optionalRenaming) fun renamedScrutinee =>
        Option.bind (noneBranch.optRename optionalRenaming) fun renamedNone =>
          Option.bind (someBranch.optRename optionalRenaming) fun renamedSome =>
            some (RawTerm.optionMatch renamedScrutinee renamedNone renamedSome)
  | .eitherInl value, optionalRenaming =>
      Option.map RawTerm.eitherInl (value.optRename optionalRenaming)
  | .eitherInr value, optionalRenaming =>
      Option.map RawTerm.eitherInr (value.optRename optionalRenaming)
  | .eitherMatch scrutinee leftBranch rightBranch, optionalRenaming =>
      Option.bind (scrutinee.optRename optionalRenaming) fun renamedScrutinee =>
        Option.bind (leftBranch.optRename optionalRenaming) fun renamedLeft =>
          Option.bind (rightBranch.optRename optionalRenaming) fun renamedRight =>
            some (RawTerm.eitherMatch renamedScrutinee renamedLeft renamedRight)
  | .refl term, optionalRenaming =>
      Option.map RawTerm.refl (term.optRename optionalRenaming)
  | .idJ baseCase witness, optionalRenaming =>
      Option.bind (baseCase.optRename optionalRenaming) fun renamedBase =>
        Option.bind (witness.optRename optionalRenaming) fun renamedWitness =>
          some (RawTerm.idJ renamedBase renamedWitness)

/-- Pointwise-equivalent optional renamings produce equal results on
every raw term.  Direct structural induction; binder cases use
`OptionalRenaming.lift_equiv`. -/
theorem RawTerm.optRename_congr {source target : Nat}
    {firstRenaming secondRenaming : OptionalRenaming source target}
    (renamingsAreEquivalent :
      OptionalRenaming.equiv firstRenaming secondRenaming) :
    ∀ rawTerm : RawTerm source,
      rawTerm.optRename firstRenaming = rawTerm.optRename secondRenaming
  | .var position =>
      congrArg (Option.map RawTerm.var)
        (renamingsAreEquivalent position)
  | .unit      => rfl
  | .boolTrue  => rfl
  | .boolFalse => rfl
  | .natZero   => rfl
  | .natSucc predecessor =>
      congrArg (Option.map RawTerm.natSucc)
        (RawTerm.optRename_congr renamingsAreEquivalent predecessor)
  | .lam body =>
      congrArg (Option.map RawTerm.lam)
        (RawTerm.optRename_congr
          (OptionalRenaming.lift_equiv renamingsAreEquivalent) body)
  | .app function argument => by
      have functionEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent function
      have argumentEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent argument
      simp only [RawTerm.optRename]
      rw [functionEquality, argumentEquality]
  | .pair first second => by
      have firstEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent first
      have secondEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent second
      simp only [RawTerm.optRename]
      rw [firstEquality, secondEquality]
  | .fst pairTerm =>
      congrArg (Option.map RawTerm.fst)
        (RawTerm.optRename_congr renamingsAreEquivalent pairTerm)
  | .snd pairTerm =>
      congrArg (Option.map RawTerm.snd)
        (RawTerm.optRename_congr renamingsAreEquivalent pairTerm)
  | .boolElim scrutinee thenBranch elseBranch => by
      have scrutineeEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent scrutinee
      have thenEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent thenBranch
      have elseEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent elseBranch
      simp only [RawTerm.optRename]
      rw [scrutineeEquality, thenEquality, elseEquality]
  | .natElim scrutinee zeroBranch succBranch => by
      have scrutineeEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent scrutinee
      have zeroEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent zeroBranch
      have succEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent succBranch
      simp only [RawTerm.optRename]
      rw [scrutineeEquality, zeroEquality, succEquality]
  | .natRec scrutinee zeroBranch succBranch => by
      have scrutineeEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent scrutinee
      have zeroEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent zeroBranch
      have succEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent succBranch
      simp only [RawTerm.optRename]
      rw [scrutineeEquality, zeroEquality, succEquality]
  | .listNil => rfl
  | .listCons head tail => by
      have headEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent head
      have tailEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent tail
      simp only [RawTerm.optRename]
      rw [headEquality, tailEquality]
  | .listElim scrutinee nilBranch consBranch => by
      have scrutineeEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent scrutinee
      have nilEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent nilBranch
      have consEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent consBranch
      simp only [RawTerm.optRename]
      rw [scrutineeEquality, nilEquality, consEquality]
  | .optionNone => rfl
  | .optionSome value =>
      congrArg (Option.map RawTerm.optionSome)
        (RawTerm.optRename_congr renamingsAreEquivalent value)
  | .optionMatch scrutinee noneBranch someBranch => by
      have scrutineeEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent scrutinee
      have noneEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent noneBranch
      have someEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent someBranch
      simp only [RawTerm.optRename]
      rw [scrutineeEquality, noneEquality, someEquality]
  | .eitherInl value =>
      congrArg (Option.map RawTerm.eitherInl)
        (RawTerm.optRename_congr renamingsAreEquivalent value)
  | .eitherInr value =>
      congrArg (Option.map RawTerm.eitherInr)
        (RawTerm.optRename_congr renamingsAreEquivalent value)
  | .eitherMatch scrutinee leftBranch rightBranch => by
      have scrutineeEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent scrutinee
      have leftEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent leftBranch
      have rightEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent rightBranch
      simp only [RawTerm.optRename]
      rw [scrutineeEquality, leftEquality, rightEquality]
  | .refl term =>
      congrArg (Option.map RawTerm.refl)
        (RawTerm.optRename_congr renamingsAreEquivalent term)
  | .idJ baseCase witness => by
      have baseEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent baseCase
      have witnessEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent witness
      simp only [RawTerm.optRename]
      rw [baseEquality, witnessEquality]

/-- Applying the identity optional renaming to a raw term yields
`some` of that term unchanged.  Direct structural induction. -/
theorem RawTerm.optRename_identity {scope : Nat} :
    ∀ rawTerm : RawTerm scope,
      rawTerm.optRename OptionalRenaming.identity = some rawTerm
  | .var _      => rfl
  | .unit       => rfl
  | .boolTrue   => rfl
  | .boolFalse  => rfl
  | .natZero    => rfl
  | .natSucc predecessor => by
      have predecessorIdentity := RawTerm.optRename_identity predecessor
      show Option.map RawTerm.natSucc (predecessor.optRename _)
        = some (RawTerm.natSucc predecessor)
      rw [predecessorIdentity]; rfl
  | .lam body => by
      have liftIdentity :
          OptionalRenaming.equiv
            (@OptionalRenaming.identity scope).lift OptionalRenaming.identity :=
        OptionalRenaming.lift_identity_equiv
      have liftedBody :=
        RawTerm.optRename_congr liftIdentity body
      have bodyIdentity := RawTerm.optRename_identity body
      show Option.map RawTerm.lam
            (body.optRename (@OptionalRenaming.identity scope).lift)
        = some (RawTerm.lam body)
      rw [liftedBody, bodyIdentity]; rfl
  | .app function argument => by
      have functionIdentity := RawTerm.optRename_identity function
      have argumentIdentity := RawTerm.optRename_identity argument
      show Option.bind (function.optRename _) (fun f' =>
            Option.bind (argument.optRename _) (fun a' =>
              some (RawTerm.app f' a')))
        = some (RawTerm.app function argument)
      rw [functionIdentity, argumentIdentity]; rfl
  | .pair first second => by
      have firstIdentity := RawTerm.optRename_identity first
      have secondIdentity := RawTerm.optRename_identity second
      show Option.bind (first.optRename _) (fun f' =>
            Option.bind (second.optRename _) (fun s' =>
              some (RawTerm.pair f' s')))
        = some (RawTerm.pair first second)
      rw [firstIdentity, secondIdentity]; rfl
  | .fst pairTerm => by
      have pairIdentity := RawTerm.optRename_identity pairTerm
      show Option.map RawTerm.fst (pairTerm.optRename _)
        = some (RawTerm.fst pairTerm)
      rw [pairIdentity]; rfl
  | .snd pairTerm => by
      have pairIdentity := RawTerm.optRename_identity pairTerm
      show Option.map RawTerm.snd (pairTerm.optRename _)
        = some (RawTerm.snd pairTerm)
      rw [pairIdentity]; rfl
  | .boolElim scrutinee thenBranch elseBranch => by
      have scrutineeIdentity := RawTerm.optRename_identity scrutinee
      have thenIdentity := RawTerm.optRename_identity thenBranch
      have elseIdentity := RawTerm.optRename_identity elseBranch
      show Option.bind (scrutinee.optRename _) (fun s' =>
            Option.bind (thenBranch.optRename _) (fun t' =>
              Option.bind (elseBranch.optRename _) (fun e' =>
                some (RawTerm.boolElim s' t' e'))))
        = some (RawTerm.boolElim scrutinee thenBranch elseBranch)
      rw [scrutineeIdentity, thenIdentity, elseIdentity]; rfl
  | .natElim scrutinee zeroBranch succBranch => by
      have scrutineeIdentity := RawTerm.optRename_identity scrutinee
      have zeroIdentity := RawTerm.optRename_identity zeroBranch
      have succIdentity := RawTerm.optRename_identity succBranch
      show Option.bind (scrutinee.optRename _) (fun s' =>
            Option.bind (zeroBranch.optRename _) (fun z' =>
              Option.bind (succBranch.optRename _) (fun f' =>
                some (RawTerm.natElim s' z' f'))))
        = some (RawTerm.natElim scrutinee zeroBranch succBranch)
      rw [scrutineeIdentity, zeroIdentity, succIdentity]; rfl
  | .natRec scrutinee zeroBranch succBranch => by
      have scrutineeIdentity := RawTerm.optRename_identity scrutinee
      have zeroIdentity := RawTerm.optRename_identity zeroBranch
      have succIdentity := RawTerm.optRename_identity succBranch
      show Option.bind (scrutinee.optRename _) (fun s' =>
            Option.bind (zeroBranch.optRename _) (fun z' =>
              Option.bind (succBranch.optRename _) (fun f' =>
                some (RawTerm.natRec s' z' f'))))
        = some (RawTerm.natRec scrutinee zeroBranch succBranch)
      rw [scrutineeIdentity, zeroIdentity, succIdentity]; rfl
  | .listNil => rfl
  | .listCons head tail => by
      have headIdentity := RawTerm.optRename_identity head
      have tailIdentity := RawTerm.optRename_identity tail
      show Option.bind (head.optRename _) (fun h' =>
            Option.bind (tail.optRename _) (fun t' =>
              some (RawTerm.listCons h' t')))
        = some (RawTerm.listCons head tail)
      rw [headIdentity, tailIdentity]; rfl
  | .listElim scrutinee nilBranch consBranch => by
      have scrutineeIdentity := RawTerm.optRename_identity scrutinee
      have nilIdentity := RawTerm.optRename_identity nilBranch
      have consIdentity := RawTerm.optRename_identity consBranch
      show Option.bind (scrutinee.optRename _) (fun s' =>
            Option.bind (nilBranch.optRename _) (fun n' =>
              Option.bind (consBranch.optRename _) (fun c' =>
                some (RawTerm.listElim s' n' c'))))
        = some (RawTerm.listElim scrutinee nilBranch consBranch)
      rw [scrutineeIdentity, nilIdentity, consIdentity]; rfl
  | .optionNone => rfl
  | .optionSome value => by
      have valueIdentity := RawTerm.optRename_identity value
      show Option.map RawTerm.optionSome (value.optRename _)
        = some (RawTerm.optionSome value)
      rw [valueIdentity]; rfl
  | .optionMatch scrutinee noneBranch someBranch => by
      have scrutineeIdentity := RawTerm.optRename_identity scrutinee
      have noneIdentity := RawTerm.optRename_identity noneBranch
      have someIdentity := RawTerm.optRename_identity someBranch
      show Option.bind (scrutinee.optRename _) (fun s' =>
            Option.bind (noneBranch.optRename _) (fun n' =>
              Option.bind (someBranch.optRename _) (fun sm' =>
                some (RawTerm.optionMatch s' n' sm'))))
        = some (RawTerm.optionMatch scrutinee noneBranch someBranch)
      rw [scrutineeIdentity, noneIdentity, someIdentity]; rfl
  | .eitherInl value => by
      have valueIdentity := RawTerm.optRename_identity value
      show Option.map RawTerm.eitherInl (value.optRename _)
        = some (RawTerm.eitherInl value)
      rw [valueIdentity]; rfl
  | .eitherInr value => by
      have valueIdentity := RawTerm.optRename_identity value
      show Option.map RawTerm.eitherInr (value.optRename _)
        = some (RawTerm.eitherInr value)
      rw [valueIdentity]; rfl
  | .eitherMatch scrutinee leftBranch rightBranch => by
      have scrutineeIdentity := RawTerm.optRename_identity scrutinee
      have leftIdentity := RawTerm.optRename_identity leftBranch
      have rightIdentity := RawTerm.optRename_identity rightBranch
      show Option.bind (scrutinee.optRename _) (fun s' =>
            Option.bind (leftBranch.optRename _) (fun l' =>
              Option.bind (rightBranch.optRename _) (fun r' =>
                some (RawTerm.eitherMatch s' l' r'))))
        = some (RawTerm.eitherMatch scrutinee leftBranch rightBranch)
      rw [scrutineeIdentity, leftIdentity, rightIdentity]; rfl
  | .refl term => by
      have termIdentity := RawTerm.optRename_identity term
      show Option.map RawTerm.refl (term.optRename _)
        = some (RawTerm.refl term)
      rw [termIdentity]; rfl
  | .idJ baseCase witness => by
      have baseIdentity := RawTerm.optRename_identity baseCase
      have witnessIdentity := RawTerm.optRename_identity witness
      show Option.bind (baseCase.optRename _) (fun b' =>
            Option.bind (witness.optRename _) (fun w' =>
              some (RawTerm.idJ b' w')))
        = some (RawTerm.idJ baseCase witness)
      rw [baseIdentity, witnessIdentity]; rfl

/-- Applying a total renaming, then an optional renaming, equals
applying their `afterRenaming` composition directly.  This is the raw
analogue of `RawTerm.rename_compose` extended to the `Option` monad on
the right.  Direct structural induction. -/
theorem RawTerm.rename_optRename {source middle target : Nat}
    (totalRenaming : Renaming source middle)
    (optionalRenaming : OptionalRenaming middle target) :
    ∀ rawTerm : RawTerm source,
      (rawTerm.rename totalRenaming).optRename optionalRenaming
        = rawTerm.optRename
            (OptionalRenaming.afterRenaming totalRenaming optionalRenaming)
  | .var _      => rfl
  | .unit       => rfl
  | .boolTrue   => rfl
  | .boolFalse  => rfl
  | .natZero    => rfl
  | .natSucc predecessor =>
      congrArg (Option.map RawTerm.natSucc)
        (RawTerm.rename_optRename totalRenaming optionalRenaming predecessor)
  | .lam body => by
      have bodyComposition :=
        RawTerm.rename_optRename totalRenaming.lift optionalRenaming.lift body
      have liftSwap :=
        RawTerm.optRename_congr
          (OptionalRenaming.lift_afterRenaming_equiv
            totalRenaming optionalRenaming) body
      show Option.map RawTerm.lam
            ((body.rename totalRenaming.lift).optRename optionalRenaming.lift)
        = Option.map RawTerm.lam
            (body.optRename
              (OptionalRenaming.afterRenaming
                totalRenaming optionalRenaming).lift)
      rw [bodyComposition, liftSwap]
  | .app function argument => by
      have functionComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming function
      have argumentComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming argument
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [functionComposition, argumentComposition]
  | .pair first second => by
      have firstComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming first
      have secondComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming second
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [firstComposition, secondComposition]
  | .fst pairTerm =>
      congrArg (Option.map RawTerm.fst)
        (RawTerm.rename_optRename totalRenaming optionalRenaming pairTerm)
  | .snd pairTerm =>
      congrArg (Option.map RawTerm.snd)
        (RawTerm.rename_optRename totalRenaming optionalRenaming pairTerm)
  | .boolElim scrutinee thenBranch elseBranch => by
      have scrutineeComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming scrutinee
      have thenComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming thenBranch
      have elseComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming elseBranch
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [scrutineeComposition, thenComposition, elseComposition]
  | .natElim scrutinee zeroBranch succBranch => by
      have scrutineeComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming scrutinee
      have zeroComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming zeroBranch
      have succComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming succBranch
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [scrutineeComposition, zeroComposition, succComposition]
  | .natRec scrutinee zeroBranch succBranch => by
      have scrutineeComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming scrutinee
      have zeroComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming zeroBranch
      have succComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming succBranch
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [scrutineeComposition, zeroComposition, succComposition]
  | .listNil => rfl
  | .listCons head tail => by
      have headComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming head
      have tailComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming tail
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [headComposition, tailComposition]
  | .listElim scrutinee nilBranch consBranch => by
      have scrutineeComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming scrutinee
      have nilComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming nilBranch
      have consComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming consBranch
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [scrutineeComposition, nilComposition, consComposition]
  | .optionNone => rfl
  | .optionSome value =>
      congrArg (Option.map RawTerm.optionSome)
        (RawTerm.rename_optRename totalRenaming optionalRenaming value)
  | .optionMatch scrutinee noneBranch someBranch => by
      have scrutineeComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming scrutinee
      have noneComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming noneBranch
      have someComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming someBranch
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [scrutineeComposition, noneComposition, someComposition]
  | .eitherInl value =>
      congrArg (Option.map RawTerm.eitherInl)
        (RawTerm.rename_optRename totalRenaming optionalRenaming value)
  | .eitherInr value =>
      congrArg (Option.map RawTerm.eitherInr)
        (RawTerm.rename_optRename totalRenaming optionalRenaming value)
  | .eitherMatch scrutinee leftBranch rightBranch => by
      have scrutineeComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming scrutinee
      have leftComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming leftBranch
      have rightComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming rightBranch
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [scrutineeComposition, leftComposition, rightComposition]
  | .refl term =>
      congrArg (Option.map RawTerm.refl)
        (RawTerm.rename_optRename totalRenaming optionalRenaming term)
  | .idJ baseCase witness => by
      have baseComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming baseCase
      have witnessComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming witness
      simp only [RawTerm.rename, RawTerm.optRename]
      rw [baseComposition, witnessComposition]

/-- The strengthening operation on raw terms — partial inverse of
`RawTerm.weaken`.  Returns `some t` exactly when the input does not
reference the freshly bound variable. -/
@[reducible]
def RawTerm.strengthen {scope : Nat}
    (rawTerm : RawTerm (scope + 1)) : Option (RawTerm scope) :=
  rawTerm.optRename OptionalRenaming.unweaken

/-- **Round-trip** for raw-term strengthening: weakening then
strengthening recovers the original term.  Reduces to
`rename_optRename` plus `optRename_identity` via the pointwise
equivalence `weaken ; unweaken ≡ identity`. -/
theorem RawTerm.strengthen_weaken {scope : Nat}
    (rawTerm : RawTerm scope) :
    rawTerm.weaken.strengthen = some rawTerm := by
  show (rawTerm.rename Renaming.weaken).optRename OptionalRenaming.unweaken
        = some rawTerm
  have composition :=
    RawTerm.rename_optRename Renaming.weaken
      OptionalRenaming.unweaken rawTerm
  have identityEquivalence :=
    RawTerm.optRename_congr
      (OptionalRenaming.weaken_unweaken_equiv_identity (scope := scope))
      rawTerm
  exact composition.trans
    (identityEquivalence.trans (RawTerm.optRename_identity rawTerm))

/-! ## Optional renaming on types. -/

/-- Apply an optional renaming to a type, threading `Option`
everywhere.  Mirrors `Ty.rename` constructor-for-constructor; the
`Ty.id` constructor delegates to `RawTerm.optRename` for its raw
endpoint fields. -/
def Ty.optRename {level source target : Nat} :
    Ty level source → OptionalRenaming source target → Option (Ty level target)
  | .unit, _ => some .unit
  | .arrow domain codomain, optionalRenaming =>
      Option.bind (domain.optRename optionalRenaming) fun renamedDomain =>
        Option.bind (codomain.optRename optionalRenaming) fun renamedCodomain =>
          some (Ty.arrow renamedDomain renamedCodomain)
  | .piTy domain codomain, optionalRenaming =>
      Option.bind (domain.optRename optionalRenaming) fun renamedDomain =>
        Option.bind (codomain.optRename optionalRenaming.lift) fun renamedCodomain =>
          some (Ty.piTy renamedDomain renamedCodomain)
  | .tyVar position, optionalRenaming =>
      Option.map Ty.tyVar (optionalRenaming position)
  | .sigmaTy firstType secondType, optionalRenaming =>
      Option.bind (firstType.optRename optionalRenaming) fun renamedFirst =>
        Option.bind (secondType.optRename optionalRenaming.lift) fun renamedSecond =>
          some (Ty.sigmaTy renamedFirst renamedSecond)
  | .bool, _ => some .bool
  | .universe universeLevel levelFits, _ =>
      some (Ty.universe universeLevel levelFits)
  | .nat, _ => some .nat
  | .list elementType, optionalRenaming =>
      Option.map Ty.list (elementType.optRename optionalRenaming)
  | .vec elementType length, optionalRenaming =>
      Option.map (fun renamedElement => Ty.vec renamedElement length)
        (elementType.optRename optionalRenaming)
  | .option elementType, optionalRenaming =>
      Option.map Ty.option (elementType.optRename optionalRenaming)
  | .either leftType rightType, optionalRenaming =>
      Option.bind (leftType.optRename optionalRenaming) fun renamedLeft =>
        Option.bind (rightType.optRename optionalRenaming) fun renamedRight =>
          some (Ty.either renamedLeft renamedRight)
  | .id carrier leftEndpoint rightEndpoint, optionalRenaming =>
      Option.bind (carrier.optRename optionalRenaming) fun renamedCarrier =>
        Option.bind (leftEndpoint.optRename optionalRenaming) fun renamedLeft =>
          Option.bind (rightEndpoint.optRename optionalRenaming) fun renamedRight =>
            some (Ty.id renamedCarrier renamedLeft renamedRight)

/-- Pointwise-equivalent optional renamings produce equal results on
every type.  Direct structural induction. -/
theorem Ty.optRename_congr {source target : Nat}
    {firstRenaming secondRenaming : OptionalRenaming source target}
    (renamingsAreEquivalent :
      OptionalRenaming.equiv firstRenaming secondRenaming) :
    ∀ resultType : Ty level source,
      resultType.optRename firstRenaming = resultType.optRename secondRenaming
  | .unit => rfl
  | .arrow domain codomain => by
      have domainEquality :=
        Ty.optRename_congr renamingsAreEquivalent domain
      have codomainEquality :=
        Ty.optRename_congr renamingsAreEquivalent codomain
      simp only [Ty.optRename]
      rw [domainEquality, codomainEquality]
  | .piTy domain codomain => by
      have domainEquality :=
        Ty.optRename_congr renamingsAreEquivalent domain
      have codomainEquality :=
        Ty.optRename_congr
          (OptionalRenaming.lift_equiv renamingsAreEquivalent) codomain
      simp only [Ty.optRename]
      rw [domainEquality, codomainEquality]
  | .tyVar position =>
      congrArg (Option.map Ty.tyVar) (renamingsAreEquivalent position)
  | .sigmaTy firstType secondType => by
      have firstEquality :=
        Ty.optRename_congr renamingsAreEquivalent firstType
      have secondEquality :=
        Ty.optRename_congr
          (OptionalRenaming.lift_equiv renamingsAreEquivalent) secondType
      simp only [Ty.optRename]
      rw [firstEquality, secondEquality]
  | .bool => rfl
  | .universe _ _ => rfl
  | .nat => rfl
  | .list elementType =>
      congrArg (Option.map Ty.list)
        (Ty.optRename_congr renamingsAreEquivalent elementType)
  | .vec elementType length =>
      congrArg (Option.map (fun renamedElement => Ty.vec renamedElement length))
        (Ty.optRename_congr renamingsAreEquivalent elementType)
  | .option elementType =>
      congrArg (Option.map Ty.option)
        (Ty.optRename_congr renamingsAreEquivalent elementType)
  | .either leftType rightType => by
      have leftEquality :=
        Ty.optRename_congr renamingsAreEquivalent leftType
      have rightEquality :=
        Ty.optRename_congr renamingsAreEquivalent rightType
      simp only [Ty.optRename]
      rw [leftEquality, rightEquality]
  | .id carrier leftEndpoint rightEndpoint => by
      have carrierEquality :=
        Ty.optRename_congr renamingsAreEquivalent carrier
      have leftEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent leftEndpoint
      have rightEquality :=
        RawTerm.optRename_congr renamingsAreEquivalent rightEndpoint
      simp only [Ty.optRename]
      rw [carrierEquality, leftEquality, rightEquality]

/-- Applying the identity optional renaming to a type yields `some` of
that type unchanged. -/
theorem Ty.optRename_identity {scope : Nat} :
    ∀ resultType : Ty level scope,
      resultType.optRename OptionalRenaming.identity = some resultType
  | .unit => rfl
  | .arrow domain codomain => by
      have domainIdentity := Ty.optRename_identity domain
      have codomainIdentity := Ty.optRename_identity codomain
      show Option.bind (domain.optRename _) (fun d' =>
            Option.bind (codomain.optRename _) (fun c' =>
              some (Ty.arrow d' c')))
        = some (Ty.arrow domain codomain)
      rw [domainIdentity, codomainIdentity]; rfl
  | .piTy domain codomain => by
      have domainIdentity := Ty.optRename_identity domain
      have liftIdentity :
          OptionalRenaming.equiv
            (@OptionalRenaming.identity scope).lift OptionalRenaming.identity :=
        OptionalRenaming.lift_identity_equiv
      have codomainLifted :=
        Ty.optRename_congr liftIdentity codomain
      have codomainIdentity := Ty.optRename_identity codomain
      show Option.bind (domain.optRename _) (fun d' =>
            Option.bind
              (codomain.optRename (@OptionalRenaming.identity scope).lift)
              (fun c' => some (Ty.piTy d' c')))
        = some (Ty.piTy domain codomain)
      rw [domainIdentity, codomainLifted, codomainIdentity]; rfl
  | .tyVar _ => rfl
  | .sigmaTy firstType secondType => by
      have firstIdentity := Ty.optRename_identity firstType
      have liftIdentity :
          OptionalRenaming.equiv
            (@OptionalRenaming.identity scope).lift OptionalRenaming.identity :=
        OptionalRenaming.lift_identity_equiv
      have secondLifted :=
        Ty.optRename_congr liftIdentity secondType
      have secondIdentity := Ty.optRename_identity secondType
      show Option.bind (firstType.optRename _) (fun f' =>
            Option.bind
              (secondType.optRename (@OptionalRenaming.identity scope).lift)
              (fun s' => some (Ty.sigmaTy f' s')))
        = some (Ty.sigmaTy firstType secondType)
      rw [firstIdentity, secondLifted, secondIdentity]; rfl
  | .bool => rfl
  | .universe _ _ => rfl
  | .nat => rfl
  | .list elementType => by
      have elementIdentity := Ty.optRename_identity elementType
      show Option.map Ty.list (elementType.optRename _)
        = some (Ty.list elementType)
      rw [elementIdentity]; rfl
  | .vec elementType length => by
      have elementIdentity := Ty.optRename_identity elementType
      show Option.map (fun renamedElement => Ty.vec renamedElement length)
            (elementType.optRename _)
        = some (Ty.vec elementType length)
      rw [elementIdentity]; rfl
  | .option elementType => by
      have elementIdentity := Ty.optRename_identity elementType
      show Option.map Ty.option (elementType.optRename _)
        = some (Ty.option elementType)
      rw [elementIdentity]; rfl
  | .either leftType rightType => by
      have leftIdentity := Ty.optRename_identity leftType
      have rightIdentity := Ty.optRename_identity rightType
      show Option.bind (leftType.optRename _) (fun l' =>
            Option.bind (rightType.optRename _) (fun r' =>
              some (Ty.either l' r')))
        = some (Ty.either leftType rightType)
      rw [leftIdentity, rightIdentity]; rfl
  | .id carrier leftEndpoint rightEndpoint => by
      have carrierIdentity := Ty.optRename_identity carrier
      have leftIdentity := RawTerm.optRename_identity leftEndpoint
      have rightIdentity := RawTerm.optRename_identity rightEndpoint
      show Option.bind (carrier.optRename _) (fun c' =>
            Option.bind (leftEndpoint.optRename _) (fun l' =>
              Option.bind (rightEndpoint.optRename _) (fun r' =>
                some (Ty.id c' l' r'))))
        = some (Ty.id carrier leftEndpoint rightEndpoint)
      rw [carrierIdentity, leftIdentity, rightIdentity]; rfl

/-- Total renaming followed by optional renaming equals the
`afterRenaming` composition.  Direct structural induction; the binder
cases use `lift_afterRenaming_equiv` plus `Ty.optRename_congr`. -/
theorem Ty.rename_optRename {source middle target : Nat}
    (totalRenaming : Renaming source middle)
    (optionalRenaming : OptionalRenaming middle target) :
    ∀ resultType : Ty level source,
      (resultType.rename totalRenaming).optRename optionalRenaming
        = resultType.optRename
            (OptionalRenaming.afterRenaming totalRenaming optionalRenaming)
  | .unit => rfl
  | .arrow domain codomain => by
      have domainComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming domain
      have codomainComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming codomain
      simp only [Ty.rename, Ty.optRename]
      rw [domainComposition, codomainComposition]
  | .piTy domain codomain => by
      have domainComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming domain
      have codomainComposition :=
        Ty.rename_optRename totalRenaming.lift optionalRenaming.lift codomain
      have liftSwap :=
        Ty.optRename_congr
          (OptionalRenaming.lift_afterRenaming_equiv
            totalRenaming optionalRenaming) codomain
      show Option.bind ((domain.rename totalRenaming).optRename optionalRenaming)
            (fun d' =>
              Option.bind
                ((codomain.rename totalRenaming.lift).optRename
                  optionalRenaming.lift)
                (fun c' => some (Ty.piTy d' c')))
        = Option.bind (domain.optRename _) (fun d' =>
            Option.bind
              (codomain.optRename
                (OptionalRenaming.afterRenaming totalRenaming optionalRenaming).lift)
              (fun c' => some (Ty.piTy d' c')))
      rw [domainComposition, codomainComposition, liftSwap]
  | .tyVar _ => rfl
  | .sigmaTy firstType secondType => by
      have firstComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming firstType
      have secondComposition :=
        Ty.rename_optRename totalRenaming.lift optionalRenaming.lift secondType
      have liftSwap :=
        Ty.optRename_congr
          (OptionalRenaming.lift_afterRenaming_equiv
            totalRenaming optionalRenaming) secondType
      show Option.bind
            ((firstType.rename totalRenaming).optRename optionalRenaming)
            (fun f' =>
              Option.bind
                ((secondType.rename totalRenaming.lift).optRename
                  optionalRenaming.lift)
                (fun s' => some (Ty.sigmaTy f' s')))
        = Option.bind (firstType.optRename _) (fun f' =>
            Option.bind
              (secondType.optRename
                (OptionalRenaming.afterRenaming totalRenaming optionalRenaming).lift)
              (fun s' => some (Ty.sigmaTy f' s')))
      rw [firstComposition, secondComposition, liftSwap]
  | .bool => rfl
  | .universe _ _ => rfl
  | .nat => rfl
  | .list elementType =>
      congrArg (Option.map Ty.list)
        (Ty.rename_optRename totalRenaming optionalRenaming elementType)
  | .vec elementType length =>
      congrArg
        (Option.map (fun renamedElement => Ty.vec renamedElement length))
        (Ty.rename_optRename totalRenaming optionalRenaming elementType)
  | .option elementType =>
      congrArg (Option.map Ty.option)
        (Ty.rename_optRename totalRenaming optionalRenaming elementType)
  | .either leftType rightType => by
      have leftComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming leftType
      have rightComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming rightType
      simp only [Ty.rename, Ty.optRename]
      rw [leftComposition, rightComposition]
  | .id carrier leftEndpoint rightEndpoint => by
      have carrierComposition :=
        Ty.rename_optRename totalRenaming optionalRenaming carrier
      have leftComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming leftEndpoint
      have rightComposition :=
        RawTerm.rename_optRename totalRenaming optionalRenaming rightEndpoint
      simp only [Ty.rename, Ty.optRename]
      rw [carrierComposition, leftComposition, rightComposition]

/-- The strengthening operation on types — partial inverse of `Ty.weaken`. -/
@[reducible]
def Ty.strengthen {scope : Nat}
    (resultType : Ty level (scope + 1)) : Option (Ty level scope) :=
  resultType.optRename OptionalRenaming.unweaken

/-- **Round-trip** for type strengthening: weakening then strengthening
recovers the original type.  Same proof shape as
`RawTerm.strengthen_weaken` — composition + identity equivalence. -/
theorem Ty.strengthen_weaken {scope : Nat}
    (resultType : Ty level scope) :
    resultType.weaken.strengthen = some resultType := by
  show (resultType.rename Renaming.weaken).optRename OptionalRenaming.unweaken
        = some resultType
  have composition :=
    Ty.rename_optRename Renaming.weaken
      OptionalRenaming.unweaken resultType
  have identityEquivalence :=
    Ty.optRename_congr
      (OptionalRenaming.weaken_unweaken_equiv_identity (scope := scope))
      resultType
  exact composition.trans
    (identityEquivalence.trans (Ty.optRename_identity resultType))

/-! ## Strengthening smoke tests. -/

namespace SmokeTestStrengthen

/-- Strengthening the variable that *is* the freshly bound one fails. -/
example :
    (RawTerm.var (scope := 1) ⟨0, Nat.zero_lt_succ 0⟩).strengthen = none :=
  rfl

/-- Strengthening unit succeeds. -/
example :
    (@RawTerm.unit 1).strengthen = some (@RawTerm.unit 0) :=
  rfl

/-- Strengthening a weakening of unit recovers unit. -/
example :
    (@RawTerm.unit 0).weaken.strengthen = some RawTerm.unit :=
  RawTerm.strengthen_weaken RawTerm.unit

/-- Strengthening a weakening of a closed lambda recovers the lambda. -/
example :
    (RawTerm.lam (RawTerm.var (scope := 1) ⟨0, Nat.zero_lt_succ 0⟩)).weaken.strengthen
      = some (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ 0⟩)) :=
  RawTerm.strengthen_weaken
    (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ 0⟩))

/-- Strengthening `Ty.unit` succeeds at any scope. -/
example :
    (@Ty.unit 0 1).strengthen = some (@Ty.unit 0 0) :=
  rfl

/-- Strengthening `Ty.bool` succeeds. -/
example :
    (@Ty.bool 0 1).strengthen = some (@Ty.bool 0 0) :=
  rfl

/-- Strengthening a weakening of arrow recovers arrow. -/
example :
    (Ty.arrow (@Ty.unit 0 0) Ty.bool).weaken.strengthen
      = some (Ty.arrow Ty.unit Ty.bool) :=
  Ty.strengthen_weaken (Ty.arrow Ty.unit Ty.bool)

/-- Strengthening fails when the type variable references the dropped
position.  `Ty.tyVar ⟨0, _⟩` at scope 1 cannot strengthen to scope 0. -/
example :
    (Ty.tyVar (level := 0) ⟨0, Nat.zero_lt_succ 0⟩).strengthen = none :=
  rfl

/-- Strengthening succeeds for an open arrow whose domain uses a higher
type variable, after weakening from scope 1.  -/
example :
    (Ty.arrow (level := 0)
      (Ty.tyVar ⟨0, Nat.zero_lt_succ 0⟩) Ty.bool).weaken.strengthen
      = some (Ty.arrow (Ty.tyVar ⟨0, Nat.zero_lt_succ 0⟩) Ty.bool) :=
  Ty.strengthen_weaken
    (Ty.arrow (Ty.tyVar ⟨0, Nat.zero_lt_succ 0⟩) Ty.bool)

end SmokeTestStrengthen

end LeanFX.Syntax
